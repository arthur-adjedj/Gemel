#import "@preview/curryst:0.5.1": rule, prooftree
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/xarrow:0.4.0"

#let mathpar(
  numbering: auto,
  row-gutter: 3em, // can be set to 'auto'
  column-gutter: 2.5em,
  ..children
) = layout(bounds => {
  // Resolve parameters
  let numbering = if numbering == auto { math.equation.numbering } else { numbering }
  let row-gutter = if row-gutter == auto { par.leading } else { row-gutter.to-absolute() }
  let column-gutter = column-gutter.to-absolute()
  let children = children.pos().map(child => [#child])

  // Spread children into lines
  let widths = children.map(child => measure(child).width)
  let lines = ((children: (), remaining: bounds.width),)
  for (child, width) in children.zip(widths) {
    if (
      child.func() == linebreak or
      (lines.last().remaining - width) / (lines.last().children.len() + 2) < column-gutter
    ){
      lines.push((children: (), remaining: bounds.width))
    }

    if child.func() != linebreak {
      lines.last().children.push(child)
      lines.last().remaining -= width
    }
  }

  // Layout children in math mode for baseline alignment
  math.equation(numbering: numbering, block: true,
    for (i, line) in lines.enumerate() {
      let space = h(line.remaining / (line.children.len() + 1))
      par(leading: row-gutter, space + line.children.join(space) + space)
      if i != lines.len() - 1 { linebreak(); v(row-gutter) }
    }
  )
})
// #let rule-set(column-gutter: 3em, row-gutter: 5em, ..rules) = {
//   set par(leading: row-gutter)
//   block(rules.pos().map(box.with(fill: gray)).join(h(column-gutter, weak: true)))
//   v(row-gutter)
// }

#import "@preview/lemmify:0.1.8": *

#let(theorem, lemma, example, proof, rules: thm-rules) = default-theorems("thm-group", lang: "en", thm-numbering: thm-numbering-linear)
#show: thm-rules

#set text(size:11.5pt)
#set page(numbering: "1", margin: 6em)
#set par(first-line-indent: 1.5em, justify: true)
#set cite(form: "prose", style: "citation-style.csl",)
#set quote(block: true)
#show quote: set pad(top : -1.5em, bottom : -0.5em)
#show math.equation.where(block: true): set par(leading: 2em)
#let aa(body) = text(fill:red, "AA: " + body)
#let yf(body) = text(fill:purple, "YF: " + body)
#let nt(body) = text(fill:red.lighten(20%), "NT: " + body)
#set raw(syntaxes: "Lean.sublime-syntax")
#show raw.where(block: true): block.with(breakable: false)
#show raw.where(block: false): box.with()
#set block(spacing: 2em)
#let ie= emph[i.e.,]
#let eg= emph[e.g.,]

#let univ = `Type`
#let lam(x,A,t) = $λ (#x : #A) mapsto #t$
#let pi(x,A,B) = $(#x : #A) -> #B$
#let app(f,t) = $f space t$
#set heading(numbering: "1.1")

#let Gemel = text(weight:"bold","Gemel")

#let appendix(body) = {
  set heading(numbering: "A", supplement: [Appendix])
  counter(heading).update(0)
  body
}

#align(center)[
  #title[Modular programs and proofs in Lean]
  Internship report \
  Arthur Adjedj\
  M2 MPRI, Université Paris-Saclay, ENS Paris-Saclay \ 
  Supervised by Yannick Forster in the Cambium team, INRIA Paris, 
]

#let abstract_margins = (left : 0.5cm, right: 0.5cm)

#let abstract(body, margin : 0.5cm) = {
  block(inset: (left: margin, right : margin))[#align(center)[
    #set align(left)
    #set par(justify: true)
    #set text(size: 11pt)
    #body
  ]]}

// #abstract[Interactive theorem provers (ITPs) do not easily allow users to adapt and extend existing codebases without either changing the original code or duplicating it.
// The pattern of extending definitions occurs particularly often in 
// programming language theory, type theory, and program verification,
// leading to a lot of code duplication and high maintenance burden.
// Existing approaches to this problem either require encoding data-types as complicated expressions—obfuscating the development— or rely on custom intermediate representations of syntax via meta-programming facilities, which were underdeveloped in most ITPs until recently.\ 
// We develop #Gemel #footnote[Pronounced gem·​el, describes pairs of trees that have undergone inosculation, i.e the act of connecting and merging with one another. ] : a tool implemented in Lean 4 to produce modular code, leveraging the strengths of dependent types and modern meta-programming techniques]

// #abstract(margin: 0.3cm)[#emph[*Note.* This research topic has been collabaratively developed by Arthur Adjedj and Yannick Forster. Arthur Adjedj was supervised by Yannick Forster and hosted in the Cambium team at the Centre Inria de Paris during a five-month internship.]]

= Summary

== General context
// What is the report about ? Where does the problem come from ? What is the state of the art in that area ?
Interactive Theorem Provers (ITPs), also known as proof assistants, are tools which allow for the development and verification of formal proofs. 
ITPs can be used to provide very strong gaurantees for software-in particular the complete absence of bugs-, which is why it's the tool of choice of several projects to verify real-world softare (@Leroy-Compcert-CACM, @Cedar). Beyond their use for software verification, ITPs have been used to formalize landmark theorems in mathematics (@Gonthier2007, @Gonthier2013), and their use is on the rise in the mathematical community, with big developments (@mathlib2020) getting more and more public attention (@quantabook). 

ITPs have particular issues regarding reusability of its definitions. For example, @Adjedj2024 formalized a dependent type theory some years ago. Several projects have since sprouted from this work, forking the 30 thousand lines of code repository to extend on the type system formalized (@Pedrot2024, @Subtyping2024), thus duplicating the codebase. In parallel, the initial repository got refactored to make the formalisation cleaner and easier to work on. Because of this code duplication, the benefits of the refactoring never reached the extensions, and would now take a lot of efforts to integrate into them. \
The issue of modularity and code maintenance is not isolated to ITPs, and is coined as the *expression problem* (@Wadler98) in the sphere of programming languages: 
#quote[“The goal is to define a datatype by cases, where one can add new cases to the datatype and new functions over the datatype, _without recompiling existing code_.”] 
Reusing and adapting existing data structures and programs modularly is a challenge for which few solutions have been produced over the years in industrial programming languages (@ObjAlgEP). The issue is exacerbated in ITPs, where in addition to programs, one needs to adapt proofs as well. In ITPs (which we focus on for the rest of the report), solutions range from making various encodings-such as Church encodings (@Jansen2013)-in which some notion of modularity comes internally "for free" (@Delaware2013, @Pyrosome), to relying on meta-programming to achieve their goals (@Forster2020, @Rocqet). Both approaches have had limited results until now, the former in part due to a lack of expressivity from the encodings used, the latter in part due to limitations in the meta-programming tools available during those developments. We discuss each tool's limitations in more depth in the related works (@related-works)


== Research problem

// What specific question(s) have you studied ? What motivates the question ? What are its applications/consequences ? Is it a new problem ? Why did you choose this problem ?

The original expression problem from 1998 does not fit the constraints of modern ITPs, in particular with regards to avoiding recompiling existing code. Indeed, computers have since become fast enough, and memory storage big enough, that the constraints of compilation time or executable sizes are not central issues anymore. We instead focus our efforts on reducing the burden of maintainance by providing better modularity in ITPs. As such, we focus on allowing users to extend datatypes by adding new constructors to them, as well as extending theorems and definitions which rely on them to hold for the new datatype. Such extensions should be doable on independent formalisations that were not made with our framework's constraints in mind.


== Our contribution
// What is your answer to the research problem ? Please remain at a high level ; technical details should be given in the main body of the report. Pay special attention to the description of the scientific approach. 

We present #Gemel#footnote[https://github.com/arthur-adjedj/Gemel], a new framework for writing modular code, written in the Lean 4 proof assistant. This library aims to provide a user-experience as similar to writing regular non-modular code as possible. This objective is achieved by avoiding the use of any internal encodings, manipulating Lean's concrete and abstract syntax trees directly, and making use of the powerful meta-programming capabilities of the language. #Gemel declarations integrate all the features of regular Lean declaration such as dependent pattern-matching, tactic-based proofs and well-founded recursion. #Gemel also allows extending a previous formalization that was not intended for extensions in mind, which we consider to be a crucial feature for the tool's adoption for real-world use-cases.

== Arguments supporting its validity

// What is the evidence that your solution is a good solution ? (Experi- ments ? Proofs ?) Comment on the robustness of your solution : does it rely on assumptions, and if so, to what extent ?

To demonstrate the capacities of our system, we present two case-studies#footnote[https://github.com/arthur-adjedj/lean-stlc/]#footnote[https://github.com/arthur-adjedj/PyrosomeLeanCaseStudy/] implemented using #Gemel. 

The first takes an existing, independent formalization (@leanstlc) of the Simply-Typed Lambda Calculus (STLC), and extends it with new constructions, modularly extending key results of the original formalisation, such as strong normalisation, about the extended calculusi. Formalisations of STLC form a recurring case-study in previous works on modularity in ITPs, ours is the only one showing the capacity to build such extended formalisations "after the fact", i.e on an independent formalisation that was not made with modularity in mind. 

The second case study consists of a construction of STLC and a Continuation-Passing Style (CPS) calculus, as well as a translation pass from the former to the latter. The formalisation then extends both STLC and CPS with various constructions, and extends the translation pass between the respective extensions. This reproduces the central case study produced by @Pyrosome in our own framework, without the need for any encodings. 

Together, these two case-studies serve to show that the fundamentally basic ideas behind #Gemel are powerful enough to scale up to all features provided by previous tools, as well as allowing one to to extend an independent formalisation after the fact, which is unique to our framework. 

== Summary and future work

We contribute a ready-to-use tool to easily extend formalisation. That tool is fairly complete in its original objective, as shown by our case-studies, though it exposes some limitations and a potential for further improvements. Improvements include the capacity to handle horizontal extensions, i.e the ability to add new fields to an existing constructor of a datatype, rather than just the ability to add new constructors entirely. A good next step would be to make the tool mature enough to be used in real world cases such as Lean's computer science library CSLib (@cslib) , where e.g various type-systems formalisation could benefit from the tool.
#pagebreak()
// What did you contribute to the area ? What comes next ? What is a good next step or question ?


// We present #Gemel, a new library, written in the Lean 4 proof assistant, which exposes new syntax for users to extend previous data-types and declarations modularly, using meta-programming techniques. This in particular allows one to extend a previous formalization that was not intended for such uses. To demonstrate this, we present two case-study,with one taking an existing, independent formalization of the Simply-Typed Lambda Calculus (STLC), and extending it with new constructions, modularly proving the strong normalization of the new calculuses, and another reimplementing Pyrosome's main case-study, which builds a formalization of STLC and a translation pass to a call-passing-style (CPS) calculus, as well as extensions for both STLC and CPS, with extended translations between their respective extensions.

// Formal presentation of extensions
// 
// This section presents the technical details of the Gemel implementation. The main three contributions are 1. A system for partially mapping terms 2. a DSL command for defining an inductive type as an extension to another based on that produces the appropriate partial mappings between the two 3. a DSL for defining definitions/theorems as extensions of others, thus reusing the appropriate information "after the fact".


= Representation of modular syntax
<sec2>

We first examine existing solutions to producing modular code in ITPs, showing their respective strength and weaknesses, before explaining our framework for modularly extending syntax in #Gemel.

== Existing solutions

Solutions to the modularity problem in ITPs appear in two flavors: some tools work by encoding the datatypes manipulated in a framework which natively allows for some form of modularity (@Delaware2013, @Pyrosome), others rely on meta-programming to achieve their goals. \ 
Encodings have yet to become viable in dependently-typed ITPs. All existing implementations incur an abstraction cost by leaking internal detail, i.e users must manipulate these encodings explicitly rather than interact with them the same way they would with regular inductive types. Furthermore, existing encodings are yet to be expressive enough to encode every datatypes that are native to such systems. Because of this, the possibility to allow for extensions after the fact, which would entail translating an initial formalisation into something relying on the needed encoding, becomes more limited and challenging. \ 
On the meta-programming side, Rocqet (@Rocqet) and Rocq à la carte (@Forster2020) both expose some additional syntax for the user to write in order to produce modular formalisms.
Rocqet's design focuses on compiler verification specifically, structuring code around building and extending "families", i.e bundles of inductive definitions and fixpoint functions, to construct translation passes between the extende . Rocq à la Carte aims to be a general framework for modular work, a scope that our project shares. We focus here on Rocq à la Carte's design here, with a deeper explanation of other frameworks in the Related Works (@related-works).

Rocq à la Carte's design centers on manipulating user-defined datatypes constructed through the merging of inductive functors:
```lean
inductive ExpVar (exp : Type) where
  | var : Nat → ExpVar exp

inductive ExpLam (exp : Type) where
  | app : exp → exp → ExpLam exp
  | lam : exp → ExpLam exp 
  
inductive Exp₁ where
  | expvar : ExpVar Exp₁ → Exp₁
  | explam : ExpLam Exp₁ → Exp₁
```
Here, `ExpVar` and `ExpLam`, referred to as "feature functors", are parametrised by a type `exp`, and can be used to instantiate an inductive type with the desired features, `Exp₁` is such an example. 
Functions over types defined using feature functors can then be defined by first constructing said functions over the various feature functors, and composing them in an appropriate recursive function for the composed type:
```lean
def ExpLam.count (f : exp → Nat) : ExpLam exp → Nat
  | app e₁ e₂ => (f e₁) + (f e₂)
  | lam e => f e

def ExpVar.count (f : exp → Nat) : ExpVar exp → Nat
  | var _ => 1

def Exp₁.count : Exp₁ → Nat -- Error: Failed to show termination
  | expvar v => ExpVar.count Exp₁.count v
  | explam v => ExpLam.count Exp₁.count v
```
However, replicating (and extending on) this technique to bring modular tooling in the Lean proof assistant is not really feasable. The previous code snippet would work in Rocq, but throws a non-termination error in Lean. Indeed, functions in ITPs are required to be total for the sake of ensuring the soundness of the type-system (i.e the inability to prove `False`). Every popular ITP ensures this restriction differently (this is discussed more in depth in @recursion), but an important divergence between Rocq and Lean is that Rocq's system for detecting structural recursion works up to reduction, whereas Lean doesn't. This feature is paramount to Rocq à la Carte's method for producing modular code, and cannot be easily replicated in Lean due to divergences in the Lean's design decisions.

== Our solution
One core objective of #Gemel is the ability to extend a formalisation or program after the fact, no matter the shape it may have been given by a former implementor. In order to do so, we shift our focus from encodings "à la Carte" to making use of the existing metaprogramming APIs provided by Lean, manipulating its core syntax directly. In particular, we want to be able to translate any definition or theorem written about one inductive type into one that instead mentions an extended version of said type. We refer to this translation function, written onwards as $⟦\_⟧$, as a *modular map*. 

For now, let's consider a degenerate example: a user has written two separate definitions of natural numbers that are the exact same in shape, and would like to translate a function using the former into one that uses the latter:

#align(center)[
#grid(columns: 2)[
```lean
inductive Nat₁ where        
  | Z : Nat₁
  | S : Nat₁ → Nat₁

def Nat₁.add : Nat₁ → Nat₁ → Nat₁        
  | n,Z => n
  | n, S k => S (add n k)
```][
```lean
inductive Nat₂ where
  | Z : Nat₂
  | S : Nat₂ → Nat₂

def Nat₂.add := ?
```
]]

A modular mapping function could traverse the definition of `Nat₁.add`, and transform every occurence of `Nat₁` to `Nat₂`. Similarly, each constructor could get mapped accordingly, i.e `Nat₁.Z` maps to `Nat₂.Z` and similarly for `S`. Such a translation need only be structural, keeping the shape of the original function (e.g $⟦ λ a : A. t  ⟧ ::= λ a : ⟦ A ⟧. ⟦ t ⟧$) while transforming the constants present inside it.  
As such, a modular map depends on a *mapping context*, i.e a context which maps some constants in the global environment to new terms.
Furthermore, users may want to choose which mapping context they are working in at a given moment. To allow for this, #Gemel adds two new Lean commands for opening, importing and closing a mapping context:
```lean
modular <mapping context name> (imports := <optional imports>)

... --modular extensions

end modular <mapping context name>
```
To quickly showcase #Gemel's syntax, `Nat₂` can be defined as an extension of `Nat₁` with no additional constructors, and translate its `add` function as follows:
```lean
modular showcase

mod inductive Nat₂ extends Nat₁

mod def Nat₂.add extends Nat₁.add 

modular end showcase
```
The following sections showcase how #Gemel make use of this system of modular maps to achieve its goal of providing a user-friendly system of modular extensions.

= Inductive Types and recursors
<ind_extension>

We hereon make use of our system of modular maps to provide users with ways to modularly extend previously defined programs and formalizations. From a user perspective, a Lean program mainly consists of defining new datatypes types, definitions and theorems. The main way to construct new datatypes in Lean is by defining new inductive types (@Coquand1990). This section focuses on how #Gemel allows users to extend inductive definitions through addition of new constructors. 

== Inductive types in type theory
// With this framework constructed, we may now use it to construct practical partial mappings, by producing useful mapping contexts. Since most constants in proof assistants are either inductive constructions (i.e an inductive type, a constructor or a recursor), or a declaration (i.e a definition or theorem), we first focus on inductive extensions, and then look at how they can be used to construct useful declaration extensions.\
First, let us look at what an inductive type is. The general intuition of an inductive type is that it is a regular datatype, of which terms can be constructed by using recursors, and which can be eliminated through the use of a recursor, i.e an induction principle. \ 
Inductive types are shaped as follows:

#let ctor = $bold("ctor")$
#let newctor = $bold("newctor")$
#let motive = $bold("motive")$
#let minor = $bold("minor")$
$bold("inductive") "Ind"  accent((p : P),→) : accent((i : I),→) → univ bold("where")\
space | ctor_1 : accent((a_1 : A_1),→) → I space accent(p,→) space  accent(d_1,→) \
space space space space ...\
space | ctor_n : accent((a_n : A_n),→) → I space accent(p,→) space accent(d_n,→) $

An inductive type is composed of a number of different components: A list of parameters $accent((p : P),->)$ which are uniform in that they stay the same in every occurrence of the type in its constructors, a telescope of indices $accent((i : I),->)$ that may vary in each occurrence, and a list of constructors for this type. Each constructor contains a list of fields  living over the context formed by the parameters, and instantiates the indices of the inductive type they inhabit in a context containing those fields. Basic examples of inductive types include the natural numbers, lists, and vectors (i.e list indexed by their lengths):

#align(center)[
#grid(columns: 2)[
```lean
inductive Nat : Type where   
  | Z : Nat
  | S : Nat → Nat
```][
```lean
inductive Vec (A : Type) : Nat → Type where
  | nil     : Vec A Z
  | cons {n}: A → Vec A n → Vec A (S n)
```]
]
#let Nat = `Nat`
#let Vec = `Vec`
#let Z   = `Z`
#let S   = `S`
#let NatRec = `Nat.rec`
#let P = `P`
#let PZ = `PZ`
#let PS = `PS`
`Nat` is an inductive type with no parameters and no indices, as well as two constructors `Z` and #S, the first one containing no field and the second containing one recursive occurrence of #Nat as its sole field. In comparison, #Vec is an inductive type which has one parameter `A`, is indexed by a natural number, and has two constructors. The former has no field and instantiate its index at 0, the second has 3 fields with one recursive one. `Vec A n` can be interpreted as the type of lists of `A` of size `n`.

To each inductive type is associated a recursor, i.e a way to eliminate a term of that type. For example, the recursor for `Nat` has the following type:\
$NatRec : (motive : Nat → univ) → motive #Z → ((n : Nat) → motive n → motive (#S n)) → (t : Nat) → motive t$\
The existence of that recursor can be interpreted as the statement that, given a predicate #motive on natural numbers, an instance of that predicate on 0, and for every n, an instance of $motive (#S n)$ given $motive n$, that predicate holds for any natural number $t$. This corresponds exactly to the regular induction principle for natural numbers. Furthermore, recursors hold computational content in that they may reduce when applied to a constructor. For example, the two reduction rules for #NatRec are as follows:
$
NatRec #P #PZ #PS #Z arrow.r.squiggly #PZ 
\ 
NatRec #P #PZ #PS (#S n) arrow.r.squiggly #PS n space (NatRec #P #PZ #PS n)
$


== Inductive types in #Gemel
<extendInd>

With the general structure of an inductive type in mind, we can now consider ways in which one may extend an inductive type into another. #Gemel provides a new Lean command which, given an inductive and new constructors, constructs another inductive type which extends the original one with these new constructors, adding the relevant mappings between from the first to the second. The syntax is as follows:
```lean
mod inductive <new inductive> extends <old inductive> where
  <new constructors>
```
Consider the following example: A user defines a notion of a variable type `Var`, which only has one constructor consisting of a natural number. 
```lean
inductive Var where
  | var : Nat → Var
```
This representation for variables is common in both imperative and functional intermediate representations of programs. After producing an extensive API for this type, one may want to use this notion of variables as part of another type. Consider a new type `Term` which corresponds to that of a lambda-calculus. Such a calculus is constructed using variables, lambdas and applications. Such a type can be defined by extending the variable type as follows:
```lean
mod inductive Term extends Var where
  | lam : Term → Term
  | app : Term → Term → Term

#print Term
/- inductive Term : Type
   constructors:
     Term.lam : Term → Term
     Term.app : Term → Term → Term
     Term.var : Nat → Term -/

``` 
Similarly, one may want to extend the lambda-calculus with other constructs, such as booleans. Since `Term` is also just an inductive type, it can itself be extended with new constructions:
```lean
mod inductive BoolTerm extends Term where
  | true  : BoolTerm
  | false : BoolTerm
  --- if     c   then   a   else   b
  | ite : BoolTerm → BoolTerm → BoolTerm → BoolTerm

-- λ b => if b then false else true
#check lam (ite (var 0) false true) -- BoolTerm
```
Internally, after constructing this new type, #Gemel adds the relevant mappings from the old type to the new one in the mapping context: 
Consider the previous example of `Var` and `Term`, their respective recursors are as follows:
```lean
Var.rec  : (motive : Var  → Type) → ((a : Nat) → motive (var a)) → 
  (t : Var) → motive t
Term.rec : (motive : Term → Type) → ((a : Nat) → motive (var a)) → 
  ((a : Term) → motive a → motive (lam a)) → 
  ((f t : Term) → motive f → motive t → motive (app f t)) → 
  (t : Term) → motive t
```

Consider a pretty-printing function for `Var`, defined explicitly using the type's recursor: 
```lean
def Var.repr (t : Var) : String := Var.rec (fun _ => String) (fun x => s!"{x}") t
```
We see that the motive, existing minor for `var` and the major `t` can be translated into a `Term.rec` call as follows: 
```lean
def Term.repr (t : Term) : String := Term.rec (fun _ => String) (fun x => s!"{x}") ?lam ?app t
```
Where `?lam` and `?app` are metavariables, i.e holes that still need to be resolved for the definition to be valid. These holes correspond to the branches for the `lam` and `app` cases respectively. The function can then be completed by giving a value to each hole:
```lean
def Term.repr (t : Term) : String := Term.rec (fun _ => String) (fun x => s!"{x}") (fun _ sf => s!"λ {sf}")(fun _ _ sf st => s!"{sf} {st}") t
```
More generally, `Var.rec` can be modularly extended:
\ `⟦Var.rec motive pvar t⟧ => Term.rec ⟦ motive ⟧ ⟦ pvar ⟧ ?lam ?app ⟦ t ⟧ ` \ 
Note that metavariable holes such as `?lam` and `?app` cannot, in general, be resolved automatically by Lean, and are instead meant to be resolved by the user, the next section on definitions extensions discusses the interface provided by #Gemel for that purpose in more details.

To generalize the previous example, consider an inductive `A` of parameters $accent((p : P),→)$, indices$ accent((i : I),→)$ and constructors $accent(ctor,→)$, as well as another type `B` with the same parameters and indices, as well as the same constructors + a new constructor $newctor$. Extending this to manage adding multiple constructors is trivial, we omit this detail here. We can map the type A to B and respectively every constructor of A to B's. The last missing piece to this 
translation is the recursor. \ 
\ 
Recursors have the following shape: \ 
$"A.rec" : accent((p : P),→) → (motive : accent((i : I),→) → A space accent(p,→) space accent(i,→) → univ) → accent((minor : ... → motive (ctor space ...)),→) → accent((i : I),→) → (a : A space accent(p,→) space accent(i,→)) → motive accent(i,→) space a$ \ 
where for every constructor of the type, there is a `minor` covering the (potentially recursive) case associated to it. \ 
`B`'s recursor is very similar, except it contains an additional minor for the `newctor`'s case. #Gemel modularly maps any application with head `A.rec` into `B.rec` by modularly mapping each argument (i.e the parameters, motive, minors and major), and adding a metavariable hole for the minor corresponding to `newctor`:

$\
⟦"A.rec" accent(p,→) motive accent(minor,→) space accent(i,→) space a⟧ := "B.rec" accent(⟦p⟧,→) space ⟦motive⟧ space accent(⟦minor⟧,→) space ?m space accent(⟦i⟧,→) space ⟦a⟧$ \
This mapping is automatically produced and added to the mapping context upon constructing a `mod inductive`. 

Additionally to the primitives surrounding an inductive type, Lean also automatically produces more than a dozen auxiliary declarations, meant to make the automation and user-experience friendlier. For example, upon defining an inductive type `Foo`, Lean will, for every constructor `ctor`, define a helper lemma `Foo.ctor.inj` which proves the injectivity property of said constructor.
In order to avoid making users define mappings between auxiliary declarations produced by the original and the extended type by hand, #Gemel automatically generates said mappings automatically (e.g `Var.var.inj` gets automatically mapped to `Term.var.inj` in the previous example).

// that need to be mapped between the two types carefully, namely, given an inductive type `Foo`, Lean constructs the following list of auxiliary declarations, which each need get translated with particular care in #Gemel:
// - `Foo.recOn`: an alternative shape for the recursor
// - `Foo.casesOn`: a recursor with no recursive hypotheses
// - `Foo.CtorIdx`: a function mapping each recursor to a respective natural number
// - `Foo.NoConfusion`: helper function for trivially proving inequality of terms with different constructors on each side  
// - `Foo.below`/`Foo.brecOn`: a recursor for "course-of-value" recursion, i.e recursion where the induction hypothesis applies to any strict subterm, a generalisation of the strong recursion principle for natural numbers. Useful for translating syntactically recursive functions into structurally recursive ones (see @recursion)   
// - `Foo.SizeOf`: helper function that maps each inductive term to a size, useful for proving the termination of a well-founded recursive function over that type (see @recursion) 
// - `Foo.ctor.inj`: injectivity lemma for each constructor

= Pattern matching and recursion

Our framework now allows for inductive types to be extended through the addition of new constructors. This section focuses on how declarations (i.e definitions and theorems) can be extended and modularly mapped correctly. \
Going back to the previous example of `Term` extending `Var`, consider a function `Var.repr`, this time written idiomatically using pattern-matching rather than a recursor:

```lean
def Var.repr : Var → String
  | var x => s!"#{x}"
```

Currently, a user would need to redo the `var` case in order to define a `Term.repr` function, e.g as follows:
```lean
def Term.repr : Term → String
  | var x => s!"#{x}"
  | app f x => s!"{Term.repr f} {Term.repr x}"
  | lam f => s!"λ {Term.repr f}"
```
This however leads to a duplication of the `var` case, which in turns lead to a burden of maintenance. If, for example, the user was to change how variables are pretty-printed in the `Var.var` case, this change would have to be copy-pasted for the `Term.var` case, which would be hard to track in general.
Instead, #Gemel introduces a new #raw("mod def", lang: "lean") syntax to allow users to reuse existing branches in a previously defined function, and only require them to fill-in the holes needed to go from a definition over one type to a definition of the same shape over an extension of said type. This syntax allows to rewrite `Term.repr` as follows:

#box[
```lean
mod def Term.repr extends Var.repr where
  extend with
  | app f x => s!"{Term.repr f} {Term.repr x}"
  | lam f => s!"λ {Term.repr f}"
```]

Now, any change done to `Var.repr` would also change downstream of it for `Term.repr`. 
 
The general elaboration process of that syntax is as follows. Given a declaration \ (e.g `Var.repr`), one may modularly map its body into a function over the extended type (here `Term`). Once that it done, users may be asked to fill in any remaining holes in the translated body to construct a well-formed declaration. Once that is done, the new declaration (here `Term.repr`) can be safely added to the global environment of declarations, and a mapping from `Var.repr` to `Term.repr` can be added to the mapping context.

In practice, implementing all of this in Lean has exposed some complications which necessitates careful design decisions, in particular with regards to how pattern-matching and recursion are to be managed. These two features are handled very differently by popular dependently-typed ITPs. In Rocq, matches and fixpoints are distinct primitive operations made explicit in the abstract syntax. Agda bundles these two notions in a single top-level primitive called a case-tree, where each function (and pattern-match present in a function) gets translated into a top-level case-tree. In both systems, termination-checking is a syntactic criteria that goes through a given fixpoint definition and checks that every recursive call in a function is ran on a strict subterm. Lean diverges from the tradition of having primitive operations, both for pattern-matching and for recursion, and elaborates both down to inductive recursor calls, following and extending on technics described in @Goguen2006 and @Cockx2018. For pattern-matching, it may appear as though Lean does have match expressions: they are part of the concrete syntax and get appropriately pretty-printed when looking back at the abstract syntax. Take for example a function of the form
```lean
def is_var_zero : Var → Bool
  | var 0     => true
  | var (n+1) => false
```
The shape of the match get elaborated into an auxiliary function:
```lean
is_var_zero.match_1 : (motive : Var → Type) → (x : Var) → 
(Unit → motive (var 0)) → ((n : Nat) → motive (var (n + 1))) → motive x
```

The function is then applied with the right arguments to explicit the return type of the match-here called the `motive`-, the discriminant -here `x`-, and the right-hand-side of each branch:
```lean
def is_var_zero : Var → Bool := fun x => 
  is_var_zero.match_1 (fun _ => Bool) x (fun _ => true) (fun _ => false)
``` 
Note that a `Unit` argument appears in the `var 0` branch. This happens because Lean compiled code is call-by-value, which justifies lazily computing the branches of a given match.

For recursions, when a recursive function is defined, Lean tries to elaborate the function either into a structurally recursive term, using the recursor of whatever term decreases structurally in the recursive calls to write the function or tries to prove the function be well-founded, morally recursing over the accessibility predicate, similarly to Rocq's Equations (@Sozeau2019).

== Extending pattern-matches

When it comes to extending matches, we are presented with two options. The first one consists of remarking that matches are simply encoded using recursors. As such, we may simply modularly map a given matcher and ask users to fill in the holes in it. This is unreasonable, as it exposes far too many internal details. The definition of a given match can quickly become complex if it matches on multiple elements, needs to generalize some variables or contains some proofs of equality between the thing matched on and a given constructor in a branch. Extending any of this would make an unreadable mess for the users and is too detached from what a user would do had he just written this as a normal definition. Consider the case of `is_var_zero` being extended to `Term`. For both the `app` and `lam` case, the result is the same (i.e `false`). Producing this extension would require both extending the implementation of `match_1` (by adding a branch for `(t : Term) → motive (lam t)` and `(f t : Term) → motive (app f t)`), and adding the right arguments for the right-hand-side of said new branches (i.e `fun t => false` and `fun f t => false`). This means, in this specific example, that a user would need to fill in 4 holes, half of them having a non-trivial shape which mentions an arbitrary `motive` that did not appear in the concrete syntax of the original definition. \ 
A second option for extending matches would be to remark that extending a match amounts to adding new branches to it such that it covers the relevant new constructors in the extended inductive type. As such, we may ask users to write down the relevant branches, in a syntax similar to how normal matches are written.
This option turns out to be the most ergonomic, although it makes the implementation work measurably harder than the former. In order to accomodate for this feature, when modularly mapping the term of a given declaration, any application whose head is a matcher gets translated into a metavariable hole, saving the original shape of the expression along the way. When trying to solve that metavariable, the original shape of the matcher is reconstructed, similarly to how the pretty-printer handles this expression. We then elaborate the new match branches provided by the user, and re-elaborate this into a new match-expression. Note that the implementation does *not* do any anti-quotations (i.e it does not construct concrete syntax from the original abstract syntax), and instead manipulates both the abstract syntax of the old matcher and the concrete syntax of the new branches in parallel, using Lean's existing internals for elaborating matchers. The end-result is a legible syntax for extending past declarations. \
Take the example of `is_var_zero` getting extended to `Term`:
```lean
def Term.is_var_zero extends is_var_zero where
  extend with
    | app _ _ => false
    | lam _   => false
```
First, the extension system of #Gemel detects that  `is_var_zero.match_1 (fun _ => Bool) x (fun _ => true) (fun_ => false)` is a matcher application and stores the information about its shape (i.e what the motive, discriminants and existing branches are). All of this information gets modularly mapped to `Term` rather than the original `Var` (e.g `Var.var` become `Term.var` in the left-hand side of each branch). Then, the branches provided by the user (i.e `| app _ => false` and `| lam _ _ => false`) get elaborated as new branches to be added to the previous ones. This bundle of data is then passed out to the existing API Lean uses to elaborate normal pattern-matches, and produces a new match application that the old one then gets translated to.

// Take the previous example of inductive extensions where `Term` extends `Var` in @ind_extension. Consider a function for printing a term of the type:
// 
// We extend Lean with a new command `mod def` which allows one to extend a previous function by expliciting the missing branches in its pattern-matches. Such a function for `Term` looks like the following:
// ```lean
// mod def Term.repr extends Var.repr where
  // extend match_1 with
  // | app f x => s!"{Term.repr f} {Term.repr x}"
  // | lam f => s!"λ {Term.repr f}"
// ```
 
== Extending recursive functions
<recursion>

Though recursion is present at the level of the concrete syntax, it gets elaborated away into structural and well-founded recursion at the abstract syntax level, which means that functions internally get translated into things that are different in shape to a user's original definition. Because of this, directly modularly mapping the body of a recursive definition is not great, since it exposes internal encodings to the user, and asks one to manipulate those directly to extend the definition. Thankfully, Lean usually provides auxiliary lemmas that exhibit the original shape of the function that was defined. One of them, `foo.eq_def`, is a theorem of the form: \ 
`(a₁ : A₁) → ... → (aₙ : Aₙ)  → foo a₁ ... aₙ = <foo's definition>`

As such, rather than use the original body of a definition, we can instead modular map the right-hand side of a function's `eq_def` whenever available, and then reuse the existing elaboration APIs Lean provides to translate such syntacticaly recursive functions to structurally recursive or well-founded functions. This in effect means a user can adapt the termination measure of an extended definition, relative to the original's, a feature no other extension system provides to our knowledge. Said feature is of particular importance when extending a non-recursive type to a recursive one, as is the case with the extension from `Var.repr` to `Term.repr`.

In particular, this allows us turn an originally non-recursive function into a recursive one if needed, as is the case with `Term.repr` extending `Var.repr`, or even change the termination measure that was originally used to adapt it to the new extended function.

== Putting it all together

In practice, being able to change the proof of termination of an extended function compared to the original provides us with much more modularity, and is a feature we have not seen in any other project of the sort. \
Furthermore, having matches be handled specially provides a clear distinction between the holes generated for matches and those generated by explicit uses of recursors, which usually only appear in proof terms generated by tactic calls such as `induction` and `cases`. branches. 
The complete syntax for #raw("mod def", lang: "lean") ends up as the following:

#box(clip:true)[
```lean
  mod def <new function name> extends <old function name> where
    <match extension>
  by
    <tactics>
  <termination-information>
```]

This in essence means our syntax for modular definitions offers a clear separation of concerns between proof holes, solved by tactics, and non-proof holes, solved by completing match 
// This sort of distinction  is not new. Indeed, `where finally` is already a feature for definitions in Lean, and can be used to fill-in proof holes after the fact:
// ```lean
// def Vec.tl (v : Vec α (S n)) : Vec α n :=
//   match h : S n, v with
//     | Z, nil => nomatch h
//     | S k, cons _ tl => (show n = k from ?_) ▸ tl 
//                   --rewrites the type of `tl` from `Vec α k` to `Vec α n`
//   where
//     finally
//     injection h
// ``` 
// Similarly, Rocq's `Equations` (@Sozeau2019) syntax provide an "Obligations" system which serve a similar purpose.
// We thus adopt a similar syntax to Lean's normal #raw("def", lang: "lean") declarations, by asking for matchers to be completed first, before asking proof holes to be solved in a #raw("finally", lang: "lean") block. The `finally` block mainly only appears when extending theorems rather than definitions. Consider the following theorem:
The syntax asks for matchers to be completed first, before asking proof holes to be solved in a #raw("by", lang: "lean") block. The `by` block mainly only appears when extending theorems rather than definitions. Consider the following theorem:
```lean
theorem is_var_zero_eq (t : Var) (h : is_var_zero t) : t = var 0 := by
  cases t
  case var n => 
    cases n 
    case zero => rfl
    case succ _ => nomatch h
```

Extending it for `Term` will add two new proof holes originating from the `cases t`. These are given by the user in the `by` block as follows:
```lean
mod def Term.is_var_zero_eq extends is_var_zero_eq where
  by
  case lam _   => nomatch h
  case app _ _ => nomatch h
```

Termination information such as #raw("termination_by", lang: "lean") or #raw("decreasing_by", lang: "lean") can be additionally provided if needed to help with producing a well-founded recursive function. 
For example, the previous `Term.repr` function could have had an explicitly given annotation such as #raw("termination_by structural t => t", lang: "lean"), indicating that the function is structurally recursive over it's argument `t : Term`. In practice, and as is the case for the regular Lean definition, most functions' termination information is trivial enough to be inferred by the Lean, and thus does not require additional user-input. 

= Making extensions modular: modular merges
The current set-up allows one to extend previous definitions iteratively, though one may argue these extensions are not strictly "modular". In particular, one can currently only construct a declaration as an extension of a single other declaration rather than multiple. This, in particular, means one isn't able to compose different extensions. Take the example of the Barendregt lambda-cube (@Barendregt1991):

// https://q.uiver.app/#r=typst&q=WzAsOCxbMCw0LCJcXGxhbWJkYSJdLFswLDEsIlxcbGFtYmRhMiJdLFszLDQsIlxcbGFtYmRhIFAiXSxbMSwzLCJcXGxhbWJkYVxcb21lZ2EiXSxbMSwwLCJcXGxhbWJkYVxcb21lZ2EiXSxbNCwwLCJcXGxhbWJkYSBDIl0sWzQsMywiXFxsYW1iZGEgUFxcb21lZ2EiXSxbMywxLCJcXGxhbWJkYSBQMiJdLFswLDFdLFswLDJdLFswLDNdLFszLDRdLFsxLDRdLFs0LDVdLFsyLDZdLFszLDZdLFs2LDVdLFsyLDddLFsxLDddLFs3LDVdXQ==
#align(center, diagram(spacing: 1em,{
	node((-2, 1), [$lambda$])
	node((-2, -2), [$lambda 2$])
	node((1, 1), [$lambda P$])
	node((-1, 0), [$lambda underline(omega)$])
	node((-1, -3), [$lambda omega$])
	node((2, -3), [$lambda C$])
	node((2, 0), [$lambda P underline(omega)$])
	node((1, -2), [$lambda P 2$])
	edge((-2, 1), (-2, -2), "->")
	edge((-2, 1), (1, 1), "->")
	edge((-2, 1), (-1, 0), "->")
	edge((-1, 0), (-1, -3), "->")
	edge((-2, -2), (-1, -3), "->")
	edge((-1, -3), (2, -3), "->")
	edge((1, 1), (2, 0), "->")
	edge((-1, 0), (2, 0), "->")
	edge((2, 0), (2, -3), "->")
	edge((1, 1), (1, -2), "->")
	edge((-2, -2), (1, -2), "->")
	edge((1, -2), (2, -3), "->")
}))

The various vertices of the cube are extensions of the initial vertex corresponding to STLC, each adding new features to the original type theory. However, an important feature of this cube is that all extensions of $lambda$ can be written as mergings of its 3 adjactent vertices, namely $lambda P$, $lambda 2$ and $lambda underline(omega)$ (e.g $lambda P 2$ corresponds to the merging of $lambda 2$ and $lambda P$). If one wanted to formalise each vertex of the cube before #Gemel, they would need to write down 8 different formalisations. With our current framework, they need only write down 1 formalisation and 7 extensions of that base formalisation. If our system was truly modular however, one would only need to write down the base formalisation and the 3 adjacent extensions, the rest being simply generated by merging the adjacent extensions. To make this possible, we extend #Gemel's handling of inductive types and definitions extensions and describe a way to make them composable, thus achieving true modularity. In practice, from a user perspective, all that gets added is the ability to define a `mod inductive` or `mod def` that `extends` more than one single declaration. 

== Inductive modularity

Extending `mod inductive` to be able to extend more than one inductive type is a fairly trivial task. Rather than only taking the constructors of one inductive, users may take constructors from multiple types. The mapping context will then map every old type to the new one, every old constructor from each old type to the relevant new ones. Consider the example of `BoolTerm` extending `Term` in @extendInd, one may also extend `Term` to handle natural numbers, and merge the two extensions as follows:
```lean
mod inductive NatTerm extends Term where
  | zero : NatTerm
  | succ : NatTerm → NatTerm
  --   match n with | 0 => P0 | n+1 => Pn n
  | natmatch : NatTerm → NatTerm → NatTerm → NatTerm

mod inductive BoolNatTerm extends BoolTerm, NatTerm
```
The merging of constructors is nominal and type-driven: when merging `BoolTerm` and  `NatTerm` together, #Gemel remarks that the `var`, `app` and `lam` constructors are in common between the two, confirms their types are compatible, and does not duplicate them in the merging. As such, the generated inductive `BoolNatTerm` will contain all of the basic `Term` constructors, as well as the additional ones provided by `BoolTerm` and `NatTerm`, and maps the old inductives' constructions to the appropriate constructions of the new one.

== Definition modularity

Consider the previous examples of defining `is_var_zero` and `is_var_zero_eq` to `BoolNatTerm`, consider the two declarations have already been extended to `BoolTerm` and `NatTerm`:
```lean
mod def BoolTerm.is_var_zero extends Term.is_var_zero where
  extend with
    | true | false | ite _ _ _ => false

mod def NatTerm.is_var_zero extends Term.is_var_zero where
  extend with
    | zero | succ _ | natmatch _ _ _ => false
```

We can modularly map both declarations into functions talking about `BoolNatTerm`. Both of them will be incomplete in that the pattern-match will be incomplete in both cases (e.g the cases for `zero` will be missing from the modular map of `BoolTerm.is_var_zero`). However, both declarations will have the same shape modulo having different holes in different places. We make use of that and construct an algorithm that syntactically merges two expressions together, and throws an error if their shape diverges. In practice, in the case of `is_var_zero`, this means the respective matches get merged correctly, meaning there is no need for the user to add anymore information in order to merge the two declarations:
```lean
-- No `extend with` block needed to complete the match
mod def BoolNatTerm.is_var_zero 
  extends BoolTerm.is_var_zero, NatTerm.is_var_zero 
```

Similarly, the proof for `is_var_zero_eq` need not anymore information after merging both `BoolTerm.is_var_zero_eq` and `NatTerm.is_var_zero_eq`:
```lean
mod def BoolTerm.is_var_zero_eq extends Term.is_var_zero_eq where by
  ... -- proof omitted

mod def NatTerm.is_var_zero_eq extends Term.is_var_zero_eq where by
  ... -- proof omitted

-- no `by` block needed
mod def BoolNatTerm.is_var_zero_eq 
  extends BoolTerm.is_var_zero_eq, NatTerm.is_var_zero _eq
```

= Case studies

== Strong normalisation of the Simply Typed Lambda Calculus
#let extCell(label) = box(
  width: 2.7cm,
  height: 1.2cm,
  inset: 6pt,
  fill: white,
  stroke: 1.3pt + black,
  radius: 7pt,
)[
  #align(center + horizon)[#label]
]

#align(center, diagram(spacing: 1.2em, {
  node((0, 2), extCell([STLC + Nat \ + Bool]))
  node((-1, 0), extCell([STLC + Nat]))
  node((1, 0), extCell([STLC + Bool]))
  node((0, -2), extCell([STLC]))

  edge((0, 2), (-1, 0), "->", label: "extends", label-angle: -40deg)
  edge((0, 2), (1, 0), "->",  label: "extends", label-angle: 40deg)
  edge((-1, 0), (0, -2), "->",  label: "extends", label-angle: 40deg)
  edge((1, 0), (0, -2), "->",  label: "extends", label-angle: -40deg)
}))
In order to iterate on this implementation and ensure its usability, we studied the case of taking an existing implementation of STLC (@leanstlc) which proves the strong normalization property of the system, and extended it with additional constructors, allowing us to modularly prove the strong normalization property of the extended system. In particular, the original normalization was *not* built with modularity in mind, and was still extendable after the fact. The original formalisation follows the usual proof of normalisation using a logical relation.

#align(center)[#box[#grid(columns: 2, column-gutter: 2em)[```lean
inductive Base.Ty : Type where
| arrow : Ty → Ty → Ty
```][```lean
inductive Base.Term where
| var : Nat → Term
| app : Term → Term → Term
| lam : Term → Term
```]
```lean
inductive Base.Typing : List Ty → Term → Ty → Type where
  | tyvar : Γ[n]? = some A → Typing Γ (var n) A
  | tyapp : Typing Γ f (arr A B) → Typing Γ t A → Typing Γ (app f t) B
  | tylam : Typing (A::Γ) t B → Typing Γ (lam t) B

... --other definitions/theorems
```
]]

We extend this base definition to add natural numbers.
#align(center)[#grid(columns: 2, column-gutter: 2em)[```lean
modular NatTerm

mod inductive Ty 
  extends Base.Ty where
  | nat
```][```lean


mod inductive Term 
  extends Base.Term where
  | zero   : Term
  | succ   : Term → Term
  | natRec : Term → Term → Term → Term
```]
#box[
```lean
  mod inductive Typing extends Base.Typing where
    | zero   : Typing Γ zero nat
    | succ   : Typing Γ n nat → Typing Γ (succ n) .nat
    | natRec : Typing Γ n nat → Typing Γ P0 A 
      → Typing Γ PS (arr nat (arr A A)) → Typing Γ (natRec n P0 PS) A

... --other definitions/theorems
end modular NatTerm
```
]]

The total formalisation contains 12 inductive types as well as 92 definitions/theorems. Almost all of these were extended with no issue. The original formalisation contains a limitation to extensions in that the logical relation `LR` it defines to prove strong normalisation is too weak to prove the property on a system extended with natural numbers. We considered manually adding a modular map from `LR` to a variant strong enough for our purpose. However, the theorems in the original formalisation that make use of that LR rely heavily on its definitional equalities, which do not hold in a stronger formulation of the relation, meaning such a mapping leads to ill-typed terms when translating said theorems. As such, `LR` and the fundamental lemma had to be written as normal lean `def`s rather than as extensions. A solution to circumventing such issues, based on the idea of removing the reliance on some definitional equalities on a given term, is discussed in the future works.

To showcase the capacity to merge separate extensions, we produce another extension of STLC containing primitives for booleans, namely a boolean constructor in `Ty`, and term constructors for `true`, `false` and `if-then-else`. We then successfully construct a formalisation of STLC with both natural numbers and booleans by merging the two previous formalisations, thus proving the strong normalization of "STLC + Bool + Nat" fully modularly. 

For lack of a better metric to measure the usability of #Gemel, we remark that, while the original, independent formalisation of STLC was written in ~1500 lines of code (LoC), the extensions for Nat and Bool respectively necessitated ~1000 Loc, including the duplicated code about `LR`. The last extension, which had both Nat and Bool, and didn't duplicate any code since it already extended a powerful enough logical relation, was written in only ~400 LoC in comparison.

== STLC to CPS translation
<CS2>
#let caseCell(label) = box(
  width: 2.9cm,
  height: 1.15cm,
  inset: 6pt,
  fill: white,
  stroke: 1.3pt + black,
  radius: 7pt,
)[
  #align(center + horizon)[#label]
]

#align(center, diagram(spacing: 1.3em, {
  // Left side: STLC extensions
  node((-2, -2), caseCell([STLC])              ,name : <STLC>)
  node((-5, -1), caseCell([STLC + Fix])    ,name : <STLCFix>)
  node((-5, 1), caseCell([STLC + Bool])   ,name : <STLCBool>)
  node((-2, 2), caseCell([STLC + Bool \ + Fix]),name : <STLCBoolFix>)

  edge(<STLCBoolFix>, <STLCBool>, "->", label: "extends", label-angle: auto)
  edge(<STLCBoolFix>, <STLCFix>, "->", label: "extends", label-angle: auto, label-pos : 60%)
  edge(<STLCBool>, <STLC>, "->", label: "extends", label-angle: auto, label-pos : 70%)
  edge(<STLCFix>, <STLC>, "->", label: "extends", label-angle: auto)

  // Right side: CPS extensions
  node((2, -2), caseCell([CPS])             , name: <CPS>)
  node((5, -1), caseCell([CPS + Fix])   , name: <CPSFix>)
  node((5, 1), caseCell([CPS + Nat])   , name: <CPSNat>)
  node((2, 2), caseCell([CPS + Nat + Fix]), name: <CPSNatFix>)

  edge(<CPSNat>, <CPS>, "->", label: "extends", label-angle: auto, label-pos : 70%)
  edge(<CPSFix>, <CPS>, "->", label: "extends", label-angle: auto)
  edge(<CPSNatFix>, <CPSNat>, "->", label: "extends", label-angle: auto)
  edge(<CPSNatFix>, <CPSFix>, "->", label: "extends", label-angle: auto, label-pos : 60%)

  // Translation extensions
  edge(<STLC>       , <CPS>      , "-->", label: $⟦ underscore ⟧$)
  edge(<STLCFix>    , <CPSFix>   , "-->", label: $⟦ underscore ⟧_"Fix"$)
  edge(<STLCBool>   , <CPSNat>   , "-->", label: $⟦ underscore ⟧_"Bool"$)
  edge(<STLCBoolFix>, <CPSNatFix>, "-->", label: $⟦ underscore ⟧_"Bool+Fix"$) 
}))
To showcase the capabilities of our framework, and provide a point of comparison with another modular system, we reproduce the central case study shown in Pyrosome's (@Pyrosome) paper. This case study introduces two type system: STLC, and CPS-style type-system, as well as a translation from the former to the latter which proves $beta eta$-equivalence is conserved through that translation pass. The case-study then extends both STLC and CPS with new constructions (resp. booleans and a fixpoint operator for STLC, natural numbers and a fixpoint operator for CPS), and extends the translation pass accordingly. One feature of Pyrosome's case study is that their framework allows for limited forms of horizontal extensions, which our framework doesn't. In particular, STLC terms are separated between values (i.e terms whose head can't be anymore reduced) and expressions (who can reduce). 
This STLC formalisation differs from the first case study's in that typing is enforced intrinsically here, meaning the type of STLC terms are indexed by a context and a type (i.e `Term` has type `List Ty → Ty → Type`), whereas well-typedness is enforced extrinsically through a predicate in the former (i.e `Term` has type `Type` and a predicate `Typing: List Ty → Ty → Term → Prop` is defined). In order to modularly reuse as much API as possible between STLC, CPS and their respective extensions (such as substitution and renaming operations), both type systems are defined as extensions of a `Base` bundle, for which terms are just variables, and which defines a common API for both extensions to build off of. The shape of both systems differ in that both expressions and values are indexed by a type in STLC, but only values are in CPS. The type of terms is instead indexed by a context, a tag, and a dependent family `Tag.Data` over that tag which explicits by what data a term of a given tag is indexed by. As such, both STLC and CPS can extend the `Tag` type, and `Tag.Data` for their respective needs:

#figure(supplement: "Figure",caption: [Definitions of Base, STLC and CPS, `Term` is indexed by a data associated to, this data gets extended accordingly for each extension.])[

#align(center + top)[
#box(fill: luma(230), inset: 5pt, radius: 4pt)[
*BASE*
#set text(size: 9.5pt)
```lean
inductive Tag where
  | val

inductive Ty where
  | unit

def Tag.Data : Tag → Type
  | val => Ty -- Values are always indexed by a type

inductive Term : List Ty → (t : Tag) → (Tag.Data t) → Type 
  | var:(n : Fin Γ.length) → Γ[n] = A → Term Γ val 

... --other definitions/theorems
```]]
#v(-1.5em)
#grid(columns: 2, align: center + top, column-gutter: 5em)[
#box(fill: luma(230), inset: 5pt, radius: 4pt, width: 125%)[
*STLC*
#set text(size: 9.5pt)
```lean

modular STLC

mod inductive Tag extends Base.Tag where
  | exp

mod inductive Ty extends Base.Ty where
  | arr (A B : Ty)


mod def Tag.Data extends Base.Tag.Data where
  extends with
  | exp => Ty --STLC terms are indexed by a type

mod inductive Term extends Base.Term where
  | ret : Term Γ val A → Term Γ exp A
  | lam : Term (A::Γ) exp B → Term Γ val (.arr A B)
  | app : Term Γ exp  (.arr A B) → Term Γ exp A 
          → Term Γ exp B




... --other definitions/theorems
end modular STLC

```]][
#box(fill: luma(230), inset: 5pt, radius: 4pt, width: 125%)[
#set text(size: 9.5pt)
*CPS*
```lean

modular CPS

mod inductive Tag extends Base.Tag where
  | exp

inductive Ty where
  | not   (A : Ty)
  | times (A B : Ty)

mod def Tag.Data extends Base.Tag.Data where
  extends with
  | exp => Unit --CPS terms are not

mod inductive Term extends Base.Term where
  | lam : Term (A::Γ) exp () → Term Γ val A.not
  | app : Term Γ val A.not → Term Γ val A 
          → Term Γ exp ()
  | and_intro : Term Γ val A → Term Γ val B 
          → Term Γ val (A.times B)
  | fst : Term Γ val (A.times B) → Term Γ val A
  | snd : Term Γ val (Ty.times A B) → Term Γ val B

... --other definitions/theorems
end modular CPS
```]]]

= Related works
<related-works>
We compare our approach with the existing solutions with the modularity problem in ITPs. 

"Meta-Theory à la Carte" (@Delaware2013) and "Pyrosome" (@Pyrosome) base their modularity on internal encodings of types. The former relies on Mendler-style Church encodings (@Jansen2013), the latter on Generalized Algebraic Theories (@Cartmell1986). In both cases, the constructions are inefficient, incapable of extending previously user-defined inductive types (#ie expecting users to rely on the aforementioned encodings from the ground up), and exposes the underlying internals of the encodings to the user.
Having to deal with encodings of types rather than types adds
a heavy burden in particular for new users interested in program verification.
The lesson to include inductive data-types natively has been learned early by popular ITPs (namely Rocq and Lean), who at first had no primitive notions of inductive types in their systems and then resorted to add those. Nowadays, most systems usually possess a syntactic notion of (co-)inductive types, and justify the ability to define these via some classes of models, allowing users to work with the abstractions these types provide, rather than with their encoding in said models. The only popular system that still relies on encodings to define such types, and manages to hide their implementation details well, is Isabelle/HOL.

On the other hand, Rocq à la Carte (@Forster2020) relies on the meta-programming capabilities offered by the MetaRocq Project (@Sozeau2020a) to allow users to construct new inductive types and functions by merging other inductive types, and/or adding new constructors. New functions on a "merged" datatype can then be constructed by merging past functions. The metaprogram then uses the given piece of information to reconstruct a new inductive type, and new functions, based on the information given by the user. While great for extending constructions "vertically" (#ie by adding constructors to a type), this system does not allow for horizontal extensions (#ie extending the type signature of inductive types and their constructors). Furthermore, this  approach has been hindered in the past by the lack of good metaprogramming frameworks in ITPs.

Rocqet comes the closest in philosophy to our implementation, relying heavily on meta-programming and seemingly manipulating Rocq's AST directly. It however also doesn't allow for extensions after the fact, and their interface for extending past definitions is more restricted. Indeed, the only allows for constructing recursive functions with a single pattern-match with a single discriminant at the top of the function, where #Gemel handles arbitrary pattern-matching. Furthermore, Rocqet is suited for defining and extending functions and proofs defined using structural induction on the datatype getting extended, #Gemel on the other hand can handle structural and well-founded induction over arbitrary terms. Lastly, Rocqet requires users to explicit the motive function of each induction in their system. All of this comes at a cost for the user-experience.

None of these systems, independently of whether they use encodings or the meta-programming, handle all of the type-system of ITPs they are implemented for (#eg none handle co-inductive types), or allow users to extend past formalizations "after the fact". Instead, formalizations have to be built from the ground up with the expectation that they will be extended with a specific framework in mind, making them much less useful for real-world uses.
 

// A central contribution on matters of modularity in regular programming languages, "Data Types à la Carte" (@Swierstra2008), provides a simple and elegant solution to the expression problem based on a parametrical approach to modular syntax in Haskell. This solution, however, cannot be easily adapted to ITPs since ITPs needs to ensure consistency via their type system. Instead, existing approaches either rely on complex encodings of datatypes that leak to the user, or on meta-programming.

// "Meta-Theory à la Carte" (@Delaware2013) and "Pyrosome" (@Pyrosome) base their modularity on internal encodings of types (namely, impredicative church-encodings in the former, and Generalized Algebraic Theories in the latter). In both cases, the constructions are inneficient, incapable of extending previously user-defined inductive types (#ie expecting users to rely on the aforementionned encodings from the ground up), and expose the underlying internals of the encodings to the user.
// Having to deal with encodings of types rather than types adds
// a heavy burden in particular for new users interested in program verification.
// The lesson to include inductive datatypes natively has been learned early by popular ITPs (namely Rocq and Lean), who at first had no primitive notions of inductive types in their systems and then resorted to add those. Nowadays, most systems usually posess a syntactic notion of (co-)inductive types, and justify the ability to define these via some classes of models, allowing users to work with the abstractions these types provide, rather than with their encoding in said models. The only popular system that still relies on encodings to define such types, and manages to hide their implementation details well, is Isabelle/HOL.

// #yf[Explain that now people do not work with datatypes anymore but with complicated encodings that are normally used to justify types in models -> there's a reason one wants to work in a nice system and not in a model for a nice system]
// On the other hand, Rocq à la Carte (@Forster2020) relies on the meta-programming capabilities offered by the MetaRocq Project (@Sozeau2020a) to allow users to construct new inductive types and functions by merging other inductive types, and/or adding new constructors. New functions on a "merged" datatype can then be constructed by merging past functions. The metaprogram then uses the given piece of information to reconstruct a new inductive type, and new functions, based on the informations given by the user. While great for extending constructions "vertically" (#ie by adding constructors to a type), this system does not allow for horizontal extensions (#ie extending the type signature of inductive types and their constructors). Furthermore, this  approach has been hindered in the past by the lack of good metaprogramming frameworks in ITPs.

// None of these systems, independently of whether they use encodings or the meta-programming, handle all of the type-system of ITPs they are implemented for (#eg none handle co-inductive types), or allow users to extend past formalisations "after the fact". Instead, formalisations have to be built from the ground up with the expectation that they will be extended with a specific framework in mind, making them much less useful for real-world uses.

= Future work
<FutureWorks>

#Gemel shows how directly manipulating the core AST of an ITP without relying on encodings can work for producing modular formalisations. There are however further design decisions that remain to be experimented with, and which may open up the door for further improvements to the tool.

There are morally two ways to extend an inductive type, referred to as vertical and horizontal extensions (@Duggan96). The former consists of adding new constructors to an inductive type, the latter of adding new fields to a type's constructor, or to the type itself. Most modular systems only allow for doing vertical extensions, as it is both the easiest one to justify and implement, and arguably the most useful one. Currently, #Gemel only manages vertical extensions, though our second case-study (@CS2) shows how some horizontal extensionality can be recovered in the system through careful use of dependent types. The space of handling horizontal extensions has not been explored much in existing literature, the only system which, to our understanding, manages some form of horizontal extensions is Pyrosome. However, the scope of their extensions is much more limited and cares only about translation passes for compilers. 

The central way in which extensions are added to the environment is by mapping constants to new (potentially incomplete) terms. For a translation using a constant found in the mapping context to work well, it is necessary that the reduction rules involving past constants also hold when mapping the constant to its associated term. This restriction is implicitly present when translating recursors and matches. However, as seen in the first case-study, it may sometimes be necessary for a formalisation to extend something (e.g the logical relation in the case study) with something possibly completely new, that may not hold the same definitional equalities. In order to do this, #Gemel could, in the future, have some mechanism for transforming an expression which relies on some particular reduction rules/definitional equalities into one that does not. This idea of removing such rules is not new, and appears in works producing translations from Extensional Type Theory to Intensional Type Theory (@Winterhalter2020), as well as works on removing definitional equalities from Lean using a similar translation (@vaishnav). The latter work could in particular possibly be adapted to our needs since it is already implemented in Lean.

One challenge with extending independent formalisations is that shape of an original proof might not be fitting to prove an extended version of it. An important example of this issue is proofs by induction: it appeared a few times when testing #Gemel that an original proof that was done by induction needed, for the extended proof to work, to generalize some variables when doing said induction, such that the induction hypotheses would be stronger. Similarly, it could happen that part of a proof originally just needed a case split where the new proof would require the full power of induction. However, the existing interface of metavariable holes morally only allows us to add the necessary content at the tips of our proof tree, not modify the proof-tree in its generality. To extend this framework, we could imagine allowing for some "after the fact" transformations, such as generalisations or turning a case split into an induction, to the rest of the proof tree, allowing for a more comfortable experience of doing extensions of independent formalisations.

#pagebreak()
#bibliography("biblio.bib", title : "References", style : "citation-style.csl")
// #pagebreak()
// #show: appendix
// = Formal presentation of modular maps
// <AppendixA>

// This section makes a partial attempt at justifying the implementation of modular maps in our system, and why it can be trusted to make well-formed terms.
// 
// First, let's define the syntax we'll be using in this toy presentation. This is a basic dependently-typed system equiped with a predicative hierarchy of universes à la Russel, as well as constants and metavariables. For the sake of simplifying the presentation, we will assume constants cannot be unfolded (i.e we will only care about $beta$/$eta$-reduction, not $delta$-reduction). This, in particular, does not give good justification as to why recursors of inductive types may be extended safely.

#let syntax_def = [
$"Terms" : t, f, A, B &::= 
    x &#text[(variable)]\ &space 
  | d &#text[(constant)]\ &space
  | m  &#text[(metavariable)] \ &space
  | app(f,t) &#text[(application)]\ &space 
  | lam(x,A,t) &#text[(abstraction)]\ &space
  | pi(x,A,B) &#text[($Pi$-type)] \ &space
  | univ_i &#text[(universe)]
$]
#let modmap(Sigma : $Sigma$,Phi : $Phi$,Theta,Gamma,Delta,t1,t2,A1,A2) = $Sigma | Phi | Theta | Gamma => Delta tack.r t1 => t2 : A1 => A2$

// #figure(syntax_def,caption: "Syntax of our type theory")
// The usual typing judgements one would expect apply. These judgement need to carry not only the usual variable context $Gamma$, but also a global constants context $Sigma$ to handle the type of constants, similarly to @MetaCoq2025, as well as a metavariable context $Theta$ that holds, for each metavariable, both the context and the type of said metavariable, similarly to @Kovacs2020. The idea is that constants may be mapped to some term containing "holes", i.e metavariables, allowing us to make the modular maps.

// We define a judgement $modmap(Theta, Gamma,Delta ,t,t', A, A')$ encompassing the behaviour of the modular map in practice. This judgement carries the same contexts found in the aforementionned typing judgements, as well as a mapping context $Phi$, which maps constants to the bundling of a metavariable context and a term that may contain the metavariables present in the context it's bundled with. The judgement states tracks both the base variable context and a variable context for the modularly mapped term, as well as the type of both the original term and the modularly mapped one. The modular map acts structurally over the usual constructors of our type-theory, and relies on the mapping context to translate constants into their modular map. Furthermore, when modularly mapping a constant, the metavariable context it carries is weakened/lifted, such that every metavariable lives in some telescope over translated variable context.

#let wk(w,body) = $attach(arrow.double.t,br: #w) #h(-0.1em) body$
#let cons(Gamma,x,A) = $Gamma,x : A$

#let modmap_univ = $prooftree(
  rule(modmap(Theta, Gamma,Delta ,univ_i,univ_i, univ_(i+1), univ_(i+1)))
)$

#let modmap_var = $prooftree(
  rule(
    modmap(Theta, Gamma,Delta ,x, x, A, A') ,
    (x : A) in Gamma,
    (x : A') in Delta,
  )
)$
#let modmap_const = $prooftree(
  rule(
    modmap( wk(Delta, Theta), Gamma, Delta, d, t, A, A') ,
    ((d : A) mapsto (Theta,t : A')) in Phi,
  )
)$
#let modmap_mvar = $prooftree(
  rule(
    modmap(Theta, Gamma_1, Delta_1, m, m, A, A') ,
    (m : (Gamma_2,A)) in Theta,
    Gamma_2 subset Gamma_1,
    Delta_2 subset Delta_1,
    modmap(Theta,Gamma_2,Delta_2,A,A',univ_i,univ_i)
  )
)$
#let modmap_app = $prooftree(
  #rule(
    $modmap(Theta_1 union Theta_2, Gamma, Delta, app(f, t), app(f', t'), B[x := t], B'[x := t'])$,
    $modmap(Theta_1 , Gamma , Delta, f, f', pi(x, A,B),pi(x,A',B'))$,
    $modmap(Theta_2, Gamma,Delta ,t,t', A, A')$, $"MV"(Theta_1) inter "MV"(Theta_2) = emptyset$
  )
)$
#let modmap_pi = $prooftree(
  #rule(
    
    $modmap(Theta_1 union Theta_2, Gamma, Delta, pi(x, A,B),pi(x,A',B'), univ_max(i,j), univ_max(i,j))$,
    $modmap(Theta_1,Gamma,Delta,A,A',univ_i,univ_i)$,
    $modmap(Theta_2,(cons(Gamma,x, A)),(cons(Delta,x, A')),B,B',univ_j,univ_j))$, $"MV"(Theta_1) inter "MV"(Theta_2) = emptyset$
))$
#let modmap_lam = $prooftree(
  #rule(
    
    $modmap(Theta_1 union Theta_2, Gamma, Delta, (lam(x, A, t)), (lam(x,A',t')), pi(x, A,B),pi(x,A',B'))$,
    $modmap(Theta_1,Gamma,Delta,pi(x, A,B),pi(x,A',B'), univ_i, univ_i)$,
    $modmap(Theta_2, (cons(Gamma,x, A)), (cons(Delta, x, A')), t, t' ,B, B'))$, $"MV"(Theta_1) inter "MV"(Theta_2) = emptyset$
))$
#let modmapJudgementSet = [#grid(columns: 2,column-gutter: 2em)[#block(inset: 0.3em,stroke: 0.1em)[$modmap(Theta, Gamma,Delta ,t,t', A, A')$]][(In global context $Sigma$, mapping context $Phi$, metavariable context $Theta$, term $t$ of type $A$ in context $Gamma$ maps to term $t'$ of type $A'$ in context $Delta$)]
// #mathpar(modmap_univ, modmap_var, modmap_const, modmap_mvar, modmap_app, modmap_pi, modmap_lam)
]

// #figure(modmapJudgementSet, caption: [Judgement rules for mappings])

