#import "@preview/curryst:0.5.1": rule, prooftree
#let rule-set(column-gutter: 3em, row-gutter: 5em, ..rules) = {
  set par(leading: row-gutter)
  block(rules.pos().map(box).join(h(column-gutter, weak: true)))
  v(row-gutter)
}

#import "@preview/lemmify:0.1.8": *

#let(theorem, lemma, example, proof, rules: thm-rules) = default-theorems("thm-group", lang: "en", thm-numbering: thm-numbering-linear)
#show: thm-rules

// #set text(size:9pt)
#set par(first-line-indent: 1.5em, justify: true)
#set cite(form: "prose", style: "citation-style.csl",)
#set quote(block: true)
#show quote: set pad(top : -1.5em, bottom : -0.5em)
#show math.equation.where(block: true): set par(leading: 2em)
#let aa(body) = text(fill:red, "AA: " + body)
#let yf(body) = text(fill:purple, "YF: " + body)
#let nt(body) = text(fill:red.lighten(20%), "NT: " + body)
#set raw(syntaxes: "Lean.sublime-syntax")
#let ie= emph[i.e.,]
#let eg= emph[e.g.,]

#align(center)[
  #title[Internship report: Modularity in Interactive Theorem Provers]
Arthur Adjedj (PhD Student)\
    Université Paris-Saclay, ENS Paris-Saclay 
]

#let abstract_margins = (left : 0.5cm, right: 0.5cm)

#let abstract(body, margin : 0.5cm) = {
  block(inset: (left: margin, right : margin))[#align(center)[
    #set align(left)
    #set par(justify: true)
    #body
  ]]}

#abstract[Interactive theorem provers (ITPs) do not easily allow users to adapt and extend existing codebases without either changing the original code or duplicating it.
The pattern of extending definitions occurs particularly often in 
programming language theory, type theory, and program verification,
leading to a lot of code duplication and high maintainance burden.
Existing approaches to this problem either require encoding datatypes as complicated expressions, obfuscating the development, or rely on meta-programming facilities which were underdeveloped in most ITPs until recently.\ 
We develop a principled way to produce modular code, leveraging the strengths of dependent types and modern meta-programming techniques.]

#abstract(margin: 0.3cm)[#emph[*Note.* This research topic has been collabaratively developed by Arthur Adjedj and Yannick Forster. Arthur Adjedj was supervised by Yannick Forster and hosted in the Cambium team at the Centre Inria de Paris during a five-month internship.]]

= Introduction

#aa[TODO some (most ?) of this should be put in related works rather than the intro.]
#aa[Emphasis to be put on the fact formalisations can be extended after the fact, see STLC case-study.]
Interactive Theorem Provers (ITPs), also known as proof assistants, are tools which allow for the development and mechanical verification of formal proofs. ITPs can be used to provide a very high level of guarantees for software (in particular the complete absence of bugs), and several projects make use of proof assistants to verify real-world software, such as the CompCert C compiler (@Leroy-Compcert-CACM), the sel4 operating systems kernel (@sel4), and AWS' authorization policy language, Cedar (@Cedar). They have also been used successfully to formalise landmark theorems in mathematics such as the Four Colour Theorem or the Feit Thompson theorem, and the use of proof assistants is on the rise in mathematics departments, with big mathematical developments like Lean's Mathlib library (@mathlib2020) getting more and more public attention. 

Like other programming languages, ITPs fall victim to the the fact that reusing definitions can be non-trivial. This is generally referred to as the *expression problem* (@Wadler98): 
#quote[“The goal is to define a datatype by cases, where one can add new cases to the datatype and new functions over the datatype, without recompiling existing code.”] In fact, reusing and adapting existing data structures and programs modularly is a challenge for which few solutions have been produced over the years in industrial programming languages (@ObjAlgEP). It is even worse for ITPs, where in addition to programs, one needs to adapt proofs and dependently typed programs as well. Most projects that try to extend existing formalisation resort to copying the original content and adapting it for its own purpose. 
Since proofs about programs are arguably even harder to maintain than programs, this copy-paste approach incurs a huge maintenance burden.

A central contribution on matters of modularity in regular programming languages, "Data Types à la Carte" (@Swierstra2008), provides a simple and elegant solution to the expression problem based on a parametrical approach to modular syntax in Haskell. This solution, however, cannot be easily adapted to ITPs since ITPs needs to ensure consistency via their type system. Instead, existing approaches either rely on complex encodings of datatypes that leak to the user, or on meta-programming.

"Meta-Theory à la Carte" (@Delaware2013) and "Pyrosome" (@Pyrosome) base their modularity on internal encodings of types (namely, impredicative church-encodings in the former, and Generalized Algebraic Theories in the latter). In both cases, the constructions are inneficient, incapable of extending previously user-defined inductive types (#ie expecting users to rely on the aforementionned encodings from the ground up), and expose the underlying internals of the encodings to the user.
Having to deal with encodings of types rather than types adds
a heavy burden in particular for new users interested in program verification.
The lesson to include inductive datatypes natively has been learned early by popular ITPs (namely Rocq and Lean), who at first had no primitive notions of inductive types in their systems and then resorted to add those. Nowadays, most systems usually posess a syntactic notion of (co-)inductive types, and justify the ability to define these via some classes of models, allowing users to work with the abstractions these types provide, rather than with their encoding in said models. The only popular system that still relies on encodings to define such types, and manages to hide their implementation details well, is Isabelle/HOL.

// #yf[Explain that now people do not work with datatypes anymore but with complicated encodings that are normally used to justify types in models -> there's a reason one wants to work in a nice system and not in a model for a nice system]
On the other hand, Rocq à la Carte (@Forster2020) relies on the meta-programming capabilities offered by the MetaRocq Project (@Sozeau2020a) to allow users to construct new inductive types and functions by merging other inductive types, and/or adding new constructors. New functions on a "merged" datatype can then be constructed by merging past functions. The metaprogram then uses the given piece of information to reconstruct a new inductive type, and new functions, based on the informations given by the user. While great for extending constructions "vertically" (#ie by adding constructors to a type), this system does not allow for horizontal extensions (#ie extending the type signature of inductive types and their constructors). Furthermore, this  approach has been hindered in the past by the lack of good metaprogramming frameworks in ITPs.

None of these systems, independently of whether they use encodings or the meta-programming, handle all of the type-system of ITPs they are implemented for (#eg none handle co-inductive types), or allow users to extend past formalisations "after the fact". Instead, formalisations have to be built from the ground up with the expectation that they will be extended with a specific framework in mind, making them much less useful for real-world uses.

= Extensions

This section presents the technical details of the LeanALaCarte implementation. The main three contributions are 1. A system for partially mapping terms 2. a DSL command for defining an inductive type as an extension to another based on that produces the appropriate partial mappings between the two 3. a DSL for defining definitions/theorems as extensions of others, thus reusing the appropriate informations "after the fact".

#aa[TODO section intro]
#aa[For each new thing presented, show the new syntax and how it can be used in practice. Build up an example over the sections using new tools progressively]

== Partial mappings

This section makes a partial attempt at justifying the implementation of partial mappings in our system, and why it can be trusted to make well-formed terms.

First, let's define the syntax we'll be using in this toy presentation. This is a basic dependently-typed system equiped with a predicative hierarchy of universes à la Russel, as well as constants and metavariables. For the sake of simplifying the presentation, we will assume constants cannot be unfolded (i.e we will only care about $beta$/$eta$-reduction, not $delta$-reduction). This, in particular, does not give good justification as to why recursors of inductive types may be extended safely.

#let univ = $cal(U)$
#let lam(x,A,t) = $λ (#x : #A) mapsto #t$
#let pi(x,A,B) = $(#x : #A) -> #B$
#let app(f,t) = $f space t$
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

#figure(syntax_def,caption: "Syntax of our type theory")
The usual typing judgements one would expect apply. These judgement need to carry not only the usual variable context $Gamma$, but also a global constants context $Sigma$ to handle the type of constants, similarly to @MetaCoq2025, as well as a metavariable context $Theta$ that holds, for each metavariable, both the context and the type of said metavariable, similarly to @Kovacs2020. The idea is that constants may be mapped to some term containing "holes", i.e metavariables, allowing us to make the partial maps.

We define a judgement $modmap(Theta, Gamma,Delta ,t,t', A, A')$ encompassing the behaviour of the partial mapping in practice. This judgement carries the same contexts found in the aforementionned typing judgements, as well as a mapping context $Phi$, which maps constants to the bundling of a metavariable context and a term that may contain the metavariables present in the context it's bundled with. The judgement states tracks both the base variable context and a variable context for the partially mapped term, as well as the type of both the original term and the partially mapped one. The partial mapping acts structurally over the usual constructors of our type-theory, and relies on the mapping context to translate constants into their partial mapping. Furthermore, when partially mapping a constant, the metavariable context it carries is weakened/lifted, such that every metavariable lives in some telescope over translated variable context.

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
    name:[$"MV"(Theta_1) inter "MV"(Theta_2) = emptyset$],
    [$modmap(Theta_1 union Theta_2, Gamma, Delta, app(f, t), app(f', t'), B[x := t], B'[x := t'])$],
    [$modmap(Theta_1 , Gamma , Delta, f, f', pi(x, A,B),pi(x,A',B'))$],
    [$modmap(Theta_2, Gamma,Delta ,t,t', A, A')$]
  )
)$
#let modmap_pi = $prooftree(
  #rule(
    name:[$"MV"(Theta_1) inter "MV"(Theta_2) = emptyset$],
    $modmap(Theta_1 union Theta_2, Gamma, Delta, pi(x, A,B),pi(x,A',B'), univ_max(i,j), univ_max(i,j))$,
    $modmap(Theta_1,Gamma,Delta,A,A',univ_i,univ_i)$,
    $modmap(Theta_2,(cons(Gamma,x, A)),(cons(Delta,x, A')),B,B',univ_j,univ_j))$
))$
#let modmap_lam = $prooftree(
  #rule(
    name:[$"MV"(Theta_1) inter "MV"(Theta_2) = emptyset$],
    $modmap(Theta_1 union Theta_2, Gamma, Delta, (lam(x, A, t)), (lam(x,A',t')), pi(x, A,B),pi(x,A',B'))$,
    $modmap(Theta_1,Gamma,Delta,pi(x, A,B),pi(x,A',B'), univ_i, univ_i)$,
    $modmap(Theta_2, (cons(Gamma,x, A)), (cons(Delta, x, A')), t, t' ,B, B'))$,
))$
#let modmapJudgementSet = [#grid(columns: 2,column-gutter: 2em)[#block(inset: 0.3em,stroke: 0.1em)[$modmap(Theta, Gamma,Delta ,t,t', A, A')$]][(In global context $Sigma$, mapping context $Phi$, metavariable context $Theta$, term $t$ of type $A$ in context $Gamma$ maps to term $t'$ of type $A'$ in context $Delta$)]
#aa[TODO fix spacing]

#rule-set(modmap_univ,modmap_var,modmap_const,modmap_mvar,modmap_app,modmap_pi,modmap_lam)


]

#figure(modmapJudgementSet, caption: [Judgement rules for mappings])

The data contained in this judgement is enough to ensure any partially mapped term to be well-typed. Note that this theorem critically relies on the fact that this system only uses 
#theorem[If for all $((d : A) mapsto (Theta,t : A')) in Phi$, we have (1) $Sigma | epsilon | epsilon tack.r d : A$, (2) $Sigma | Theta | epsilon tack.r t : A'$ and (3) $modmap(Theta , epsilon, epsilon, A, A', univ_i, univ_i)$ for some $i$, then for all $Gamma, t, A$ s.t $Sigma | Gamma tack.r t : A$, there exists $Delta,t',A'$ s.t $Sigma | Phi | Theta | Delta tack.r t' : A'$ and $modmap(Theta, Gamma, Delta, t, t', A, A')$]
Proof: by induction on the typing judgement $Sigma | Gamma tack.r t : A$.
#aa[TODO: actually prove this #emoji.face.woozy]
== Inductive extensions

With this framework constructed, we may now use it to construct practical partial mappings, by producing useful mapping contexts. Since most constants in proof assistants are either inductive constructions (i.e an inductive type, a constructor or a recursor), or a declaration (i.e a definition or theorem), we first focus on inductive extensions, and then look at how they can be used to construct useful declaration extensions.\
First, let us look at the shape of an inductive type. Inductive types are shaped as follows:

#let ctor = $bold("ctor")$
#let motive = $bold("motive")$
#let minor = $bold("minor")$
$bold("inductive") "Ind"  [(p_j : P_j)]_j : [(i_k : I_k)]_k -> univ bold("where")\
space | ctor_1 : [(a_(1,l) : A_(1,l))]_l → I space [p_j]_j space [d_(1,k)]_k \
space space space space ...\
space | ctor_n : [(a_(n,l) : A_(n,l))]_l → I space [p_j]_j space [d_(n,k)]_k $

An inductive (family of) type(s) is composed of a number of different components: A list of parameters which constitute a context, a telescope of indices over that context of parameters, and a list of constructor. Constructor contain a telescope of fields living over the parameter context, and instantiate the indices of the inductive type they inhabit in a context containing those fields. Basic examples of inductive types include the natural numbers, list, and vectors (i.e list indexed by their lengths):
#align(center)[
#grid(columns: 2)[
```lean4
inductive Nat : 𝒰︀ where   
  | Z : Nat
  | S : Nat -> Nat
```][
```lean4
inductive Vec (A : 𝒰︀) : Nat -> 𝒰︀ where
  | nil : Vec A Z
  | cons : (n : Nat) -> A -> Vec A n -> Vec A (S n)
```]
]

There are many apparent ways in which an inductive type may be modified/extended, i.e by either adding, removing or modifying either parameters, indices or constructors. We will only focus on adding constructors here.
consider an inductive A of type $[(p_j : P_j)]_j -> [(i_k : I_k)]_k -> univ$ with constructors $[ctor_n]_n$, constructing a new type B with the same telescope of parameters/indices, as well as the same constructors + a new constructor $ctor_(n+1)$ of appropriate shape (in practice, B doesn't have "the same" parameters/indices/constructors, but rather correctly partially mapped ones), we may then partially map both A to B and its constructors to B's. The last apparent missing piece to this translation is the recursor. A recursor has the shape $"A.rec" : [(p_j : P_j)]_j -> (motive : [(i_k : I_k)]_k -> A -> univ) -> [(minor_n : ... -> motive (ctor_n ...))]_n -> [(i_k : I_k)]_k -> (a : A [p_j]_j [i_k]_k) -> motive [i_k]_k a$ 
As such, we can map this recursor to $"B.rec"$ by simply mapping all the arguments straightforwardly, and leaving a metavariable hole for the minor of the new constructor:

$\
"A.rec" => lambda [p_j]_j motive [minor_n]_n [i_k]_k a mapsto.long "B.rec"  [(p_j : P_j)]_j motive [minor_n]_n space ?m space [i_k]_k space a$

Using this, we provide a new Lean command which, given an inductive and new constructors, constructs another inductive type which extends the original one with these new constructors, adding the relevant mappings between the two:
```lean
inductive Var (α : Type) where
  | var : α → Var α
inductive Term α extends Var α where
  | lam : Term A → Term A
  | app : Term A → Term A → Term A
``` 

#aa[Mention all the various auxiliary declarations that Lean uses internally and that need to be mapped appropriately]
== Definition extensions

With inductive types interacting correcting with partial mappings, we now look into how declarations (i.e definitions and theorems) can be partially mapped correctly. 
The initial idea is simple: 
- take a given declaration
- partially map its term
- ask the user to fill-in the generated holes
- add the newly completed declaration to the environment
- map the new declaration to the old one

However, all of this turns out to quickly become very complex, mainly because the way lean declarations are elaborated is in itself very complex. This can be clearly observed by looking at how much a user-written declaration differs from what it ends up being elaborated to. #aa[TODO example that's ugly but not too much ?].
Two big reasons why the elaboration is so complex are respectively how Lean handles recursion and pattern-matching.
#aa[Mention that the holes can be solved in the same way tactic holes are solved.]

=== Recursive functions

Other proof-assistants like Rocq implement recursive functions using fixpoint constructs that are primitive to the abstract syntax, coupled with syntactic criterias for making sure recursive functions are well-founded. Lean, on the other hand, does not have such constructs. Instead, when a recursive function is defined, Lean tries to elaborate the function either into a structurally recursive term, using the recursor of whatever term decreases structurally in the recursive calls to write the function (à la @McBride1999), or tries to prove the function be well-founded, morally recursing over the accessibility predicate. 

Because of this, directly partially mapping the value of a recursive definition is not great, since it exposes internal encodings to the user, and asks one to manipulate those directly to extend the definition. Thankfully, Lean usually provides auxiliary lemmas that exhibit the original shape of the function that was defined. One of them, `foo.eq_def`, is a theorem of the form 
`
(a_1 -> A_1) -> ... -> (a_n -> A_n)  -> foo a_1 ... a_n = <foo's original definition>`
As such, rather than use the original value of a definition, we may instead partial map the right-hand side of its `eq_def` whenever available, and then reuse the existing pipelines Lean uses to translate such syntacticaly recursive functions to structurally recursive or well-founded functions. In particular, this allows us turn an originally non-recursive function into a recursive one if needed (e.g `Term.repr` example in the next section), or even change the termination measure that was originally used to adapt it to the new extended function.

=== Extending pattern-matches

Match expressions are a ubiquitous feature of modern functional languages, and proof assistants make no exception of that. In Rocq, matches are a primitive operation made explicit in the abstract syntax. In Agda, functions are defined as case trees, allowing users to branch on terms, similarly to regular matches. Lean however does diverge from this tradition a bit. For regular users, it may appear as though Lean does have match expressions: there are part of the concrete syntax and get appropriately pretty-printed when looking back at the abstract syntax too! However, they are in fact not part of the abstract syntax, it's all smoke and mirrors! Indeed, when encountering a `match`-expression, Lean elaborates this match down to the necessary inductive recursors, following technics described in @Goguen2006. Take for example a function of the form
```lean
def is_zero : Nat → Bool
  | 0 => true
  | n + 1 => false
```
The shape of the match get elaborated into an auxiliary function 
```lean
is_zero.match_1 : (motive : Nat → Sort u_1) → (x : Nat) → (Unit → motive 0) → ((n : Nat) → motive n.succ) → motive x
```

The function is then applied with the right arguments to explicit 1. the return type (called here `motive`) 2. the discriminant (`x`) and 3. the righ-hand-side of each branch:
```lean
def is_zero : Nat → Bool :=
fun x => is_zero.match_1 (fun x => Bool) x (fun _ => true) (fun n => false)
``` 

In practice however, the pretty-printer recognises when an application has a match expression as its head, and thus prints it back to the user as a `match`. 

When it comes to extending matches, we are now presented with two options: 
- Matches are simply encoded using recursors, we may simply partially map a given matcher and ask users to fill in the holes in it. 
- Extending matches amounts to adding new branches to it such that it covers the relevant constructors in the extended inductive type. As such, we may ask users to write down the relevant branches, in a syntax similar to how normal matches are written.

The second option turns out to be the most ergonomic, although it makes the implementation harder. In order to accomodate for this feature, when partially mapping the term of a given declaration, any application whose head is a matcher into a metavariable hole, saving the original shape of the expression along the way. When trying to solve that metavariable, the original shape of the matcher is reconstructed, similarly to how the pretty-printer handles this expression. We then elaborate the new match branches provided by the user, and re-elaborate this into a new match-expression. Note that the implementation does *not* do any anti-quotation (i.e reconstructing concrete syntax from the original abstract), and instead manipulates both the abstract syntax of the old matcher and the concrete syntax of the new branches in parallel, using Lean's existing internals for elaborating matchers. The end-result is a legible syntax for extending past declarations. Take the previous example of inductive extensions where `Term` extends `Var`. Consider a function for printing a term of the type:
```lean
def Var.repr {α} [ToString α] : Var α → String
  | var x => s!"#{x}"
```
We may now extend this function for `Term` as such:
```lean
mod def Term.repr extends Var.repr where
  matcher match_1 with
  | app f x => s!"{Term.repr f} {Term.repr x}"
  | lam f => s!"λ {Term.repr f}"
```
In practice having matches be handled specially makes a clear distinction between the holes generated for matches and those generated by explicit uses of recursors, which usually only appear in proof terms generated by tactic calls such as `induction`. This in essence means our syntax for modular definitions offers a clear separation of concerns between proof holes, solved by tactics, and non-proof holes, solved by completing match branches
```mod def foo extends bar where
    <matchers>
  finally
    <tactics>
```
This sort of distinction appears is not new. Indeed `where finally` was already a feature in Lean, and could be used to fill-in proof holes after the fact:
```lean
def Vec.tl (v : Vec α (n+1)) : Vec α n :=
  match h : n+1, v with
    | 0, zero => nomatch h
    | k+1, succ _ tl => (show n = k from ?_) ▸ tl 
                        --rewrites the type of `tl` from `Vec α k` to `Vec α n`
  where
    finally
    injection h
``` 
Similarly, Rocq's `Equations` (@Sozeau2019) provide an "Obligations" system which serve a similar purpose.

= Making extensions modular
#aa[TODO section intro]

== Inductive modularity

== Definition modularity
#aa[Empty for now, no work has been done here, write down your ideas]

= Case study: extending STLC

In order to iterate on this implementation and ensure its usability, we studied the case of taking an existing implementation of STLC#footnote("https://github.com/amarmaduke/lean-stlc") which prove the strong normalization property of the system, and extended it with additional constructors, allowing us to modularly prove SN for the extended system. In particular, the original normalization was *not* built with modularity in mind, and was still extendable after the fact. The original formalisation is extrinsically typed, and follows the usual proof of normalisation using a logical relation.
#align(center)[#grid(columns: 2, column-gutter: 2em)[```lean
inductive Ty : Type where
| base : Ty
| arrow : Ty -> Ty -> Ty
```][```lean
inductive Term where
| var : Nat -> Term
| app : Term -> Term -> Term
| lam : Ty -> Term -> Term
```]]
We extend this base definition to add natural numbers:
#align(center)[#grid(columns: 2, column-gutter: 2em)[```lean
inductive Ty extends Ty where
  | nat
```][```lean
inductive Term extends Term where
  | zero : Term
  | succ : Term → Term
  | natRec : Term → Term → Term → Term
```]]

== Related works

// @Forster2020 already explores the angle consisting of extending inductive types vertically (#ie by adding new constructors or merging inductive types of similar shape), before exposing "obligations", #ie holes in the original definitions/proofs that need to be filled in by the user in order to complete the formalisation. Similarly, Pyrosome (@Pyrosome) additionally provides some forms of horizontal extensions (#ie adding new parameters and indices to inductive types), although limits itself to working for programming languages formalisation, and constrains such languages to be encoded as GATs instead of usual inductive types. \
// #yf[ maybe do all of related work briefly here?]  \


// #aa[Mention that recent progress in metaprogramming capabilities in proof assistants (#eg lean 4 and Mathis's current work) means making good modularity is becoming more accessible ?] \ 
// 

//= Objectives
//
//The main objective for this PhD thesis will be to provide a better understanding of modularity in ITPs, and to produce useful tools to answer the expression problem in a dependently typed setting in the process. This entails iterating on past attempts at solving the issue, developing principled ways to extend existing formalisations, and applying those to various case studies to refine the implementation. These tools will be implemented in the Lean 4 proof-assistant.
//
//The end result of this research will be a generic tool for modularity that could take an arbitrary formalisation and allow the user to adapt it in various ways such as extending user-defined (co-)inducive types both vertically and horizontally, tweaking existing definitions, and providing the opportunity to correct proofs from the original formalisation. \
//To give an example of what modularity would look like in practice, consider the original example for the expression problem, written in Lean:
//
//```lean
//namespace Example
//  structure EvalExp : Type where
//    eval : Int
//
//  def lit (n : Int) : EvalExp where
//    eval := n
//
//  def add (left right : EvalExp) : EvalExp where
//    eval := left.eval + right.eval
//
//  def ex : EvalExp := add (lit 1) (lit 2)
//end Example
//```
//
//This code defines, in the namespace `Example`, a record type `EvalExp` containing a single field `eval : Int`, as well as two functions `lit` and `add` to construct `EvalExp`, the former constructing such an exp from a given `n : Int` and another taking two `EvalExp`s and returning the addition of their respective values. finally, we can compose those to construct a `ex : EvalExp`, evaluating `ex.eval` gives `3`.  We now want to modularly extend this code by adding two new fields `toString : String` and `toStringCorrect : toString.toIntEval = eval`. The former is a string representation of the value, and the second a proof that parsing and evaluating that string as an arithmetic expression returns the same value as `eval`.
//
//```lean
//modular Example as ExtendedExample --Extend the previous namespace by adding two fields to `EvalExp`
//  extend EvalExp where
//    toString : String
//    toStringCorrect : toString.toIntEval = eval
//
//  lit.toString (n : Int) := n.toString --Fill in the obligations
//  lit.toStringCorrect (n : Int) := <some proof>
//
//  add.toString (left right : EvalExp) := s!"{left.toString} + {right.toString}"
//  add.toStringCorrect (left right : EvalExp) := <some proof>
//```
//
//Extending `EvalExp` with these fields necessitates populate the new fields for `lit` and `add`. Once that is done, the new, extended structure and definitions get added to the environment in the `ExtendedExample` namespace. In particular, `ExtendedExample.ex` gets automatically generated, with `ex.toString` having `"1 + 2"` as its value, and `ex.toStringCorrect` a proof that `"1 + 2".toIntEval = 3`.
//
//In Lean, even though inductive types are a primitive notion of the system, co-inductive types are not. In particular, Lean provides stricly encapsulated co-inductive predicates encodings, #ie the encoded types behave just like primitive coinductive types would if they were implemented, and do not leak their implementation. We thus also want to provide good modular reasoning on such encodings. This includes looking into the denotational semantics of type systems, in particular that of inductive and co-inductive types, and studying modularity as a mathematical notion in relevant models. Examples include Categories with Families, extended with Theories of Signatures à la Kovács to encode complex inductive types (@KovacsPhD), and Quotient Polynomial Functors (@Avigad2019), for which there already exist an implementation in Lean 4 (@QpfTypes).
//// Furthermore, when studying the categorical semantics of (dependent) type theories, a toposical tool known as Artin Glueing (@Wraith74) can used to modularly prove important properties of a type theory constructed by merging of two others. This is notably used to prove the strong normalisation property of Cubical Type theory (@Sterling2021), and may help us understand the metatheory of our work better. #aa[TODO remove artin glueing] \ 
//From a user-friendliness perspective, we may find inspiration for the syntax of our system in @Marmaduke2025, which presents a type system with open types and open function, allowing one to easily extend inductive types vertically. Developing automations, in particular tactics, to allow users to fill in the holes of definitions and theorems easily after extending an inductive type is of particular importance, and may be related to works in the field of proof-repair (@Gandhi2025 @Ringer2021).
//
//The development of modular tooling will be made through experimentations on various case studies to both better understand the ways in which modularity can be used in practical settings, and to develop useful modular formalisations and libraries. Potential case studies can be split in 4 categories:
//- Formalisation of programming languages and type theories: A given formalised type theory can then be extended by first extending its syntax and typing/reduction rules, and then adapting the logical relation to adapt to the added constructs. A good example, and potential case study, would be to formalise the Barendregt's Lambda Cube (@Barendregt1991), starting with the Simply Typed Lambda-Calculus (STLC) as a basis, building the 3 base vertices of the cube on top of STLC, and merging these 3 in various ways to build the remaining vertices of the cube. Another would be to look at "Martin-Löf à la Coq" (@Adjedj2024), and the many extensions that were built on top of the base formalisation (@Pedrot2024, @baillon2026 and @Subtyping2024). All of these formalisations are non trivial and have big codebases, containing about 30 000 lines of Rocq code each. Adapting the latter formalisations to "simply" be modular extensions of the former would be a great working example of real-world use.
//- Compilers and interpreters: The modular construction and verification of interpreters has been studied in the past  (@Pyrosome, @Michelland2024, @VanDerRest2022), and serve as good basis for our case studies.
//- Programming language semantics: Strata (@Strata) is a recent in-development library that aims to offer a unified platform for formalizing language syntax and semantics. Users of the library can construct new intermediate representations, referred to as _dialects_. The correctness of optimization passes over a program written in a given dialect is then discharged to a SMT solver. Instead of extending the trusted code base and relying on (sometimes) slow SMT procedures, the system could be improved by providing static proofs of correctness for the optimization passes. Since one can construct a new dialect by extending another, allowing for modular proofs of correctness for the passes is desirable.
//
//// #aa[I'm not sure what to say about Strata ? they seem to have some ways of extending a given dialect vertically, but they discharge all of their "verification conditions" (what those are I am not sure) to (untrusted) SMT solvers as far as I can see, so ithis doesn't feel all that relevant.] #yf[we can say that they can get rid of their SMT solvers and do everything natively in Lean]
// - Mathematics: While inductive types are used extensively in computer science, mathematics tend to rely more on record types, who come in many different flavours. Row types, and in particular row polymorphism (@row23) allow for some modular reuse of functions and theorems over records types. As such, being able to replicate this behaviour in systems that do not support such polymorphism through metaprogramming encodings should be explored.

// A tentative timeline for this PhD is as follows: Relying on a reimplementation of "Coq à la carte" in Lean 4, we will spend the first year focusing our efforts on providing a well-behaved notion and implementation of vertical and horizontal modularity, and use this to formalise Barendregt's Lambda-Cube, including the Calculus of Constructions. Once that is done, we will shift our focus towards being able to modularise existing non-modular developments such as Strata. Lastly, we will focus our attention on managing modular developments over types defined using encodings, such as Lean's co-inductive predicates. 

// #aa[We don't want to make a feature for a case-study, instead we have this problem in formalisations that they're not modular, and want to fix those (#eg horizontal modularity)]
// #yf[We're missing a concrete workplan: We will do X, then Y, then Z.] \
// #aa[(pre). Pretend lean à la carte is done by the time phd starts]
// #aa[1. Horizontal modularity is strictly necessary for #eg the lam-cube, namely for System F, so lam-cube as a case study and making horizontal modularity is the first step]
// #aa[2. Modularisation of non-modular developments, modularly extending an existing formalisation, #eg Strata]
// #aa[Ask yaël about potential issues with structures in Lean]
// #aa[3. Look into semantics encodings, #eg impredicative encoding, look into co-inductive predicates using that]
// 
// #aa[Writing down here as a temptative plan to discuss on monday before really redacting: 
// - First, dig deeper into the existing systems to wage the pros/cons of each, and make a list of wanted features/design plans
// - Experiment with toy implementations of a modular system, #eg a Lean version of Coq à la Carte that tries to implement basic expected features
// - Choose a case-study (#eg the lam-cube) and start work on this case-study with the help of the toy implementation (BTW I couldn't find any full formalisation of CoC in Coq (ignoring MetaRocq and their SN axiomatisation and Barras' incomplete work), so unless I'm mistaken, this "case study" could serve as a contribution of its own, ignoring modularity concerns)
// - Refine the implementation along the way
// - ..?
// ]

// = Adequacy
// 
// We believe that Arthur Adjedj is well-suited for this topic because he has a background in
// dependently-typed proof assistants and type theory. He worked on "Martin-Löf à la Coq" (@Adjedj2024), a formalisation of Martin-Löf Type Theory in Rocq, during an internship under the supervision of Nicolas Tabareau and Loïc Pujet, as well as " AdapTT: Functoriality for Dependent Type Casts" (@Adjedj2026) under the supervision of Meven Lennon-Bertrand. The latter paper uncovers a general notion of type-casting in dependent type theory that exhibits the functoriality of type formers, encompassing a core construct which underlies many recent works in the field. He has furthermore contributed to the Lean 4 proof assistant for many years. All these works have provided him a deep understanding of both the theory and implementation of ITPs.
// 
// Nicolas Tabareau is a key member of the Rocq development team, and has worked on proof translation between Rocq and Lean.
// He has coordinated large formalisations of type theory in Rocq that would have benefited greatly from modular methods.
// 
// Yannick Forster has worked on meta-programming in Rocq for years (@Sozeau2020a, @Liesnikov2020) and both informally and formally supervised projects, including a past effort in providing modularity to Rocq (@Forster2020). He has initiated the meta-programming rosetta stone project for Rocq. He is a member of the MetaRocq team and maintains strong connections to the development teams of Rocq (Matthieu Sozeau, Nicolas Tabareau, Hugo Herbelin), Rocq-Elpi (Enrico Tassi), Ltac2 (Pierre-Marie Pédrot, Gaëtan Gilbert), Agda (Jesper Cockx), and Lean (Sebastian Ullrich, Mario Carneiro)

#bibliography("biblio.bib", title : "References", style : "citation-style.csl")