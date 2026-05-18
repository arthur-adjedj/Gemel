
#set text(size:9pt)
#set par(first-line-indent: 1.5em, justify: true)
#set cite(form: "prose", style: "citation-style.csl",)
#set quote(block: true)
#show quote: set pad(top : -1.5em, bottom : -0.5em)
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
#aa[TODO section intro]
#aa[For each new thing presented, show the new syntax and how it can be used in practice. Build up an example over the sections using new tools progressively]

== Partial mappings

== Inductive extensions

#aa[Mention all the various auxiliary declarations that Lean uses internally and that need to be mapped appropriately]
== Definition extensions

=== Extending matchers
#aa[Explain that the internal implementation of matchers does not reflect the kind of extension you would want to see in practice, mention auto-generalizations, and how they are actually handled in practice.]

= Making extensions modular
#aa[TODO section intro]

== Inductive modularity

== Definition modularity
#aa[Empty for now, no work has been done here, write down your ideas]

= Case study: extending STLC

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
// #aa[1. Horizontal modularity is strictly necessary for #eg the lambda-cube, namely for System F, so lambda-cube as a case study and making horizontal modularity is the first step]
// #aa[2. Modularisation of non-modular developments, modularly extending an existing formalisation, #eg Strata]
// #aa[Ask yaël about potential issues with structures in Lean]
// #aa[3. Look into semantics encodings, #eg impredicative encoding, look into co-inductive predicates using that]
// 
// #aa[Writing down here as a temptative plan to discuss on monday before really redacting: 
// - First, dig deeper into the existing systems to wage the pros/cons of each, and make a list of wanted features/design plans
// - Experiment with toy implementations of a modular system, #eg a Lean version of Coq à la Carte that tries to implement basic expected features
// - Choose a case-study (#eg the lambda-cube) and start work on this case-study with the help of the toy implementation (BTW I couldn't find any full formalisation of CoC in Coq (ignoring MetaRocq and their SN axiomatisation and Barras' incomplete work), so unless I'm mistaken, this "case study" could serve as a contribution of its own, ignoring modularity concerns)
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