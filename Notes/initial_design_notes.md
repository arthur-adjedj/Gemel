Why was AutoSubst2 necessary for Rocq à la carte ?

First, let's implement a Rocq à la Carte equivalent framework. This implies providing the ability to:
- construct a new inductive type combining two others or adding new constructors
- extend existing functions 

The former is trivial, the latter less so. Design ideas:
First, if we restrict ourselves to the case of constructing a type `B := A + c` where `A` is a type and `c` a new constructor
- Initially, provide (potentially partial) mappings from one type to the other, namely:
  - `⟦A⟧ := B` 
  - `⟦A.ci⟧ := B.ci`
  - `⟦A.rec motives minors Is major⟧ := B.rec (⟦motives⟧ + holes for potential added motives) (⟦minors⟧ + holes for new constructor(s)) Is ⟦major⟧` (TODO how to manage partial recursor apps ?)+
  - Functions that *construct* terms of type *A* Should be trivial to translate, those that *take* a term of type *A* probably recurses on it and may have mappings with holes, including potential holes to the function arguments in case additional info needs to be given for the extended type
  - For other terms, the translation is applied structurally.s
  Interesting questions may arise around auxiliary functions ,e.g :
  - `A.casesOn`
  - `foo._match_i` for a function matching on an `A`
  - similarly, `foo.eq_i` and `foo.eq_def`, 
  - `A.below`/`A.brecon` : For a given type, we probably need to also provide mappings between their `below` variants
  - "sparse matches", e.g in the case
  ```lean
    inductive A where
      | a | b | c
    def foo : A → Nat 
      | .a => 1
      | _ => 0
    inductive B extends A with 
      | d
  ```
  Should `foo` get a partial hole or should the sparse match consume `d` in its wildcard ? How could one give the option to the user ?

Technically, "holes" in the partial mapping should probably me synthetic mvars probably ? The library should store a global maps that keeps the holes as loose bvars that are then instantiated at call-site with synthetic mvars. 

Caveat: 
- some holes may be unifiable easily, and so it might make sense not to expect users to fill in "trivial" obligations: should unification and/or automation be attempted for every obligation ? Probably not, but there needs to be a way for users to chose which holes should be automated away, and take control over particular instances of said holes when they want to.
It might make sense to rely on Lean's `autoParam`s for this.
- What about holes that are nested in other binders ? e.g in the future for horizontal extensions`⟦f (λ x : A => x⟧ := ⟦f⟧ (λ x : A  => x ?_)`, one must make sure that the scope of the mvar is the expected one.

Once this base system for extensions is built, it *shouldn't* be too hard to add horizontal extensibility since it will "just" amount to having holes in the type and constructors, not just in the recursor. Adding horizontal extensions implies also allowing users to add or adapt fields of some existing constructors

Questions I haven't thought about:
- What to do about typeclasses
- Same with other attributes (e.g should a theorem that extends a `@[simp]`-tagged theorem also be tagged as such ? Currently, there is no way to retrieve all tags for a given declaration sadly, should some be hardwired ? should the choice be given to the user ? if so how)
- Same with docs
- Should users be able to define types that do not *extend* types but rather *restrict* them, e.g by removing a recursor ? The mappings for that would be trivial since they would never contain holes, but is this desirable ?

/!\ BIG ISSUE
- Ironically, it won't be possible for users to modularly extend `private` and non-`@[exposed]`defs/theorems imported from other `modules`

Questions about syntax: 
- The users should be able to "extend" a library that was not initially built with modularity in mind
- Hopefully, "modular" blocks should be elaborated incrementally, that's a can of worms I'm very worried of getting into, this would definitely require some help from/communication with sebastian

How should the partial "mappings"/"substitutions" be stored and applied ? Relying on Lean's `DiscrTree` sounds the most sensible, it is already used in many other systems after all. It might make sense to work from the new `SymM` monad to do all the rewriting. It would also be cheap to do so since expressions in defs/theorems are already maximally shared! A quick look into the internals seem to show "backward rules" as a potential way to do the substitution and add the relevant holes, although it does not seem to allow for "nested" subgoals such as `foo (λ x => ?_)`. How much of an issue is this in practice ?

Other thing: obligations that are "morally the same" should get bundled together rather that expecting users to say the same thing multiple times

Note, one must ensure that an "extended" type must bind the same universes, and live in the same sort as the type(s) it extends.

Users should be able to "discard" now-untrue lemmas/def of a module, and have an error be thrown when the system tries to translate a discarded constant
Should users be able to extend arbitrary instances of inductive families, and not just straightforward ones, e.g should this be allowed ? I believe so, but I'm worried it could lead to conflicts/diamonds, similarly to what structures already deal with.
```
  inductive Foo (A) extends Prod A A where
    ...
``` 

important questions: how should a user specify what bundle of inductives+ defs/theorems should be modularly extended ? In particular, we should ensure users to have explicitly specify/extend auxilary/internal lemmas/defs by hand. **Internal details must stay internal**

"partial mappings", especially with horizontal extensions, should to be directed by both the type of the original term **and** the resulting type, e.g judgements of the form :
`Γ ⇒ Δ ⊢ ⟦t : A⟧ ⇒ t' : B`
where
`Γ` : The original context
`Δ` : The translated context
`t : A`: the term `t` of type `A` which translates to `t'` of type `B`
e.g wrt extending Lists to `Vec`s

```
∅ ⇒ ∅ ⊢ ⟦List.rec : (A : Type) → (P : List A → Sort u) → P [] → (∀ hd tl, P tl → P (hd::tl)) → ∀ l, P l⟧
        ⇒ Vec.rec : (A : Type) → (P : ∀ n, Vec A n → Sort u) → P 0 [] → (∀ n hd tl, P n tl → P (n+1) (hd::tl)) → ∀ n l, P n l
```
Given `A : Type`, `P : List A → Sort u`

`A : Type ⇒ ⟦A⟧ : Type ⊢ ⟦P : List A → Sort u⟧ ⇒ ?_ : ∀ n, Vec A n → Sort u` (i.e such a problem should leave a hole rather than try to "translate" an arbitrary `P`)
However, if `P` is either a constant with a suitable translation (e.g a function that ignores arguments such as `λ l => Nat`), the system *could* try to approximate a translation as `λ _ _ => Nat`, though should still allow the user to customize the motive when the approximation is not right.
Ideally: translations should be best effort, and backtrack to a suitable place upon failure (e.g when failing inside lambdas, backtrack out of the lambdas to avoid making the user eta-expand his solution if it's not needed). If the translation of a minor of a recursor happens, users should have the option to not just fix the specific minor, but also change the motive(s). 