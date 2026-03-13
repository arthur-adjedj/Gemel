Why was AutoSubst2 necessary for Rocq à la carte ?

First, let's implement a Rocq à la Carte equivalent framework. This implies providing the ability to:
- construct a new inductive type combining two others or adding new constructors
- extend existing functions 

The former is trivial, the latter less so. Design ideas:
First, if we restrict ourselves to the case of constructing a type `B := A + c` where `A` is a type and `c` a new constructor
- Initially, provide (potentially partial) mappings from one type to the other, namely:
  - `⟦A⟧ := B`
  - `⟦A.ci⟧ := B.ci`
  - `⟦A.rec motives minors Is major⟧ := B.rec (⟦motives⟧ + holes for potential added motives) (⟦minors⟧ + holes for new constructor(s)) Is ⟦major⟧` (TODO how to manage partial recursor apps ?)
  - Functions that *construct* terms of type *A* Should be trivial to translate, those that *take* a term of type *A* probably recurses on it and may have mappings with holes, including potential holes to the function arguments in case additional info needs to be given for the extended type
  - Interesting questions may arise around auxiliary functions ,e.g :
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

Once this base system for extensions is built, it *shouldn't* be too hard to add horizontal extensibility since it will "just" amount to having holes in the type and constructors, not just in the recursor.

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

How should the partial "mappings"/"substitutions" be stored and done ? I know `simp`/typeclasses/`grind` have some system of tabled resolution that should probably be reused here, I've never looked into it in depth, but it looks desireable here.

Other thing: obligations that are "morally the same" should get bundled together rather that expecting users to say the same thing multiple times