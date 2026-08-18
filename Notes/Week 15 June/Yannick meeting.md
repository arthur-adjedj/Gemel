Yannick isn't available for meeting this week, so this is just a pack of notes of what I did last week.

Least important first:
Spent friday (12th) incorporating feedback from the rehearsal on my slides, I then spent my slides to Thibaut, Meven and Kenji on monday (15th) and spent monday fixing my slides


Spend the first part of the week consolidating parts of the Gemel code, especially around feature functors. The syntax to construct feature functors is now finally exposed to the users, and having it be available gave me thoughts about how to go moving forward.

I don't believe feature functors to be a sensible basis for composability, even more so when it comes to defining "feature definitions" (I still don't know how to call these), i.e the possibility of composing definitions done on extensions. To make sure we use all of Lean's existing scaffolding, staying in the territory of "real" inductive types and declarations is extremely useful. The main (apparent) issue with that until now was diamonds in modular code. I think that is solvable though. 

The idea goes as follows: rather than reason in terms of "extensions", we should really just think in terms of merging various definitions. Take STLC for example, as well as an extension with natural numbers:

```hs
inductive STLC where
  | var : Nat → STLC
  | app : STLC → STLC → STLC
  | lam : STLC → STLC

modular
  inductive NatSpec extends STLC where
    | zero : NatSpec
    | succ : NatSpec → NatSpec
    --         P         P0        PSucc     n
    | natRec : NatSpec → NatSpec → NatSpec → NatSpec → NatSpec
```

Instead, what we should really care about is two separate inductive types, one being STLC, the other being
```hs
-- not extending anything here, just a normal inductive
inductive NatSpec where
  | zero : NatSpec
  | succ : NatSpec → NatSpec
  --         P         P0        PSucc     n
  | natRec : NatSpec → NatSpec → NatSpec → NatSpec → NatSpec
```
Now all that matters is how things are merged with one another, i.e `inductive STLCNat := STLC + NatSpec`
Once this is our basis, doing `mod def f extends g, h`s where `g` is a function over STLC and `h` one over `NatSpec` amounts to:
1. modmapping `g` and `h` respectively
2. "merging" the two modmapped declaration to fill the fillable holes
3. only then leave obligations for the user to complete, if necessary

Now remains the obvious question: how does one merge 2 modmapped functions, let alone an arbitrary amount of modmapped functions. Two obvious options:
1. If we only care about merging matches, not proofs, we simply assume named matchers have the same names between one another, we simply merge the branches of each, warranted they have the same shape
2. If we wanna merge proof holes as well, we should instead progressively traverse a "main" term (eg the modmap of `g`), follow the same traversal in the modmap of the other (eg `h` here), and whenever encountering an mvar in the modmap of g, assign it to whatever is in the modmap of `h` here. I fear this may be brittle in some way that I have yet to predict ? It does nonetheless seem like the most logical/structured way to do things, so I think I will look into this one more.

If we adopt the idea that things should be done through merges rather than modular buildups, we should abandon the idea of feature functors, altogether, or at least declare that feature functors should only be "inductive extension", and not "extend with new ctors", since the second doesn't really fit this narrative. I still need to think more about all this before starting the actual implementation.