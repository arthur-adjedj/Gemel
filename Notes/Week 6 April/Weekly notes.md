Spent the week implementing the API for constructing adequate `MatcherInfo`s from the original ones, it seems to work well enough. I've also refactored the whole codebase by a fair amount to make it less flaky. I changed the syntax of `mod_def` to make it so that users can write match branches instead of tactics where matcherInfos are produced, and uses that to extend matches. I also found a bug in the equational theorems generator that's blocking my progress by some margin...
I have started writing a (modular-ish) formalisation of STLC to make the system robust and prove it's working (it's not yet but you see what I mean). The big goal for making this formalisation truly modular will be to construct and manipulate (inductive and functional) functors, I think inductive functors are trivially easy to implement, functional ones not so much, but I am thinking about it. I don't see how I could make "partial extensions" without breaking everything tbh...
I almost forgot: functions are now elaborated as predefinitions, which is huge since it gives things like doc-comments, modifiers, termination measures and auxiliary lemmas for free !
I'm quite sure some modifiers are currently not managed as they should. Namely, I saw in `MutualDef` that things like `meta` and `private` tags are managed *before* the predefs are even constructed, not after, TODO look into this 

Many things are still untested and surely buggy, namely:
- `where finally`: haven't tested it once
- extending theorems rather than defs : same
- Haven't tested extending well-founded functions too much, although most of those will rely on `eq_def` anyway so the details will be hidden
- I haven't given a single thought to mutual defs/inductives. In particular, the current syntax doesn't handle those too well
- I have also not tested nested types ! I assume the translation for matchers should be no issues, but I wonder whether the modmap for recursors is robust enough for this...
