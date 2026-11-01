# Native NNF implies Gödel–Gentzen translation: author replay

The guarded author run `/tmp/ipra-native-forward-77hc1klz` passed all five modules and final authentication. The native NNF reader preserves positive atoms, reads negative atoms as intuitionistic negations, and retains native disjunction and existential quantification. The rewriting theorem proves this reader commutes with arbitrary capture-avoiding Foundation rewrites. `nativeForward` constructs a Hilbert proof of `native φ → φᴺ` by structural recursion on every classical NNF proposition; `theoryNativeForward` lifts it to an arbitrary intuitionistic `Theoryᵢ`, with no arithmetic or theory premises. This discharges the forward premise of the earlier conditional negation lemma for the new native reader. It does not define iPRA, bind the actual ZFC predicate or prove the remaining comparison `rhoᴺ → ¬¬native rho`.

The build uses frozen current source snapshots and rehashes five direct inherited Foundation source/object anchors and the Lean executable. It does not establish that the inherited objects were built from those sources or certify their transitive package closure. The complete check log records Lean metatheory axiom dependencies; the produced object-language calculus is intuitionistic. Independent replay is required.

Replay: `python3 Computability/DiophantineConsistency/research/ipra-refutation-logic/build-native-forward.py`.

- `IPRANativeFormula`: source `dcc5601c6d138dcf999efbf3d84f75dcef29aef4c0fd471c71c1216c0214abef`, object `662da3a362dcf0c996abf4b208868870bb3826594b6d7447d9233b5bcdf2c6fe`, full log `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `IPRANativeFormulaRew`: source `1540057f00458e3990b21cba869b44bd5651a30791beb750ea67a9d7c66cf1d4`, object `4cd6134dc5dee8fcba1b74b2d677061a33a5632e9b57c45327d1c07c4b8fe0d7`, full log `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `IPRANativeForward`: source `5939f2364aaa2730a2efbbcc54f820d05a5c6e051f14c57c0f3cc85052c6518d`, object `c6b356a31f82eccdfc6934f053dfd9c28ac883e094cfe80264717abf6d535d85`, full log `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `IPRANativeForwardTheory`: source `c24f61025d66c5f41918a19a2f04a284ebd138ad13564589e90753edad0c8b1c`, object `dc32dd85c012329e264904eca750485386f74f3cff33a2a3fa2eae772eb82a51`, full log `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `IPRANativeForwardChecks`: source `2803ad0d2367027d2965df65869a5dd07a81ae418fc6d212c9949d0c4b810495`, object `084f59a82a128dcb0d4f61b07aa4b0c65685eeb6d80d020de1765973d6fbb624`, full log `a3ea1dd70c16bdd02ee79f8cb2315b44e0f22277d63303c3ab5cd888b7b2ac55`.

State `8ea39344b43f13ebc55a79fa4728e689f9796f8287c14967788f2b46ea36464e`; manifest `e4d64b352bb5113aed3b1f2c7f56eb5ba9c900f28c45efe5cb1d2d90844e3142`.
