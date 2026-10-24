# Review of the direct branch's logical calibration scope

An additional AI-assisted source inspection distinguished completed ordinary
mathematical dependencies from the absence of a new full proof-assistant build.

`direct/source/calibration/KEndpoint.lean` supplies both proof directions of
`KEndpoint.c222_iff_zf_refutation`. The declaration precedes the section with
machine-specific hypotheses; those hypotheses do not qualify this equivalence.

`direct/source/calibration/ConstructibleChoice.lean` supplies both directions of
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`, after the model-parameter
section has ended. These are unconditional proved theorem declarations rather
than conjectural bridges.

The retained factorial-carrier and derived-label texts give completed ordinary
arguments from the arithmetic source to finite C222 refutations and back. Some
preserved historical one-stack notes discuss earlier incomplete compiler
proposals; those earlier gaps are not missing obligations of the final direct
source used here.

The inspection found no ordinary-proof gap at this stated interface. It did
not compile or independently recheck the full transitive Lean development.
The precise claim is an ordinary mathematical proof, using the inherited
proved C222–ZF and ZF–ZFC refutation equivalences, that ZFC proves absence of
integer zeros if and only if Con(ZFC). No assumption of consistency is used.
