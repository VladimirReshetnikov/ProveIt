# Sources, checks, and review status

This is a new independent follow-on. Frozen Reports 43 and the square/product82 counterfamily were read only, and no upstream code or saved schedule was executed. No original report was modified.

The proof was developed from the exact files read successfully at the start of this investigation:

1. square-product82-counterfamily-20261004/COUNTERFAMILY.md, especially Sections 1, 4, 7, 8: literal P5=1, A even, p divisible by4, R=3 modulo4, and full actual outer coordinates.
2. free83-structural-packet-frozen-20261004/source/complete83_free_coefficient_scout.md: literal V, Na, Ns and complete product interface.
3. free83-structural-packet-frozen-20261004/author/early_auxiliary_norm_lemma.md: unconditional auxiliary square/sign descent, including exact exceptional negative solutions.
4. free83-inner-families-release-20261004/author/PROOF.md and SIMPLE_FAMILY_ADDENDUM.md: odd-index extension and its congruence formulation, used as context rather than as a proof of the new obstruction.

The root recovered the delivered Report43 bytes separately under recovered-delivered-packages/free83-report43, with delivered ZIP SHA256 501af9d4cb0666caef0d70ccd165e0191572f24346653c81af123f275d6871c9. This recovery and authentication were reported by the root, not performed by this worker. Input-source hashes are deliberately not invented in this packet. The checker is purely independent bounded arithmetic and does not depend on access to source directories.

Independent mathematical review:
- The check_even_rank_obstruction worker confirmed the full nonsquarefree Na=1,Ns=Delta proof, and strengthened the residue lemma to all strong indices m rather than only even m.
- The root reported its own full proof review PASS and the independent auditor audit_even_rank_nonextension PASS.

The root-visible proof is self-contained except for the explicitly stated elementary auxiliary square/sign lemma from the authenticated Report43 packet. Its hypotheses are checked directly: the fixed five-factor product is1, hence Na*Ns=Delta and all required factor-size bounds hold. Generic circuit normalization, Delta squarefreeness, and f=chi_A(m) are not assumed.

The independently authored checker ran successfully under normal Python and python -O, producing byte-identical CHECKS.json and CHECKS.optimized.json. It checks 455 complete finite Pell residue periods, 7200 odd-index coprimality cases, 14560 nested/nonsquarefree strong-lattice residue cases, and 21 small strong-divisor candidates. Finite checks are corroborative only.

Scope is fixed-family nonextension, not free83 language soundness. Replacing some retained five-factor/outer witnesses may avoid this theorem and is unresolved.
