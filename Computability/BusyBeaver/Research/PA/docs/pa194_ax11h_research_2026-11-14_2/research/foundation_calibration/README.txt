Foundation PA to ordinaryPAeq: written weak-arithmetic completion
=================================================================

Main theorem
------------
foundation_paeq_completion.tex proves, in current I-Sigma-1, the exact
uniform implication

  Proof_PA_current(d, 13)
    -> Proof_ordinaryPAeq(D_current(d), 13),

where D_current is an explicitly specified total primitive-recursive
proof transformer, 13 is the shared Foundation falsity code, and the
current Foundation revision is 32e1a0956a8622fad067328ca1959729a7634428.

The current source predicate is the one underlying paRefutation,
mappedPARefutation, and nativePAConsistency in
DiophantineConsistency/IPRAPA196Consistency.lean. It is not replaced by
the historical PA recognizer merely because they describe PA.

What is newly completed
-----------------------
1. The repaired formula-substitution identity is used in the source
   induction-axiom translation; its I-Sigma-1 proof is referenced exactly.

2. The historical full-PA proof-opening/closing induction is replaced by
   explicit OpenOne/CloseOne proof constructors and a fixed finite chain.
   The correctness invariant is a single Delta-1 proof-check statement,
   with the original formula and parameter count fixed.

3. The source induction supplier retains the source closure count while
   constructing a genuinely canonical target induction axiom with its
   own exact bound-variable support. Bounded recognizer witnesses are
   explicit; the unary matrix bound is the opened-body code, not the
   original closed axiom code.

4. The current source recognizer is bound to the historical syntax
   equations and to the target compiler on arbitrary internal codes.
   The only changed finite arithmetic leaf is explicitly handled:
   historical addEqOfLt requires z < y+1, current addEqOfLt does not.
   A literal six-node existential projection and fixed logical templates
   construct the current translated leaf from the supplied old proof.

5. The metatheory mismatch is addressed separately. Current PA-minus
   derives the historical bounded axiom without induction. The historical
   prenex Sigma-1 class embeds structurally in the current Sigma-1 class.
   Thus the historical I-Sigma-1 syntax lemmas apply in the current base.

Independent finite replay
-------------------------
From this directory (or pass the full script path), run:

  python check_closure_constructors.py --output closure_receipt.json

The replay checks 308 opening/closing chains, 140 canonical induction
readbacks, 36 existential projection instances, and 4 complete finite-leaf
adapters, including the exact translated addEqOfLt instance. It checks
8,828 distinct proof nodes against the actual ten in-place sequent rules.

The checker uses AST representations of the literal rules and a
hypothetical input proof for the old finite leaf. The separate
finiteImageProof source supplies that fixed proof. The finite tests check
the constructor equations and binders; the written induction proves the
uniform all-code theorem. Neither is described as a Lean kernel rebuild.

References
----------
references/manifest.json records the exact ProveIt source paths and SHA256
hashes for the historical calibration files and repaired current formula/
proof transport files. The current_endpoint/ directory contains the
independently retrieved current/historical Foundation source snapshots,
their manifests, and the exact coding-comparison script and receipt.

The mathematical endpoint was independently reviewed by proof_audit:
Open/Close invariants, both changed finite-axiom directions, the current
induction recognizer, hierarchy inclusion, and the all-internal-code
table argument were checked. This is independent written review, not a
machine proof certificate.

Integration
-----------
The TeX file is an include fragment requiring amsmath, amssymb, amsthm,
and a theorem environment. standalone.tex provides a minimal wrapper.
Compose this result with the separately supplied ordinaryPAeq-to-C4
compiler, command/scheduler simulations, physical TM proof, and the
existing one-way I-Sigma-1-to-iPRA transfer to obtain the requested
machine theorem. This folder alone proves only the named source endpoint.

