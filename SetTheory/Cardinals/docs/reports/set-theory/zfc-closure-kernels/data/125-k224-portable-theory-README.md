# Theory and logical certificates for the K224 research package

## The actual machine's logical family

The main candidate retains the original eight logical rows and membership
vacuity. Its only theory change is the equality helper

    Eq(a,b) -> All_{RelCode(a,b)} Eq(a,b),
    RelCode(a,b) = 4 P(a,b)+1.

It also cancels eight redundant numerical negation constructors. The old
whole-bundle gate c!=a,b remains, and the K matrix and private binder both
remain the actual opaque code c. The two existential-macro reassociations
used in the source are closed register-program reassociations computing
the same constructor, not a change to the K formula.

`k_equality_helper_extension.md` gives the new uniform finite-proof
calibration of this exact helper family with the current K theory. Its
essential extra step is to interpret the matrix's equality first and then
choose the actual matrix/private code c from that interpreted matrix.
This avoids silently reusing the old CP/GIC actual-code argument from
Source 116. No full primitive equality-vacuity derivation is asserted.

`fused_k_theory.md` explains the eight elementary cancellations. The
certificate specific to the independent helper binder is
`rel_helper_fusion_certificate.json`, with 1,563 closed Hilbert proof
nodes. It uses only K/S/Peirce, the literal retained rho2/rho6 rows, MP,
and theorem GEN. K/S/Peirce have their pinned derivations from rho8 in
upstream CD230. It assumes no set axiom or freshness fact.

`bind_rel_fusion_certificate.py` substitutes k=m=c and
kappa=RelCode(a,b) and checks that the certified fused formula is exactly
`emitter_contract.json`'s canonical expression. The fresh receipt
`rel_fusion_emitter_binding.json` records that match and both hashes.

## Newly replayed exact-helper evidence

`rel_helper_certificate.json` integrates the actual Rel-code helper with
the membership-indiscernibility bootstrap. It expands every primitive
symmetry premise using rho7 and the actual helper; it transports the
helper's Rel-code auxiliary to the fixed Eq-code auxiliary used to define
indiscernibility. It contains 68 checked closed roots, 59,947 proof nodes,
and 54,980 formulas. Its independent checker accepts neither primitive
symmetry leaves nor old canonical Eq-code helper leaves. It rejects four
adversarial controls, including an arithmetically wrong helper binder.

TAUT leaves in this larger certificate are independently Boolean-checked
propositional tautologies. In the current calculus they abbreviate finite
derivations from retained rho8/rho6, through K/S/Peirce and explosion. No
positive canonical-V axiom is added. This clarification matters because
some verbatim Source 116 metadata describes its older canonical-V route
to the same propositional basis.

These finite certificates check explicit proof instances and the exact
formula interface. The arbitrary-label theorem and current-K consistency
calibration are the separate uniform mathematical proof. None of these
files claims a newly compiled Rocq or Lean endpoint. Transition counts,
source/runtime simulation, the state fold, and blank initialization have
their separate candidate-specific certificates in the main package.

## Reproduce the checks

All commands use the Python standard library. From this directory:

```sh
python -O check_rel_helper_certificate.py
python -O check_fusion_certificate.py rel_helper_fusion_certificate.json --output rel_helper_fusion_certificate_receipt.json
python -O bind_rel_fusion_certificate.py emitter_contract.json
python -O source116/proofs/check_general_kappa.py
python -O source116/proofs/replay_indiscernibility.py
python -O source116/audit/check_independent.py
```

The last three commands replay the restored logical subset of Source 116:
169 roots/27,486 nodes for all helper builders; 51 roots/51,413 nodes for
the saved indiscernibility certificate; and 93 additional edge roots/
128,379 nodes in its independent audit. The general-helper suite's
Rel(a,b) lane has 20 roots/3,384 nodes. Those original modular checks keep
some derived-rule interfaces separate; the new 68-root actual-helper
certificate closes the symmetry/helper interfaces for the main family.

Generators are included for reproducibility:

```sh
python generate_rel_helper_certificate.py
python generate_fusion_certificate.py --equality-binder kappa --output rel_helper_fusion_certificate.json
```

The two new certificate checkers import no generator. The fusion binding
imports only the independent Hilbert checker, reads the emitter contract
as data, and compares symbolic constructor trees for arbitrary natural
parameters. Some verbatim Source 116 regression drivers do generate
proof objects; their independent rule checks treat those objects as
untrusted input.

## Provenance

The upstream K230 proof providers are pinned to
`elliotglazer/k230-rocq` commit
`3142e4dd980f0be12f4abb636c4ae2528afc17eb`.

The restored Source 116 logical files come from ProveIt commit
`ad8cbe8249445f43408617e88a0edb668b00248d`, under
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels`.
`source116/restoration_manifest.json` gives every original repository
path, restored path, and SHA-256. The original files are copied unchanged;
fresh replay receipts are additional files. The restored subset contains
the logical proof material needed here, not the old frontend/runtime
package.

Key result hashes are:

| Artifact | SHA-256 |
|---|---|
| Actual Rel-helper certificate | `3cba11f96eb71dcaeac32b69e662aa640d7728e18fd8b3b995e709555119c23b` |
| Independent-helper fusion certificate | `fc8cf39949eafa8f7e5a23d5db64941ea237f79ba1ac976ee8a3b6d918324120` |
| Exact emitter contract | `9ca4077ff110f7a644982eb23fa74b2ef361f79f17a7e402b093c4759d48909e` |

## Additional research, not used by the main machine

`conditional_k_calibration.md` proves that conditionally seeded K+IR is
equiconsistent with ZFC, by a two-marker hereditary-domain interpretation.

`native_fixed01_calibration.md` proves a further fixed input0/output1
conditional family is calibrated even at codes0 and1. Its upper
interpretation deliberately permits every raw object to have a member.

`k_schema_obstructions.md` shows why deleting support loses the required
strength, via an explicit rational-order model, and why conditional K
cannot recover raw emptiness directly. These counterexamples motivate
the more careful hereditary interpretation.

`enumerator_adaptation.md` records the unchanged proof compiler, the
explicit cofinal reset family needed for the nonzero proof cutoff, and
the optional logical-row permutations considered during the search.

The conditional/fixed01 theories are research results and compiler
alternatives. They are not invoked to certify the main machine.
