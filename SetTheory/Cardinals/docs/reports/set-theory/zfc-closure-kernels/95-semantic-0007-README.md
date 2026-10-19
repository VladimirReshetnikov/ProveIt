# Portable logical-basis and bundle experiments

**Result:** the complete K/S/Peirce alternative has a retained **250-state**
binary table. The 264 bundle-reassociation encodings have best cost
**245 states**, attained by the original arrangement. These experiments
do not establish a machine below 245 states. No final Coq/Lean endpoint
for the changed 250-state source and table has been closed.

The ordinary mathematical construction is described in
`foundations_notes.md`: both directions of the numerical calculus
equivalence, the changed ten-row proof-stack macros, preservation of
cofinal proof coding after removing the fourth AX field, and the scope of
the literal binary audits. Exact Hilbert certificates are independently
replayed. A small selected vendor directory makes all required replay
commands local and independent of the original workspace location.

## Required replay

From this directory, with Python 3.10 or newer:

```sh
python verify.py
```

This uses the Python standard library only and performs finite work:

- Checks the hashes of 30 unmodified selected dependency files.
- Replays the 77-node K/S/Peirce proof of the original four-variable L.
- Independently parses and checks the upstream L-only proofs of K, S
  and Peirce: 111 declarations, 106 MP steps.
- Replays the 299-node and 251-node minimal-logic bundle proofs.
- Checks the generic stack macro identities, including early halting on
  the falsity code, and the finite fixed-falsity countermodel.
- Rebuilds the exact 250-state table, checks the correspondence to the
  independently emitted new source, all 8,794 affine instruction cases,
  and the sparse/dense blank prefix of 407,915 steps.

The reconstructed table must have SHA256
`125b42fb7ac3db95e43f74e20d75cbfde543de71354e8ee488152ecd2e90dcc1`.
It uses start state 0, working states 0–249, halt target 250, and contains
all 500 transition rows. The file format is `state read write move next`.

The audit reuses the inherited affine register-box contracts as explicit
macro assumptions. It does not silently change their rules, prove an
internal-ZFC proof-code representation, or invoke a new Coq/Lean endpoint.
The ordinary new-enumerator completeness argument is supplied in the
notes; a final proof-assistant port remains open.

For only the small logical certificates:

```sh
python verify.py --logic-only
```

## Optional finite cost searches

The original measurements and every case of the 264-bundle search are
retained. To rerun the 1,296 basis orientations and the 264 bundle cases:

```sh
python verify.py --searches
```

This takes roughly two minutes on the research environment and may take
longer elsewhere. It rewrites search summaries and the corresponding best
input files. It does not rerun annealing. The retained 133-rule annealing
witness is `routing_KSP_best/search45.json`; checking that witness and
the exact final table does not depend on the duration or randomness of
the original search. Search results are not universal lower bounds.

The first-pass source emitter can be rerun independently:

```sh
python basis_experiment.py
```

It produces the named Wade tables and costs. The smaller named-Wade
K/S-only table is an incomplete research experiment until classical
completeness of the enriched quantified system is proved. Likewise raw
fixed-falsity exploratory JSONs are cost observations, not complete
calculus claims. `status_index.json` records the final assessment of each
variant. The finite matrix refutes L[u:=F]+K as a pure propositional basis
even after EFQ and DNE are added; it does not interpret the additional
quantifier and equality schemas.

## Artifact map

| Artifact | Purpose |
|---|---|
| `foundations_notes.md` | Complete mathematical argument, costs, proof macros and limitations |
| `ksp_to_lukasiewicz.json` | Exact forward Hilbert certificate |
| `prove_ksp_lukasiewicz.py` | Generator and independent node replay |
| `check_upstream_lukasiewicz.py` | Independent reverse-basis proof replay |
| `flat_bundle_equivalence.json` | Both minimal-logic bundle certificates |
| `prove_flat_bundle.py` | Bundle certificate generator and node replay |
| `generic_proof_macros.py` | Symbolic identities for arbitrary helper count, including m=10 |
| `propositional_countermodels.py` | Exhaustive finite matrix replay |
| `basis_results.json` | Initial complete/incomplete basis cost measurements |
| `basis_orientation_results.json` | 1,296 parameter and order search summary |
| `flat_bundle_results.json` | Fully flattened 24-order search |
| `bundle_shapes_results.json` | All 264 n-ary conjunction encodings |
| `routing_KSP_best/` | Literal 250 table, grammar witness, source correspondence and runtime evidence |
| `routing_flat_bundle_best/` | Best fully flattened source and grammar search inputs |
| `vendor_manifest.json` | Exact dependency hashes and source labels |
| `appendix/DirtySeed35.lean` | **UNCOMPILED** original-source specialization, no binary theorem |

## Provenance

The published source and proof calculus are due to Mira-Cult, Jeff
Ketchersid and Andrew James Wade; this work uses the exact source pin
`297ab8df7e5de329605c3875b4934643b371a5e3`. The current ProveIt declarations
were inspected at `6d69a46dce1de15397a9d2448dcc946d08c90327`. Selected
routing and affine-checker dependencies come from the recovered 245
package and retain its provenance record and notices. Relevant MIT-0
licenses are included under `vendor/wade` and
`vendor/route245/reference/context246/sources`.

The newly authored top-level proof generators, replay adapters,
experiments and notes are made available under MIT-0 for integration in
ProveIt; see `LICENSE`.
