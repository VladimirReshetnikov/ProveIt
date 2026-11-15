# PA194H5X: a new equality-witness emitter

The accepted construction in this directory is **PA194H5X**, with 194 working states and a separate terminal state. Its exact dense table is `machines/PA194H5X/machine.tm`, with start 0, working labels 0 through 193, and terminal 194. The tape is the all-zero two-way infinite binary tape. Every transition writes and moves, including transitions into the terminal state.

The source changes the ordinary equality-witness schema

    U(D, E(H,D) -> 1) -> 1

to the independent-consequent schema

    U(D, E(H,D) -> 1) -> A.

Here A is the independent first AX operand. The sixth quantifier-distribution head has its original, unexchanged premise order. The source retains explicit-binder generalization `U(c,h)`, no-dummy-push MP, cache-only Shift, and eleven AX entries with the real fourth field. Exact free-term binding finds identity parameter maps in every head of the accepted machine; the search's permission to permute parameters did not remain in the selected output.

The parent report supplies the written iPRA proof of the schema equivalence and its PA calibration. This directory's source, table, and tape certificates establish the implementation part. They are executable mathematical evidence, not a new Lean or Rocq kernel proof.

## Accepted state budget and verification

- 134 fixed controls + 69 raw AX readers - 9 simultaneous local folds = 194 controls.
- 189 AX macro tokens, 3,677 resolved primitive instruction sites, and 4,786 branch outcomes.
- Construction-level symbolic verification: all 4,786 outcomes; 1,546,312 symbolic steps.
- Independent literal verification: all 4,786 outcomes; 1,110,171 symbolic steps; four generic list lemmas reconstructed from literal rows; no arithmetic-box oracle.
- Complete blank startup: 57,922 transitions, checking every nonzero tape cell and the entire clean source frame.
- Affine clock/frame audit: positive duration constants, zero net motion at all nonhalting source boundaries, source-address closure, and the single literal halting boundary.
- The exact dense graph is absent from all 139 spanning 194-state classes in the current pinned corpus, even under the expanded symmetry test; the parent census contains its independent novelty receipt.

Dense SHA-256:

    caffdd9f10d87d0d050eff07ab8f6e8edd9ab443aa94c948f03ee5316e37b614

Native SHA-256:

    f45696ad9e78599bcc469d887c6295a4dc4afa00ff90458e230c9ee3ad3966d3

## Offline reconstruction

All required code and frozen inputs are local. Python 3.10 or newer and its standard library suffice. Run without `-O` or `PYTHONOPTIMIZE`.

```sh
python3 -B construction/build_PA194H5X.py --output /tmp/rebuilt-PA194H5X
python3 -B check_emitter.py /tmp/rebuilt-PA194H5X --output /tmp/rebuilt-emitter.json
python3 -B verification/check_literal.py /tmp/rebuilt-PA194H5X --output /tmp/literal-replay
```

The final command writes `PA194H5X` beneath its output directory. Copy those four independent certificate files into `/tmp/rebuilt-PA194H5X/independent/`, then run:

```sh
python3 -B verification/physical_ipra_audit.py --machine /tmp/rebuilt-PA194H5X --output /tmp/closure-audit.json
```

The frozen full results are already retained under `machines/PA194H5X/independent/` and `physical_ipra_audit.json`. The frozen `construction/build_PA194H5X.py` does not search for grammars or folds and checks exact table hashes. The exploratory assembler is not needed to reproduce the accepted result.

`verification/exchange_certificate.py` reproduces the inherited 61-line K/S/MP premise-exchange proof. It connects the ordinary and exchanged sixth heads once K and S are supplied by the unchanged dominated implication basis. The parent report supplies the explicit endpoint dependencies.

## Research status

No valid machine below 194 states is established here. Exploratory 195-state files are clearly named and are not accepted replacements for the requested 194-state bound. Searches include ordinary/exchanged sixth-head variants, independent schema-parameter permutations, fixed and individual-occurrence binary-tree rotations, equal-length head-order exchanges, radix-five implementations, fixed-consequent shifts, and coupled positive forms of the first logical head. Their logs distinguish effective reader scores from actual validated machine sizes.

The accepted ordinary-head h5X search performed 9,391,599 mutation iterations in 900.004 seconds, accepted 1,597,061 mutations, and reached effective score 60. Its 200 recorded hits are frontier occurrences, not necessarily 200 distinct semantic machines. The first score-60 hit occurred at iteration 1,537,756. These stochastic searches do not establish a lower bound.

See `PROVENANCE.json` and the retained licenses for unchanged ancestors. The compiler, arithmetic-runtime checker, independent literal induction engine, and list-source resolver are attributed inherited software; the new contribution is the schema change, its literal realization, new search inputs and mutations, and the reconstruction/certification of this candidate.
