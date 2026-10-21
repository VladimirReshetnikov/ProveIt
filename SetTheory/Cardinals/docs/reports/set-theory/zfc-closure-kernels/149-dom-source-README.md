# Source calibration for the 218-state candidate

This directory contains the complete, standard-library-only source reconstruction and finite control-flow certificate for the register source used by the 218-state binary machine. The binary transition table and its runtime/startup proofs are supplied separately in the machine directory of the release.

The mathematical change is to retain the original common additive input, set `U = oldD + z`, emit `GEN(U, oldH)`, and load `U` into the partially constructed fourth-parameter axiom before reading the next additive parameter. That later read sets `A = U + x`. Thus every emitted fourth-parameter axiom satisfies `U <= A`. The separate theory certificate proves that this restricted numerical calculus derives every instance of the original unrestricted axiom; formula codes need not be decodable syntax.

The exact wire order of an AX command is `(c, z, y, x)`. Its parameters are `U = oldD + z`, `A = U + x`, `B = oldH + y`, and `C = c`. MP, DROP, and NIP keep their original common additive field and exact source branches. In the AX prefix, the inherited closed macro word is:

```
a, b, Q, c, a, READ_H, READ_D, I, a, I, a, c, I, b, c, I, I, I
```

Here `a`, `b`, and `c` load the current D, H, and selector parameters; `I` and `Q` are the inherited implication and universal constructors. The first `a,b,Q` emits `GEN(U,oldH)` before either local read. The next `c,a` loads C and U. `READ_H` consumes y; `READ_D` consumes x and sets D to A. The first I then forms `C -> U`.

## Reproduce the finite certificate

Python 3 and its standard library are sufficient:

```
python3 verify_release.py
```

The underlying constructor/checker can also be run directly:

```
python3 build_dominated_source.py baseline_sites219.json replay --common --equivalent sites218.json
```

It reconstructs `dominated_zyx206.json` from the accepted baseline by three closed macro splices, checks their control boundaries, computes the full transition graph by two independent resolvers, and compares the optimized source's graph exactly. It also verifies literal preservation of every old primitive path outside the AX subtree. The generated receipt must match `source_receipt.json` exactly.

## Exact finite results

| Item | Accepted baseline | New reference | Selected source |
|---|---:|---:|---:|
| Distinct source subtrees | 206 | 206 | 203 |
| Primitive occurrences | 4,744 | 4,751 | 4,751 |
| Maximum source depth | 38 | 38 | 45 |
| Maximum consecutive zeroes in a source address | 6 | 8 | 6 |

The selected source has 23 primitive kinds: CI and CD for registers 0–8, CB1, CC1–CC3, and CH. It does not use CC4. There are 6,176 guarded primitive cases. Both independent source resolvers give exactly the same transition graph for the new reference and selected source. `ordinal_cfg.json` records that common graph explicitly.

The selected source preserves all 186 original primitive paths outside the AX subtree whose prefix is `11101001001`: 40 leaves before AX and 146 after its exit. Each preserved path has the same opcode and operand. Binary startup also requires the separately checked physical transition rows; source address preservation alone is not a startup proof.

The three baseline edits use zero-based half-open primitive intervals:

1. Delete the old cached-parameter read at `[121,135)`.
2. Replace the old fourth-parameter construction at `[161,194)` by the inherited parameter-load macro `a`.
3. Replace the implication macro at `[194,221)` by `(READ_H,(READ_D,I))`.

These give the 206-node reference. Later source rebracketing is certified directly by equality of the guarded ordinal graph, so replaying the heuristic search is unnecessary. At a given ordinal and register tuple, both sources perform the same increment, decrement/zero test, or halt and reach the same next ordinal. Induction gives a primitive-step bisimulation for all natural-valued register tuples. This is an exact finite verification of a universal statement, not bounded simulation.

## Files and proof scope

- `baseline_sites219.json`: unmodified accepted K219 source.
- `dominated_zyx206.json`: source reconstructed by the three closed splices.
- `sites218.json`: selected 203-node source, originally `root_work/hw_common_cc4/source_0059.json`.
- `build_dominated_source.py`: portable source constructor and two independent CFG resolvers.
- `ordinal_cfg.json`, `source_receipt.json`, `manifest.json`: exact certificates and byte identities.
- `verify_release.py`: rebuilds and verifies the frozen certificate.
- `common_input_calibration.tex`: ordinary mathematical proof of the new command semantics, strong proof compiler, cofinal enumeration, and source equivalence.
- `dirty_seed_calibration.tex`: ordinary proof allowing arbitrary values in the six nonformula fields at the root; this explains the nonzero D and N in the inherited startup frame.

The calculus proof, source proof, universal binary-runtime proof, and blank-tape startup are distinct components of the complete machine theorem. This directory supplies the source component and its mathematical calibration. It does not claim a new Lean-checked theorem for the complete binary machine.

Upstream baseline: `VladimirReshetnikov/ProveIt`, commit `f8ec6158f3bdc885139ee395ae34fe44c3251b9f`, file `Computability/BusyBeaver/Research/ZFC/candidate-k219/sites219.json`.
