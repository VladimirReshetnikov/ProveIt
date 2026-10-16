# A smaller complete initializer for the clean Mira assembler

Prepared for Vladimir Reshetnikov, 16 October 2026.

This package gives a new contiguous-counter initializer and explicit transition
quotients. Applied to ProveIt's clean assembler, they reduce its complete
original-program controls from **341/343 states to 334/336 states**. The smaller
numbers in each pair initialize the next-proof register to zero; the larger
numbers initialize it to two. The latter is the published proof-search starting
value. These are improvements to reproducible compiler controls. The public
253-state machine is smaller and has a separate verification history; this
package does not improve that record or prove a new Con(ZFC) endpoint.

## Reproduction

The minimal input snapshot is included, with original bytes and provenance.
Python's standard library suffices; there are no network downloads.

```sh
python -B verify_saved.py
python -B reproduce.py
```

The first command independently reparses the saved machine files, checks each
complete transition-homomorphism certificate, and replays every exact finite
bootstrap. The second regenerates all 18 controls, runs all 8,391 affine
instruction cases for every control, repeats both forms of the initializer
on 432 parameter/register cases each, and checks the two published tables.
It reads the bundled source without modifying it and overwrites only `results/`.
Optional `--repo`, `--upstream`, and `--output` arguments select separate source
checkouts or an output directory.

## Complete counted results

All columns count binary working states, including every initializer and
runtime state. The distinct terminal is not counted.

| Program data | Initial next-proof | Previous compact initializer | Previous plus exact quotient | New standalone plus quotient | New shared-cleanup plus quotient |
|---|---:|---:|---:|---:|---:|
| Original 219-node DAG | 0 | 341 | 338 | 335 | **334** |
| Original 219-node DAG | 2 | 343 | 340 | 337 | **336** |
| Full-logic rebracketed 206-node DAG | 0 | 328 | 325 | 322 | **321** |
| Full-logic rebracketed 206-node DAG | 2 | 330 | 327 | 324 | **323** |
| Preserved 202-node decoder control | 0 | 313 | 310 | 311 | **309** |
| Preserved 202-node decoder control | 2 | 315 | 312 | 313 | **311** |

The previous original-DAG initializer uses `(n,m)=(6,15)`, gap 104, and 880
steps when all registers start at zero. The new standalone form uses `(9,10)`,
gap 102, and 1,196 steps. The selected shared-cleanup form uses the same
parameters, gap 104, and **1,218 steps**. Initialization with next-proof two
adds two states before quotienting and two literal steps. Thus the 334/336
results use gap **104**, not 102.

The 202-node controls need only gap 41. The new standalone initializer costs
one more state than the old one there. The shared-cleanup form chooses
`(n,m)=(6,5)`, achieves exactly gap 41, and needs 393/395 literal steps. No
monotonic improvement for every gap is asserted.

## Deliverables and proved scope

- `contiguous_initializer.py` constructs both forms and checks full tape support.
- `exact_quotient.py` generates and independently verifies ordinary complete
  transition quotients. The argument applies on **every input tape**.
- `notes.md` gives the initializer invariant, exact state/time formulas, their
  integer optimization, and the quotient proof.
- `reproduce.py` reads only the identified source inputs and regenerates the
  complete tables and measurements.
- `verify_saved.py` checks all saved quotient certificates and literal boots
  without the original compiler or any register-box summary.
- `results/evidence.json` records all inputs, counts, hashes, exact finite
  supports, and the named pairs of identified states.
- `results/*_quotient.json` and the corresponding source/target `.tm` files are
  complete reviewable certificates.
- `vendor/` retains only the needed original compiler modules, finite machine
  and program data, and notices.

Every successful affine runtime audit uses ProveIt's existing Python checker
and its existing four register-box contracts. This package has no new proof of
that checker's soundness or of the arbitrary register-box contracts. The
initializer's ordinary mathematical proof and the exact quotient theorem are
independent of those contracts. Neither new theorem establishes that one of
these larger compiler controls is an implemented, internally calibrated
ZFC-consistency machine.

## Published-machine negative control

Exact partition refinement leaves all **254** states of the published main
table separate and all **253** states of the public reduced table separate.
The shared `e:5`/`b:1` pair exists in the **clean assembler's output**, where
the generic decrement patch and explicit break scan duplicate a state. It is
not an additional merge in the public 253 machine. These checks give no lower
bound against contextual folds, different programs, or different initializers.

See `NOTICE.md` for attribution and license boundaries.
