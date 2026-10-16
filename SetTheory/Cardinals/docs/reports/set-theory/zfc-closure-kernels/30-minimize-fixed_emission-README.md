# Fixed CP/GIC emission: a measured compiler experiment

This package implements the fixed-variable specialization proposed in the
ProveIt source-09 theory notes. The new work here is the concrete emitter,
search, tables and executable audits. The fixed-variable normalization idea
is prior work. The experiment **does not produce a smaller known
ZFC-consistency machine** and asserts no new ZFC state bound.

## Result

The best measured table has **283 working states**, composed of 221 decision
states and 62 framework states. It retains all nine original logical outputs
(GEN plus the eight original logical axioms), equality, the original
base-four formula codec, and the original general membership/equality
vacuity rows with their two freshness gates.

| Compilation | Decision states | Framework states | Total working states |
|---|---:|---:|---:|
| Published 219-node source recompiled by public Wade backend | 219 | 62 | 281 |
| Fixed CP/GIC, direct right-associated macro word | 304 | 61 | 365 |
| Fixed CP/GIC, best searched grammar | 221 | 62 | 283 |

The 281-state row is a calibration of the public Wade backend. It is not
Mira-Cult's different 254-state interpreter. The best fixed-emission table
has 566 complete transitions after the backend's single undefined row is
replaced by an explicit transition to the separate terminal state.

SHA256 of `results/candidate.tm`:

```
2e544e7fcb295696fd839d2f8268c799d729f05d95e12cdb3ebef04bfff578a6
```

The original expanded axiom-emission word has 186 tokens. The selected
fixed-emission word has 200. Fixed constants and the offset binder add
16 explicit scalar increments; emitting CP and GIC separately removes two
conjunction tokens. Thus fixing the logical variable names did not reduce
the cost in this representation. Grammar sharing recovers most, but not
all, of the difference.

## New emission

The exact original 88-token logical prefix is unchanged. It is followed by:

1. `bundle_C(0, 1, 2)`, the original CP formula with those fixed labels;
2. GIC with input variable 0, output variable 1, matrix whose numeric code
   is `c`, and collection binder `k = c + 2`;
3. the original conjunction of general membership and equality vacuity,
   followed by the original five cleanup/gate macros.

For the GIC row, with `phi` denoting the matrix and `R` membership, the
emitter constructs exactly

```
W = exists 1, (phi and R(1,k))
G = exists k,
      ((forall 0, (R(0,1) -> forall 1, (phi -> W)))
       and (forall 1, (R(1,k) -> exists 0, phi)))
```

The binder `k` is emitted by the unchanged push-c macro followed by two
increments of `topwff`. Constant 2 is emitted by the unchanged push-one
macro followed by one increment. Only conjunction commutations are
searched; no quantifier permutation, altered logical axiom, discarded
equality row, or codec substitution is used.

The source-09 prior proposal is in
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/09-decoder-notes-theory_findings.md`,
section 4, at ProveIt commit
`4747142d5d15213eb711bdadfa3cc7e769fcb7a7`.

## Search scope

The main grid has 1,024 entries: 8 CP conjunction commutations, 4 GIC
conjunction commutations, 2 CP/GIC orders, 2 grouping choices, 4 random
seeds, and Re-Pair exponents 1 and 4. The grouping choices emit either
CP/GIC separately or their conjunction, always followed by the separately
gated original vacuity conjunction. Another 248 seeds/exponents refine the
best structural choice, for **1,272 actual compiler runs** in total.

Every candidate is passed to the real backend and garbage-collected before
counting. Framework cost is measured, including the depth-dependent
dispatcher; it is not assumed constant. The best recipe is CP variant 5,
GIC variant 1, CP then GIC, separate emission, seed 2, exponent 4. This is
a finite search result, not an optimization lower bound.

## Validation and limits

The symbolic stack audit compares the unchanged logical prefix to the
pinned original specification and checks the exact new CP/GIC/vacuity
stack. Every grammar expands to the exact proposed macro word. All reused
macro roots are checked to be closed under the reassociation operation.

The added scalar fragments are executed on 144 combinations of matrix
code, prior top value and stack tail, checking all registers and the new
stack value. The direct fixed-word register program and its compressed
version are related by an independently verified finite operation
bisimulation with 4,248 related sites. Both have 6,041 unfolded instruction
sites. Both branches of every decrement are checked. Six deliberately
corrupted certificate controls are rejected. The emitted decision edges
are also independently inverted and compared with the candidate DAG.

These checks validate formula emission, scalar helpers, word compression,
and finite register-operation correspondence. They do not establish the
modified proof enumerator's complete object-theory bridge, the binary TM
compiler's unbounded tape invariant, or an internal ZFC proof of the final
equivalence. In particular, a register-program certificate is not a proof
of binary-TM compiler correctness. The candidate is an engineering
measurement, not a new 283-state exact-equivalence theorem.

## Reproduce offline

Python 3.10 or later is sufficient; no downloads or third-party Python
packages are needed. From this directory:

```sh
python experiment.py --seeds 4 --refine-seeds 128
python audit.py
python verify_operation_certificate.py \
  --reference results/reference_dag.json \
  --candidate results/candidate_dag.json \
  --certificate results/rm_bisimulation.json
```

The first command deliberately overwrites the generated results directory.
The resulting candidate bytes are deterministic. Wall-clock timings in
the evidence are environment dependent. `results/all_measurements.json`
contains every measured recipe, not just successful improvements.

## Provenance and licenses

The upstream snapshot is pinned to
`jeff87654/busy-beaver@297ab8df7e5de329605c3875b4934643b371a5e3`.
`vendor/snapshot/` retains the unchanged Wade backend, `Dag254.v`, original
symbolic specification and `LICENSE.wade`. `vendor/python/` retains the
ProveIt reconstruction, formula-emission and Re-Pair/certificate tools
used as building blocks; source08's generator and independent checker are
included unchanged. `vendor/LICENSE.ProveIt` retains the repository license.
`results/vendor_hashes.json` records their exact hashes. New code is in
`experiment.py`, `audit.py`, and `verify_operation_certificate.py`.
