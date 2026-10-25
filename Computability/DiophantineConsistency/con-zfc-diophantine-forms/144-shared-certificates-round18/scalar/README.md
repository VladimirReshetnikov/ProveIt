# Eleven-integer whole-expression centers

Four new fixed Con(ZFC)-calibrated ordinary polynomial tradeoffs:

| Exact degree | Binary operations | File |
|---:|---:|---|
| 300 | 148 | `free_whole_center11_c300.json` |
| 304 | 144 | `free_whole_center11_c304.json` |
| 308 | 140 | `free_whole_center11_c308.json` |
| 316 | 133 | `free_whole_center11_c316.json` |

Every circuit has eleven unrestricted integer variables. The six coefficient
ports are fixed actual numerals: full bytes, binding, and finite recipe are
included in `coefficients/`. No public-repository publication is performed.

Read **PROOF.md** for all polynomial definitions, the complete signed
nondegeneracy/even-weight equivalence proof, source-calibration boundary,
exact weighted cancellation identities, and actual leading coefficients.
`section.tex` contains the same complete proof for the parent report.

Primary recommended degree endpoint: **300/148**. Economical added degree
tradeoff: **316/133**. The intermediate points remain distinct tradeoffs.
The incoming round17 degree328/130 endpoint is not cost-dominated; still
lower-operation incoming constructions (including degree840/108 and924/107)
are not superseded. These are improvements of a particular inspected
frontier, not a minimum theorem.

## Reproduce locally

Only Python's standard library is needed for every release check:

```
python build.py
python check.py
python -O check.py
python audit_mutations.py
python -O audit_mutations.py
python replay.py
```

`check.py` does not import the producer. It binds all live arithmetic gates
against separately stated polynomial register identities, authenticates and
fully reconstructs the coefficient tuple, checks copied source pins, verifies
exact sparse-ring cancellation identities, recounts operations, and carries
actual positive-coefficient leading certificates through every gate. The
normal and optimized JSON outputs record every expanded center remainder
and attained gate leader. `audit_mutations.py` rejects both alternative
operation labels at every arithmetic gate of every released circuit.
`replay.py` runs a fresh copied release and checks byte-identical rebuilding.

`source/LINEAR_COFACTOR_ROUND17_PROOF.md` is the immediate ordinary arithmetic
source, with its complete retained dependencies under `source/` and pinned
in `SOURCE_PINS.json`. The reduction uses its existing native/compiler/
finite-syntactic-refutation calibration; no new end-to-end formal certificate,
proof of consistency, or proof of actual unsolvability is claimed. Finite
algebra checks do not replace the unbounded ordinary theorem inputs.

`research/` preserves exploratory symbolic calculations for transparency; it
is not imported by any release check and is not required for reproduction.
