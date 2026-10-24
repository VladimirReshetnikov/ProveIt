# Tightened nine-positive main-root folding

| Equation | Positive variables | Live binary operations | Exact total degree |
|---|---:|---:|---:|
| boundary_simple.json, whole original31 tuple | 9 | 409 | 1,191,572 |
| compact_simple.json, whole compact54-sharp tuple | 9 | 417 | 1,316,548 |

This new sibling preserves the separately reviewed
`research/nine-folded-saturation/` 414/422-operation packet. It drops J
from the strong ordinate, uses positive j directly, removes the n carrier
shift, and shares the strong norm with its majorant. Section6 of `PROOF.md`
identifies every change and its complete ordinary witness justification.

All inputs are strictly positive integers. Every live binary addition,
subtraction and multiplication counts, including squares and scalar products.
Numeral/fixed leaves and reuse are free. The two complete circuits have
441/448 live nodes; every one of the nine inputs and all original fixed
leaves is used.

The unshifted carrier E=Jn+Q needs a new positivity-first proof: the first
Pell norm gives a strict root-gap lower bound excluding negative margin,
and the zero-margin branch forces Q>0 directly. Root integrality, strong
folding, rank congruences and source decoding follow in that order. Two
explicit finite matrix periods construct positive i,j; a strict bound
constructs positive n. No domain or cofinality assumption is hidden in a
coordinate subtraction.

The exact total-degree proof uses the complete centered-norm identity and
its unique maximal-degree summand. All actual fixed integers are bound to
the complete retained native tuples. Nonzero highest homogeneous diagonal
values modulo primes prove attainment over the integers; the larger raw
DAG bounds 1,599,036/1,766,812 are reported separately.

From the repository root:

```
python3 -B Computability/DiophantineConsistency/research/nine-folded-saturation-tight/build.py --check
python3 -B -O Computability/DiophantineConsistency/research/nine-folded-saturation-tight/build.py --check
python3 -B Computability/DiophantineConsistency/research/nine-folded-saturation-tight/check.py
python3 -B -O Computability/DiophantineConsistency/research/nine-folded-saturation-tight/check.py
```

The checker imports no new builder. It verifies the full literal prefix
mapping, every local formula including the changed E, complete node coverage,
all fixed payloads, topology/liveness/counts, full norm and defect identities,
the strict-gap polynomial identity, exact degree witnesses, and four rejected
corruptions. `CHECK.json`/`CHECK_OPTIMIZED.json` retain normal/-O receipts.
`BUILD.json` and `MANIFEST.json` seal all packet bytes.

The source/native/compiler/refutation interpretation remains the pinned
ordinary dependency. There is no new native calibration, absence-of-zeros
claim, proof of Con(ZFC), global optimum, or Lean/internal-ZFC certificate.
No Lean or historical H10/native emitter is executed. Frozen parents and
common documentation remain unchanged.
