# Explicit ten-integer Con(ZFC) equation

`generated/signed10.json` is the main division-free polynomial circuit.
Its **ten and only ten unknowns** are the unrestricted integers
`f,g,h,k,l,w,x,y,z,m`. All other leaves are completely fixed.

The ordinary mathematical proof establishes in ZFC that it has an integer
zero exactly when ZFC is inconsistent. Thus its lack of integer zeros is
equivalent in ZFC to `Con(ZFC)`, with the repository's inherited proof
predicate and compiler endpoint.

The main equation has **1,442 binary arithmetic operations** and exact degree
**126496·5^31 + 27064 = 589042901992797851562527064**. The operation count is
566 additions, 25 subtractions and 851 multiplications. All constant powers
are expanded into binary gates; fixed leaves and reuse are free.

## Attribution and proof status

The general ten-integer theorem is due to **Zhi-Wei Sun (2026 preprint)**.
This package supplies a completely fixed Con(ZFC) instance from the explicit
source coding in his 2021 paper. It then proves three local simplifications:
a quintic divisibility merger, a coprime positivity-square merger, and
smaller separating weights. It does not claim a new universal ten-variable
theorem or optimality among all Diophantine descriptions.

See [SIGNED10_PROOF.md](SIGNED10_PROOF.md) for all formulas and both directions,
[SIGNED10_SECTION.tex](SIGNED10_SECTION.tex) for the report section, and
[SOURCES.json](SOURCES.json) for primary sources and exact sections.
The proof depends on the stated Lucas/bridge theorems, including Sun's
2026 preprint. Finite program checks are not an end-to-end formal proof.

## Reproduce

From this directory, with Python 3 and its standard library:

```sh
python build_signed10.py
python verify_signed10.py
```

The verifier reconstructs the weighted source coefficients directly from
the 22 shifted quadratic residuals, checks all binary payload hashes and
all coefficient bounds, proves the formal 35-term and 495-term norm
identities exactly, compares independent literal formulas with every
variant's circuit modulo three primes, and proves degree attainment.
It does not search for a solution or decide consistency.

## Fixed data

`data/INSTANCE.json` is authoritative. The four native ports are the
complete 943-tile tuple with rho=2^121 and side length 8801, whose adapter
is in the package's `coefficients` directory. The source is the parent
31-positive-variable system shifted to nonnegative variables and combined
as a sum of 22 residual squares. Its 402 nonzero factorial-weighted
coefficient recipes are in `data/constants.json`.

The one additional source constant is `beta_sun=2^4269882`, explicitly
materialized in `data/beta_sun.bin.gz`. Coefficient recipes and payloads
are literals, not existential parameters. The dummy source input is fixed
to zero before the final circuit is built.

## Comparison variants

All have ten unrestricted integer variables and the same fixed source.
Write t=5^31.

| Circuit | Operations | Exact degree |
|---|---:|---:|
| `signed10.json`: structural signed weights | 1,442 | 126496t + 27064 |
| `signed10_universal_weights.json` | 1,444 | 158592t + 33880 |
| `signed10_h3quintic.json`: Sun's generic three-square weights | 1,445 | 807360t + 172560 |
| `signed10_h4quintic.json` | 1,492 | 2403200t + 513696 |
| `signed10_sun6.json`: literal Sun final formula | 1,492 | 2407680t + 514640 |

Every file above is in `generated`. The literal Sun specialization lets
reviewers separate the explicit source binding from the three local
improvements. `generated/VERIFICATION.json` gives exact receipts.

## Circuit format

Nodes occur in topological order. A `literal` is its listed integer; a
`fixed` leaf is resolved through `data/INSTANCE.json`, the 402 coefficient
recipes, and `generated/coefficient_aliases.json`; a `variable` is one of
the ten listed unknowns. An `add`, `sub`, or `mul` node operates on its
earlier `left` and `right` nodes. The integer in `output` selects the
polynomial's final node. A `named_nodes` entry is an abbreviation for a
node and does not introduce an unknown.

The norm expansions in `generated/norm3_polynomial.json` and
`generated/norm4_polynomial.json` are ordinary sparse integer polynomials.
Their root-product descriptions are proofs of identities; no radical
operation appears in any emitted circuit.
