# Independent finite audit: product-saturated low-operation addendum

## Verdict and scope

**PASS.** Both frozen literal eleven-integer polynomials have the stated exact degrees and operation counts at the actual authenticated source34 coefficients. Every variable is algebraically essential. Normal and optimized-Python runs agree and reject all 235 negative controls.

| Literal graph | Variables | Exact degree | Live operations | Nonzero leading coefficient of the exact ray mod 65521 |
|---|---:|---:|---:|---:|
| `product_main_guard11_native.json` | 11 | 924 | 109 | 4210 |
| `product_main_guard11_short.json` | 11 | 840 | 110 | 54438 |

The ordinary unbounded mathematical review is separate, in `../lowops/`; its reviewer reports ACCEPT. This finite audit does not prove consistency, global optimality, a ten-variable result, or an end-to-end proof-assistant certificate. It does not replace the retained native/compiler/finite-refutation argument.

The independently frozen producer manifest SHA-256 is `c5618a882fe0ab42ced99c87b022b8c22b4132b5cee9296990d1d5d5425832bd`. Graph hashes are:

- Native: `3b90018065bc96195b240332ecce281227426089224388fdea0a5c5ef6f73ffd`.
- Short: `404d1684eba1ced01864a6d6096909dd0818e2f1def520f4848a865d2dd027ff`.

`FROZEN_INPUTS.json` authenticates 123 technical files. Producer `RESULTS.json` and `MANIFEST.json` are excluded solely to allow recording the completed review; Python caches are excluded. No file in the previously reviewed degree352 family or its 804-control review was changed.

## Independent checker

`check_independent.py` is standalone and imports no producer Python modules. It reuses the reviewer's independently written coefficient reconstruction, graph validation, degree evaluation, and mutation infrastructure from the degree352 audit, with a new exact symbolic transcription of these two complete low-operation formulas. It depends on Python and SymPy, not on the producer's ring, builder, checker, or coefficient-recipe program.

The exact local polynomial checks cover every named register and every live arithmetic gate, including the two distinct index moduli, original cubic `Y`, strengthened product radicand `BP=Dm P`, the saturated `Df` and `Q`, auxiliary term `4 U BP T`, carrier `S=srH`, quintic `Ac`, and final polynomial `delta Z^2-S^2 BP Df Cy`. Each local difference is expanded exactly over commuting indeterminates, not checked only at sample values. All local identities compose to the displayed complete equation.

Topology validation enforces exactly eleven coordinate leaves, six coefficient leaves, only integer/add/subtract/multiply primitives, backward binary edges, valid output/register indices, no unreachable nodes, exact domain and family metadata, and actual opcode counts. The 109-operation graph has 23 additions, 68 multiplications, and 18 subtractions; the 110-operation graph has 23 additions, 69 multiplications, and 18 subtractions. Scalar operations and squares are charged.

## Actual numeral and source authentication

All six actual compressed payloads are decompressed. Their minimal unsigned encoding, actual bit lengths, byte counts, binding records, and independently hard-coded raw SHA-256 pins are checked. The checker then independently rebuilds all six million-bit-scale values from the pinned 430-transition machine table, independently reconstructs all 943 ordered tiles, reconstructs the 989-position packing, and proves integer equality with each actual payload. In particular, the MF shift is applied exactly once. No producer builder is imported or executed, and no machine simulation is attempted.

This is a fresh reconstruction against the lowops payload bytes, not merely a claim that their names resemble the earlier package. All 109 retained source dependency pins also match actual bytes, including the incoming short-index proof. Hash preservation identifies the retained dependencies but does not itself prove their unbounded theorems.

## Degree upper bounds and attained lower bounds

No centered cancellation cut is needed for these graphs. Direct degree propagation through every literal gate proves upper bounds 924 and 840.

| Register | Native bound | Short bound |
|---|---:|---:|
| k | 7 | 5 |
| P | 94 | 82 |
| Dm | 14 | 14 |
| BP | 108 | 96 |
| U | 9 | 9 |
| Df | 138 | 126 |
| Q | 150 | 138 |
| V | 256 | 232 |
| Cy | 662 | 602 |
| S | 8 | 8 |
| Z | 35 | 35 |

The first summand `delta Z^2` has bounds 220 and 208. The second summand `S^2 BP Df Cy` has bounds 924 and 840, respectively.

For rigorous matching lower bounds, the authentic fixed integers are reduced modulo the prime 65521, and the literal graphs are evaluated as complete univariate polynomials under `(j,C,z,h,r,v,w,T,c,n,s)=(t,2t,...,11t)`. The resulting exact polynomials have degrees 924 and 840, with nonzero leading coefficients 4210 and 54438. A specialization cannot increase total degree. Therefore these are deterministic lower-bound certificates at the actual coefficients, not a generic-coefficient assertion or a probabilistic polynomial-identity test.

Separately, symbolic propagation of the top components verifies the displayed common top form

`2^36 3^7 q0^14 X0^64 Y0^106 k0^42 s^16 r^12 c^34 T^2`.

The complete leading-form coefficient derivation is also checked in the separate mathematical review. The exact finite-field certificate here independently establishes attainment without depending on that derivation.

Each of the eleven coordinates has an exact nonzero partial derivative at a recorded finite-field point, obtained by differentiating the literal graph. This proves algebraic essentiality of every coordinate over the integers. The receipt records the point and derivative for each coordinate.

## Algebraic checks supporting the ordinary proof

The checker verifies exact polynomial remainder identities for `Df=1 mod BP`, `Da=1 mod BP`, `Da=A^2 Dm mod Df`, `Df=1 mod A`, and `Df=1 mod Dm`. It verifies the finite residue statement `4 | (A^2-1)A^2`, the product-square clearing identity, the integral-root divisor-recovery identity, rescaling `I T_old=U p0^2 T`, the short projector identity, and the complete quintic expansion.

The nonzero/sign bootstrap, early absolute Pell folding before splitting P, denominator descent, genuine `c^2 | I` strong-rank premise, short-index no-wrap argument, projector size bound, old-source witness regeneration, and fixed-guard/fixed-strong-pair interpolation remain ordinary mathematical arguments. They are not inferred from these finite symbolic checks.

## Exhaustive gate mutation controls and reproduction

For each of the 219 arithmetic gates across both graphs, the checker changes its opcode and requires rejection by the exact symbolic identity layer. Operation-count and file-hash checks are bypassed in this test so they cannot cause trivial rejection. It additionally tests three wrong named-register bindings, one cycle, and one false degree per graph, and a bit flip in each of the six actual coefficient payloads. All **235** corruptions are rejected normally and with `python -O`. No correctness check uses `assert`.

From this review directory:

```sh
python check_independent.py --receipt receipt-normal.json
python -O check_independent.py --receipt receipt-optimized.json
```

The default layout is `review/integer_lowops` beside `integer_lowops`; `--source` accepts another source directory. The two substantive receipts are identical apart from their optimized-execution flag. They include all graph and payload hashes, local identities, upper bounds, exact lower-bound witnesses, variable-dependence witnesses, dependency verification, and individual mutation rejection messages. `FINITE_AUDIT_MANIFEST.json` authenticates this independent deliverable.
