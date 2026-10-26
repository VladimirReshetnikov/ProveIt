# A Start-only marker and compositional reductions for Con(ZFC)

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026, with AI assistance.

Start with [report.pdf](report.pdf), whose complete editable source is
[report.tex](report.tex). This package supplies three explicit advances relative
to repository commit `fb1bed5eb7196cf35abfaa746c18c6ee7eae6cfb`. Each final equation
has fixed integer coefficients and a stated domain. The ordinary mathematical
proofs, composed with the identified inherited calibrations, establish in ZFC
that a zero exists exactly when a finite syntactic ZFC refutation exists.
Negation gives unsolvability in that domain if and only if `Con(ZFC)`.

## Results

| Construction | Domain and variables | Exact degree | Binary arithmetic operations | Further size information |
|---|---|---:|---:|---|
| Preferred Start-only compact equation | 15 strictly positive integers | 157 | 66 | 97,046 raw coefficient bytes; native cell length 4,127 |
| Trace plus inverse Lucas correction | 10 strictly positive integers | 232 | 85 | Two complete variants; the squared-transport variant lowers carrier degree from 57 to 21 |
| Direct balanced quartic | 233 unrestricted integers | 4 | Not optimized | 169 quadratic residuals; 18,482 collected monomials; coefficient height 5,632 |
| Direct sparse quartic | 233 unrestricted integers | 4 | Not optimized | 169 quadratic residuals; 10,182 collected monomials; coefficient height 8,880 |
| Sparse companion quartic | 234 unrestricted integers | 4 | Not optimized | 170 quadratic residuals; 5,018 collected monomials; coefficient height 8,880 |

The last three rows are tradeoffs within the third result. A binary operation
is one addition, subtraction, or multiplication, including fixed scalar
multiplications and every step needed for a fixed power. Named polynomial
registers are abbreviations, not additional unknowns. Coefficient height is
the largest absolute coefficient of the fully collected polynomial.

### 1. A completed Start-only native encoding

The compact equation keeps the existing P66 evaluation graph. A physical flag
now copies the distinguished Start selector, instead of copying the number of
all selected tiles. Eight prescribed consecutive Start-label bits and one flag
test force alignment. The final possible false alignment is excluded by the
actual decoded color of tile 942. This removes 942 terms from the constant
kernel and reduces the native cell from 6,007 to 4,127 radix digits.

All four coefficients change together. Their minimal unsigned byte strings
shrink from 141,226 to 97,046 bytes, saving 44,180 bytes, approximately 31.28%,
at unchanged variable count, degree, and arithmetic cost. The new controller
prime and every coefficient byte are supplied. The independently checked
intermediate cell of length 4,159 is retained with its simpler support-only
alignment proof.

The pinned repository's `SIZE_REDUCTION.md` already suggested investigating
a Start-only marker. The contribution is completion of this branch: an explicit
shorter layout, complete new native proof, and discharged finite controller
conditions. No worldwide priority claim is made.

### 2. Trace and inverse-Lucas constructions composed

The ten-variable result combines package 163's unsquared explicit Pell trace
with package 164's inverse Lucas correction. The composition gives 85 operations
at exact degree 232, compared with its immediate parents' 87/232 and 85/304
operation/degree pairs. A second complete equation uses a squared-transport
weight and proves the additional negative-rank estimate left open at that
interface, lowering the carrier numerator's degree from 57 to 21. Its total
degree and operation count remain 232 and 85.

Both equations retain their own complete coherent radix-67 coefficient tuple.
The trace substitution is not automatically valid in P66; the precise
nontransfer issue is recorded in `positive85/NONTRANSFER_NOTE.md`.

### 3. Direct quartics in the C222 proof calculus

The third result combines a linear binomial selector with the self-power
horizon construction, then applies exact integer projections and reversible
row operations. It uses the direct C222 proof-calculus calibration rather
than the K215/native route. All final quadratic residuals and every collected
quartic coefficient are supplied; a variable exponent appears only in the
semantic proof, not in a final polynomial.

Against package 159's direct 234-variable, 171-residual, 19,050-term equation
of height 4,480, the new 233-variable forms remove one variable and two
residuals, at larger height. These are explicit tradeoffs. Other repository
branches have substantially fewer integer variables with different degree or
coefficient costs; 233 is not a general variable-count record.

## Coefficient tuples and domains must remain separate

The preferred compact tuple has `B=2^193969`. The intermediate compact tuple
has `B=2^195473`. The ten-positive-variable equations retain the separate
indexed radix-67 tuple with `B=2^590069`. These specializations are not the
same polynomial, and individual coefficient ports must not be mixed between
them. The compact payloads are unsigned big-endian bytes; the ten-variable
payloads are gzip-compressed unsigned little-endian bytes. Their local
manifests and verifiers specify the formats exactly.

The domains are also part of the theorems: strictly positive integer witnesses
in the first two components and unrestricted integer witnesses in the direct
quartics. Merely changing a domain does not preserve the stated equivalence.

## Navigation

| Path | Contents |
|---|---|
| `report.tex`, `report.pdf` | Combined article, complete compact formula and coefficient recipe, ten-variable construction, direct-quartic argument, and further research questions |
| `appendices/` | Complete indexed finite language and printed direct residuals used by the article |
| `compact66/preferred4127/` | Preferred 66-gate equation, full new native proof, all four coefficient payloads, tile/weight data, and controller certificate |
| `compact66/intermediate4159/` | Preserved intermediate Start-only construction and its separate tuple/certificate |
| `compact66/calibration/` | Retained ordinary positive-P66 arithmetic and historical calibration records |
| `positive85/COMPOSITION_PROOF.md` | Complete new trace/inverse-Lucas composition and squared-transport proof |
| `positive85/equations/`, `positive85/coefficients/` | Both literal 85-gate graphs and their complete fixed coefficient data |
| `direct233/PROOF.md` | New direct C222 arithmetic composition, signed bootstrap, and inherited calibration boundary |
| `direct233/equations/` | Three final residual lists, complete expansions, metrics, and certificates |
| `direct233/stages/` | Intermediate projection stages and exact reconstruction data |
| `checks/` | Independent compact reconstruction checks and retained review records |
| `PROVENANCE.json`, `NOTICE.md`, `LICENSE` | Comparison pin, immediate source identities, attribution, and reuse terms |

## Verification and rebuilding

From this package directory, run:

```bash
python3 verify_all.py
```

Python 3.10 or later and its standard library suffice for the mathematical
artifact checks. The component verifiers reconstruct the explicit coefficients,
literal graphs, full residual expansions, projection identities, and finite
controller conditions. Normal and optimized Python component checks are
recorded separately. No program searches for a consistency witness.

To rebuild the combined article with a standard TeX installation:

```bash
python3 build_report.py
```

Use a working copy when rebuilding generated artifacts. A rebuilt PDF can have
different metadata or font bytes without changing its mathematical content.
The component READMEs describe their focused checks, reconstruction commands,
and direct-polynomial evaluation format.

## Proof and verification boundaries

The new unbounded arguments are ordinary mathematics intended to be formalizable
in ZFC. Finite checks authenticate the actual formulas and certificates; they
do not establish the unbounded equivalence by testing examples. The proofs
explicitly compose with retained Pell/native/K215/refutation results for the
first two components and C222/ZF/ZFC refutation results for the third.

This release does not supply or claim a new end-to-end Lean/Rocq proof or an
encoded object-language ZFC derivation. Some deeper historical dependencies
advertised by package 165 are absent from the inspected tree; no unavailable
inherited checker is claimed to have run. The included direct source chart and
every new algebraic transformation are independently checked within the
documented scope. AI-assisted internal reviews are not external human
endorsements.

No consistency assumption is used to prove the equivalences, and neither
consistency nor inconsistency is decided. There is no global simplest-equation
or minimum-variable theorem in this package.

## Suggested repository placement

Place this directory as a new named package under
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/`, for example
`start-marker-compositions/`, beside the existing packages. Leave any intake
number to the repository's integration process. Preserve the earlier packages
and this package's separate component coefficient bindings. The combined
article and the three headline results can then be linked from the collection
README without replacing existing tradeoffs.
