# Fixed-input Diophantine equations for Con(ZFC)

This packet specifies an ordinary integer polynomial `P70` for which ZFC proves

> P70 has no strictly positive integer solution if and only if ZFC is consistent.

The main construction has **16 strictly positive unknowns, one equation, 70 binary arithmetic operations (40 multiplications and 30 additions/subtractions), and exact total degree 169**. Its five fixed numeral ports are completely determined by the literal K215 machine and the finite coefficient recipe supplied here. There is no unspecified universal-machine index or existential exponent.

The article is [`report/zfc_diophantine.pdf`](report/zfc_diophantine.pdf); its source is [`report/zfc_diophantine.tex`](report/zfc_diophantine.tex). The article includes the full formula, proof, coefficient formulas, literal evaluator, alternative system, domain conversions, and open research questions.

## Status and scope

This is an ordinary mathematical construction and proof based on the pinned ProveIt Pell, helical-compiler, and K215 consistency-calibration results. It includes executable finite checks and an independent mathematical review. It is **not a new end-to-end Lean/Rocq theorem or a derivation encoded in ZFC's own proof syntax**. The report explains why the mathematical argument is formalizable in ZFC and distinguishes this from the inherited external proof-assistant statements.

The equivalence does not assume Con(ZFC), decide it, or prove that the target equation has no solutions. If ZFC is consistent, the absence of positive solutions is unprovable in ZFC by the second incompleteness theorem. No stronger independence claim is inferred from consistency alone.

The count of 70 treats fixed numerals as supplied constants and counts every binary addition, subtraction, and multiplication, including the finalizer. It does not charge for constructing or printing the coefficients. It is the smallest evaluator obtained in this packet; **global minimality is not claimed**. Variable count, degree, coefficient height, and operation count are different optimization criteria.

## Constructions included

| Packet | Positive unknowns | Equations | Operations | Exact degree |
|---|---:|---:|---:|---:|
| `fixed70` | 16 | 1 | 40M + 30A = 70 | 169 |
| `fixed71` | 16 | 1 | 40M + 31A = 71 | 156 |
| `fixed73` | 16 | 1 | 41M + 32A = 73 | 157 |
| `transparent61` | 17 | 8 | 33M + 28A = 61 | maximum residual degree 28 |
| `transparent84_sos` | 17 | 1 | 41M + 43A = 84 | 56 |

The inherited 84-operation universal polynomial has 18 existential unknowns plus its ordinary input and degree 187. The present simplification fixes that input, so its contract differs from a uniform universal bound.

For nonnegative unknowns, replace every positive coordinate by `u+1`: the direct evaluator has 16 unknowns, degree 169 and 86 operations. For unrestricted integer unknowns, replace each coordinate by one plus four squares: the direct equation has 64 integer unknowns, degree 338 and 198 operations. The raw positive-domain polynomial must not simply be interpreted over all integers.

## Main formula

The sixteen positive unknowns are

`J, F, alpha, t, f, h, i, T, s, w, tau, eta, zeta, y, Z, gamma`.

The five fixed coefficients are `beta, K, M, N, W`. They are specified below. All following names are polynomial abbreviations, not extra unknowns:

```text
C = Z+W                 u = C+alpha             q = u+F
v = u-Z                 P = beta*J
X = w*q^2               Y = s*q^3               E = X*Y
k = eta+zeta            c = k*Y+eta              a = E+Y
H = 4*a+3               Delta = a^2+H           D = X+a*c+gamma*H
L = E*(k*Y)
R = (P*u+v)*(q^2-1) + (M+q*N)*J
V = c*(T*f-1)-R*f^2
Astar = (i*Delta*c^2)^2

U0 = q-P
U1 = tau^2-L*(L+k)
U2 = D^2-Delta*c^2
U3 = Astar*(V^2-y^2)+y^2
U4 = k-h*E-R
U5 = (K+w)*C+u-t*P
U6 = Delta*f^2-Astar

P70 = U0*U1*U2*U3*U4*U5*U6-Delta
```

The equation is `P70 = 0` with every listed unknown strictly positive. The literal 70-row circuit is in the JSON packet and the article's Appendix A. The arithmetic-source SHA-256 is

`458aa30130504edf7e00b6a4aea294a6dbab110d904032d19ff8803a651ad96f`.

The proof first cancels positive `Delta`, recovers integer-unit norm factors, restores auxiliary witnesses and the actual Pell index, obtains `X=2^R`, and only then rules out the negative sign of `q-beta*J`. The exact repunit and native transport equations follow. The fixed Start/End markers then select a genuine initialized finite computation. Both directions of this reduction are proved in the article; numerical fixtures are not used as evidence for the all-size semantic theorem.

## Exact coefficients

The coefficient construction starts from the authenticated literal 215-state binary K215 table. A fully materialized **435-state, 10-symbol** normalizer erases its unary input and simulates K215 on blank tape. A specified local predicate gives exactly **4,366 tiles** and

`113175624520853754856480928432`

allowed 3-by-3 windows. Their ordered finite list is Start, End, then the other accepted tile-index tuples in lexicographic order. The standalone generator defines that finite list exactly; normal verification does not attempt to materialize it.

The retained compiler produces

```text
b = 5^44
L0 = 5^45
d = b*L0 = 5^89
B = 2^d
beta = B-1
K = DC+B*DR
M = MC
N = MF_native+B-1
W = 2^(b+2*d)
```

All sums defining `DC`, `DR`, `MC`, and `MF_native` are written out in [`artifacts/compiler/COEFFICIENTS.md`](artifacts/compiler/COEFFICIENTS.md) and Appendix B of the article. The latter are huge fixed integers defined by finite arithmetic recipes. Their decimal expansions, the complete window list, and the numerical value of the optional mod-5 correction bit are not materialized. The correction is a fully defined fixed constant, not a free parameter. In particular the circuit's `MF` port denotes **`MF_native+B-1`**, not the unshifted native mask.

The fixed marker corresponds to ordinary compiler input 1, helical marker distance 2, an I-run of length 3, and four initial unary ones. The explicit loader reaches blank folded K215 after exactly ten transitions.

## Reproduce the finite checks

Use Python 3.10 or later with the standard library; no external Python packages, network connection, or copy of ProveIt is needed for these checks. From this directory run:

```bash
python3 verify.py
```

The wrapper runs these commands in dependency order and records their outputs under `artifacts/verification/`:

```bash
python3 artifacts/fixed_input.py --output artifacts/fixed_input.json
python3 artifacts/domain_variants.py --output artifacts/domain_variants.json
python3 artifacts/compiler/k215_one_sided.py
python3 artifacts/compiler/finite_window_constants.py
python3 artifacts/review/review_fixed70.py
```

The checks cover:

- All five circuit packets, exact arithmetic identities, acyclic dependencies, liveness, operation counts, and finite-field degree diagnostics.
- Both complete domain-conversion circuits, their counts, liveness, and substitution identities.
- The source-table hash, all 3,440 valid local fold cases, and 64 unary loader lengths.
- Two exhaustive 18-tile local-predicate fixtures, each checking 1,889,568 crosses; the exact compressed census and scalar layout for the real normalizer.
- Independent transcription of all seven main factors and the final output on 64 signed and positive arithmetic fixtures.
- An independent virtual-coordinate audit of 5,160 fold cases and the fixed four-one loader endpoint.

All delivered checks passed. These finite checks neither decide K215 halting nor search for a solution of `P70`. The exact-degree assertion is supported by the article's nonzero leading homogeneous form; the degree fixtures supplement that proof.

To rebuild the PDF, install pdfLaTeX with standard packages including `lmodern`, `microtype`, `xurl`, and `listings`, then run:

```bash
python3 build_report.py
```

This authenticates the main source, regenerates `report/circuit70.tex`, and runs pdfLaTeX twice. To regenerate only the circuit appendix, use `python3 build_report.py --appendix-only`. Both TeX includes are delivered, so direct compilation from `report/` also works.

## File guide

| Path | Purpose |
|---|---|
| `report/zfc_diophantine.tex`, `.pdf` | Main article and compiled PDF |
| `report/circuit70.tex` | Generated literal evaluator appendix |
| `report/coefficient_recipe.tex` | Complete finite coefficient formulas |
| `artifacts/fixed_input.py`, `.json` | Circuit generator/verifier and all five source packets |
| `artifacts/domain_variants.py`, `.json` | Complete nonnegative16 and integer64 evaluators and checks |
| `artifacts/fixed_input_notes.md` | Detailed derivation of the fixed-input reductions |
| `artifacts/CIRCUIT_FORMAT.md` | JSON schema, numeral/variable ports, and cost conventions |
| `artifacts/parent84_reference.json` | Authenticated retained parent receipt |
| `artifacts/compiler/k215.tm` | Exact upstream binary machine |
| `artifacts/compiler/normalized_machine.json` | All 4,350 explicit controller transitions |
| `artifacts/compiler/k215_one_sided.py` | Controller construction and finite checks |
| `artifacts/compiler/finite_window_constants.py` | Finite predicate, exact census, and layout |
| `artifacts/compiler/NORMALIZATION.md` | Controller and tableau semantics |
| `artifacts/compiler/COEFFICIENTS.md` | Complete fixed coefficient recipe |
| `artifacts/review/` | Independent mathematical review, verifier, and receipt |
| `artifacts/verification/` | Replayed check outputs and summary receipt |
| `SOURCE_PINS.json` | Upstream file paths, revision, and byte hashes |
| `SHA256SUMS` | Delivered file integrity manifest |

## ProveIt integration and provenance

All inherited sources are pinned to ProveIt revision

`cdd582bec13f908df3711fa9e05d1ddac368a5db`.

The user's two entry points are:

- [K215 verification](https://github.com/VladimirReshetnikov/ProveIt/tree/cdd582bec13f908df3711fa9e05d1ddac368a5db/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215)
- [Hilbert's tenth problem constructions](https://github.com/VladimirReshetnikov/ProveIt/tree/cdd582bec13f908df3711fa9e05d1ddac368a5db/Computability/HilbertTenthProblem)

A suitable destination is `Computability/HilbertTenthProblem/Papers/research-wip/zfc-fixed-input/`, with links from the H10 and K215 indexes. Keep the fixed-input claim separate from the existing uniform universal84 and certificate74 bounds.

The new files are prepared for incorporation under ProveIt's repository license. Retained K215 and predecessor notices and terms remain in `artifacts/compiler/`. `NOTICE.md` identifies the new and inherited material. The proof-assistant source files and all transitive proofs are referenced by the source pin rather than copied wholesale.

