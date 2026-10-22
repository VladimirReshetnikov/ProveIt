# Smaller Diophantine forms of Con(ZFC)

Research synthesis for ProveIt, 22 October 2026.

This packet combines the inputless K215 construction with ordinary strong-Pell equations, integer-unit grouping, quadratic root elimination, and a smaller local-tile compiler. Its principal mathematical claim is that, for each supplied construction in its declared domain,

\[
\mathrm{ZFC}\vdash
\bigl(\text{there is no solution}\bigr)
\longleftrightarrow \mathrm{Con}(\mathrm{ZFC}).
\]

The proof uses the pinned repository's syntactic K215 calibration and the inherited Pell/compiler development, with new reductions proved in `report.pdf` and the proof notes. This is an ordinary mathematical proof, not a new end-to-end Lean/Rocq certificate. The finite checks audit the implementations; they do not establish the consistency of ZFC or replace the mathematical soundness/completeness arguments.

## Read first

- `report.pdf`: integrated mathematical report, including complete formulas, coefficient definitions, proofs, comparisons, and verification boundaries.
- `report.tex` and `sections/`: editable LaTeX source.
- `code/verify.py`: one-command offline reproducibility entry point.
- `verification/summary.json`: the recorded final check results.
- `provenance.json`: immutable upstream URLs and SHA-256 hashes of included source evidence.

All four compiler coefficients are fixed integers. They are specified by a complete finite recipe rather than printed in decimal. The recipe still denotes extremely large integers; its size improvement is mathematical, not a claim of practical materialization.

## Results

Unmarked unknowns range over strictly positive integers. For systems, degree means the largest residual degree. Each binary addition, subtraction, or multiplication counts as one operation; reading a fixed coefficient and reusing a register are free. Comparisons in a system are free. Creating polynomial residuals and a sum of squares incurs the indicated extra operations.

| Construction | Unknowns | Equations | Exact degree | Operations |
|---|---:|---:|---:|---:|
| Inherited normalized polynomial, new coefficients | 15 | 1 | 155 | 67 |
| Ordinary strong system | 15 | 6 | 28 | 61 |
| Grouped ordinary system | 15 | 4 | 28 | 63 |
| Ordinary product `P69` | 15 | 1 | 99 | 69 |
| Four-square polynomial `Q56` | 15 | 1 | 56 | 74 |
| Root-eliminated `Psi14` | 14 | 1 | 342 | 73 |
| Root-eliminated `Phi14` | 14 | 1 | 293 | 75 |
| Root-eliminated system | 14 | 5 | 244 | 69 |
| Quadratic lift / its sum of squares | 33 | 24 / 1 | 2 / 4 | not optimized |
| Signed-domain lift of `P67` | 33 unrestricted integers | 1 | 292 | 130 |
| Signed-domain lift of `P68` | 33 unrestricted integers | 1 | 228 | 131 |

For the clearest small system, start with the four equations. For fewer primary unknowns, use either fourteen-variable polynomial. The inherited 67-operation evaluator remains the lowest operation count verified here. Fourteen is not a global variable minimum: the repository also develops the classical nine-natural-unknown existence theorem.

### The recommended four-equation system

The fixed ports are

\[
\beta=B-1,\qquad K=D_C+BD_R,\qquad M_C,\qquad
M_F=M_F^{\mathrm{nat}}+B-1.
\]

In particular, **the source port `MF` is shifted**. It is not the native mask by itself. With fifteen positive unknowns

\[
J,F,\alpha,z,f,h,i,T,s,w,\tau,\eta,\zeta,y,\gamma,
\]

define

\[
\begin{aligned}
q&=\beta J+1,&C&=q-F-\alpha,\\
X&=wq,&Y&=sq^3,&E&=XY,\\
k&=\eta+\zeta,&c&=kY+\eta,&a&=E+Y,\\
H&=4a+3,&\Delta&=a^2+H,&D&=X+ac+\gamma H,\\
L&=E(kY),&G&=(q-1)(q-F)+\alpha,\\
R&=G(q^2-1)+(M_C+qM_F)J,&V&=c(Tf-1)-Rf^2.
\end{aligned}
\]

Set

\[
\begin{aligned}
N_0&=\tau^2-L(L+k),&N_1&=D^2-\Delta c^2,\\
N_k&=k-hE-R,&N_t&=(K+w)C+q-F-z(q-1),\\
I&=ic^2,&W&=\Delta(f^2-1),\\
N_a&=W(V^2-y^2)+y^2.
\end{aligned}
\]

The system is

\[
\boxed{N_0N_t=1,\quad N_1N_k=1,\quad N_a=1,\quad I^2=W.}
\]

Its degree-56 single-polynomial version is

\[
\boxed{(N_0N_t-1)^2+(N_1N_k-1)^2+(N_a-1)^2+(I^2-W)^2=0.}
\]

Every displayed abbreviation is a polynomial expression, not an additional quantified unknown. The exact common-subexpression circuits are in `circuits/`. The ordinary strong coordinate is not interchangeable tuplewise with the normalized strong coordinate; `report.pdf`, Section 3, supplies the necessary relaxed-rank proof.

### Smaller coefficient recipe

The old full `3 x 3` window alphabet has 1,420,903,358,357,108,792,377 permitted windows. The local predicate ignores four corners and reads the previous cell only through a boundary indicator. The projected alphabet therefore uses five fields and has exactly 87,923,161 permitted tiles.

The revised dimensions are

\[
b=5^{13},\qquad L_0=5^{15},\qquad d=bL_0=5^{28}.
\]

The original package 06 used `d = 5^67`. Thus the exact binary length of `B - 1 = 2^d - 1` decreases by a factor of `5^39`. Each of the four fixed ports has at most `2d` binary digits. The alphabet projection, four overlap constraints, native masks, reserved impossible selector, carry bounds, and modulo-five tuning condition are proved in Section 6. No coefficient integer of this size is materialized by the scripts.

## Reproduce

Python 3.10 or later, using only the standard library:

```sh
python3 code/verify.py
```

The default mode checks and reuses the included exact thirteen-class census. To rerun its left/right enumeration as well:

```sh
python3 code/verify.py --full
```

The scripts resolve paths from their own locations, so an absolute path to the entry point also works from another current directory. The checks regenerate the circuit data and receipts, verify the literal machine against the included Lean/Rocq transition tables, audit operation counts and register liveness, expand the quartic exactly, check coefficient supports and local tableau fixtures, and exercise formula identities on deterministic diagnostic assignments. Finite-field line evaluations corroborate the degree calculations; uniform exact-degree arguments are in the report.

Build the PDF with a standard TeX Live installation containing `latexmk`, `pdflatex`, Latin Modern, AMS packages, `mathtools`, `microtype`, `geometry`, `booktabs`, `enumitem`, `needspace`, `hyperref`, and `fancyhdr`:

```sh
make pdf
```

Alternatively run `latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex` in this directory. No network is needed for the Python checks or for a TeX build with those packages installed.

## Packet layout

| Path | Contents |
|---|---|
| `circuits/` | Complete straight-line arithmetic sources and the expanded quartic |
| `code/` | Standalone generators and verifier |
| `coefficients/` | Projected compiler specification and exact inherited census |
| `machine/` | Literal K215 table plus Lean and Rocq dense-table sources |
| `proofs/` | New ordinary, signed-domain, and projected-compiler arguments; separate review note |
| `evidence/` | Selected unchanged upstream proof notes, source circuits, endpoint statements, and licenses |
| `verification/` | Reproducible finite-check receipts |
| `sections/` | Included sections of the LaTeX report |

The `evidence/` files are selected source evidence, not a complete checkout capable of rebuilding the upstream proof assistants. In particular, the included Lean/Rocq files retain imports into their parent development.

## Provenance and status

All upstream material is pinned to ProveIt commit

```text
3b201cdea32d2c816f5f3d20734051f25fd3ef14
```

The baseline packages were developed against `cdd582bec13f908df3711fa9e05d1ddac368a5db`; their original internal metadata is preserved. The literal K215 table has SHA-256

```text
fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090
```

This is an AI-assisted mathematical synthesis and implementation audit prepared for incorporation into ProveIt. Separate review within this work is not independent human peer review or proof-assistant certification. No new Lean/Rocq theorem or encoded ZFC proof object is supplied. The report explicitly states the inherited mathematical inputs and the new proof obligations it discharges.

The conclusion concerns an equivalence with consistency. If ZFC is consistent, its second incompleteness theorem prevents it from proving the resulting unsolvability statement. No assertion that ZFC is consistent is made or needed to prove the equivalence.

See `NOTICE.md` and `LICENSE` for provenance and licensing. `MANIFEST.sha256` records the delivered files before any regeneration.
