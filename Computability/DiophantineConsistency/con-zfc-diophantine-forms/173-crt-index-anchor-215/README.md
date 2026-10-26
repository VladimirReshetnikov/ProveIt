# A reused CRT index: an explicit Diophantine consistency equation

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026.

## Result

The recommended equation is

\[
P_{215}(x_0,\ldots,x_{214})=\sum_{j=0}^{153}R_j(x_0,\ldots,x_{214})^2=0,
\qquad (x_0,\ldots,x_{214})\in\mathbb Z^{215}.
\]

Every residual is a literal polynomial of degree at most two. The complete
154-row list is printed in `report/report.pdf` and `report/residuals.tex` and
stored in `equations/principal/equation.json` and `residuals.txt`. The adjacent
`expanded_polynomial.json` gives every collected coefficient of the single
quartic. No coefficient is defined by a search, an unspecified machine, or an
uninstantiated universal polynomial. All variables are unrestricted integers.

The report gives an ordinary mathematical proof, composed with the explicitly
identified inherited Pell and numerical-calculus calibration, of

\[
\mathrm{ZFC}\vdash
\bigl(\neg\exists\boldsymbol x\in\mathbb Z^{215}\;P_{215}(\boldsymbol x)=0\bigr)
\longleftrightarrow\operatorname{Con}(\mathrm{ZFC}).
\]

Consistency means absence of a finite refutation in the fixed effective ZFC
presentation used by the inherited calibration. The argument is internal to
ZFC; it does not silently restrict proof codes to externally standard integers.
It proves the equivalence without assuming either consistency or inconsistency.
It does not prove that this polynomial has no zero.

## Measured improvement and companions

The baseline is the immediate 225-variable pooled-power polynomial at ProveIt
commit `953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4`, source package
`158-pooled-powers`. All support and height figures refer to the fully collected
polynomial, not its unexpanded circuit.

| Equation | Integer variables | Squared residuals | Degree | Nonzero monomials | Polynomial coefficient height |
|---|---:|---:|---:|---:|---:|
| Pinned parent | 225 | 162 | 4 | 7,867 | 128,446 |
| **Principal P215** | **215** | **154** | **4** | **5,660** | **91,679** |
| Companion P214 | 214 | 153 | 4 | 5,486 | 1,099,511,627,852 |
| Companion P213 | 213 | 152 | 4 | 5,402 | 2,417,851,639,242,452,488,945,685 |

The principal's maximum residual coefficient is **192**, versus 256 for its
parent. It has 1,042 residual monomials before squaring. P213 is the smallest
variable count delivered in this package; P215 provides the preferable balance
of coefficient size and variable count. The companions are complete equations,
with the same type of proof and exact reconstruction certificates.

These comparisons establish a concrete improvement within the directly
compiled quartic family. They do not establish a global minimum over all
Diophantine equations or worldwide priority. Smaller-variable representations
in other degree and coefficient regimes are already considered in ProveIt.

The principal equation file has SHA-256:

```text
8d919a1e5d6a802765b6d010c0140fb1d83c3d36d211b209b7a8d2fb3f3fb6f6
```

## The main new idea

The previous arithmetic source used a derived sum of formula labels in two
roles: a local range certificate and the nominal largest index for a shared
Pell certificate. These roles can be separated. The CRT row-index
representative `C` already has its own Pell pair and range request. It can be
chosen **even and arbitrarily large in its prescribed residue class**.
Choosing it after the other representatives and before the radix and Pell
frame makes it a valid replacement anchor.

This removes the derived-label range request and its arithmetic overhead. The
freed Pell pair certifies a larger growth index. To retain exact proof decoding
without the deleted local range, the principal source uses

\[
\ell=2^{20},\quad t=128+4z^2,\quad T_2=t^2,\quad K=T_2^2=t^4,
\quad F=t^K.
\]

The last equality is enforced by retained polynomial Pell machinery. The final
quartic contains no exponentiation operation. An independent constructor-tree
certificate proves that each retained local label is less than
`t^(2^20 - 1)`. Hence `F >= L^t` for `L=t^(2^20)`.

The useful separation lemma is:

> For positive integer labels at most `L`, with `L >= t` and `F >= L^t`,
> equality of products of `1+F*j`, with at most `t` factors on one side and at
> most `2*t+1` on the other, forces equality of their multisets of labels.

The proof first recovers equal factor counts, then uses elementary symmetric
coefficients in `[1,F]`. Their differences have absolute value less than `F`,
even at the boundary `F=L^t`. Evaluating at `F` therefore cannot hide a
nonzero polynomial difference. A single-conclusion Horn-flow argument recovers
a finite refutation even when the selected rule multiset has cycles.

The factorial-free CRT construction is inherited from sources151/157, and the
original square-shell C222 calculus is retained. The main construction does
not simulate Turing machine K215 or instantiate Jones' universal polynomial.

## From the new source to the final quartic

The semantic change produces a 221-variable system with 160 quadratic rows.
Five certified projections along the common Hessian kernel give 216 variables.
An exact affine consequence gives 215. Integral coordinate shears,
unimodular residual-row operations, and translations then reduce support and
coefficient height. Each operation has an explicit integer inverse or an
integer reconstruction map on the relevant zero set.

The main chain is:

```text
source/anchor221
stages/projection216
stages/affine215
the six P215 stages in OPTIMIZATION_CHAIN.json
equations/principal
```

The last optimization chain has 75 elementary invertible operations. Some
changes replace the sum of squares by a different polynomial with the same
integer zero set. Equality of the two polynomials is not asserted where only
zero-set equivalence is needed.

P214 and P213 use `t=16+4*z^2` and `K=2^20*t`. Retaining `K` as a separate
coordinate yields P214; substituting it directly yields P213 and larger
coefficients. The same boundary-valid separation lemma applies.

## Verify and reproduce

Python 3.10 or later is recommended. All coefficient verification, construction,
and evaluation use only the Python standard library. No network access is
needed.

From the extracted package directory:

```bash
python3 -B verify.py
python3 -B -O verify.py
```

Each command prints one JSON receipt. To save it outside the frozen archive:

```bash
python3 -B verify.py --receipt /tmp/conzfc-replay.json
```

To reconstruct all three profiles and every intermediate coefficient stage in
a separate directory:

```bash
python3 -B code/rebuild.py --output-dir /tmp/conzfc-rebuilt
```

The reconstruction freshly runs the new source producer from the frozen parent,
then replays projection and optimization certificates. Later equation files
supply descriptive metadata only. Every residual coefficient and expanded
quartic is recomputed. The delivered run reconstructs **26 stages**, and every
equation and expansion is byte-identical to the supplied counterpart.

To regenerate the human-readable residuals and metric includes:

```bash
python3 -B code/export_equation.py
```

To rebuild the report with TeX Live or an equivalent installation:

```bash
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The report uses standard AMS, Latin Modern, geometry, microtype, booktabs,
longtable, enumitem, fancyhdr, hyperref and xurl packages. TeX versions or
timestamps can change PDF bytes. `SHA256SUMS` authenticates the original
delivered bytes; after intentionally rebuilding a PDF, use `--skip-manifest`
to rerun the mathematical artifact checks without asserting original PDF-byte
identity. The frozen equation hashes are still checked in this mode.

## What was verified

The release verifier performs:

1. Frozen equation hash and release-manifest checks.
2. Independent comparison of fourteen constructor outputs with pinned source,
   exact depth computation, and the local majorant ledger.
3. Independent reconstruction of all source changes, including fourteen Pell
   pairs, sixteen power requests, and thirty-five frame atoms, for all profiles.
4. Exact projection checks, integral reconstruction identities, rank
   certificates, and deliberate certificate-corruption rejection controls.
5. Every forward and inverse residual identity in the optimization chains,
   including their composed inverse, and all expanded coefficients.
6. Independent parsing of all 154 printed residuals back into polynomials,
   six report-macro checks, and thirteen deliberate print-corruption controls.
7. Evaluator input controls and fresh reconstruction of all 26 coefficient
   stages.

Checks were run normally and with `python -O`, which removes Python `assert`
statements. The substantive independent checks use explicit failures. The
normal and optimized receipts are in `verification/`.

The PDF was compiled, rendered, and visually reviewed, including the full
literal appendix. The new mathematical argument was reviewed by independently
assigned AI research agents; this is not described as external human peer
review.

## Proof boundary

The mathematical result is an ordinary proof formalizable in ZFC, using
identified inherited theorems. Finite coefficient checks do not prove the
unbounded Pell or logical calibration theorems by testing examples.

The logical endpoints are
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation` at the pinned commit.
The former concerns the numerical calculus directly and has no machine
argument. The lower construction uses an internally well-founded model; it
does not assume an externally well-founded or transitive model of ZF.

`inherited/` contains selected source proofs and the inspected Lean files.
It is **not a complete compilable Lean dependency closure**, and no new
end-to-end Lean/Rocq verification or fresh build of that closure is claimed.
See `proofs/ORDINARY_PROOF_DEPENDENCY_BOUNDARY.md` and
`proofs/MATHEMATICAL_REPORT_REVIEW.md` for the exact scope. No unresolved new
mathematical gap was identified in the portions reviewed.

## Additional research preserved

The report and `proofs/FIXED_ROLE_SEED_CALCULUS.md` preserve an explored logical
alternative: split the guarded seed bundle into a fixed-role seed and a
separate vacuity schema. It reduces the largest formula depth but loses
arithmetic sharing; its measured compiler result had 229 variables against
the 225-variable control. It is recorded as a useful negative result and a
future direction, and is not used to calibrate the principal equation.

The optional producer `code/experiments/build_split.py` preserves that
comparison. Invoke it with `--mode split` or `--mode old` and an `--output`
directory. Its recorded metrics are in `verification/SEED_EXPERIMENT.json`;
the 26-stage principal/companion replay is independent of this experiment.

`INTEGRATION.md` gives suggested repository placement. `PROVENANCE.json`, the
copied notices, and `SHA256SUMS` identify the origins and exact release files.
