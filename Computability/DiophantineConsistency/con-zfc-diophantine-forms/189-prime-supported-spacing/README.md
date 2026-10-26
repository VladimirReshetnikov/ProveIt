# Prime-supported Pell growth and binomial sequence spacing

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026.

## The delivered result

The equation is the single ordinary polynomial

\[
P(x_0,\ldots,x_{208})=\sum_{j=0}^{149}R_j(x_0,\ldots,x_{208})^2=0,
\qquad \boldsymbol x\in\mathbb Z^{209}.
\]

Every quadratic residual is printed in the standalone LaTeX source and PDF,
and stored literally in `equations/equation.json`. The fully collected
polynomial is in `equations/expanded_polynomial.json`. No variable exponent,
binomial primitive, unspecified coefficient, or external predicate remains.

Using the retained ordinary C222/ZF/ZFC calibration, the report proves in
mathematics formalizable in ZFC that

\[
\neg\exists\boldsymbol x\in\mathbb Z^{209}\ P(\boldsymbol x)=0
\quad\longleftrightarrow\quad\operatorname{Con}(\mathrm{ZFC}).
\]

The report proves an equivalence; it does not prove consistency. The proof is
internal to ZFC and does not add an externally-standard-code restriction.

## Exact comparison

| Measure | Frozen incoming P210 | New P209 |
|---|---:|---:|
| Unrestricted integer variables | 210 | **209** |
| Squared quadratic residuals | 150 | 150 |
| Total degree | 4 | 4 |
| Collected monomials | 5,282 | 5,283 |
| Collected coefficient height | 1,099,511,627,776 | **274,899,927,541** |
| Maximum residual coefficient | 1,048,576 | **524,309** |
| Residual terms | 999 | 999 |

The new equation saves one variable, reduces height by almost a factor of
four, and adds one collected monomial. This is an improvement in the direct
quartic family, not a global minimum or a claim of worldwide priority.
Other repository families use fewer variables at different degrees,
coefficient costs, and domains.

## Main new arithmetic idea

The old beta spacing was `y = F*(2*v+1)` with a free multiplier. We force
`y = F*B`, reusing the already authenticated selector `B = binom(F+t,t)`.
The eliminated coordinate is that multiplier.

The replacement is made complete by a new Pell certificate:

\[
t=32(2z+1)^2,\quad Z=ctF,\quad X^2-Z^2-2ZF=1,\quad F+t=ctu,
\qquad c=524309.
\]

After the existing front recovers `F > 0`, the residue forces the Pell
index to be at least `(c-1)*t`, supplying the required growth. For
completeness choose cofinal horizons `t = 32*c^(2*k)`. Elementary finite-field
annihilating indices make it possible to choose `F` divisible by every prime
at most `t` and by a sufficiently large power of two. The selector is then
odd; `y = F*B` makes the beta moduli pairwise coprime and dominates all
pending proof states. The report gives the entire argument, including
the initial sign-free bound and the noncircular witness order.

This route encodes the numerical C222 proof calculus directly. It does not
simulate K215 or instantiate Jones's universal polynomial.

## Contents

- `ConZFC_Prime_Supported_Spacing.tex` and `.pdf`: self-contained report,
  proof, exact comparison, and all 150 literal residuals.
- `equations/`: literal system, expanded polynomial, coordinate map,
  metrics, readable residuals, and exact changes from the parent.
- `code/`: deterministic builder, independent verifier, exact evaluator,
  printed-equation parser, arithmetic regression, and report builder.
- `proofs/`: two independent AI mathematical reviews.
- `verification/`: fresh verification receipts and PDF checks.
- `inherited/`: exact parent ZIP, exact parent equation JSON, and license.
- `PROVENANCE.json`, `NOTICE.md`, `LICENSE`, `SHA256SUMS`: origins,
  licensing, and integrity.

## Verify and reproduce offline

Python 3.10 or later and its standard library suffice for the arithmetic.
Run from the extracted package root:

```sh
python3 -B code/verify.py
python3 -B -O code/verify.py
python3 -B code/check_printed.py
python3 -B code/check_arithmetic.py
```

The independent coefficient verifier imports neither the builder nor the
inherited polynomial helpers. It reconstructs all residuals, expands all
squares, checks every coefficient and metric, and rejects deliberate
coefficient corruptions. The printed-equation checker independently parses
all 150 printed residuals. Verification checks remain active under `-O`.

Rebuild the equation with `python3 -B code/build.py`. Rebuild the standalone
TeX and PDF with `python3 -B code/build_report.py` using a standard TeX Live
installation. To evaluate a JSON array of exactly 209 integers, run:

```sh
python3 -B code/evaluate.py tuple.json --residuals
```

The new equation file SHA-256 is:

```text
b0413e587c595c6813f8eb67ef1581a507cee6155a38b8d091ca064f3e29b9f6
```

## Proof and verification boundary

The release provides ordinary mathematical proofs formalizable in ZFC,
with explicitly retained Pell/binomial-CRT and C222/ZF/ZFC dependencies.
The arithmetic first uses the inherited square-shell recoding of C222,
which fixes truth code 0 and falsity code 1 and transports each guarded
rule. Those constructors are not literally the original Lean constructors.
The subsequent inherited original-calculus interfaces are
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`.

The parent release verifier was freshly run, including its manifest,
inherited source checks, exact projections, and reconstruction. The new
finite coefficient checks passed normally and with Python optimization.
The unbounded number-theoretic arguments are proofs, not conclusions
extrapolated from the finite tests. Independent review means separate
AI research tasks and separately written code, not external human review.

This is not a newly compiled end-to-end Lean/Rocq proof or a complete Lean
dependency closure. It does not assert pointwise equivalence with every
old parent witness; completeness constructs an appropriate new witness
from the underlying finite refutation.

## Integration

The work is pinned to ProveIt commit
`32e9e9eb5999c96b0efe80c80a4018afd33d44ae`. The immediate parent is the
incoming `ConZFC_Pell_Growth_210_2026-10-25.zip` at that snapshot.

Suggested placement: a new numbered source directory under
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/` through
the repository's `docs/incoming/` workflow. Assign a source number at intake.
Preserve the earlier reports and their historical metrics. No remote
repository files have been changed by this release.
