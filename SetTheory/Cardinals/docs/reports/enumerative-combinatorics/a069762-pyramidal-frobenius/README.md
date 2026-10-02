# Exact solution for OEIS A069762

**Three Consecutive Square-Pyramidal Numbers: Exact Frobenius Formulas,
Gap Laws, and Algebraic Inversion**

Research report prepared for Vladimir Reshetnikov, October 1, 2026.

## Main result

For s(n) = n(n+1)(2n+1)/6 and F(n) the Frobenius number of
<s(n), s(n+1), s(n+2)>, set h(n) = (0,3,2,3,0,5)[n mod 6]. Then

    F(n) = [4n^5 + 32n^4 + (101-10h)n^3 + (175-45h)n^2
            + (102-65h)n - 36 - 30h]/36 + epsilon(n),

where epsilon is zero except for

    n:        2   3    5    11    17    23
    epsilon: 10  40  315  1612  3135  2400.

The report proves the formula, the complete exception list, an explicit
Apery normal form, exact genus and gap moments, the triangular normalized
gap law with O(1/n) cumulative-distribution error, a minimal eventual
order-18 recurrence, and convergent all-orders inverse expansions. It also
proves a general transfer theorem from Apery limit measures to gap measures.

## Files

- `article.tex`, `article.pdf`: the self-contained 20-page article, including
  proofs, literature/provenance discussion, and ten further research directions.
- `verify.py`: exact formula, genus, membership/representation and inverse
  algorithms; independent Dijkstra and dynamic-programming checks.
- `verification.txt`: executed output of `python verify.py --symbolic`.
- `derive_moments.py`: symbolic finite-summation derivation of the gap moment
  polynomial for a user-specified nonnegative order; no interpolation.
- `moment1.json`, `moment2.json`: exact six residue-class polynomial expressions
  for the first and second gap-power sums.
- `moment1_verification.txt`, `moment2_verification.txt`: executed outputs of
  those symbolic derivations and checks.
- `data.csv`: values for n=2..1000, including generators, Frobenius number,
  genus, and symmetry defect.
- `rational_gf.json`: exact numerator and denominator of sum(F(n)*x^n,n>=2),
  encoded in increasing powers of x.
- `oeis_submission.txt`: draft contribution text, not submitted.
- `requirements.txt`: the exact SymPy version used for the symbolic checks.

## Reproduction

The verification was executed using Python 3.13.5 and SymPy 1.14.0.
The source uses Python 3.10+ syntax. The basic audit has no third-party
Python dependencies:

    python verify.py

For symbolic checks and moment derivation:

    python -m pip install -r requirements.txt
    python verify.py --symbolic
    python derive_moments.py --power 1 --output moment1.json
    python derive_moments.py --power 2 --output moment2.json

Larger moment orders are supported mathematically and by the algorithm,
but symbolic runtime and output size grow substantially. The supplied
exact derivations were run for orders 1 and 2; direct finite moment checks
were run for orders 0 through 3.

Compile the manuscript with a standard LaTeX installation:

    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

The PDF was rendered and visually reviewed; the final LaTeX build had no
reported warnings, overfull boxes, or underfull boxes.

## Trust boundary and novelty

These are conventional proofs in an unrefereed manuscript, with reproducible
exact computational support. No Lean or Rocq formalization is claimed.
The finite checks do not replace the infinite arguments in the article.
General eventual quasipolynomiality and the standard Apery identities are
not claimed as new.

The inspected OEIS entry had no explicit formula or asymptotics. A targeted
primary-source literature search did not locate the explicit result here;
this is not a proof of priority. Independent mathematical and literature
review is appropriate before publication or OEIS submission.

The ProveIt inspection was scoped, not an exhaustive audit. The inspected
root-tree identifier was 29aca108ed25d714f31b1316512777fbbdc8e006. The report
uses its separation of exploratory and formally verified results as a
methodological model; no ProveIt theorem is needed as a hypothesis.
No GitHub commit or OEIS edit was made. No external paper PDFs or font files
are included.
