# Strict growth and the Catalan limit for adjacency-bounded 132-avoiding permutations

Research report prepared for Vladimir Reshetnikov, September 19, 2026.

## Main results

Let a_n^(m) count the 132-avoiding permutations of {1,...,n} with every
adjacent absolute difference at most m, and let alpha_m be their exponential
growth constant (n tends to infinity with m fixed).

The article proves:

1. alpha_(m+1) > alpha_m for every integer m >= 1. More strongly, both
   irreducible component growth rates increase strictly for m >= 2.
2. 4 - alpha_m = (2 log(m) + 4 log(log(m)) + O(1))/m.
3. For E_m = m(4-alpha_m)-2 log(m)-4 log(log(m)),
   2 log(pi)-4 log(2) <= liminf E_m <= limsup E_m <= 2 log(pi).

The proof of strict increase completes the remaining strict-inequality part
of Nadler's Conjecture 2, using the endpoint system introduced by Mayama and
Akita. The report includes proofs of its finite-state prerequisites. The
asymptotic refinement has a separate counting and analytic proof.

The literature check found no later resolution in the inspected sources;
this is not an exhaustive novelty certification or external peer review.
The all-m component ordering (V dominates U for every m >= 5) and convergence
of E_m are NOT claimed. The component ordering is certified only for m=2..20.

## Read the report

- `article.pdf`: the comprehensive report, with proofs and computational audit.
- `article.tex`: its complete editable LaTeX source; references are embedded.
- `figures/`: the two separate figures in PDF and PNG form.

## Exact verification (no third-party packages)

From this directory, run:

```text
python code/verify.py
```

Run without Python's `-O` optimization flag: the verifier uses assertions and
explicitly refuses to run with assertions disabled. The bundled run used
Python 3.13.5. The exact verifier and model use only the standard library.
They require no network, CAS, numerical eigensolver, or theorem prover.

The successful output is preserved in `data/verification_log.txt`.

Checks performed:

- Direct definition-based 132 avoidance against the recursive Catalan
  generator for all permutations through length 7.
- First-entry formula for every Catalan avoider through length 10.
- 2,840 cumulative endpoint counts, m=1..8 and n=1..10.
- 53,534 exact weighted-edge comparisons for the shift m -> m+1,
  m=2..30, and strong connectivity of both components in those cases.
- Coefficientwise scalar upper bounds and skew-block lower bounds through
  n=100, m=2..12, d=1..min(5,m-1).
- 38 rational Perron-radius interval certificates, m=2..20, using 3,458
  strict integer row inequalities. These also certify the finite component
  ordering and the componentwise strict increase in that range.
- Exact full polynomial-matrix identities for all four generating functions
  (m=1..4), plus coefficient checks through n=200.
- Independent reconstruction of the certificate matrices using Catalan
  convolutions, rather than the binomial first-entry formula used by the
  numerical generator.

Finite checks do not prove an all-parameter theorem. Those theorems are
proved in English in the article. The certificates verify finite exact
algebraic statements, not the analytic limit proof in a proof assistant.

## Regenerate numerical proposals and symbolic certificates

Optional dependencies are NumPy, SciPy, SymPy, and Matplotlib. The exact
versions used are recorded in `data/environment.json`; the requirements file
pins those versions for the numerical/symbolic workflow.

```text
python -m pip install -r requirements.txt
python code/compute.py --max-m 20 --symbolic-max 4 --large-scalars
python code/verify.py
python code/plot_results.py
```

The generator overwrites its tables and certificates in `data/`. Use the
arguments shown above to reproduce the bundled verification ranges.
A positive numerical eigenvector is only a proposal: the generator refuses
to issue a certificate unless the integer inequalities pass. The verifier
checks those inequalities again without importing the numerical solver.

The large-m scalar bounds are floating-point evaluations of roots for which
the article proves exact comparison theorems. Their displayed decimals are
NOT outward-rounded, certified interval endpoints. The exact Perron
certificates, by contrast, are rational interval proofs.

For reproducibility, one may set `OPENBLAS_NUM_THREADS=1` before running the
numerical generator. This is optional; exact certificate checking is
independent of thread count or numerical proposal details.

## Build the PDF

A full TeX Live installation with pdfLaTeX is sufficient. Run from this folder:

```text
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

`build.sh` and `build.ps1` run these passes on Unix-like systems and Windows
PowerShell, respectively. The existing PDF figures are sufficient; Python is
not needed to rebuild the article. No font files are included.

## Data formats

- `sequences.csv`: exact integers a_n^(m), n=0..200, m=1..12; a_0=1.
- `growth_constants.csv`: numerical component roots and derived quantities,
  m=2..20. `dominant` is corroborated by the rational certificates.
- `perron_certificates.json`: one object per (m, component). Each rational
  radius endpoint has numerator, denominator, and a positive integer vector.
  The inequalities are W(lower)*v < v and W(upper)*w > w, coordinatewise.
- `symbolic_certificate_m*.json`: common denominator and all state numerators,
  coefficients in ascending degree, verifying (I-W)N = x D 1, with D(0)=1.
- `generating_functions.json`: exact numerator/denominator coefficient arrays
  and readable polynomial strings for m=1..4. Arrays are ascending-degree.
- `large_m_scalar_bounds.csv`: scalar root evaluations through m=1,000,000,
  using d=1,2,4,8 for the lower construction.
- `computation_log.txt`, `verification_log.txt`: actual successful run logs.
- `environment.json`: the numerical/symbolic environment used for this run.
- `SHA256SUMS`: integrity hashes for the distributed files except itself.

## Sources and attribution

Nathaniel Nadler, *On 132-Avoiding Permutations with an Adjacency Constraint*,
arXiv:2604.22135v1, Conjecture 2 in Section 5.2.
https://arxiv.org/abs/2604.22135

Teruki Mayama and Dai Akita, *Finite-state enumeration of adjacency-constrained
132-avoiding permutations*, arXiv:2605.23519v1, especially Theorem 2.4,
Proposition 2.7, Theorems 4.12 and 4.14, and Problem P3.
https://arxiv.org/abs/2605.23519

The finite-state system, rationality, existence of the growth constants,
non-strict monotonicity, and the earlier O(log(m)/m) bound are established
work and are credited in the article. The new arguments developed here are
the shift embedding, its strict-growth consequence, and the refined
asymptotic comparison. No third-party paper PDFs or font files are included.
