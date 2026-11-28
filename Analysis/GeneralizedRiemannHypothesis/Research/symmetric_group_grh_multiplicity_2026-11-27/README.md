# Asymptotically sharp symmetric-group zero-multiplicity bounds

Research packet, 27 November 2026. Suggested placement in ProveIt: `Analysis/GeneralizedRiemannHypothesis/docs/incoming/` (no repository writes performed).

## Main advances

- For every n >= 3 the monomial-character cone contains `U_n(C_n)`, where
  `U_n(c) = c Ind_{<t>}^{S_n}(sigma) - Reg + 1`, `B(1)=0`,
  `B(k)=k+B(k/P(k))`, `P(k)` is the largest prime factor, and
  `C_n=sum_{k=2}^n B(k)/k`. The proof is uniform and does not rely on LPs.
- The conjectured sharp constant is `n-1`. The uniform excess has asymptotic
  `C_n-(n-1) ~ sum_{k<=n} 1/P(k)`, taking `P(1)=1`. The paper supplies a
  self-contained stretched-exponential relative error bound and derives a
  finer asymptotic using a classical smooth-number theorem.
- Exact rational cone certificates for n=13,14,15,16 improve the prior
  reported range n<=12. The exact all-degree claim remains unresolved.
- The quotient holomorphy result is unconditional. Only its off-line
  specialization without the quadratic sign factor uses Dirichlet GRH.
  No Artin holomorphy assumption is used and no new RH is claimed.

## Files and reproducibility

| File | Purpose |
|---|---|
| `paper.tex`, `paper.pdf` | Complete proof and source audit; 9-page compiled paper |
| `cert13.json` through `cert16.json` | Exact positive rational identities |
| `verify.py` | Independent stdlib-only verifier, reconstructs every row |
| `verification.txt` | Output of an actual verification run |
| `search.py` | Optional discovery program, including original solver choices |
| `bounds.py`, `bounds.csv` | Computation and illustrative table of uniform constants |
| `sources.md` | Repository provenance, dependency and novelty status |
| `SHA256SUMS` | Integrity checks for the files |

With Python 3.10+ (no external dependencies):

```sh
python3 verify.py
python3 bounds.py
```

Expected verification: 92, 119, 143, 190 strictly positive terms across 101,
135, 176, 231 conjugacy classes, respectively. The verifier directly enumerates
block groups and checks all coefficients using `fractions.Fraction`. Run without
`-O` so assertions remain enabled. The CSV is a numerical illustration, not a
certificate; `bounds.exact_bound(n)` evaluates the exact rational constant.

Optional certificate discovery (tested settings used NumPy, SciPy 1.17.0 and
SymPy 1.14.0):

```sh
python3 -m pip install numpy scipy sympy
OPENBLAS_NUM_THREADS=1 python3 search.py 13 14 15 16
python3 verify.py generated_cert13.json generated_cert14.json generated_cert15.json generated_cert16.json
```

Discovery is not required to verify the proof. Solver changes can alter support
or prevent exact reconstruction. The supplied verified certificates remain
unchanged by discovery. The subgroup family is not exhaustive.

Build the PDF with ordinary LaTeX (two passes):

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

No Lean kernel verification of the new mathematics or independent rebuild of
the upstream GRH development was performed. The paper is a research-level
human proof with exact computational certificates for its four finite cases.
