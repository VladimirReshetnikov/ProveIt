# Proposed ProveIt integration

## Baseline and destination

This package was prepared against commit
`a0a90ef31877f98be437191c48b46f02d5456867` after inspecting the manuscript
and all 16 incoming archives present there. It does not modify the repository.

Suggested complete-report destination:

`Analysis/Polylogarithms/docs/reports/extremal-bounds-cyclic-descent/`

Keep the article, exact programs, certificates, provenance, and build files
together. The package is deliberately independent of repository build paths.

## Results to integrate

| Topic | Source in this package | Suggested manuscript neighborhood |
| --- | --- | --- |
| Positive beta allocation and exact endpoints | `article/gaussian.tex`, first section | Signed kernels and the incoming real-order extension |
| Resolved critical Euler conjecture | `article/gaussian.tex`, second section | `05-signed-kernels.tex` and `ProveIt_RealOrder_Threshold.zip` |
| Sharp global envelope and inverse identities | Remaining sections of `article/gaussian.tex` | Gaussian constants / real-order analysis |
| Absolute Euler convergence for all positive real orders | `article/euler_secant.tex` | Euler acceleration and threshold discussion |
| Prime-order cyclic torsion and finite jets | `article/cyclic.tex` | `08-distribution.tex`, `08-conductor-jets.tex` |
| Extremal Lerch zero comparison and branch dichotomy | `article/lerch.tex` | `09-zero-geometry.tex` and boundary report |
| Exact enlarged finite-span S6 obstruction | `article/s6_obstruction.tex` | `04-cyclotomic-quotients.tex` |

`manuscript-addendum.tex` is a compact overview for editorial use. It refers
to the complete report for proofs. It is not a replacement for importing
the proof sections and their hypotheses.

## Status changes supported by this report

1. Promote `conj:constant` in
   `ProveIt_RealOrder_Threshold/article/real_order_threshold.tex` to a theorem.
   The beta allocation identity proves its strict monotonicity; the endpoint
   atom and positive remainder formula prove the optimal all-N constant.
2. Reconcile `research:conj:minimum` in the Formal Reductions report with
   the already-proved k=1 uniqueness in `proveit_lerch_boundary_research.zip`.
   Cite the boundary report for that case. This continuation extends the
   branch analysis to a general criterion and the k=2/k=3 decisions.
3. Preserve the current S4 theorem and S6 conjecture statuses. The new S6
   theorem concerns exactly the finite relation span described in the paper.

## Hypotheses and conventions to preserve

- `g_(a,b)` at the critical line and below means the analytic or Abel value.
  The Euler transform converges absolutely for all a,b>0, even when the
  untransformed boundary series diverges.
- The global maximum C* bounds `-2g`, equivalently the first normalized Euler
  remainder. The optimal uniform all-N constant proved in this report is
  restricted to a+b=1.
- The cyclic theorem requires q=md, gcd(m,d)=1, d>1, u=1 mod m,
  gcd(u-1,d)=1, and ell not dividing phi(m). The factor m can equal 1.
- Retain e_0 in the unanchored distribution module. Anchoring it changes
  the quotient and its torsion.
- The torsion is that of a formal integral module, not numerical periods.
  In the jet theorem the torsion B-module is specified; the free summand
  is asserted only as a free abelian group.
- The Lerch k=3 result is the smallest **individual** derivative order with
  both branches decreasing. Persistence for every k>=3 remains open here.
- The S6 separator excludes the prescribed 5,131-row family, not every
  possible depth-four relation, arbitrary higher-depth elimination, or the
  numerical identity.

## Dependencies and labels

The complete paper recalls the positive double integral, the critical signed
measure, the finite integral distribution resolution, and the Lerch zero-count
input with attribution. Keep these proof dependencies available when extracting
a theorem.

The cyclic, Lerch, and S6 sections use the `cpc:`, `lershape:`, and `s6bounded:`
label prefixes. The Gaussian and editorial source labels should be prefixed
as needed during a chapter-level import to avoid a collision with existing
generic labels. The supplied single-source file already compiles as a report.

The bibliography is split into `article/references.tex`, `article/cyclic_bib.tex`,
and `article/lerch_bib.tex`. A suitable bibliography item for the report itself
appears in `report-bibitem.tex`.

## Verification before integration

Run `python code/replay_all.py` from the extracted package. It checks the exact
maximum, inverse coefficients, 52 Smith examples, complete Lerch endpoint
signs, and the complete S6 row family with integer pairings. Then run `make pdf`.
The supplementary `provenance/VALIDATION.md` records the delivered validation.

No automatic patch is proposed against the moving main branch. The pinned
source paths and hashes make a later merge reviewable.
