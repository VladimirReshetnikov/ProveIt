A CUBIC LOGARITHMIC LAW FOR MERGING PRIME-COUNTING SCALES
Research note, 26 November 2026

START HERE
  prime_scale_coalescence.pdf  Complete mathematical paper.
  prime_scale_coalescence.tex  Editable, self-contained LaTeX source.

RESULT
For the normalized native-ramp smoothed zeta prime error, observations
at r fixed distinct logarithmic offsets epsilon*u_j have limiting
covariance eigenvalues of orders

  1, epsilon^2, epsilon^3*log(1/epsilon), ...,
     epsilon^3*log(1/epsilon).

The last group has r-2 eigenvalues. Their explicit leading-constant
brackets are determined by the finite cubic form

  B(c) = (1/12) sum_i,j c_i*c_j*abs(u_i-u_j)^3
       = integral (sum_i c_i*(t-u_i)_+)^2 dt,

on contrasts satisfying sum c_i = sum u_i*c_i = 0. The normalized form
lies asymptotically between B and (4/3)B. A localized version of
Montgomery's proved pair-correlation estimate controls squared zero
multiplicities; the pair-correlation conjecture is not assumed.

For three equally spaced observations, the normalized limiting bounds
are [1/9, 4/27] for the smallest eigenvalue, [2/3, 8/9] for the raw
second-difference variance, and [1/6, 2/9] for optimal midpoint prediction.
The normalization is epsilon^3*log(1/epsilon).

Every fixed raw finite difference of order at least two has this same
rate. No fixed number of at least two nearby predictors can improve the
optimal linear prediction-error order. Fixed finite frequency deletion
does not change the cubic form or its bounds.

STATUS AND ASSUMPTIONS
The analytic proof takes RH from the inspected Lean development and
uses Montgomery's proved theorem under RH. No simplicity or independence
assumption is needed for the main result. Exact limiting constants,
as opposed to the explicit brackets, are separately stated under a
squared-multiplicity-density assumption. The factor 4/3 is convenient,
not claimed to be the best possible numerical factor.

The paper contains a complete ordinary mathematical proof of the new
steps. It is not a new Lean formalization, and the upstream development
was not rebuilt in this session. Finite checks are diagnostics, not a
kernel verification of the analytic proof.

PROVENANCE AND NOVELTY
  provenance/source_manifest.json
  provenance/prior_overlap_audit.txt
  provenance/independent_review.txt

The result answers the scalar case of a scale-merging question in the
earlier grh_multiscale_covariance packet. The inspected ProveIt catalogue
contains 61 placed packets, with a further 29 incoming archives screened.
Generic kernel-matrix flat limits and cubic-spline forms are established
prior art and explicitly credited. The candidate new contribution is
the arithmetic logarithmic law, the explicit treatment of unknown
multiplicities, and its prediction/difference consequences. Priority has
not been exhaustively certified.

REPRODUCING THE CHECKS
  python3 verification/verify_geometry.py

This uses Python's standard library only. It verifies exact rational
geometry identities, positive restricted forms, and normalization
constants. Recorded output: verification/geometry_checks.json.

Optional numerical illustration (dependencies in requirements.txt):
  python3 verification/continuum_model.py

This integrates an explicitly defined continuous positive spectral
model. It uses no actual zeta-zero table and makes no assertion about
zero simplicity. Its CSV/JSON outputs and two-panel figure are included.
Floating-point quadrature is illustrative, not an interval certificate.

REBUILDING THE PDF
On an initialized TeX installation, run pdfLaTeX three times on the TEX
file, from this directory. Alternatively:
  python3 build.py
  python3 build.py --checks

The helper uses pdfLaTeX and can initialize a local format/font map if
an installed TeX Live tree has no generated format. It modifies no system
files. Figures needed to compile the paper are already supplied. Logs
and temporary files go to build_cache and are omitted from the archive.

LIMITS OF THE CLAIM
The number and geometry of offsets are fixed before epsilon tends to
zero. Long-time covariance is taken before the scale-merging limit.
There is no explicit numerical onset claimed. The full residue-class
matrix problem and nonlinear prediction are not settled here.
Truncating the zero series at a fixed height before epsilon tends to zero
changes the rate; the paper explains why.
