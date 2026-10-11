# Lerch lattice-jet continuation: scope and provenance

Repository checkpoint: `f7e35be357654198c1546fd40f363694c5bcc2cc` of
`VladimirReshetnikov/ProveIt`.

## Incoming sources inspected

1. `docs/incoming/ProveIt_Continuous_Depth_Lerch_2026-10-10.zip`,
   internal `ProveIt_Continuous_Depth_Lerch_2026-10-10/article.tex`.
   In particular:
   - Definitions `cdl:eq:K`, `cdl:eq:Fintro`, `cdl:eq:Zseries`,
     `cdl:eq:ZMellin`.
   - Centered reflection `cdl:thm:reflection`, `cdl:eq:completed`.
   - Odd values `cdl:eq:oddZ`, `cdl:eq:oddF`.
   - Gamma/polylog convolution `cdl:eq:polylogGamma` and its proof.
   - Harmonic master `cdl:thm:harmonicmaster`; its express warning that
     differentiation of a discrete index is invalid.
   - Depth derivatives and primitive calculus.
   - Final research list Q8, “Spectral derivatives on the odd evaluation
     lattice,” is the exact target resolved in the new section.
2. `docs/incoming/ProveIt_Tilted_Lerch_Binary_Cancellation_2026-10-10.zip`,
   its article overview, section inventory, independent-order-jet and
   finite-closure statements, and final research list. Its independent
   order/shift derivatives are distinct prior work; they are not claimed
   again here.
3. `docs/incoming/Algebraic_Gauss_Centered_Harmonic_Reflection.zip`,
   article/body.tex section inventory and introduction. Its centered
   Barnes-harmonic family uses a different Mellin kernel. No alleged
   correction or priority claim about its unreviewed proofs is made.

The canonical manuscript's `chapters/10-discovery.tex` and the existing
Stieltjes derivative-tower setting were also consulted. Searches across
the local Polylogarithms text found no preexisting version of the explicit
all-order odd-lattice cumulants plus normally convergent mixed-jet Euler
evaluation proved here. This is a scoped audit, not an exhaustive worldwide
novelty search.

## Classical external inputs

- NIST DLMF §3.9(ii), especially equations 3.9.2–3.9.4:
  <https://dlmf.nist.gov/3.9#ii>. The Euler transformation itself is
  classical. Its use at all complex spectral orders and joint parameter
  differentiation is justified in the supplied proof by holomorphy on the
  slit z-plane and the Möbius substitution `z = -v/(1-v)`.
- NIST DLMF §25.14:
  <https://dlmf.nist.gov/25.14>. Standard Lerch notation, branches, and
  its polylogarithm specialization.
- NIST DLMF §25.11:
  <https://dlmf.nist.gov/25.11>. Standard Hurwitz argument derivatives
  and spectral conventions. The Stieltjes transport is a transparent
  consequence of the classical derivative identity and is labelled a
  recovery, not a new theorem about Hurwitz zeta.
- The source report itself credits the Gamma-product Fourier transform
  to Ramanujan, with modern treatment by Chakrabarti and Srinivasan,
  arXiv:1206.5122. The supplied section includes the short beta-integral
  normalization and a proof of the centered reflection input to prevent
  dependence on a hidden Fourier convention.

## Claims and limits

- **Proved:** every mixed depth/order derivative of the continuous-depth
  centered family at every positive odd order, with explicit Bell
  cumulants.
- **Proved:** the reflected generalized Lerch function and all its fixed
  mixed jets possess an absolutely, locally normally convergent Euler
  series at every complex spectral order.
- **Proved:** all corresponding spectral derivatives under the Gamma
  weight, and their polygamma-weighted mixed depth derivatives, are
  ordinary absolutely convergent integrals with the stated exact formulas.
- **Recovered:** Stieltjes parameter transport at depth two; the known
  odd values and fixed odd-polylogarithm Gamma integrals.
- **Not claimed:** finite classical-constant closure for arbitrary
  noninteger-depth spectral jets; arithmetic independence; an interval
  certificate for the numerical diagnostics; proof-assistant verification.
- **Errata:** no false theorem was found in the portions of the Lerch
  sources inspected. Their warning against differentiating the discrete
  odd-value formula is correct. The new holomorphic local germ supplies
  precisely the missing operation.

## Executed verification

`python verify_lerch_lattice_jets.py` succeeded with default arguments.
`lerch_lattice_verification.json` records:

- 48 exact symbolic cumulant comparisons;
- 45 exact finite Euler evaluations at negative integer orders, including
  20 odd trivial-zero checks;
- 2 exact differentiated-product identities;
- 30 independent comparisons, at depths 1.3, 2, and 1.4+0.2i, of Gamma
  moment integrals with Euler-evaluated reflected jets;
- direct numerical differentiation of generalized Stieltjes constants
  for the two simplest order derivatives;
- the displayed polylogarithm first derivative evaluated in both negative
  and positive zeta coordinates.

The Gamma integrals used 90 decimal digits. The Euler series used 230
terms and 135 digits to absorb finite-difference cancellation. The maximum
relative residual of the 30 independent comparisons was
`1.1622149e-71`. These floating-point checks are clearly labelled
diagnostics; the all-parameter identities rest on the analytic proofs.
