# Proposed ProveIt integration

## Placement

Add this directory as:

`Analysis/Transseries/docs/series-and-transseries/Polylogarithm_Order_Jet_Filters/`

Preserve `article.tex`, `article.pdf`, the code and retained data, the source audit,
and the claim-status notes together. Add a backlink in the Polylogarithms reports
index; do not copy a bare theorem without its order and lateral-sign conventions.
No remote edits or pull requests have been made by this delivery.

## Suggested inventory entry

> **Order-Jet Filters for Polylogarithmic Transseries** (12 October 2026).
> Sharp degree costs and the complete real joint-cancellation ideal for
> logarithmic spectral nodes; detuning robustness; algebraic-normalization
> rigidity; a convergent moving-order curve with zero jump but nonzero physical
> completion; all order-zero jets in Stieltjes and regularized-integral
> coordinates; an exact digamma Borel kernel; global real monotonicity and
> convergent small/large inverse charts. Conventional proofs, 165 finite exact
> assertions and 46 high-precision non-interval checks. Sufficient inverse disks,
> not exact radii. Existing resonant-polylogarithm Gamma/Bell formulas and generic
> inverse-transport results are credited. Incoming-archive comparison remains
> required; no formalization or worldwide-priority clearance is claimed.

## Stable labels and dependencies

- `ojf:thm:dictionary` uses the exact completion already present under
  `thm:lattice` in the resonant package.
- `ojf:thm:cost`, `ojf:thm:joint`, `ojf:cor:robustness`, and
  `ojf:cor:reconstruction` are finite-polynomial targets suitable for early
  formalization.
- `ojf:thm:parity` and `ojf:cor:algebraic-rigidity` import Gelfond–Schneider.
- `ojf:thm:neutral` needs normal convergence and holomorphic implicit functions.
- `ojf:thm:stieltjes` and `ojf:thm:regularization` provide two independent analytic
  coordinate systems for all jets at zero.
- `ojf:thm:borelzero` extends the first-jet meromorphic kernel to m=0 with a
  separately specified contour proof; do not remove the original m>=1 hypothesis
  from the old theorem without adding this proof.
- `ojf:thm:global`, `ojf:thm:small-inverse`, `ojf:thm:large-inverse`, and
  `ojf:cor:defect` form the concrete inverse package.

The automatically generated `theorem_map.csv` contains delivered theorem numbers
and PDF pages, so downstream references need not guess numbering.

## Before canonical promotion

Compare with the three actually existing incoming ZIPs at the pinned snapshot,
then obtain independent proof review. The package makes no remote modifications,
and no deletion or replacement of existing files is proposed. Any proof ledger
entry should distinguish conventional proof from numerical replay and from a
future Lean or interval-certified implementation.
