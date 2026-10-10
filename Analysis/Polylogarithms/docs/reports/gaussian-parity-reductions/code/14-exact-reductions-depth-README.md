# Depth reduction contributions

These files use the descending-index convention

`Li_{a,b}(z,1) = sum_{n>m>0} z^n/(n^a m^b)`.

They were checked against the consolidated ProveIt manuscript at commit
`afed07429d3d37eceb6c8e9e54cf4da2d3f39d53`, specifically
`Analysis/Polylogarithms/docs/manuscript/chapters/04-depth.tex`.

## Files

- `../../article/sections/03_depth.tex`: complete proofs, ready for inclusion in the parent article.
- `verify_depth.py`: exact symbolic coefficient checks and independent
  Mellin/iterated-integral quadrature diagnostics.
- `depth_results.json`: recorded diagnostics at 65 decimal working digits.
- `gaussian_parity_through_weight12.json`: exact expressions for all Gaussian
  doubles in the parity-reducible component through weight 12.
- `gaussian_parity_through_weight12.tex`: the same expressions as align rows.
- `verify_mixed.py`: independent audit of the inherited inverse-argument
  mixed-value reductions.
- `mixed_results.json`: its recorded diagnostics.

In the generated tables, `g_{a,b}` is the imaginary part (even total weight),
`h_{a,b}` the real part (odd total weight), `L = log(2)`, `G = beta(2)`,
and `Bn = beta(n)` for even `n`.

Reproduce the diagnostics with Python 3, `mpmath`, and `sympy`:

```sh
python verify_depth.py
python verify_mixed.py
```

Numerical quadrature is used only as an independent implementation check.
The identities are proved by the analytic arguments in `../../article/sections/03_depth.tex`;
the numerical residuals are not certified interval error bounds.

## Status and scope

Five formerly numerical Gaussian weight-six double identities and three
formerly numerical Gaussian weight-four triple identities in the current
manuscript are proved here. Exact SymPy subtraction checks every displayed
coefficient against the current source. The binomial parity formula also
generates additional identities at all weights, with examples through 12
included as executable data.

The general parity phenomenon, including explicit formulas at depths two
and three, is established literature. The binomial formula here is a
convenient independently derived specialization, not a claim to have
discovered the general parity theorem. Similarly, the all-depth one-two
reduction follows from classical iterated integrals and elementary
antiderivatives; its use here supplies rigorous proofs of the manuscript's
three particular triple formulas.

The four inverse-argument mixed reductions were already proved in the
project's 2026-10-08 continuation. They are rederived and checked here to
reconcile that result with the current consolidated manuscript; they must
not be counted as newly resolved conjectures in this continuation.

Nothing here proves numerical independence of the remaining constants.
The weight-six triple candidates `(3,1,2)`, `(3,2,1)`, `(4,1,1)` are not
individually reduced by the one-two mechanism.

## Primary-source context

- Erik Panzer, *The parity theorem for multiple polylogarithms*, Journal of
  Number Theory 172 (2017), 93–113. DOI: 10.1016/j.jnt.2016.08.004.
  https://arxiv.org/abs/1512.04482
  The primary PDF explicitly gives arbitrary-weight formulas at depth two
  (3.2) and depth three (4.3). Its ascending-index convention reverses the
  present index/argument tuples. The introductory Gaussian example already
  prints `Re Li_{2,1}(i,1)=29*zeta(3)/64-pi*G/4` in that reversed notation.
- Ryota Umezawa, *An explicit parity theorem for multiple polylogarithms*,
  arXiv:2508.02040 (2025).
  https://arxiv.org/abs/2508.02040
  https://arxiv.org/html/2508.02040v1
  This gives general-depth explicit parity formulas, including the required
  regularized specializations at roots of unity.
- Takashi Nakamura, *A simple proof of the functional relation for the Lerch
  type Tornheim double zeta function*, Tokyo Journal of Mathematics 35
  (2012), 333–337. https://arxiv.org/abs/1012.1144
  Panzer cites Proposition 1.2 as the prior unit-circle version of his
  depth-two formula. This bibliographic attribution was verified in
  Panzer's primary PDF; no originality claim is made for that special case.

## Proof audit

- All branch choices used at `i` are stated explicitly, including
  `log(1-i)=log(2)/2-i*pi/4` and `log(-(1-i))=log(2)/2+3*i*pi/4`.
- The double proof covers indices equal to one without ever assigning a
  value to `zeta(1)`: the two partial-fraction divergences cancel before
  taking the summation limit.
- The boundary product identity is justified in `L^2`/`L^1`, followed by
  Dirichlet convergence and Abel–Poisson summation away from `z=1`.
- The inverse binomial matrix is proved exactly by the binomial theorem.
- All triple shuffle multiplicities are derived from the corresponding
  words; the two required multiplicities are `1,3` and `3,2,1`.
- No integer-relation search or numerical rank occurs in these proofs.

