# Formalization roadmap

This file is a plan for a future Lean formalization. It is not executable
Lean code and contains no claim that the new results have been kernel-checked.

## Design

Keep the finite algebra independent of analytic number theory. Use a finite
abelian group X, a finite dual group V, and an integral signed packet c with
zero total sum. Work with exact histograms first; obtain the polynomial
interpretation by unique factorization only after the finite results.

Packets may be represented by finitely supported natural-valued functions.
The signed difference lives in finitely supported integer-valued functions.
The group is finite, so ordinary finite functions are also possible. Choose
one representation early to avoid unnecessary coercions.

## Declaration groups

| Group | Required content | Depends on |
|---|---|---|
| Histograms | Pushforward, composition, cancelled mass, agreement preserved by powers | Finite sums, integer positive/negative parts |
| Cyclic marginals | Coordinate marginal, contraction of L1 norm, minimum nonzero marginal | Products of finite sets |
| Trade induction | Nonzero integral array with vanished low marginals has mass at least 2^r | Slice decomposition and induction |
| Cyclic classification | Faithful-coordinate cylinder, density formula, parity construction, padding | CRT, finite cyclic groups, marginal lemma |
| Dual kernels | Orthogonality and positive Fourier expansion of corrected K_y | Finite character theory |
| Mass theorem | Expectation identity, pointwise oscillation bound, sharp coefficient bound | Dual kernels and finite inequalities |
| Mass equality | Zero-deficit argument, collapsed values, Fourier subgroup invariance | Mass theorem, finite Fourier inversion |
| Torsion lift | X[p] annihilator is pV; separate a point from a subgroup | Finite abelian duality |
| Saturation | Unit orbits, p-root lifting, smallest invariant factor, attainment | Structure theorem for finite abelian groups |
| Saturated equality | Quotient fibre balances and Galois invariance of primitive Fourier support | Cyclotomic conjugacy, finite Fourier inversion |
| Prime interpretation | Evaluation onto V and density by reduced residue classes | PNT in arithmetic progressions |
| GRH transfer | Smooth character estimate, Fourier norm sum, window certificate | Separate Dirichlet-GRH input |

## Core finite statements

1. For every nonzero balanced integral array of total positive mass m, there
   is a nonzero coordinate marginal involving at most floor(log_2(2m))
   primary components. A formally easier version avoids logarithms and proves
   directly that a minimal nonzero r-coordinate marginal implies 2^r <= 2m.
2. For p-primary X and every y, the average of
   K_y(v) = [v(y)=1] - (1/p)[v(py)=1]
   is (1-1/p)[y=0]. Avoid division in intermediate cardinality statements.
3. With anchor a, |J_a(v)| <= m[disagreement(v)]. Multiplying by group order
   turns the main density inequality into an exact finite-sum inequality.
4. Equality forces every nonzero coefficient to be +/-1. For each evaluation
   in the disagreement set, all summands must attain their extreme allowed
   values. Prove this by summing nonnegative deficits; no limiting argument
   is involved.
5. Fourier support inside the annihilator of P is equivalent to translation
   invariance under P. This is the main bridge to full subgroup cosets.
6. Disagreement at pv implies disagreement at v. Combine this with unit-orbit
   invariance to obtain the saturation cardinality without any analysis.

## Analytic boundary

The finite results must compile without assuming RH, GRH, or a prime
distribution theorem. The prime-density corollaries add PNT in progressions.
The finite-window theorem should take the smoothed character estimate as an
explicit separate dependency, with constants and all conductor assumptions
visible. A later integration can connect that estimate to the repository's
Dirichlet-GRH development.

## Verification milestones

First formalize histograms and the cyclic finite theorem. Next establish the
corrected projection and mass bound, then equality and saturation. The exact
enumeration programs in `code/` give regression examples for finite instances,
but do not substitute for the general proofs. Do not introduce the main
theorem as an axiom, use an opaque placeholder, or label a file containing
unproved obligations as a completed formalization.
