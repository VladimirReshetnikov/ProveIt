# Source audit: transferable interfaces in grh-lean

Pinned source: `lsernau/grh-lean` commit `72fead102f663d5c7a407964a13dc0cf9d977207`. Inspection date: November 25, 2026 (client date). Source inspected directly through the GitHub connector and the local checkout. No independent Lean build was attempted.

## 1. Exported scope and validation status

`grh/src/Statements.lean` imports only Mathlib. `grh/src/Main.lean` proves five statements:

1. `riemannHypothesis : RiemannHypothesis`.
2. `riemannZeta_eq_zero_re : RiemannZetaZerosOnLine`: zeros other than negative even integers and the pole have real part one half.
3. `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`: for every positive modulus, every complex Dirichlet character, and every `s` with real part greater than one half, nonvanishing away from the principal-character pole.
4. `LFunction_eq_zero_re : DirichletLZerosOnLine`: all zeros in the open critical strip have real part one half, for all characters including imprimitive ones.
5. `LFunction_eq_zero_re_of_isPrimitive`: specialization of (4).

The exports do not state GRH for general Hecke, Artin, or automorphic L-functions. This is a scope distinction, independent of accepting the supplied proof. `grh/README.md` reports compilation without `sorry` in imported sources, dependencies only on `propext`, `Classical.choice`, `Quot.sound`, and acceptance by three independent checkers. These are the repository's reports; this session does not independently reproduce them.

## 2. Exact reusable source map

All paths below have prefix `grh/src/`.

| Interface | File and declaration | Essential content |
|---|---|---|
| Prime-sum conclusion | `New/Reduction/OneSidedBound.lean`, `eventually_primeRemainder_natCast_le`, `grh` | Fixed modulus and admissible quadratic field; one-sided remainder bound of order `x^(-1/2+6 epsilon)`; then zero exclusion. |
| Arithmetic comparison | `New/Reduction/MainInequality.lean`, `star_inequality` | `m totalRemainder <= f a logB^5`, obtained by comparing one covolume and cancelling the main amount. |
| Short vectors | `New/Reduction/ShortAndEnough.lean`, `span_short_integralRamified_eq_top` | Source integral vectors span, with uniform bounds at every complex conjugate. |
| Integral index | same, `indexLe_normalizedPoincare` | One integral matrix at each p-adic embedding works for every twist allowed there. This compatibility is stronger than separate local integrality. |
| Near spanning | same, `enough_forms` | Independent target images occupy at least `(1-4/b^2)` of the target dimension; the number of source translates has logarithmic cost. |
| Determinant principle | `New/Reduction/Lattices/TwistedLattice.lean`, `covolume_add_index_nonneg` | `0 <= c+2 delta+n' (b_short+b_denom)+b_volume`. Uses common reference Gram determinant, paired conjugate integrality, and a twist selected for every p-adic embedding. |
| Long vectors | `New/Determinant/Twist/LongForms.lean`, `integral_forms_long` | For a near-full independent family, `d(mainAmount-3 f a logB^4) <= c+2 delta`. |
| Completion cost | same, `mul_completion_cost_le` | Each missing basis vector costs `2 x1^2 b^2+b`; near-spanning controls the total. |
| Product of lift determinants | same, `heightLe_chainDeterminant_one_div` | Negative main term in the height bound for `Z(1)/Z(theta_iota)`, with explicit additive error. |
| Degree-independent torsion specialization | `New/Congruences/Selmer/RootsOfUnity.lean`, `exists_rootsOfUnity_ellVal_eval_le_add` | Root order bound selected before polynomials, degrees, family cardinality, and separate witnessing points, with total valuation budget fixed. |
| Finite simultaneous twists | `New/Congruences/Selmer/GeneralTheorem.lean`, `exists_anticyclotomic_twist` | One finite-order character works for a finite collection of Selmer data and systems and every power `1,...,m`. |
| Actual Selmer object bounded | `New/Congruences/Selmer/Line.lean`, `TwistedLengthLe` | Bounded normalized length of a divisible-coefficient Selmer module over all sufficiently large coefficient rings. |
| Selmer eligibility | `New/Congruences/Selmer/SelmerData.lean`, `SelmerDatum` | Residual absolute irreducibility in spanning form; local rank bound; finite conjugate-dual Hom term and local terms; scalar inertia with `zeta^2-1` a unit. |
| Generic descent tool | `New/Congruences/Selmer/Descent.lean`, `tilting` | Outside at most the target rank many residue classes, a linear combination of two maps has a short kernel. |

## 3. Incremental insight A: rank coverage is an actual arithmetic resource

A terse description of the proof can misleadingly suggest that a fixed positive fraction of target vectors suffices. It suffices for the *last division* in `star_inequality`, but does not suffice for Theorem C as currently proved. Theorem C needs `n >= (1-4/b^2)d` because it completes the selected family by costly auxiliary vectors.

Let `d=n+r`, with `n>0`, and let the generic determinant principle give

`0 <= c+2I+rK-dA+V`.

Suppose the short family gives `c <= n(A-mR+U)`, where `m>0`. Direct rearrangement yields the exact tradeoff

`n m R <= nU+2I+V+r(K-A)`.

Consequently, if `A>=0`,

`R <= [U+(2I+V)/n+(r/n)K]/m`.

This is a proved algebraic consequence of the determinant interface, not a new arithmetic estimate and not a conjecture resolution. It separates two possible strategies for a new L-function: improve spanning so that `r/n` is tiny, or construct much cheaper auxiliary vectors so that `K` is small. Merely replacing the existing near-spanning theorem by positive-proportion spanning will usually lose the square-root exponent.

In the actual source, `K=2 x1^2 b^2+b` and `r<=4d/b^2`, giving total cost at most `4d(2x1^2+b^(-1))<=db`. The cost is absorbed using the very large scale separation `x1^(10^6)<=b`.

## 4. Incremental insight B: only selected twists need injective lifts

`TwistedLattice.covolume_add_index_nonneg` assumes `Function.Injective (L.lift xi)` for every twist `xi`. Inspecting its proof shows that this hypothesis is invoked only for `xi=1` (nonzero reference Gram determinant) and for `xi=theta iota` (nonzero denominator in the volume ratio).

Therefore the theorem remains valid with exactly these two assumptions:

* `Function.Injective (L.lift 1)`;
* for each p-adic embedding `iota`, `Function.Injective (L.lift (theta iota))`.

Proof: use the first at `h_ne`; use the second at `hZ_ne` inside `h_factor`; all other lines are unchanged. No local-to-global existence theorem is needed for this weakening.

This could help in an automorphic transfer where bad twists have zero lifts but the torsion-selection procedure can choose good twists. It does **not** remove the common reference determinant, common basis, height controls, integrality at both `iota` and its complex-conjugate embedding, or the compatibility of index matrices with the selected twists. It is a valid simplification of the proof interface, not a proof of the required nonabelian arithmetic construction.

## 5. Incremental insight C: finite length already rules out positive corank

The actual `TwistedLengthLe` definition bounds the length of the module with coefficients `Frac(O')/O'`. The bound is not confined to a single quotient `O'/ell^M`. If it is finite, the resulting module has no nonzero divisible submodule. Indeed, multiplication by a uniformizer on a divisible finite-length module is surjective; equality of lengths makes it injective; but a power of the uniformizer annihilates every finite-length module, forcing zero.

Thus the general twisting theorem already gives a simultaneous *finite-length/corank-zero* conclusion for its eligible twisted Selmer objects. It need not make their torsion subgroups zero. Growth of coefficient ramification explains why an arbitrarily small **normalized** positive length cannot be rounded down to zero: `O'/varpi` has normalized length `1/e(O'/Q_ell)`.

A transfer to named Bloch--Kato, Mordell--Weil, or Tate--Shafarevich groups still requires an identification of the source local conditions, lattice, and class normalization with the conventional objects. In particular `SelmerDatum` already requires a finite conjugate-dual Hom term. A conjugate-self-dual representation generally violates that requirement, so one cannot take the finiteness conclusion as a general BSD argument.

## 6. Torsion quantifiers to retain exactly

The theorem `exists_rootsOfUnity_ellVal_eval_le_add` has the order

`for s0,rho>0,beta,epsilon>0, exists h0, for every finite variable set and finite polynomial family and points ... exists a root tuple ...`.

The constraints are at most `s0` variables, coordinates of each witness point of valuation at least `rho`, and total witnessing valuation at most `beta`. The tuple has each order dividing `ell^h0`; orders need not be equal or maximal. The conclusion controls each polynomial by its own witnessing value plus `epsilon`.

The general twisting theorem preserves finite-family and bounded-power uniformity but allows the auxiliary ramification set `Q` to change with the data and error. A single fixed character is not shown to handle an infinite family or unbounded powers. Torsion order is not a conductor norm bound.

## 7. Recommended interpretation

The best next mathematical task remains the construction of an arithmetic lattice for one concrete nonabelian L-function. The rank-budget inequality and selected-twist injectivity weakening make that task more precise. They locate independent obligations: near-spanning versus completion cost, determinant lower bound, prime-sensitive divisibility, and compatible local choices. They do not solve those obligations. The finite-length content of the Selmer theorem is a genuine reusable conclusion, but attaching it to a major named conjecture requires hypotheses not provided by the generic source theorem.

## Primary source links

* https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Statements.lean
* https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Main.lean
* https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/README.md
* https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Lattices/TwistedLattice.lean
* https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/MainInequality.lean
* https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Determinant/Twist/LongForms.lean
* https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Congruences/Selmer/RootsOfUnity.lean
* https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Congruences/Selmer/GeneralTheorem.lean
* https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Congruences/Selmer/SelmerData.lean
* https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Congruences/Selmer/Line.lean
