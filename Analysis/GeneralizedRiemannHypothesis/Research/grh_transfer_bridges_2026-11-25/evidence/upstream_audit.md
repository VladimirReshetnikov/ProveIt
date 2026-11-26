# Independent upstream interface audit

Audit target: `lsernau/grh-lean`, default branch `main`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, authored 2026-11-25 20:38:07 UTC.
GitHub repository metadata and current `commits/main` were read through the GitHub plugin.
The commit remains the one audited by the preceding ProveIt reports.

## 1. Exact endpoint and verification boundary

`grh/src/Statements.lean` imports only Mathlib. Its predicates quantify over
`DirichletCharacter ℂ N`, with `N : ℕ` and `[NeZero N]`.
`grh/src/Main.lean` exports exactly:

- `riemannHypothesis : RiemannHypothesis`;
- `riemannZeta_eq_zero_re : RiemannZetaZerosOnLine`;
- `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`;
- `LFunction_eq_zero_re : DirichletLZerosOnLine`;
- `LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine`.

Thus the endpoint covers all Dirichlet characters over Q, primitive or not. It does
not quantify over arbitrary number fields, Hecke characters, Artin representations,
or automorphic representations. The endpoint's vocabulary is unambiguous.

The upstream README reports successful compilation, `#print axioms` containing
only `propext`, `Classical.choice`, `Quot.sound`, replay by Lean's kernel, independent
nanoda/con-leche/con-ron checking, and Comparator acceptance. It also explicitly
says the proof has passed machine checks only and no mathematician has read it all.
These are upstream-reported checks, not checks rerun by this audit. Neither `lean`
nor `lake` was on this environment's PATH. A current Git commit's verified signature
is a provenance fact and is not a proof certificate.

Sources:

- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Statements.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Main.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/README.md

## 2. Transferable mechanism: comparison of the same corrected covolume

The reusable mechanism is much more specific than a generic assertion that
arithmetic divisibility competes with size. In `MainInequality.lean`, the exact
comparison is between the same target space, the same lifted Gram determinant,
and an index term entering with coefficient two. A family of n independent target
forms spans at least `(1-4/b²)D` dimensions of a D-dimensional space. Theorem A gives
short forms and small index, Theorem B provides this near-full span, and Theorem C
gives a lower bound for the corrected logarithmic covolume. The common principal
term cancels. The actual theorem is

`star_inequality : D.m * D.totalRemainder ≤ D.f * D.a * D.logB ^ 5`.

Theorem C is

`integral_forms_long`:
`D * (mainAmount - 3 f a log^4 b) ≤ c + 2 δ`,

assuming linear independence, rank at least `(1-4/b²)D`, `IndexLe y δ`, and
`CovolumeLe y c`. It is a theorem about `D : Data P`; `Data P` contains the special
cyclotomic-CM field, places, weights, theta chains and levels. Replacing its prime
sum by a nonabelian Frobenius statistic without replacing those constructions is
not an instantiation of the theorem.

The genuinely abstract interface is
`New.TwistedLattice.covolume_add_index_nonneg`. Its conclusion is

`0 ≤ c + 2 δ + n' (b_short + b_denom) + b_volume`.

Its assumptions include an injective lift for every twist, a completed basis of
`V`, an allowed twist chosen separately at each p-adic embedding, integral images
of the completion after multiplication by a nonzero scalar γ, bounds at every
complex conjugate, and heights for both `|γ|^{-2}` and the ratio of untwisted to
twisted volumes. This abstract interface can be reused outside the RH proof, but
the arithmetic construction supplying these assumptions carries almost all the
difficulty.

The `GUIDE.md` explicitly warns that some background interfaces are deliberately
weaker than standard theories: attached representations match Hecke polynomials
only on a dense “most Frobenii” filter up to each tolerance; local polynomials may
only annihilate rather than be characteristic polynomials; no Weil-Deligne
representation is built. A transfer must inspect exact theorem types rather than
equate the interface's name with the entire standard theorem.

Sources:

- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/MainInequality.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/ShortAndEnough.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Determinant/Twist/LongForms.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Lattices/TwistedLattice.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/GUIDE.md

## 3. The analytic end is not a black box for arbitrary L-functions

`New.LFunction_ne_zero_of_primeRemainder_le` assumes a one-sided smoothed prime
remainder bound for **every prime d in a specified congruence class**, not merely
for one auxiliary field. For β>1/2 the bound is eventually `R_{d,q}(x)≤x^(β-1)`.
The proof chooses d such that the auxiliary quadratic twists have no zeros in a
rectangle containing the hypothetical zero. This makes the polar residues
nonnegative and prevents cancellation. Only then does the Landau argument exclude
the target zero.

Consequently a nonabelian analogue must supply (i) an exact logarithmic-derivative
identity, (ii) the correct residue signs or an equivalent noncancellation argument,
(iii) sufficient auxiliary twist selection if that route is used, and (iv) the
new arithmetic prime-sum bound. A finite computation of prime sums proves none of
the eventual estimates in (iv).

Source:
https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Zeros/Criterion.lean

## 4. General Selmer twisting theorem: exact eligibility conditions

`New.Selmer.exists_anticyclotomic_twist` is a promising independent export. For
finitely many `SelmerDatum` objects and Stickelberger systems, a positive ε and
an integer m≥1, it produces a finite auxiliary set Q and an anticyclotomic
ℓ-power-order character ψ such that every ψ^j, 1≤j≤m, simultaneously has:

1. normalized divisible-Selmer length at most β_T+ε;
2. valuation at each Stickelberger element at most β_Y+ε;
3. total valuation `Σ_{w∈Q∪conj(Q)} v_ℓ(ψ^j(γ_w)-1)≤ε`.

The character is trivial on decomposition groups over ℓ, is ramified at every
prime of Q, and Q avoids the original bad set and its conjugate. There is also a
torsion-level hypothesis (`IsTorsionLevel T M`), and the initial element g0 must be
inertia away from ℓ inside the supplied bad set.

Each `SelmerDatum` includes these substantive hypotheses:

- a continuous integral representation of positive rank, unramified outside a
  finite set S containing the primes over ℓ;
- finitely generated local cocycle modules Z_w containing coboundaries, with
  `Σ rank Z_w≤(#places above ℓ + #infinite places) rank(T)`;
- `span_O {ρ(g)}=M_n(O)`, a strong integral form of residual absolute irreducibility;
- finite `congruenceTerm`, the supremum over all a≠0 of lengths of
  `Hom_G((O/a)^n,((O/a)^n)^{*c})`, where the star includes the cyclotomic twist;
- finite local terms, including valuations of `det(ρ(g0)-I)` and
  `det(ρ(g0^{-c})-I)`;
- an inertial γ away from ℓ with **both** `ρ(γ)=ζI` and `ρ(γ^{-c})=ζI`, and
  `ζ²-1` a unit.

The concrete automorphic `IsMainSummandLike` interface is stronger still. Its
scalar inertia y must satisfy `||y^(ℓ^a j)-1||=1` for every a≥0 and every
`1≤j≤4 rank(T)+2`. It also requires trace conjugate self-duality, prescribed
Hodge-Tate jumps, specific local type conditions and scalar elements with
prescribed cyclotomic value.

Pure Tate twists are unramified at the allowed inertial γ, so ζ=1 and the unit
condition fails. The usual symplectic similitude structure of an elliptic Tate
module gives ζ²=1 at an inertial scalar away from ℓ, again incompatible with the
unit condition. This blocks direct substitution into BSD, not all future variants
of the method. Independently, a normalized length `length/e≤ε` over varying
coefficient rings cannot imply the module vanishes: `O/(uniformizer)` has length
one and normalized length 1/e.

Sources:

- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Congruences/Selmer/GeneralTheorem.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Congruences/Selmer/SelmerData.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Congruences/GaloisRepresentations/SelmerHypotheses.lean

## 5. Odd cocycles and K-theory: useful finite bounds, missing comparison

`New.exists_length_shaOdd_le` assumes a CM field E contained in Q(μ_N). For every
cutoff t it produces one nonzero integer

`X≤2^(4(N+t+3)^27) h_E`

whose valuation bounds `length_O shaOdd(ℓ,E,O,e,n)` for all primes ℓ, all n, all
e<t and suitable coefficient rings. Thus primes not dividing X have zero custom
odd-cocycle module. The source itself says its model has not been compared with
the usual Sha^1 group, and it does not prove an equality of characteristic ideals.
The theorem's form does not make X a computable named integer without extracting
the Stickelberger witnesses. A K-theory vanishing claim needs the precise
cohomological comparison, parity, local-condition comparison, and control of all
exceptional prime factors. Existing arithmetic certificates cannot replace those
interfaces.

Sources:

- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Lib/Cyclotomic/OddSha.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Lib/GaloisRep/Main/SelmerModules.lean

## 6. Conclusion for transfer prioritization

No overlooked direct theorem application resolving a new named conjecture was
found in these interfaces. The strongest reusable exports are the abstract
twisted-covolume theorem, the general anticyclotomic twisting theorem, torsion
specialization, and the explicit uniform odd-cocycle bound. The most honest next
step is a single small target with a proved comparison to these exact objects,
rather than expanding the list of conditional analytic criteria. This is an
interface audit, not a claim that such a transfer is impossible or that all
independent intermediate declarations have been exhausted.

