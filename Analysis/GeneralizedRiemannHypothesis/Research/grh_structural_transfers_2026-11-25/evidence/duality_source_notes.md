# Source-level polarization obstruction and exact repair target

## Status

- Human mathematical proof completed in `sections/duality.tex`.
- No claim that a named open conjecture is proved.
- No Lean compilation attempted; no Lean runtime installed in task environment.
- Compared terms against all extracted prior reports using `rg` over `*.tex` and `*.md`: no prior discussion found of the infinite `congruenceTerm` obstruction or its invariance under anticyclotomic twists. Prior material contains general representation-hypothesis caveats and scalar-inertia failures. This is a scoped corpus comparison, not a global novelty assertion.

## Upstream at commit 72fead102f663d5c7a407964a13dc0cf9d977207

All paths relative to `grh/src/New/Congruences/Selmer/`.

- `SelmerData.lean` lines 59–77: `conjDualHom` and `congruenceTerm` definitions.
- `SelmerData.lean` lines 105–151: `SelmerDatum` requires finite `congruenceTerm` (line 139); scalar inertia and `IsUnit (ζ^2 - 1)` are separate requirements.
- `SelmerData.lean` lines 165–179: `globalTerm`, local terms, β, finite β.
- `SelmerData.lean` lines 690–724: source scalar comparison gives one sufficient bound for congruenceTerm; it is not the definition.
- `Mirror.lean` lines 660–701: `length_dualSelmer_le`, explicit injective Φ from dual Selmer to `conjDualHom`, characterized by Φ(y)(z(h)) = y(h^c).
- `Descent.lean` lines 454–467: `length_tiedSelmer_le_of_isUnit` uses full dual length and hence full global term.
- `Line.lean` line 493: `IsTorsionLevel.β_lt` requires normalized β + 1 < M.
- `GeneralTheorem.lean` lines 367–398: exact twisting theorem, all powers 1…m, anticyclotomic ℓ-power character, finite β input.

## Main conclusions

1. For free DVR lattice T and its conjugate Tate dual D(T), any nonzero rational intertwiner forces globalTerm=∞ by reducing a primitive integral intertwiner modulo π^n and embedding O/π^n.
2. Anticyclotomic twist ψ preserves the exact intertwining equations: both sides gain the same unit ψ(g). This remains an obstruction after coefficient extensions, even if a preliminary twist repairs scalar-inertia conditions.
3. The Tate module of any polarized abelian variety descending to the totally real subfield carries a conjugate Tate-duality via the Weil pairing and complex conjugation. Thus the exact BSD Tate module is outside the source theorem; no residual irreducibility is needed for the exclusion.
4. Finite relation matrices give the exact formula `hn + Σ min(n,a_i)` and bounded quotient by the genuine invariant lattice. Root is independently adding a worked matrix example.
5. The proposed arithmetic repair requires controlling the kernel created by quotienting the source mirror injection by the genuine polarization maps. Correct inequality `len dual Selmer ≤ len Φ^{-1}(H_n) + Σ a_i`. Bounded quotient alone is insufficient.

## External primary references (parent must open before citing refs)

- Milne, *Abelian Varieties* (v2.00, 2008), section I.13, Weil pairings: https://jmilne.org/math/CourseNotes/AV.pdf . Web ref turn959612349view2. This provides background on the polarization pairing; all deductions here are proved explicitly.
- Mazur–Rubin, *Finding large Selmer rank via an arithmetic theory of local constants*, Annals 166 (2007), 579–612: https://annals.math.princeton.edu/2007/166-2/p08 ; arXiv https://arxiv.org/abs/math/0512085 . Web refs turn959612349view0, turn959612349view1. Under the paper's hypotheses, odd pro-p Selmer rank over a quadratic K/k forces rank at least [F:K] in finite anticyclotomic p-extensions unramified at bad primes. This is relevant context: a repaired theorem cannot blindly promise rank-zero twists in all polarized situations. Need quote the actual hypotheses if using it as a formal counterexample.
- Mazur–Rubin with Larsen appendix, *Diophantine stability*, arXiv:1503.04642, cited by source itself. Not newly applied here.
- Bellaïche–Chenevier, *The sign of Galois representations attached to automorphic forms for unitary groups*, Compositio 147 (2011), 1337–1352, https://arxiv.org/abs/0804.2860 and author PDF https://gaetan.chenevier.perso.math.cnrs.fr/articles/sign.pdf . Search refs turn647971440academia17, turn647971440search18. Their sign theorem says polarized irreducible constituents of regular algebraic polarized cuspidal GL_n representations over CM fields have sign +1. Match multiplier conventions before invoking it formally. This reinforces that the opposite-sign algebraic opening is not automatically a new automorphic central-value application.

## Warnings for statement precision

- Distinguish conjugate Tate self-duality `V ≅ V^∨(1)^c` from source's more general weight-shifted conjugate self-duality. The latter need not force congruenceTerm infinity.
- The original source's scalar-inertia requirement uses ζ²−1, not merely ζ−1.
- For a general polarization at primes dividing its degree, use rational self-duality plus primitive scaling, rather than asserting perfect integral self-duality.
- Anticyclotomic invariance holds for all unit-valued characters with ψ^c=ψ^{-1}, including but not limited to the source's finite-order characters.
- Finite relation set exists by Noetherianity but need not be effectively computable from an abstract infinite group representation. An explicit certificate must separately certify that the finite chosen rows generate all relations, or that the group is generated by the displayed matrices.

## Additional positive refinement (completed after initial notes)

See `sections/symmetry.tex`. `Mirror.lean` proves mirrorForm=0; substitute h'=k^c to see that its injection Φ has **symmetric bilinear image**. Thus the length target can be sharpened to symmetric conjugate-dual Hom. This identity uses no division by 2. The exact rational obstruction is therefore the symmetric part of the rational Hom space.

For a one-dimensional rational Hom space generated by an alternating primitive P, the finite-level symmetric part has length at most `Σ min(n,a_i) + min(n,vπ(2))`, hence uniformly bounded, even when the original full congruenceTerm is infinite. At odd ℓ the 2 term vanishes. This suggests a real source refactor to weaken finite-globalTerm to finite-symmetric-globalTerm. Full refactor is **not yet compiled/proved as a complete new arithmetic theorem**; all displayed mirror/Smith algebraic lemmas have complete proofs.

For abelian varieties descending to a totally real field, the conjugate Weil pairing B(v,w)=e(v,Cw) is **symmetric**, since e is alternating and C anti-symplectic. Therefore this positive refinement does not remove the BSD obstruction. The one-dimensional explicit linear mirror model in the fragment shows quotienting by the pairing line destroys injectivity even with mirrorForm=0 and spanning; it is labeled an abstract model, not a Galois datum.

Usage audit command: `rg -n 'congruenceTerm|globalTerm|β_ne_top|congruenceTerm_ne_top' grh/src/New/Congruences/Selmer --glob '*.lean'`. Apart from constructors/bounds in SelmerData and MainSummands, only Mirror, Descent, Line, GeneralTheorem use the global term. MainSummands can still use the old full bound because the symmetric term is a submodule bound. No other use of finite-globalTerm was found in this module subtree.

## Final integrated refinement

The report also proves the exact sign dichotomy under the source integral matrix-span hypothesis: a rational conjugate-dual map becomes a perfect integral pairing, the full finite-level Hom module is its scalar line, and the symmetric lengths are n for positive sign and min(n,v_pi(2)) for negative sign. The report clarifies that coefficient twists of ell-power order cannot repair a residual scalar-inertia failure. A suitable prime-to-ell residual character is a different preliminary construction.
