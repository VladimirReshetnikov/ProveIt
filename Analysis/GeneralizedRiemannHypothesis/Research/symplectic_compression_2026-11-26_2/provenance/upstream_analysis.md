# Analysis of lsernau/grh-lean

Inspected on 2026-11-27 UTC (2026-11-26 America/Los_Angeles).

## Snapshot and trust boundary

Repository HEAD: `72fead102f663d5c7a407964a13dc0cf9d977207`, commit authored 2026-11-25 20:38:07 UTC, message "Lean proof of GRH".
Mathlib pin reported by compact README: `56a005855ea17e0b0958f73ec801ae140b0a1679`; Lean v4.35.0.
The repository reports completed build, kernel replay, and Comparator checks with only `propext`, `Classical.choice`, `Quot.sound`.
I read source; I did not reproduce the full 1–2 hour build.

The public theorem scope is **Dirichlet** GRH, including imprimitive characters, not GRH for every automorphic L-function. `grh/src/Statements.lean` imports only Mathlib; the final statements do not depend on internal redefinitions. Their source hashes:
- Statements.lean: 1cd1bce93344065936b2b392b23306254e0785ef.
- Main.lean: 1adf4187a938510363cdb0dde0a6d628ff39c600.
- New/Reduction/MainInequality.lean: 97f83ab52b2feb420e952a2722b4cef454b9e579.
- New/Reduction/Lattices/TwistedLattice.lean: c6eacd876cd9b12bf9ded06150eedbdda966435b.

Exact public interface:
1. Mathlib RiemannHypothesis.
2. Every nontrivial zeta zero except s=1 has real part 1/2.
3. For N≥1, every Dirichlet character χ mod N, Re(s)>1/2 and (χ≠1 or s≠1), L(s,χ)≠0.
4. Every Dirichlet L zero in 0<Re(s)<1 has Re(s)=1/2.
5. Same restricted to primitive χ.

## Central reusable mechanism

For a complex vector space V, twists ξ, and linear maps Θ_ξ into hermitian spaces, let
Z(ξ)=det(Θ_ξ*Θ_ξ).
Integral vectors are simultaneously integral under all twists allowed at a given finite prime.
A prime may select a different twist ξ_ι; the denominator-clearing matrix at that prime must be independent of the selected twist.

The exact product-formula statement `TwistedLattice.covolume_add_index_nonneg`:
Let y_1,...,y_n,z_1,...,z_n' form a basis of V, and assume all Θ_ξ injective.
If y has logarithmic squared covolume ≤c and index ≤δ; γ(ξ)Θ_ξ z_i is integral at every allowed finite place; each z_i has untwisted squared norm at every conjugate ≤exp(b_short); and the families |γ(ξ_ι)|^{-2} and Z(1)/Z(ξ_ι) have heights ≤b_denom and ≤b_volume, respectively, then
    c + 2δ + n'(b_short+b_denom) + b_volume ≥ 0.
Proof: clear Gram determinant at each prime; factor the untwisted determinant as twisted integral determinant times denominator and determinant-ratio factors; use a common multiplier in the height definition and the product formula.

The many short forms are produced by differentiated theta lifts and a Poincaré map. A second moment gives n≥(1−4/b²)dim. The source comments summarize:
    mainAmount ≤ (V+2δ)/dim ≤ mainAmount−(n/dim)m·rem + errors.
The same dominant mainAmount cancels. Exact conclusion:
    m·totalRemainder ≤ f a (log b)^5.
Scales: m≈√x, r≈x^5, t=5r, a=xb; log b chosen as x^ε. This yields one-sided prime remainder bound.

## Analytic interface

Let λ_d,q(n)=Λ(n)(1−χ_d(n))1_{n≡1 mod q}, where d≡7 mod8 is prime and (d,q)=1. Define
    R_d,q(x)=Σ_{n≤x}λ_d,q(n)(1/n−1/x)−(log x)/φ(q)−c_d,q.
The arithmetic proof gives R_d,q(x)≤x^{−1/2+ε} eventually for every ε>0, with q multiple of 18480 and d≡q/2−1 modq.

The one-sided criterion (New/Reduction/Zeros/Criterion.lean) is more general:
q>0 multiple of8, d0≡7 mod8 coprime to q, β>1/2.
If R_d,q(x)≤x^{β−1} eventually for each prime d≡d0 modq, then all Dirichlet L-functions modq are nonzero at ρ≠1 with Reρ>β.

To prove it for a given ρ, choose one d such that all quadratic twists χχ_d are nonzero in Re(s)≥β, |Im(s)|≤|Imρ|. The Mellin transform of R_d,q(e^v) has residue
    [Σ_χ ord_s(entire Lχ)]/[φ(q)s(1−s)]
in this box. Residues at real x>β are nonnegative. Landau's positivity lemma plus the one-sided bound forces all right-hand residues to vanish. For each target modulus the final proof induces to 18480q; added Euler factors have no zero in Re(s)>0.

## Zero-density input independent of GRH

Lib/Analytic/QuadraticTwist.lean proves, for β=1/2+9δ, δ>0 and fixed height H:
    #{bad primes d≤X in the class} = O(X^{1−δ/2}).
"Bad" means some χ modq has a twist zero in Re(s)≥β, |Im(s)|≤H.
Mechanism: theta tail J(χ,T)=∫_{1/T}∞(|θχ(u)|+|θμχ(u)|)du/u; a zero forces J>T^{2δ} by three-lines; the sum of J over d≤T² is O(T^{2+δ}) via Pólya–Vinogradov; then T²≈qX.
The proof uses Dirichlet divergence Σ_{p in class}(log p)/p to find a good d, rather than PNT for AP.

## Small but exact possible extension

The one-sided criterion need only hold on a subfamily D of primes in the class with
    limsup_{X→∞} #D∩[1,X]/X^{1−(β−1/2)/18}=∞.
Then D cannot be entirely bad for any fixed H, so a good twist satisfying the certificate exists. Eventual thresholds may depend on d. This directly strengthens the interface but is too modest, and may be too standard, to label a significant novel theorem alone. A positive relative-density family is far more than enough.

Another proof-architecture direction is an all-exterior-power extension of the determinant comparison, yielding bounds on an entire dimension/height polygon instead of one scalar determinant. This requires genuine novel quantitative formulation and comparison with known adelic slope inequalities.

## Permanent source links

All files are under https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/

- grh/GUIDE.md
- grh-compact/README.md
- grh/src/Statements.lean
- grh/src/Main.lean
- grh/src/New/Reduction/MainInequality.lean
- grh/src/New/Reduction/Lattices/TwistedLattice.lean
- grh/src/New/Reduction/Lattices/Heights.lean
- grh/src/New/Reduction/OneSidedBound.lean
- grh/src/New/Reduction/Zeros/Criterion.lean
- grh/src/Lib/Analytic/QuadraticTwist.lean
- grh/src/Lib/Analytic/Landau.lean

Working copies of inspected source files are in research/grh_source/. These are evidence/research inputs, not a claim of re-verification, nor necessarily intended for redistribution.

