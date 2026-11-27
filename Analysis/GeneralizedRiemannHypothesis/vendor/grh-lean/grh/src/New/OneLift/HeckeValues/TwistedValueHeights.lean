import New.Congruences.GaloisRepresentations.SelmerHypotheses
import New.Derivatives.Sharpness.BoundAttained
import New.OneLift.ComparisonOperator.ThreeExchanges
import New.OneLift.FalseLifts.PeriodsOfFalseLifts
import New.OneLift.HeckeValues.AlgebraicPartSize
import New.OneLift.HeckeValues.CentralAction

/-!
# Heights of ratios of twisted to untwisted Hecke values via rank-one theta lifts

This file builds a test form (`New.DescentPair.IsTestForm`: integral above `ℓ` and orthogonal to the
false lifts) from class sums on four blocks of indices. Its pairing with the lift of a main pair has
small valuation at `ℓ`. With the bound for the denominators of the projections to the line of the
lift, this bounds the valuation of the squared norm of the twisted lift from above. Here
`New.HeightLe c y` says that the family `y ι`, one number for each `ι : ℂ ≃ ℚ̄_ℓ`, has height at
most `c`; the file bounds the heights of inverse ratios of twisted to untwisted Hecke values, with
twists along a family `θ` with `New.Data.IsRegularFamily`.

## Main definitions and results

* `New.Data.exists_isTestForm_le_norm_inner_trivialLift`: at every prime `l` coprime to `ϑ.normQ` of
  a twist `ϑ`, some test form has a pairing of small valuation with the lift
  `New.Data.CriticalPair.trivialLift` of a main pair.
* `New.Data.heightLe_inv_ratio`: the inverse ratios of a main pair have height at most
  `6 denominatorBudget - directionAmount`.
* `New.Data.exists_heckeValueProd_eq_mul_prod_ratio`: the quotient of the Hecke values
  `New.Data.heckeValueProd j` at a twist and at `1` as a product of ratios of L-values.
* `New.Data.heightLe_inv_heckeValueProd_div`: a bound for the height of the inverse of this
  quotient.

Notions from other files:
* `New.Data.CriticalPair`: An integer 1 ≤ z ≤ t and a character ν of U(1)(𝔸) of weight −c,
  z ≤ c(v) ≤ 4b, with tame part supported on the chosen places.
* `New.Data.CriticalPair.integralAlgebraicPart`: The product of
  `n_L = chosenGroupOrder * denomBound ^ 2` and the algebraic part `‖φ‖² / N(Q) ^ (2 z - 1)`
  (`New.Data.CriticalPair.algPart`); the first factor of `n_L` clears the orders of automorphism
  groups, the second the denominators of `φ`.
* `New.Data.CriticalPair.ratio`: The ratio |L(z, (νϑ^s)⁻¹)| / |L(z, ν⁻¹)| for a sign s (by default
  1), without the Euler factors at the level.

The data `D` over the parameters `P` supply the CM field `D.E`, with `f` infinite places and
`D.towerExp` its index in the tower over `K = ℚ(i√d)`, the natural numbers `m`, `k`, `r`, `t`, `M`
and `a`, and the reals `b`, `x`, `x₁` of the bounds. Here `M ^ f` is the norm of the product of the
chosen places, `x` the length of the prime sum, `denominatorBudget = f a log³ b / (m k)` and
`directionAmount` the sum over the infinite places `σ` of `jetSize (κ σ) - primeSum (κ σ) σ`, where
`κ = D.weight`, `jetSize` is the size of a derivative and `primeSum` measures its guaranteed
divisibility.

`P.vacuumScale D.towerExp` scales the vacuum of rank one to integral values, `P.jetScale D.towerExp`
scales Taylor series of theta functions, `modKernel` is the theta kernel given by a function on
matrices modulo an ideal and a polynomial, and `p.rowLengthSum` is `∑ τ, (p.negWeight τ - p.z)`.

## Relation to the literature

Norms of lifts of Hecke characters as L-values, their divisibility via congruences, and divisibility
at inert primes are known from the literature. Related work: Prasanna, Integrality of a ratio of
Petersson norms, 2006; Coates–Liang–Sujatha, Tate–Shafarevich group for elliptic curves with CM II,
2010 (after Katz, 1977); Y.-S. Lee, Hida family of theta lift from U(1) to definite U(2), 2024.
-/

noncomputable section

namespace New.Data

open Matrix Fintype Real Finset IsUltrametricDist Rows LValueData Submodule CriticalPair Exchange
  AutChar

variable {P : Parameters} {D : Data P}

/-- Let `u` be a norm-one adele, rational or with integral finite part congruent to `1` at the
places of `S`, or a product of such. Let `Γ` contain the rational points of `U(1)`, and let `K`
contain the principal level at places `w i ∈ S`. Then the finite part of `u`, as a `1 × 1` matrix,
lies in `Γ ⊔ K`. -/
lemma _root_.New.rationalU1_sup_integralU1_le_comap {E κ : Type} [Field E] [CMType E]
    {w : κ → FinPlace E} {S : Finset (FinPlace E)} (hS : ∀ i : κ, w i ∈ S)
    {Γ K : Subgroup (Gf E Unit)} (hΓ : stdRatPoints ≤ Γ) (hK : levelOf w ⊥ ≤ K)
    {fin : unitary (𝔸 E) →* Gf E Unit}
    (h_entry : ∀ (u : unitary (𝔸 E)) (i j : Unit), (fin u).val i j = (u : 𝔸 E).2) :
    rationalU1 ⊔ integralU1 S ≤ (Γ ⊔ K).comap fin := by
  refine sup_le ?_ ?_
  · rintro u ⟨γ, hγ⟩
    refine Γ.mem_sup_left (hΓ (mem_stdRatPoints_iff.2 fun i j ↦ ⟨γ, ?_⟩))
    exact (congrArg Prod.snd hγ).trans (h_entry u i j).symm
  · rintro u ⟨h_int, h_one⟩
    have h_mem : fin u ∈ stdLevel E Unit := mem_stdLevel.2 fun i j ↦ by rwa [h_entry]
    refine Γ.mem_sup_right (hK (mem_levelOf.2 ⟨h_mem, ?_⟩))
    have h_red (i : κ) : reduceAt (w i) ⟨(fin u).val () (), mem_stdLevel.1 h_mem () ()⟩ = 1 := by
      simpa only [h_entry] using h_one (w i) (hS i)
    ext i
    simpa using! h_red i

open QuotientGroup DoubleCoset IsMulCommutative in
/-- Orthogonality of characters on the classes of `U(1)(𝔸_f) = Gf E Unit`. Let `Γ` contain the
rational points, let `K` contain the principal level at the places `w i ∈ S`, let `K` be compact
open and `Γ \ U(1)(𝔸_f) / K` finite (`HasFiniteType`), and let all stabilisers be trivial, so that
`classSum Γ K` is the sum over chosen representatives of the classes. Let `l` be a prime and
`ι : ℂ → ℂ_l` an embedding. Then for every function `s` there are a translation `z` and a character
`χ` of weight zero, with tame part trivial off `S`, such that the class sum of
`g ↦ χ(det(g z)) · s(g z)`, divided by the class sum of `1`, has norm under `ι` at least that of
`s 1`. -/
theorem _root_.New.exists_norm_le_norm_twisted_classSum {l : ℕ} [Fact l.Prime] {E κ : Type}
    [Field E] [CMType E] (w : κ → FinPlace E)
    (S : Finset (FinPlace E)) (hS : ∀ i : κ, w i ∈ S) (ι : ℂ →+* ℂ_[l]) (s : Gf E Unit → ℂ)
    {Γ K : Subgroup (Gf E Unit)} (hΓ : stdRatPoints ≤ Γ) (hK : levelOf w ⊥ ≤ K) [HasFiniteType Γ K]
    (h_aut : ∀ g : Gf E Unit, classAut Γ K g = ⊥) :
    ∃ z : Gf E Unit, ∃ χ : tameChars S,
      ‖ι (s 1)‖ ≤ ‖ι
          (classSum Γ K (fun g : Gf E Unit ↦ χ.val.1.val (detFin 1 (g * z)) * s (g * z)) /
            classSum Γ K 1)‖ := by
  classical
  -- The group is commutative, so the double cosets are the cosets of `Γ ⊔ K`.
  have h_setoid : setoid Γ K = leftRel (Γ ⊔ K) := by
    ext x
    simp only [rel_iff, eq_comm, leftRel_apply, Γ.mem_sup, mul_left_comm x, eq_inv_mul_iff_mul_eq,
      mul_assoc]
  have : Finite (_root_.Quotient (leftRel (Γ ⊔ K))) := by
    rw [← h_setoid]
    exact HasFiniteType.finite_classes
  have : Fintype (Gf E Unit ⧸ Γ ⊔ K) := ofFinite (_root_.Quotient _)
  have h_sum (f : Gf E Unit → ℂ) : classSum Γ K f = ∑ o : Gf E Unit ⧸ Γ ⊔ K, f o.out :=
    calc classSum Γ K f = ∑ᶠ c : _root_.Quotient (setoid Γ K), f c.out := by
          simp only [classSum, h_aut, Subgroup.card_bot, Nat.cast_one, inv_one, one_smul]
          rfl
      _ = ∑ᶠ c : _root_.Quotient (leftRel (Γ ⊔ K)), f c.out := by rw [h_setoid]
      _ = ∑ o : Gf E Unit ⧸ Γ ⊔ K, f o.out := finsum_eq_sum_of_fintype _
  -- The finite part `fin` of a norm-one adele maps the rational points and the units of tame
  -- level `S` into `Γ ⊔ K`, so every character of the classes comes from a tame character.
  let fin : unitary (𝔸 E) →* Gf E Unit :=
    (scalarFin Unit).comp (Unitary.map ⟨MonoidHom.snd _ _, by simp⟩).toMonoidHom
  have h_entry (u : unitary (𝔸 E)) (i j : Unit) : (fin u).val i j = (u : 𝔸 E).2 := rfl
  have h_le : rationalU1 ⊔ integralU1 S ≤ (Γ ⊔ K).comap fin :=
    rationalU1_sup_integralU1_le_comap hS hΓ hK h_entry
  have h_det (g : Gf E Unit) : fin (detFin 1 g) = g := by
    ext
    simp [G.det, U.det, Gf.atPlace, h_entry]
    rfl
  have h_lift (ψ : AddChar (Additive (Gf E Unit ⧸ Γ ⊔ K)) ℂ) :
      ∃ χ : tameChars S, ∀ g : Gf E Unit, χ.val.1.val (detFin 1 g) = ψ (.ofMul ⟦g⟧) := by
    obtain ⟨χ, hχ⟩ : ∃ χ : tameChars S, ∀ u : unitary (𝔸 E), χ.val.1.val u = ψ (.ofMul ⟦fin u⟧) :=
      AutChar.exists_mem_tameChars (ψ.toMonoidHom.comp (QuotientGroup.map _ _ fin h_le))
    exact ⟨χ, fun g ↦ by rw [hχ, h_det]⟩
  choose χ hχ using h_lift
  -- Translate so that the representative of the trivial class becomes 1. By orthogonality the
  -- normalised class sums add up to `s 1`, and an ultrametric norm of a sum is at most one term's.
  let z : Gf E Unit := (1 : Gf E Unit ⧸ Γ ⊔ K).out⁻¹
  let term (ψ : AddChar (Additive (Gf E Unit ⧸ Γ ⊔ K)) ℂ) : ℂ :=
    classSum Γ K (fun g ↦ (χ ψ).val.1.val (detFin 1 (g * z)) * s (g * z)) / classSum Γ K 1
  have h_orth : ∑ ψ, term ψ = s 1 := by
    simp only [term, hχ, h_sum, ← sum_div]
    rw [sum_comm]
    simp [z, ← sum_mul, AddChar.sum_apply_eq_ite]
  obtain ⟨ψ, -, hψ⟩ : ∃ ψ ∈ univ, ‖∑ ψ', ι (term ψ')‖ ≤ ‖ι (term ψ)‖ :=
    exists_norm_finsetSum_le_of_nonempty univ_nonempty fun ψ ↦ ι (term ψ)
  rw [← map_sum, h_orth] at hψ
  exact ⟨z, χ ψ, hψ⟩

/-- Multiplicative pigeonhole. Let `V^{|G|} = ∏_χ a(χ)b(χ)` over a finite group `G`, and let `ι` be
a ring homomorphism into a normed field. Then every `ψ` has a factorisation `ψ = φχ` with
`‖ι V‖ ≤ ‖ι(a(φ)b(χ))‖`. -/
theorem exists_mul_eq_norm_map_le_norm_map_mul {G F : Type*} [Group G] [Fintype G] [NormedField F]
    (ι : ℂ →+* F) {a b : G → ℂ} {V : ℂ} (hV : V ^ Fintype.card G = ∏ χ : G, a χ * b χ) (ψ : G) :
    ∃ φ χ : G, φ * χ = ψ ∧ ‖ι V‖ ≤ ‖ι (a φ * b χ)‖ := by
  -- Take `χ` with `‖ι (a (ψ / χ) * b χ)‖` largest; `χ ↦ ψ / χ` permutes `G`, so the product of
  -- these sizes is `‖ι V‖ ^ card G`.
  obtain ⟨χ, -, h_max⟩ :=
    exists_max_image univ (fun χ ↦ ‖ι (a (ψ / χ) * b χ)‖) univ_nonempty
  refine ⟨ψ / χ, χ, div_mul_cancel ..,
    le_of_pow_le_pow_left₀ (n := card G) card_ne_zero (norm_nonneg _) ?_⟩
  calc ‖ι V‖ ^ card G = ∏ χ, ‖ι (a (ψ / χ) * b χ)‖ := by
        simp [← norm_pow, ← map_pow, hV, ← (Equiv.divLeft ψ).prod_comp a, prod_mul_distrib]
    _ ≤ ∏ _, ‖ι (a (ψ / χ) * b χ)‖ := prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) h_max
    _ = ‖ι (a (ψ / χ) * b χ)‖ ^ card G := prod_const _

/-- The point form with vector `v`, supported on one class next to the point `h`, is integral at
`j : ℂ → ℂ_l`, for a prime `l`, if `v` has gauge at most one at `h`. The gauge `weylGauge` is the
largest `l`-adic norm of a coordinate of `h⁻¹ v`, in the representation of weight `O.columnCount`
twisted by the determinant powers `O.detExp`, with coordinates indexed by
`WeylIndex n O.columnCount`. -/
theorem pointForm_mem_integralForms {l : ℕ} [Fact l.Prime] {E r n : Type} [Field E] [CMType E]
    [WeilData E] [Fintype r]
    [DecidableEq r] [Fintype n] [DecidableEq n] (j : PadicPlace l) {O : DescentPair E r n}
    {h : Gf E n} {Y : ∀ i : O.ChosenIndex, Matrix n r (ResField (O.placeAt (.inl i)))}
    {hY : ∀ i : O.ChosenIndex, (Y i).mulVec.Injective} {e : r ↪ n}
    {v : WeylIndex n O.columnCount → ℂ} (hv : weylGauge (p := l) O.columnCount O.detExp h v ≤ 1) :
    pointForm h hY e v ∈ LevelPlaces.LevelForm.integralForms j := by
  -- The form is supported on the class of `h * k` with `k` integral, which keeps the gauge.
  let k : stdLevel E n := pointLift hY e
  change deltaForm stdEmbFin _ O.levelChar (h * k) v ∈ _
  intro g
  refine (weylGauge_deltaForm_le LevelPlaces.isOfFinOrder_level_char).trans ?_
  rwa [weylGauge_mul_of_mem_integralAbove h (stdLevel_le_localLevel k.2)]

section ClassSum

variable {n : Type} [Fintype n] [DecidableEq n]
  {X : LValueData D.E n} {m : ℕ} {q : D.CriticalPair}

/-- For a pair `q = (ν, z)` that is flat (`HasEmptyRow`: the character has weight `-z` at every
infinite place, and the index type has `2 z ≥ 4` elements) on `Fin m` and a function `F` on
`U(m)(𝔸_f)` with values in the forms for `X`, this is `D.chosenGroupOrder` times the class sum over
`h` of `d / N(Q) ^ (m - 1) * ⟨1, d • Ξ h⟩ • F h`. Here `Ξ = trivialLift H.hasLiftRank ϑ` is the
normalised lift of `ν ϑ`, `d = q.denomBound`, `N(Q) = ϑ.normQ` is the norm of the modulus of `ϑ`,
and `⟨ , ⟩` is the pairing `gramForm`. -/
def CriticalPair.trivialLiftClassSum (H : q.HasEmptyRow (Fin m)) (ϑ : D.TameChar)
    (F : Gf D.E (Fin m) → X.descentPair.FormV) : X.descentPair.FormV :=
  D.chosenGroupOrder •
    stdClassSum (lValueData H.hasLiftRank ϑ).descentPair.levelGroup fun h ↦
      (q.denomBound / ϑ.normQ ^ (m - 1) *
        gramForm 1 ((q.denomBound : ℂ) • trivialLift H.hasLiftRank ϑ h)) • F h

/-- Let the pair `q = (ν, z)` be flat on `Fin m`, and fix a prime `l` with an embedding `ℂ → ℂ_l`
(`PadicPlace l`), of valuation ring `embValRing`. Let `l` be prime to the norm `ϑ.normQ` of the
modulus of `ϑ`. If `F` takes values in an `embValRing`-module `N` of forms for the lift data `X`,
then `N` contains `trivialLiftClassSum hq ϑ F`, the class sum of `F` over `U(m)` weighted by the
values of the lift of `ν ϑ`. -/
theorem CriticalPair.trivialLiftClassSum_mem {l : ℕ} [Fact l.Prime] {ϑ : D.TameChar}
    {F : Gf D.E (Fin m) → X.descentPair.FormV} (hq : q.HasEmptyRow (Fin m)) [PadicPlace l]
    (hl : l.Coprime ϑ.normQ) {N : Submodule embValRing X.descentPair.FormV}
    (hF : ∀ g : Gf D.E (Fin m), F g ∈ N) :
    trivialLiftClassSum hq ϑ F ∈ N := by
  -- `D.chosenGroupOrder` clears the orders of the stabilisers in the class sum, so it suffices that
  -- each summand lies in `N`; its scalar is a product of two integral numbers.
  have h_rank : card (Fin m) ≤ 2 * D.n D.m := hq.2.1.trans_le D.nat_le_of_hasLogBound
  have h_unit := hl.norm_natCast_eq_one ℂ_[l]
  have h_quot : (q.denomBound / ϑ.normQ ^ (m - 1) : ℂ) ∈ embValRing := by
    generalize ϑ.normQ = Nm at h_unit
    simp [← NNReal.coe_le_coe, norm_natCast_le_one, h_unit]
  -- In jet degree zero the group acts trivially, so the vector `1` has gauge at most one.
  have h_gram (g : Gf D.E (Fin m)) :
      gramForm 1 ((q.denomBound : ℂ) • trivialLift hq.2 ϑ g) ∈ embValRing :=
    gramForm_mem_embValRing _ (by simp [weylGauge, weylRep, schur_eq_one, hq])
      (denomBound_smul_trivialLift_mem_integralForms hq.2 ϑ _ hl g)
  exact smul_classSum_mem N (D.card_classAut_dvd_chosenGroupOrder h_rank levelOf_le_stdLevel)
    fun g ↦
    N.smul_mem ⟨_, mul_mem h_quot (h_gram g)⟩ (hF g)

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let `ϑ` be a tame character, `g` a point of `Gf D.E Unit`, and `F` a map from `Gf D.E (Fin m)`
to the forms `X.descentPair.FormV`. Let the pair `q = (ν, z)` have an empty row on `Fin m`. Let a
conjugate-linear form `L` take at `F h` the value `B * (A * kernelForm g h i)`, for every `h` and
every coordinate `i` of the theta kernel at `(g, h)` of the lift data `lValueData` of `ν ϑ`. Then
`N * P.vacuumScale D.towerExp ^ m` times the value of `L` at the class sum
`trivialLiftClassSum hq ϑ F` is `B * integralAlgebraicPart * A`. Here
`N = stdClassSum chosenLevel 1` is the class sum of `1` on `U(1)` at the chosen level. -/
theorem CriticalPair.smul_apply_trivialLiftClassSum {ϑ : D.TameChar}
    {F : Gf D.E (Fin m) → X.descentPair.FormV} (hq : q.HasEmptyRow (Fin m)) (g : Gf D.E Unit)
    {A B : ℂ} {L : X.descentPair.FormV →L⋆[ℂ] ℂ}
    (h_pair : ∀ (h : Gf D.E (Fin m))
      (i : WeylIndex (Fin m) (lValueData hq.hasLiftRank ϑ).descentPair.columnCount),
      L (F h) = B * (A * (lValueData hq.hasLiftRank ϑ).kernelForm g h i)) :
    ((stdClassSum (lValueData hq.hasLiftRank ϑ).chosenLevel 1 * P.vacuumScale D.towerExp ^ m) • L)
        (trivialLiftClassSum hq ϑ F) =
      B * integralAlgebraicPart hq.hasLiftRank ϑ * A := by
  -- By adjointness `‖trivialLift‖²` is the class sum over `U(1)` of the pairing of the kernel with
  -- `trivialLift`, which does not depend on the point of `U(1)`, since the operators
  -- `normalizedCentralOp` fix `trivialLift`.
  let Y : LValueData D.E (Fin m) := lValueData hq.hasLiftRank ϑ
  have h_const (k : Gf D.E Unit) :
      inner ℂ (Y.kernelForm (k * g)) Y.trivialLift = inner ℂ (Y.kernelForm g) Y.trivialLift := by
    rw [mul_comm' k g, ← normalizedCentralOp_kernelForm, ← inner_normalizedCentralOp,
      normalizedCentralOp_trivialLift]
  have h_norm : (‖Y.trivialLift‖ : ℂ) ^ 2 = stdClassSum Y.chosenLevel fun _ ↦
      starRingEnd ℂ (inner ℂ (Y.kernelForm g) Y.trivialLift) := by
    simpa [map_classSum, normalizedDescent_eq_inner_kernelForm, h_const] using
      congrArg (starRingEnd ℂ) (Y.inner_trivialLift g Y.trivialLift)
  -- Both sides unfold to double class sums of double sums over coordinates, and these agree term
  -- by term by `h_pair`.
  simp [inner, LevelPlaces.LevelForm.innerAt_eq_stdClassSum, trivialLiftClassSum,
    integralAlgebraicPart,
    trivialLift,
    norm_smul, mul_pow, Y, h_norm, ← Complex.mul_conj', apply_eq_evalForm, map_classSum,
    ↓classSum_mul, mul_classSum, division_def, hq.1, gramForm_apply, mul_sum, sum_mul,
    dot_mulVec_eq_sum_sum, -norm_pow]
  congr! 6 with _ h
  rw [h_pair h]
  ring!

end ClassSum

/-- Let the pair `q = (ν, z)` be flat on `Fin m`, let `ϑ` be a tame character and `lValueData` the
data of the lift of `ν ϑ` from `U(1)` to `U(m)`. Every coordinate of its kernel at `(g, h)` is the
theta kernel `modKernelStdSpace`, with polynomial `1` and character `charV = ν ϑ υ ^ z` (`υ` the
splitting character), of the function `residueBlockDatum`, read modulo any multiple `𝔪` of
`levelModulus 2` through the residues `levelResidueAt`. This function is zero unless the residue at
each chosen place is the standard column, and is then the product over the twist places `w` of the
tame part at `w` of the determinant of the chosen row. -/
lemma CriticalPair.kernelForm_eq_modKernelStdSpace_of_hasEmptyRow {q : D.CriticalPair} {m : ℕ}
    (hq : q.HasEmptyRow (Fin m)) (ϑ : D.TameChar) {𝔪 : Modulus D.E}
    (h_le : 𝔪.ideal ≤ ((lValueData hq.hasLiftRank ϑ).levelModulus 2).ideal) (g : Gf D.E Unit)
    (h : Gf D.E (Fin m))
    (i : WeylIndex (Fin m) (lValueData hq.hasLiftRank ϑ).descentPair.columnCount) :
    (lValueData hq.hasLiftRank ϑ).kernelForm g h i =
      modKernelStdSpace (stdSpace D.E Unit) 1 (lValueData hq.hasLiftRank ϑ).descentPair.charV 𝔪
        (fun T : Matrix (Fin m) Unit 𝔪.ResidueRing ↦
          (lValueData hq.hasLiftRank ϑ).descentPair.residueBlockDatum
          fun w : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex ↦
            (T.map (Ideal.Quotient.factor h_le)).map (levelResidueAt w)) 1 (1, g) h := by
  have h_deg : (lValueData hq.hasLiftRank ϑ).rowLength = 0 := funext fun τ ↦ by simp [hq.1 τ]
  rw [kernelForm_of_rowLength_eq_zero _ _ _ h_deg, ← modKernel_factor h_le]

section Seesaw

variable {p q q₂ q₃ : D.CriticalPair}

/-- The chosen row of the second of the four blocks of `RankOneIndex z`, the block that carries the
twist. -/
def twistRow (z : ℕ) : Unit ↪ RankOneIndex z :=
  arbitraryIndexEmbedding.trans (.trans .inl (.trans .inr .inl))

open LevelPlaces in
/-- For a main pair `p` and a chosen place `i`, the column over the residue field at `i`, with rows
`RankOneIndex p.z`, made of the residue of `x₀` on the first block, of size `12`, and of a standard
basis vector on each of the other three blocks. -/
def testColumn (H : q.HasEmptyRow (Fin (2 * p.z - 20))) {j : ℕ} (hE : p.IsMainPair j) (ϑ : D.Twist)
    (x₀ : Matrix (Fin 12) Unit ((lValueData hE.hasLiftRank ϑ).levelModulus 1 false).ResidueRing)
    (i : (lValueData hE.hasLiftRank ϑ).ChosenIndex) :
    Matrix (RankOneIndex p.z) Unit
      (ResField ((lValueData hE.hasLiftRank ϑ).descentPair.placeAt (.inl i))) :=
  fromRows
    (fromRows (x₀.map (modulusResidue _ (places_levelModulus_false.ge ⟨_, rfl⟩)))
      (fromRows (inclMatrix _ arbitraryIndexEmbedding) (inclMatrix _ arbitraryIndexEmbedding)))
    (inclMatrix _ (lValueData H.hasLiftRank .one).descentPair.incl)

/-- The column `testColumn` is injective as a linear map, since its last block is a standard basis
vector. -/
lemma testColumn_injective (hq : q.HasEmptyRow (Fin (2 * p.z - 20))) {j : ℕ} (hp : p.IsMainPair j)
    (ϑ : D.Twist)
    (x₀ : Matrix (Fin 12) Unit ((lValueData hp.hasLiftRank ϑ).levelModulus 1 false).ResidueRing)
    (i : (lValueData hp.hasLiftRank ϑ).ChosenIndex) :
    (testColumn hq hp ϑ x₀ i).mulVec.Injective := by
  intro v v' h_eq
  simp only [testColumn, fromRows_mulVec] at h_eq
  exact inclMatrix_mulVecLin_injective _ _ (funext fun k ↦ congrFun h_eq (.inr k))

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
open MvPolynomial Ideal.Quotient Selmer Nat LevelPlaces in
/-- Seesaw factorisation at one point. Let `X` be the lift data of a main pair `p`, with point
`z = p.z`, at the twist `ϑ`; its `2 z` indices form blocks of sizes `12`, `4`, `4`, `2 z - 20`. Let
`q₂`, `q₃`, `q` be flat on the last three blocks; `q₂` is taken at `ϑ`, the other two at the trivial
character. Take the point form, supported on one class of `U(2 z)(𝔸_f)`, at the block diagonal point
`diag (1, h₂, h₃, h₁)`. Its datum is `testColumn` (`x₀` on the first block) at the chosen places and
reads the row `twistRow` of the second block at the places of the modulus of `ϑ`. Its vector `c` has
as polynomial `a` times the monomial `α` in the first block. If `χ` and the characters of the last
three blocks multiply to the character of `X`, then the inner product of the point form with the
theta kernel `X.kernelForm g`, for `g ∈ U(1)(𝔸_f)`, is `a` times a product of four theta kernels at
`g`, one for each block. The first, `modKernel`, belongs to `χ`, the indicator of `x₀` and `α`. -/
theorem inner_pointForm_kernelForm (hq : q.HasEmptyRow (Fin (2 * p.z - 20)))
    (hq₂ : q₂.HasEmptyRow (Fin 4)) (hq₃ : q₃.HasEmptyRow (Fin 4)) {j : ℕ}
    {α : NumberField.InfinitePlace D.E × Fin 12 × Unit →₀ ℕ} {χ : AutChar D.E}
    (hp : p.IsMainPair j) (ϑ : D.Twist)
    (x₀ : Matrix (Fin 12) Unit ((lValueData hp.hasLiftRank ϑ).levelModulus 1 false).ResidueRing)
    {c : WeylIndex (RankOneIndex p.z) (lValueData hp.hasLiftRank ϑ).descentPair.columnCount → ℤ}
    {a : ℂ}
    (h_pol : (lValueData hp.hasLiftRank ϑ).descentPair.fockPoly (star ((↑) ∘ c)) =
      a • renameRowsCols (Function.Embedding.trans .inl .inl : Fin 12 ↪ RankOneIndex p.z) id
        (monomial α 1))
    (h_char : χ * ((lValueData hq₂.hasLiftRank ϑ).descentPair.charV *
        (lValueData hq₃.hasLiftRank .one).descentPair.charV) *
          (lValueData hq.hasLiftRank .one).descentPair.charV =
      (lValueData hp.hasLiftRank ϑ).descentPair.charV)
    (g : Gf D.E Unit) (h₁ : Gf D.E (Fin (2 * p.z - 20))) (h₂ h₃ : Gf D.E (Fin 4))
    (i₁ : WeylIndex (Fin (2 * p.z - 20)) (lValueData hq.hasLiftRank .one).descentPair.columnCount)
    (i₂ : WeylIndex (Fin 4) (lValueData hq₂.hasLiftRank ϑ).descentPair.columnCount)
    (i₃ : WeylIndex (Fin 4) (lValueData hq₃.hasLiftRank .one).descentPair.columnCount) :
    let X : LValueData D.E (RankOneIndex p.z) := lValueData hp.hasLiftRank ϑ
    let u : D.TameChar := TameChar.one
    innerSLFlip ℂ (X.kernelForm g)
        (pointForm (U.blockSumOne (U.blockSumOne (1, U.blockSumOne (h₂, h₃)), h₁))
          (testColumn_injective hq hp ϑ x₀) (twistRow p.z) ((↑) ∘ c)) =
      a * (modKernel (stdSpace D.E Unit) (stdSpace D.E (Fin 12)) 1 χ (X.levelModulus 1 false)
          (Pi.single x₀ 1) (monomial α 1) (1, g) (1, 1) *
        (lValueData hq₂.hasLiftRank ϑ).kernelForm g h₂ i₂ *
        (lValueData hq₃.hasLiftRank u).kernelForm g h₃ i₃ *
        (lValueData hq.hasLiftRank u).kernelForm g h₁ i₁) := by
  classical
  intro X u
  have h_not_chosen (i : X.TwistIndex) : ¬D.IsChosen (X.twistPlace i) :=
    (D.normQ_mem_and_notMem_of_mem_Q ϑ (.inl i.2)).2.1
  have h_no_twist : IsEmpty (D.levelPlaces u).TwistIndex := ⟨nofun⟩
  -- Read the data of the four blocks modulo the same `𝔪`.
  let 𝔪 : Modulus D.E := X.levelModulus 2
  have h_first : 𝔪.ideal ≤ (X.levelModulus 1 false).ideal := by
    simp [𝔪, New.LevelPlaces.levelModulus, sq, Ideal.mul_le_left.trans]
  have h_untwisted : 𝔪.ideal ≤ ((D.levelPlaces u).levelModulus 2).ideal := by
    simp +instances [𝔪, New.LevelPlaces.levelModulus, levelPlaces, X, ↓prod_of_isEmpty,
      Ideal.mul_le_left.trans]
  let Ψ₀ (T : Matrix (Fin 12) Unit 𝔪.ResidueRing) : ℂ :=
    Pi.single (M := fun _ ↦ ℂ) x₀ 1 (T.map (Ideal.Quotient.factor h_first))
  let Ψ₂ (T : Matrix (Fin 4) Unit 𝔪.ResidueRing) : ℂ :=
    (lValueData hq₂.hasLiftRank ϑ).descentPair.residueBlockDatum fun w ↦
      (T.map (Ideal.Quotient.factor le_rfl)).map (levelResidueAt w)
  let Ψ₃ (T : Matrix (Fin 4) Unit 𝔪.ResidueRing) : ℂ :=
    (lValueData hq₃.hasLiftRank u).descentPair.residueBlockDatum fun w ↦
      (T.map (Ideal.Quotient.factor h_untwisted)).map (levelResidueAt w)
  let Ψ₁ (T : Matrix (Fin (2 * p.z - 20)) Unit 𝔪.ResidueRing) : ℂ :=
    (lValueData hq.hasLiftRank u).descentPair.residueBlockDatum fun w ↦
      (T.map (Ideal.Quotient.factor h_untwisted)).map (levelResidueAt w)
  -- The datum of the point form is the product of the data of the four blocks.
  have h_datum (T : Matrix (RankOneIndex p.z) Unit 𝔪.ResidueRing) :
      pointFormDatum (O := X.descentPair) (testColumn hq hp ϑ x₀) (twistRow p.z)
          (fun i ↦ T.map (levelResidueAt i)) =
        Ψ₀ (T.submatrix (.inl ∘ .inl) id) *
          (Ψ₂ (T.submatrix ((.inl ∘ .inr) ∘ .inl) id) *
            Ψ₃ (T.submatrix ((.inl ∘ .inr) ∘ .inr) id)) *
          Ψ₁ (T.submatrix .inr id) := by
    obtain ⟨T, rfl⟩ := mk_surjective.comp_left.comp_left T
    -- Both sides are the same product over the twist places under a condition, block by block.
    simp [Modulus.matrix_eq_iff_map_modulusResidue_eq X.isConjApart_chosenPlace.injective
      X.ideal_levelModulus_one_false, ← ext_iff, DescentPair.residueBlockDatum, pointFormDatum, X,
        𝔪, Ψ₀, Ψ₁,
      Ψ₂, Ψ₃, Pi.single_apply, testColumn, twistRow, tamePart_eq_one, h_not_chosen, univ_eq_empty,
      forall_and, ← ite_and]
    congr! 1
    tauto
  rw [innerSLFlip_apply_apply, ← inner_conj_symm, ← X.normalizedDescent_eq_inner_kernelForm 1]
  -- `erw` identifies the space and the level data of `X.descentPair` with those of `X`.
  erw [normalizedDescent_pointForm, h_pol, ← modKernelBilin_apply]
  rw [mul_assoc (modKernel ..), ← h_char, ← modKernel_factor h_first,
    kernelForm_eq_modKernelStdSpace_of_hasEmptyRow hq₂ ϑ (𝔪 := 𝔪) le_rfl,
    kernelForm_eq_modKernelStdSpace_of_hasEmptyRow hq₃ u h_untwisted,
    kernelForm_eq_modKernelStdSpace_of_hasEmptyRow hq u h_untwisted]
  -- Join the four kernels by the seesaw identity.
  simp_rw [← modKernelStdSpace_block (.refl _)]
  rw [Complex.conj_conj, map_smul, smul_eq_mul, modKernelBilin_apply]
  congr! 3
  · simp [DescentPair.charW]
  · exact h_datum _
  · simp only [map_one, mul_one, rename_rename]
    rfl

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum Finset.prod Finset.univ in
open MvPolynomial Ideal.Quotient Selmer Nat LevelPlaces in
/-- Let `l` be a prime, `p` a main pair for `j` with point `z = p.z`, whose `2 z` indices form
blocks of sizes `12`, `4`, `4`, `2 z - 20`, and `ϑ` a twist. Let `q` be flat on the last block. Take
the point forms at the block diagonal points `diag (1, h₂, h₃, h₁)` of `U(2 z)(𝔸_f)` whose datum is
`testColumn` at the chosen places and reads the row `twistRow` of the second block at the twist
places. Let their integer vector `c` be fixed by `weylRep`, the representation of weight
`columnCount` twisted by the powers `detExp` of the determinant, at every family `g` over the
infinite places `D.Φ`, over a field of characteristic zero, whose columns in the first block are
those of the identity. Then their class sum `trivialLiftClassSum` over `h₁`, weighted by the values
of the untwisted lift of `q`, is a test form (`IsTestForm`): integral above `l` and orthogonal to
the false lifts, the forms in the kernel of the descent to `U(1)`, in the image of the mean over the
residue units at the chosen places, that the Hecke polynomial of a split place `w` at
`liftHeckeRoot w` kills. -/
theorem isTestForm_trivialLiftClassSum_pointForm {l : ℕ} [Fact l.Prime]
    (hq : q.HasEmptyRow (Fin (2 * p.z - 20))) {j : ℕ} (hp : p.IsMainPair j) (ϑ : D.Twist)
    (x₀ : Matrix (Fin 12) Unit ((lValueData hp.hasLiftRank ϑ).levelModulus 1 false).ResidueRing)
    {c : WeylIndex (RankOneIndex p.z) (lValueData hp.hasLiftRank ϑ).descentPair.columnCount → ℤ}
    (h_fix : ∀ {R : Type} [Field R] [CharZero R] {g : D.Φ → GL (RankOneIndex p.z) R},
      (∀ (τ : D.Φ) (a : Fin 12) (b : RankOneIndex p.z),
        (g τ).val b (.inl (.inl a)) = if b = .inl (.inl a) then 1 else 0) →
      weylRep (lValueData hp.hasLiftRank ϑ).descentPair.columnCount
        (lValueData hp.hasLiftRank ϑ).descentPair.detExp
        g *ᵥ ((↑) ∘ c) = (↑) ∘ c)
    (h₂ h₃ : Gf D.E (Fin 4)) :
    (lValueData hp.hasLiftRank ϑ).descentPair.IsTestForm l
      (trivialLiftClassSum hq .one fun h₁ : Gf D.E (Fin (2 * p.z - 20)) ↦
        pointForm (U.blockSumOne (U.blockSumOne (1, U.blockSumOne (h₂, h₃)), h₁))
          (testColumn_injective hq hp ϑ x₀) (twistRow p.z) ((↑) ∘ c)) := by
  classical
  let X : LValueData D.E (RankOneIndex p.z) := lValueData hp.hasLiftRank ϑ
  let u : D.TameChar := TameChar.one
  have h_not_chosen (i : X.TwistIndex) : ¬D.IsChosen (X.twistPlace i) :=
    (D.normQ_mem_and_notMem_of_mem_Q ϑ (.inl i.2)).2.1
  have h_large : 45 < 2 * p.z := by
    have hz_gt : D.m < p.z := hp.z_mem.1
    have hm : 10000 ≤ D.m := D.ten_thousand_le_m
    omega
  have hu : l.Coprime u.normQ := .prod_right nofun
  have h_no_twist : IsEmpty (D.levelPlaces u).TwistIndex := ⟨nofun⟩
  have h_inj (i : X.ChosenIndex) : (testColumn hq hp ϑ x₀ i).mulVec.Injective :=
    testColumn_injective hq hp ϑ x₀ i
  let e : Unit ↪ RankOneIndex p.z := twistRow p.z
  let F (h₁ : Gf D.E (Fin (2 * p.z - 20))) : X.descentPair.FormV :=
    pointForm (U.blockSumOne (U.blockSumOne (1, U.blockSumOne (h₂, h₃)), h₁)) h_inj e ((↑) ∘ c)
  change X.descentPair.IsTestForm l (trivialLiftClassSum hq u F)
  -- `F` is integral: the point is `1` on the first block, so it fixes the integral vector `c`.
  have h_int (v : PadicPlace l) (h₁ : Gf D.E (Fin (2 * p.z - 20))) :
      F h₁ ∈ LevelForm.integralForms v := by
    refine pointForm_mem_integralForms v ?_
    -- the coefficients are rational integers, and the point fixes them
    have h_cast : v.ιₚ ∘ Int.cast ∘ c = Int.cast ∘ c := funext fun i ↦ map_intCast v.ιₚ (c i)
    erw [weylGauge, h_cast, h_fix]
    · simp [pi_norm_le_iff_of_nonneg, norm_intCast_le_one]
    · simp [← map_inv, U.sum, Matrix.one_apply]
  refine ⟨fun v ↦ trivialLiftClassSum_mem hq hu (h_int v), fun w hw hS y hy ↦
    inner_eq_zero_symm.1 ?_⟩
  -- Pair the sum with a `y` in the image of the idempotent that the Hecke polynomial and the
  -- descent kill.
  -- Expanding `trivialLift` over `U(1)` gives a sum of periods, and these vanish.
  obtain ⟨⟨⟨y₀, h_good⟩, h_hecke⟩, h_theta⟩ := hy
  let X₁ : LValueData D.E (Fin (2 * p.z - 20)) := lValueData hq.2 u
  have h_period (g : Gf D.E Unit) :
      stdClassSum X₁.descentPair.levelGroup (fun x ↦
        starRingEnd ℂ (gramForm 1 (evalForm x (X₁.kernelForm g))) *
          innerSLFlip ℂ y (F x)) = 0 := by
    refine stdClassSum_period_eq_zero X.fitsParams_descentPair
      (by simpa [X, tamePart_eq_one, h_not_chosen] using! fun i ↦ ϑ.tamePart_ne_one _ i.2)
          (fun i v hv ↦ ?_)
        h_theta
      h_hecke (by simpa using by omega) (.refl _) h_inj
      (.toSpanSingleton _ _ ((↑) ∘ c) ∘ₛₗ (gramForm (κ := X₁.descentPair.columnCount)).flip 1)
      (fun g g' ζ hg ↦ ?_) (b := X₁.descentPair.charV) (𝔪 := X₁.levelModulus 2) ?_ (e' := e)
      (Ψ := fun T ↦ X₁.descentPair.residueBlockDatum fun i ↦ T.map (Rows.levelResidueAt i))
        (g := (1, g))
      (h₁ := U.blockSumOne (1, U.blockSumOne (h₂, h₃))) (one_mem _) (fun x ↦ ?_) rfl fun k hk ↦ ?_
    · -- `y` is killed by the hyperplane sums, since a main pair is ramified at the chosen places
      have h_chosen (i : X.descentPair.ChosenIndex) :
        X.descentPair.tamePart (X.descentPair.chosenPlace i) ≠ 1 := by
        have h_place : D.IsChosen (X.descentPair.chosenPlace i) :=
          D.isChosen_levelPlaces_chosenPlace ϑ i
        simpa [X, ϑ.toTameChar.tamePart_eq_one_of_isChosen h_place] using (hp.isRamified _).2
          h_place
      exact hyperplaneSum_apply_eq_zero_of_rank_one h_chosen ⟨y₀, h_good⟩ i v hv
    · -- equivariance: `g` fixes `c`, and `g'` acts trivially in weight zero
      suffices h_triv : gramForm ζ 1 = gramForm (conjWeylRep X₁.descentPair.columnCount 0 g' ζ) 1 by
        simp [conjWeylRep, X, h_fix, hg, Matrix.one_apply, h_triv]
      simp [conjWeylRep, weylRep, schur_eq_one, hq.1, X₁]
    · simp [places_levelModulus, X, X₁, u, levelPlaces, toAutChar_one_and_toTwist_one_and_Q_one]
    · -- in weight zero every coordinate of `kernelForm` is the same theta constant
      simp [X₁, kernelForm_of_rowLength_eq_zero, kernelVector, nablaBasis_eq_one, hq.1,
        _root_.funext_iff, gramForm_apply, ← apply_eq_evalForm, dot_mulVec_eq_sum_sum, ← mul_sum,
        ← sum_mul, DescentPair.charW]
      have h_block (a : Gf D.E (Fin 12 ⊕ Fin 4 ⊕ Fin 4)) :
          U.blockSumOne (a, x) = U.block (.refl _) (a, x) := rfl
      unfold F
      rw [h_block]
      ring
    · -- an element of the level fixes the unit column at the chosen places, hence both data
      have h_col (i : X₁.descentPair.ChosenIndex) :
          (stdLevel.reduceFamily X₁.descentPair.placeAt k (.inl i)).1 * inclMatrix _
            X₁.descentPair.incl =
            inclMatrix _ X₁.descentPair.incl :=
        mem_stabilizer_col_iff.1 ((mem_levelOf.1 hk).2 (.inl i) ⟨⟩)
      refine ⟨?_, by simpa using (map_block_eq_blockGL (reduceAt w) _ 1 k).1, fun i ↦ ?_⟩
      · simp [X₁, DescentPair.residueBlockDatum, ↓Matrix.map_mul, ↓reductionGL_map_modulusResidue,
          inv_mul_eq_iff_eq_mul_of_invertible, univ_eq_empty, -Sum.elim_inl]
        intro T
        congr! 3
        exact h_col _
      · simp
        erw [(map_block_eq_blockGL _ _ 1 k).2, fromBlocks_mul_fromRows]
        simpa +instances [testColumn, fromRows_ext_iff] using! h_col i
  -- Pull out the scalars and exchange the two class sums; the inner sums are the periods.
  simp [trivialLiftClassSum, CriticalPair.trivialLift, apply_eq_evalForm, LValueData.trivialLift,
    map_classSum, mul_assoc,
    ← mul_classSum, classSum_comm (K' := levelOf _ ⊥), ← innerSLFlip_apply_apply]
  simp only [X₁, h_period]
  simp [classSum]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum Finset.prod Finset.univ in
open MvPolynomial Ideal.Quotient Selmer Nat LevelPlaces in
/-- Seesaw factorisation. Let `l` be a prime with a chosen embedding `ℂ → ℂ_l`. Let `p` be a main
pair for `j` with point `z = p.z`, and let `X` be the lift data of `p` at the twist `ϑ`, with `l`
prime to `ϑ.normQ`. Let `q₂`, `q₃`, `q` have empty row on blocks of sizes `4`, `4` and `2 z - 20`:
`q₂` is taken at `ϑ`, the other two at the trivial character. Let the monomial `α` have degree
`X.rowLength τ` at each infinite place `τ`, and let `χ` and the characters of the three blocks
multiply to that of `X`. Then there is a test form `Ξ` on `U(2 z)` at `l`. Its inner product with
the theta kernel `X.kernelForm g`, for `g ∈ U(1)(𝔸_f)`, times
`N ^ 3 * vacuumScale ^ (2 z - 20 + 8)`, is `∏ (X.rowLength τ)! / α!` times the three numbers
`integralAlgebraicPart` and the theta kernel `modKernel` of `χ`, the indicator of `x₀` and `α`. Here
`integralAlgebraicPart` is `chosenGroupOrder * denomBound ^ 2 * ‖φ‖² / N(Q) ^ (2 z' - 1)` for the
normalised lift `φ` of a pair with point `z'` at a twist of norm `N(Q)`, `N` is the class sum of `1`
over `X.chosenLevel`, `vacuumScale` scales the vacuum vector of the Weil representation of rank one
to integral values, and `x₀` is read modulo `X.levelModulus 1 false`, the product of the chosen
places. -/
theorem exists_isTestForm_inner_kernelForm_eq {l : ℕ} [Fact l.Prime]
    (hq : q.HasEmptyRow (Fin (2 * p.z - 20))) (hq₂ : q₂.HasEmptyRow (Fin 4))
    (hq₃ : q₃.HasEmptyRow (Fin 4)) {j : ℕ}
    {α : NumberField.InfinitePlace D.E × Fin 12 × Unit →₀ ℕ} {χ : AutChar D.E} [PadicPlace l]
    (hp : p.IsMainPair j) (ϑ : D.Twist) (hl : l.Coprime ϑ.normQ)
    (x₀ : Matrix (Fin 12) Unit ((lValueData hp.hasLiftRank ϑ).levelModulus 1 false).ResidueRing)
    (hα : ∀ τ : NumberField.InfinitePlace D.E,
      ∑ i : Fin 12, α (τ, i, ()) = (lValueData hp.hasLiftRank ϑ).rowLength τ)
    (h_char : χ * ((lValueData hq₂.hasLiftRank ϑ).descentPair.charV *
        (lValueData hq₃.hasLiftRank .one).descentPair.charV) *
          (lValueData hq.hasLiftRank .one).descentPair.charV =
      (lValueData hp.hasLiftRank ϑ).descentPair.charV) :
    let X : LValueData D.E (RankOneIndex p.z) := lValueData hp.hasLiftRank ϑ
    let u : D.TameChar := TameChar.one
    ∃ Ξ : X.descentPair.FormV,
      -- the pairing with the kernel of `X` is a product over the four blocks
      (∀ g : Gf D.E Unit,
        inner ℂ Ξ (X.kernelForm g) *
            (stdClassSum X.chosenLevel 1 ^ 3 * P.vacuumScale D.towerExp ^ (2 * p.z - 20 + 8)) =
          (∏ τ : NumberField.InfinitePlace D.E, (X.rowLength τ)! : ℕ) /
            α.prod (fun _ (k : ℕ) ↦ (k ! : ℂ)) * q.integralAlgebraicPart hq.hasLiftRank u *
            q₃.integralAlgebraicPart hq₃.hasLiftRank u *
            q₂.integralAlgebraicPart hq₂.hasLiftRank ϑ *
            modKernel (stdSpace D.E Unit) (stdSpace D.E (Fin 12)) 1 χ (X.levelModulus 1 false)
              (Pi.single x₀ 1) (monomial α 1) (1, g) (1, 1)) ∧
      -- `Ξ` is an integral test form
      X.descentPair.IsTestForm l Ξ := by
  classical
  -- The form is the class sum, against the lifts of the last three blocks, of a point form `F`
  -- whose vector `c` reads the coefficient of the monomial `α` in the first block.
  intro X u
  have hu : l.Coprime u.normQ := .prod_right nofun
  obtain ⟨c, h_pol, h_fix⟩ := exists_int_weylRep_invariant_fockPoly_eq_smul_monomial X
    (.trans .inl .inl) hα
  let F (h₁ : Gf D.E (Fin (2 * p.z - 20))) (h₂ h₃ : Gf D.E (Fin 4)) : X.descentPair.FormV :=
    pointForm (U.blockSumOne (U.blockSumOne (1, U.blockSumOne (h₂, h₃)), h₁))
      (testColumn_injective hq hp ϑ x₀) (twistRow p.z) ((↑) ∘ c)
  -- The pairing of `F` with the kernel of `X` factors over the four blocks.
  have h_pair (g : Gf D.E Unit) (h₁ : Gf D.E (Fin (2 * p.z - 20))) (h₂ h₃ : Gf D.E (Fin 4))
      (i₁ : WeylIndex (Fin (2 * p.z - 20)) (lValueData hq.2 u).descentPair.columnCount)
      (i₂ : WeylIndex (Fin 4) (lValueData hq₂.2 ϑ).descentPair.columnCount)
      (i₃ : WeylIndex (Fin 4) (lValueData hq₃.2 u).descentPair.columnCount) :
      innerSLFlip ℂ (X.kernelForm g) (F h₁ h₂ h₃) =
        (∏ τ, (X.rowLength τ)! : ℕ) / α.prod (fun _ k ↦ (k ! : ℂ)) *
          (modKernel (stdSpace D.E Unit) (stdSpace D.E (Fin 12)) 1 χ (X.levelModulus 1 false)
              (Pi.single x₀ 1) (monomial α 1) (1, g) (1, 1) *
            (lValueData hq₂.2 ϑ).kernelForm g h₂ i₂ * (lValueData hq₃.2 u).kernelForm g h₃ i₃ *
            (lValueData hq.2 u).kernelForm g h₁ i₁) := by
    unfold F X u
    exact inner_pointForm_kernelForm hq hq₂ hq₃ hp ϑ x₀ h_pol h_char g h₁ h₂ h₃ i₁ i₂ i₃
  -- The class sum over the last block is a test form, and the two outer class sums keep both
  -- integrality and orthogonality to the false lifts.
  have h_test (h₂ h₃ : Gf D.E (Fin 4)) :
      X.descentPair.IsTestForm l (trivialLiftClassSum hq u fun h₁ ↦ F h₁ h₂ h₃) :=
    isTestForm_trivialLiftClassSum_pointForm hq hp ϑ x₀ h_fix h₂ h₃
  refine ⟨trivialLiftClassSum hq₂ ϑ fun h₂ ↦ trivialLiftClassSum hq₃ u fun h₃ ↦
    trivialLiftClassSum hq u fun h₁ ↦ F h₁ h₂ h₃, fun g ↦ ?_,
    fun v ↦ trivialLiftClassSum_mem hq₂ hl fun h₂ ↦ trivialLiftClassSum_mem hq₃ hu fun h₃ ↦
      (h_test h₂ h₃).1 v,
    fun w hw hS ↦ (restrictScalars_mem embValRing ..).1 <|
      trivialLiftClassSum_mem hq₂ hl fun h₂ ↦ trivialLiftClassSum_mem hq₃ hu fun h₃ ↦
        (h_test h₂ h₃).2 w hw hS⟩
  -- Sum out the three blocks one after the other.
  refine .trans ?_ (smul_apply_trivialLiftClassSum hq₂ g fun h₂ i₂ ↦
    smul_apply_trivialLiftClassSum hq₃ g fun h₃ i₃ ↦
    smul_apply_trivialLiftClassSum hq g fun h₁ i₁ ↦ h_pair g h₁ h₂ h₃ i₁ i₂ i₃)
  simp [-classSum_mul]
  ring!

end Seesaw

/-- The theta kernel `modKernel` of the datum given by a function `Ψ` modulo `𝔪` and a polynomial
`Q`, with the characters `a` and `b` that twist the action, is multiplied at `(g, h)` by
`ψ (det g)` when `b`, the character of the first group, is divided by `ψ`. -/
lemma modKernel_div_apply {E r n : Type} [Field E] [CMType E] [WeilData E] [Fintype r]
    [DecidableEq r] [Fintype n] [DecidableEq n] {s : r → ℤˣ} {s' : n → ℤˣ} (S : Space E r s)
    (T : Space E n s') (a b ψ : AutChar E) (𝔪 : Modulus E) (Ψ : Matrix n r 𝔪.ResidueRing → ℂ)
    (Q : MvPolynomial (NumberField.InfinitePlace E × n × r) ℂ) (g : G E s) (h : G E s') :
    modKernel S T a (b / ψ) 𝔪 Ψ Q g h = ψ.val g.det * modKernel S T a b 𝔪 Ψ Q g h := by
  simp [modKernel, pairTheta, pairWeil, division_def]
  ring

/-- For an embedding `ι` of `ℂ` in a normed field and `ρ ≠ 0`, the bound
`‖ι (V * ρ)‖ * a ≤ ‖ι y‖` is the bound `‖ι V‖ * a ≤ ‖ι (y / ρ)‖`. -/
lemma norm_map_mul_le_iff_le_div {F : Type*} [NormedField F] (ι : ℂ →+* F) {V y ρ : ℂ} {a : ℝ}
    (hρ : ρ ≠ 0) : ‖ι (V * ρ)‖ * a ≤ ‖ι y‖ ↔ ‖ι V‖ * a ≤ ‖ι (y / ρ)‖ := by
  have h_pos : 0 < ‖ι ρ‖ := norm_pos_iff.2 ((map_ne_zero ι).2 hρ)
  rw [map_mul, map_div₀, norm_mul, norm_div, le_div_iff₀ h_pos, mul_right_comm]

/-- Let `χ` run over the finite group `tameChars` of characters of `U(1)(𝔸)` of weight zero whose
tame part is trivial off the chosen places. Let the critical pairs `q₁ χ` and `q₃ χ` have empty row
(`HasEmptyRow`) on `n` and on `Fin 4`. Some geometric mean `L` over `χ` of the products of their
untwisted values `integralAlgebraicPart` is not zero, and its conjugates have size at most
`exp (x ^ 34) ^ 2`. -/
lemma exists_root_prod_integralAlgebraicPart {n : Type} [Fintype n] [DecidableEq n]
    [Fintype (tameChars D.finite_isChosen.toFinset)]
    {q₁ q₃ : tameChars D.finite_isChosen.toFinset → D.CriticalPair}
    (hq₁ : ∀ χ : tameChars D.finite_isChosen.toFinset, (q₁ χ).HasEmptyRow n)
    (hq₃ : ∀ χ : tameChars D.finite_isChosen.toFinset, (q₃ χ).HasEmptyRow (Fin 4)) :
    ∃ L : ℂ, L ≠ 0 ∧
      L ^ card (tameChars D.finite_isChosen.toFinset) =
        ∏ χ : tameChars D.finite_isChosen.toFinset,
          (q₃ χ).integralAlgebraicPart (hq₃ χ).hasLiftRank .one *
            (q₁ χ).integralAlgebraicPart (hq₁ χ).hasLiftRank .one ∧
      ∀ σ : ℂ ≃+* ℂ, ‖σ L‖ ≤ exp (D.x ^ 34) ^ 2 := by
  obtain ⟨L, hL_pow⟩ : ∃ L : ℂ, L ^ card (tameChars D.finite_isChosen.toFinset) =
      ∏ χ, (q₃ χ).integralAlgebraicPart (hq₃ χ).hasLiftRank .one *
        (q₁ χ).integralAlgebraicPart (hq₁ χ).hasLiftRank .one :=
    IsAlgClosed.exists_pow_nat_eq _ card_pos
  have h_pow_ne : L ^ card (tameChars D.finite_isChosen.toFinset) ≠ 0 := by
    simp [hL_pow, prod_eq_zero_iff]
  refine ⟨L, ne_zero_pow card_ne_zero h_pow_ne, hL_pow, fun σ ↦ ?_⟩
  -- By the pigeonhole principle `‖σ L‖` is bounded by a product of values at two characters.
  obtain ⟨φ, χ, -, h_le : ‖σ L‖ ≤
      ‖σ ((q₃ φ).integralAlgebraicPart (hq₃ φ).hasLiftRank .one *
        (q₁ χ).integralAlgebraicPart (hq₁ χ).hasLiftRank .one)‖⟩ :=
    exists_mul_eq_norm_map_le_norm_map_mul (σ : ℂ →+* ℂ) hL_pow 1
  grw [h_le, map_mul, norm_mul, norm_map_integralAlgebraicPart_le (hq₃ φ),
    norm_map_integralAlgebraicPart_le (hq₁ χ), sq]

/-- A form with small pairing. Let `1 ≤ j ≤ m`, let `p` be a main pair for `j` (`IsMainPair`) and
`q₂ = (ν₂, 2)` a pair with empty row on `Fin 4`. There is a number `c₀ ≠ 0` whose conjugates have
size at most `exp (f m b / k + 3 x ^ 34)` such that, for every prime `l`, every embedding
`ιₚ : ℂ → ℂ_l` (`PadicPlace l`) and every twist `ϑ` with modulus prime to `l`, some test form `Ξ` on
`U(2 p.z)` has `v ⟪Ξ, φ⟫ ≤ v(c₀ · q₂.ratio ϑ) + localPrimeSumTotal l`. Here `φ` is the normalised
lift of the character of `p` times `ϑ`, `q₂.ratio ϑ = |L(2, (ν₂ ϑ)⁻¹)| / |L(2, ν₂⁻¹)|` without the
Euler factors at the level, `localPrimeSumTotal l` is the exponent of `l` that is forced on
derivatives of order `D.weight`, summed over the infinite places, and the valuation `v` of `ιₚ` is
written with norms. -/
theorem exists_isTestForm_le_norm_inner_trivialLift {j : D.LiftIndex} {p q₂ : D.CriticalPair}
    (hp : p.IsMainPair j) (hq₂ : q₂.HasEmptyRow (Fin 4)) :
    ∃ c₀ : ℂ, c₀ ≠ 0 ∧
      (∀ σ : ℂ ≃+* ℂ, ‖σ c₀‖ ≤ exp (D.f * D.m / D.k * D.b + 3 * D.x ^ 34)) ∧
      ∀ (l : ℕ) [Fact l.Prime] [PadicPlace l] (ϑ : D.Twist), l.Coprime ϑ.normQ →
        ∃ Ξ : (lValueData hp.hasLiftRank ϑ).descentPair.FormV,
          (lValueData hp.hasLiftRank ϑ).descentPair.IsTestForm l Ξ ∧
          ‖ιₚ (c₀ * q₂.ratio ϑ)‖ * (l : ℝ) ^ (-D.localPrimeSumTotal l) ≤
            ‖ιₚ (inner ℂ Ξ (CriticalPair.trivialLift hp.hasLiftRank ϑ))‖ := by
  -- Split the `2 z` indices of `p` into blocks of sizes 12 (the derivative), 4 (the twist), 4 and
  -- `2 z - 20` (the two factors of a character `ψ` of the classes of `U(1)`). A test form built on
  -- these blocks pairs with `trivialLift` to a sum of derivatives on the first block, weighted by
  -- `ψ`, times values of pairs with empty row on the other three. `c₀` is the product of the
  -- number `t` of `exists_rpow_neg_localPrimeSumTotal_le_norm_coeff`, the untwisted value `L_twist`
  -- of the second block and the geometric mean `L` of the values of the last two blocks.
  have fin : Fintype (tameChars D.finite_isChosen.toFinset) := ofFinite _
  have h_large : 10000 ≤ D.m := D.ten_thousand_le_m
  have h_free : ∀ g : Gf D.E Unit, classAut stdRatPoints D.chosenLevel g = ⊥ :=
    D.classAut_eq_bot_of_le_chosenLevel le_rfl (card_unit.trans_le D.nat_le_of_hasLogBound)
  obtain ⟨hz_gt : D.m < p.z, hz_le : p.z ≤ D.r⟩ := hp.z_mem
  -- Pairs with empty row for the last two blocks, one over every tame character.
  have h_card : card (Fin (2 * p.z - 20)) = 2 * (p.z - 10) := by
    rw [Fintype.card_fin]
    lia
  have h_card_le : card (Fin (2 * p.z - 20)) ≤ D.t := by
    rw [h_card, Data.t]
    lia
  have h_four_le : card (Fin 4) ≤ D.t := (Fintype.card_fin 4).trans_le D.nat_le_of_hasLogBound
  have exists_last (χ : tameChars D.finite_isChosen.toFinset) : ∃ q : D.CriticalPair,
      (rankTwist q.character (Fin (2 * p.z - 20)) = χ.val.1 ∧ q.tamePart = χ.val.2) ∧
        q.HasEmptyRow (Fin (2 * p.z - 20)) :=
    D.exists_hasEmptyRow (Fin (2 * p.z - 20)) (by lia) h_card_le ⟨p.z - 10, h_card⟩ χ
  have exists_third (χ : tameChars D.finite_isChosen.toFinset) : ∃ q : D.CriticalPair,
      (rankTwist q.character (Fin 4) = χ.val.1 ∧ q.tamePart = χ.val.2) ∧ q.HasEmptyRow (Fin 4) :=
    D.exists_hasEmptyRow (Fin 4) (by simp) h_four_le (by simp) χ
  choose q₁ hχ₁ hq₁ using exists_last
  choose q₃ hχ₃ hq₃ using exists_third
  -- The jet degrees `p.negWeight τ - p.z` of `p` lie in the range where
  -- `exists_rpow_neg_localPrimeSumTotal_le_norm_coeff` applies.
  obtain ⟨t, ht_ne, ht, h_depth⟩ := D.exists_rpow_neg_localPrimeSumTotal_le_norm_coeff
    (fun τ ↦ p.negWeight τ - p.z)
    fun τ ↦ Set.mem_Icc.1 (hp.negWeight_sub_z_mem_Icc τ)
  obtain ⟨L, hL_ne, hL_pow, hL_le⟩ := exists_root_prod_integralAlgebraicPart hq₁ hq₃
  let L_twist : ℂ := q₂.integralAlgebraicPart hq₂.2 .one
  refine ⟨t * L_twist * L, by simp [L_twist, ht_ne, hL_ne], fun σ ↦ ?_, ?_⟩
  · calc ‖σ (t * L_twist * L)‖ = ‖σ t‖ * ‖σ L_twist‖ * ‖σ L‖ := by
          simp only [map_mul, norm_mul]
      _ ≤ exp (D.f * D.m / D.k * D.b) * exp (D.x ^ 34) * exp (D.x ^ 34) ^ 2 := by
          gcongr
          exacts [ht σ, norm_map_integralAlgebraicPart_le hq₂ σ, hL_le σ]
      _ = exp (D.f * D.m / D.k * D.b + 3 * D.x ^ 34) := by
          simp only [sq, ← exp_add]
          ring_nf
  intro l _ _ ϑ hl
  let N : ℕ := Nat.card (StdClasses (n := Unit) D.chosenLevel)
  -- On the first block `h_depth` gives a point `x₀` and a monomial `α`; `s` is their kernel.
  let χ₀ : AutChar D.E :=
    (lValueData hp.hasLiftRank ϑ).descentPair.charV / (lValueData hq₂.2 ϑ).descentPair.charV
  obtain ⟨α, x₀, hα, h_coeff⟩ :=
    h_depth (D.twistModulus ϑ 1 false) (D.ideal_untwistedModulus_eq_span.trans (by simp)) l
  let s (g : Gf D.E Unit) : ℂ :=
    modKernel (stdSpace ..) (stdSpace ..) 1 χ₀ _ (Pi.single x₀ 1) (.monomial α 1) (1, g) 1
  -- Averaging: a character `ψ` whose twisted mean of `s` is as large as `s 1`, and a
  -- factorisation `ψ = ψ₃ ψ₁` whose product of values is as large as `L`.
  have h_chosen (i : (D.levelPlaces ϑ).ChosenIndex) :
      (D.levelPlaces ϑ).chosenPlace i ∈ D.finite_isChosen.toFinset :=
    D.finite_isChosen.mem_toFinset.2 (D.isChosen_levelPlaces_chosenPlace ϑ i)
  obtain ⟨z, ψ, h_avg⟩ := exists_norm_le_norm_twisted_classSum (D.levelPlaces ϑ).chosenPlace _
    h_chosen ιₚ s le_rfl le_rfl h_free
  obtain ⟨ψ₃, ψ₁, hψ, hL_l⟩ := exists_mul_eq_norm_map_le_norm_map_mul ιₚ hL_pow ψ
  -- The characters of the four blocks multiply to that of the lift data of `p`, as `ψ = ψ₃ ψ₁`.
  obtain ⟨Ξ, h_pair, h_test⟩ := exists_isTestForm_inner_kernelForm_eq (hq₁ ψ₁) hq₂ (hq₃ ψ₃)
    (χ := χ₀ / ψ.1.1) hp ϑ hl x₀ hα
    (by simp [χ₀, DescentPair.charV, ← hψ, hχ₁, hχ₃, toAutChar_one_and_toTwist_one_and_Q_one,
      div_div, mul_assoc])
  refine ⟨Ξ, h_test, ?_⟩
  have hN : stdClassSum (lValueData hp.hasLiftRank ϑ).chosenLevel 1 = (N : ℂ) := by
    change stdClassSum D.chosenLevel 1 = _
    simp [classSum, h_free, N, ↓ finsum_eq_sum_of_fintype]
    rfl
  -- The scaled Taylor coefficient bounded below in `h_coeff` is `s 1` times the scalar `c`.
  let c : ℂ := P.vacuumScale D.towerExp ^ 12 / t * (∏ τ, (p.negWeight τ - p.z).factorial :) *
    ((starRingEnd ℂ D.piMBar.1.1 * P.jetScale D.towerExp) ^ α.degree / α.prod fun _ k ↦
      (k.factorial : ℂ))
  have h_lower : (l : ℝ) ^ (-D.localPrimeSumTotal l) ≤ ‖ιₚ c‖ * ‖ιₚ (s 1)‖ := by
    simpa [c, s, MvPowerSeries.coeff_apply, Space.jetSeries_apply, modKernel, pairTheta, pairWeil,
      modDatum, mul_assoc, Prod.mk_one_one] using! h_coeff
  set W : ℂ := (q₃ ψ₃).integralAlgebraicPart (hq₃ ψ₃).2 .one * (q₁ ψ₁).integralAlgebraicPart
    (hq₁ ψ₁).2 .one
  set A : ℂ :=
    stdClassSum (lValueData hp.hasLiftRank ϑ).chosenLevel
        (fun g ↦ ψ.1.1.1 (detFin 1 (g * z)) * s (g * z)) /
      stdClassSum (lValueData hp.hasLiftRank ϑ).chosenLevel 1
  -- By adjointness the pairing with `trivialLift` is the class sum of the pairings of `h_pair`,
  -- whose kernels are `ψ` times `s`. The factor `t` cancels the `/ t` of `c`, and dividing by
  -- `q₂.ratio` turns the twisted value `q₂.integralAlgebraicPart hq₂.2 ϑ` into the untwisted value
  -- `L_twist`.
  have h_inner : t * L_twist * W * (c * A) =
      N ^ 2 * inner ℂ Ξ (CriticalPair.trivialLift hp.hasLiftRank ϑ) / q₂.ratio ϑ := by
    let V : ℂ := P.vacuumScale D.towerExp
    let J : ℂ := (starRingEnd ℂ D.piMBar.1.1 * P.jetScale D.towerExp) ^ p.rowLengthSum
    let T : ℂ := (∏ τ, (p.negWeight τ - p.z).factorial :) / α.prod fun _ k ↦ (k.factorial : ℂ)
    let I : ℂ := inner ℂ Ξ (lValueData hp.hasLiftRank ϑ).trivialLift
    have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    -- Each pairing with the kernel is a constant times `ψ (det g) * s g`; sum over the classes.
    have h_term (g : Gf D.E Unit) :
        inner ℂ Ξ ((lValueData hp.hasLiftRank ϑ).kernelForm g) * (N ^ 3 * V ^ (2 * p.z - 20 + 8)) =
          T * W * q₂.integralAlgebraicPart hq₂.2 ϑ * (ψ.1.1.1 (detFin 1 g) * s g) := by
      rw [← hN, h_pair, modKernel_div_apply, mul_assoc (_ / _),
        mul_comm (integralAlgebraicPart (hq₁ ψ₁).2 _)]
      rfl
    have h_sum : I * (N ^ 3 * V ^ (2 * p.z - 20 + 8)) =
        T * W * q₂.integralAlgebraicPart hq₂.2 ϑ * (A * N) := by
      have h_adjoint : I = stdClassSum (lValueData hp.hasLiftRank ϑ).chosenLevel fun g ↦
          inner ℂ Ξ ((lValueData hp.hasLiftRank ϑ).kernelForm (g * z)) := by
        unfold I
        rw [trivialLift_eq_stdClassSum_translate _ z]
        exact map_classSum (innerSL ℂ Ξ) _
      rw [← hN, div_mul_cancel₀ _ (hN.trans_ne hN_ne), hN, h_adjoint, classSum_mul, mul_classSum]
      simp only [h_term]
    -- The scalars of `c` and of `trivialLift` agree up to `T / t` and a power of `V`.
    have h_c : c = V ^ 12 / t * T * J := by
      have h_degree : α.degree = p.rowLengthSum := by
        simp [α.degree_eq_sum, sum_prod_type, hα]
      simp only [c, V, T, J, h_degree]
      ring
    have h_lift : inner ℂ Ξ (CriticalPair.trivialLift hp.hasLiftRank ϑ) =
        V ^ 12 * V ^ (2 * p.z - 20 + 8) * J * I := by
      have h_card : card (RankOneIndex p.z) = 12 + (2 * p.z - 20 + 8) := by
        simp only [card_sum, Fintype.card_fin]
        ring
      rw [CriticalPair.trivialLift, inner_smul_right, h_card, pow_add]
      rfl
    have h_twist_ne : q₂.integralAlgebraicPart hq₂.2 ϑ ≠ 0 := by simp
    rw [ratio_eq_integralAlgebraicPart_div hq₂.2, h_lift, h_c, div_div_eq_mul_div,
      eq_div_iff h_twist_ne]
    apply mul_left_cancel₀ hN_ne
    linear_combination -(L_twist * V ^ 12 * J) * h_sum +
      N * L_twist * W * V ^ 12 * T * J * A * q₂.integralAlgebraicPart hq₂.2 ϑ *
        mul_inv_cancel₀ ht_ne
  rw [norm_map_mul_le_iff_le_div ιₚ (q₂.ratio_ne_zero ϑ 1)]
  calc ‖ιₚ (t * L_twist * L)‖ * (l : ℝ) ^ (-D.localPrimeSumTotal l)
      ≤ ‖ιₚ (t * L_twist)‖ * ‖ιₚ W‖ * (‖ιₚ c‖ * ‖ιₚ A‖) := by
        grw [map_mul, norm_mul, h_lower, hL_l, h_avg]
    _ = ‖ιₚ (N ^ 2 * inner ℂ Ξ (CriticalPair.trivialLift hp.hasLiftRank ϑ) / q₂.ratio ϑ)‖ := by
        simp only [← h_inner, map_mul, norm_mul]
    _ ≤ ‖ιₚ (inner ℂ Ξ (CriticalPair.trivialLift hp.hasLiftRank ϑ) / q₂.ratio ϑ)‖ := by
        -- the class number `N` is an integer
        rw [mul_div_assoc, ← Nat.cast_pow, map_mul, norm_mul, map_natCast]
        exact mul_le_of_le_one_left (norm_nonneg _) (norm_natCast_le_one ..)

/-- Let `θ ι` be `m`-fold twists (characters of weight zero whose first `m` powers are ramified at
every place of the modulus), one for each prime `l` and isomorphism `ι : ℂ ≃ ℚ̄_l`. Let them form a
regular family (`IsRegularFamily`): the modulus is prime to `l`, the inverse ratios of `L`-values of
ramified pairs have height at most the second cut-off `x₁ = D.x₁`, and the logarithmic denominators
of projections to lifts add up over `l` to at most `denominatorBudget`. Let `p = (ν, z)` be a main
pair for `j` (`IsMainPair`) and `p.ratio ϑ = |L(z, (ν ϑ)⁻¹)| / |L(z, ν⁻¹)|`, without the Euler
factors at the level. Then the family over `ι` of the inverse ratios at `ϑ = (θ ι) ^ j` has height
(`New.HeightLe`) at most `6 denominatorBudget - directionAmount`. Here
`denominatorBudget = f a log³ b / (m k)`. -/
theorem heightLe_inv_ratio {θ : PrimePadicIso → D.MFoldTwist} (hθ : D.IsRegularFamily θ)
    (j : D.LiftIndex) (p : D.CriticalPair) (hp : p.IsMainPair j) :
    HeightLe (6 * D.denominatorBudget - D.directionAmount) fun ι : PrimePadicIso ↦
      (p.ratio ((θ ι).powTwist j))⁻¹ := by
  -- Up to a power of `N(Q)`, the inverse ratio is `‖φ₁‖² / ‖φ‖²` for the untwisted lift `φ₁` and
  -- the twisted lift `φ`. With test forms `Ξ`, `Ξ'` at `ι` and at its conjugate it is the product
  -- of four factors: `‖φ₁‖²`, `⟪pr Ξ, pr Ξ'⟫`, `1 / ρ²` and `ρ² / (⟪Ξ, φ⟫ ⟪φ, Ξ'⟫)`, where `pr`
  -- projects to the line of `φ` and `ρ = q₂.ratio`. Their heights add.
  have h_large : 10000 ≤ D.m := D.ten_thousand_le_m
  have h_rank : p.HasLiftRank (RankOneIndex p.z) := hp.hasLiftRank
  -- The pair `q₂` with empty row over `D.chiM` is ramified and gives the ratio `ρ`.
  have h_tame (w : FinPlace D.E) (hw : w ∉ D.finite_isChosen.toFinset) : D.chiMLocal w = 1 :=
    D.chiMLocal_eq_one_of_not_isChosen (by simpa using hw)
  have h_four_le : card (Fin 4) ≤ D.t := (Fintype.card_fin 4).trans_le D.nat_le_of_hasLogBound
  obtain ⟨q₂, hχ₂, hq₂⟩ := D.exists_hasEmptyRow (Fin 4) (by simp) h_four_le (by simp)
    ⟨(D.chiM, D.chiMLocal), D.chiM_hasWeight, h_tame⟩
  have h_ram : q₂.IsRamified := by
    simpa [CriticalPair.IsRamified, hχ₂] using
      D.chiMLocal_zpow_ne_one_iff_isChosen 1 one_ne_zero (by omega)
  obtain ⟨c₀, hc₀_ne, hc₀_small, h_test⟩ := exists_isTestForm_le_norm_inner_trivialLift hp hq₂
  have h_budget : D.f * D.m / D.k * D.b + 3 * D.x ^ 34 ≤ D.denominatorBudget := D.le_of_hasLogBound
  have hc₀_le (σ : ℂ ≃+* ℂ) : ‖σ c₀‖ ≤ exp D.denominatorBudget :=
    (hc₀_small σ).trans (exp_le_exp.2 h_budget)
  let φ (ι : PrimePadicIso) := CriticalPair.trivialLift h_rank ((θ ι).powTwist j)
  let ρ (ι : PrimePadicIso) : ℂ := q₂.ratio ((θ ι).powTwist j)
  -- Multiply the bounds at `ι` and at its conjugate; `ρ` is real.
  have exists_tests (ι : PrimePadicIso) :
      ∃ Ξ Ξ', (lValueData h_rank ((θ ι).powTwist j)).descentPair.IsTestForm ι.1 Ξ ∧
        (lValueData h_rank ((θ ι).powTwist j)).descentPair.IsTestForm ι.1 Ξ' ∧
        ‖ι.2 (c₀ * star c₀ * ρ ι ^ 2)‖ * ((ι.1 : ℝ) ^ (-D.localPrimeSumTotal ι.1)) ^ 2 ≤
          ‖ι.2 (inner ℂ Ξ (φ ι) * inner ℂ (φ ι) Ξ')‖ := by
    obtain ⟨Ξ, hΞ, h_le⟩ := @h_test ι.1 _ ⟨complexToCp ι.2⟩ ((θ ι).powTwist j) (hθ.coprime ι)
    obtain ⟨Ξ', hΞ', h_le'⟩ := @h_test ι.1 _ ⟨(complexToCp ι.2).comp starRingAut.toRingHom⟩
      ((θ ι).powTwist j) (hθ.coprime ι)
    refine ⟨Ξ, Ξ', hΞ, hΞ', ?_⟩
    have h_mul : ‖ι.2 (c₀ * ρ ι)‖ * ι.1 ^ (-D.localPrimeSumTotal ι.1) *
        (‖ι.2 (star c₀ * ρ ι)‖ * ι.1 ^ (-D.localPrimeSumTotal ι.1)) ≤
        ‖ι.2 (inner ℂ Ξ (φ ι))‖ * ‖ι.2 (inner ℂ (φ ι) Ξ')‖ := by
      simpa [φ, ρ, star_ratio] using
        mul_le_mul h_le h_le' (by positivity) (norm_nonneg _)
    simp only [map_mul, map_pow, norm_mul, norm_pow] at h_mul ⊢
    linarith
  choose Ξ Ξ' hΞ hΞ' h_both using exists_tests
  have hρ (ι : PrimePadicIso) : ρ ι ≠ 0 := q₂.ratio_ne_zero ((θ ι).powTwist j) 1
  have h_pos (ι : PrimePadicIso) : 0 < ‖ι.2 (inner ℂ (Ξ ι) (φ ι) * inner ℂ (φ ι) (Ξ' ι))‖ := by
    have h_ne : ι.2 (c₀ * star c₀ * ρ ι ^ 2) ≠ 0 := by simp [hc₀_ne, hρ]
    exact lt_of_lt_of_le (by have := ι.1.2.pos; positivity) (h_both ι)
  -- The second factor: few congruences.
  obtain ⟨γ, hγ⟩ := hθ.exists_denominator_bound j
  have h_proj : HeightLe D.denominatorBudget fun ι ↦
      inner ℂ ((ℂ ∙ φ ι).starProjection (Ξ ι)) ((ℂ ∙ φ ι).starProjection (Ξ' ι)) := by
    refine .of_le hγ.sum_le fun ι ↦ ?_
    have h_line : (ℂ ∙ (lValueData h_rank ((θ ι).powTwist j)).trivialLift) = ℂ ∙ φ ι :=
      (span_singleton_smul_eq
        (left_ne_zero_of_smul (trivialLift_ne_zero h_rank .one)).isUnit _).symm
    simpa only [h_line] using (hγ.hasDenominatorsLe ι).mainPair p hp (hΞ ι) (hΞ' ι)
  -- The fourth factor: small pairings, with the multiplier `c₀ * star c₀`.
  have h_pair : HeightLe (2 * D.denominatorBudget + ∑ τ, D.primeSum (D.weight τ) τ) fun ι ↦
      ρ ι ^ 2 / (inner ℂ (Ξ ι) (φ ι) * inner ℂ (φ ι) (Ξ' ι)) := by
    refine .of_mul_le (H := c₀ * star c₀) (α := D.denominatorBudget + D.denominatorBudget)
      (e := fun l ↦ 2 • (D.localPrimeSumTotal l * log l))
        (mul_ne_zero hc₀_ne (star_ne_zero.2 hc₀_ne))
      (fun σ ↦ ?_) (fun ι ↦ ?_) fun T hT ↦ ?_
    · rw [exp_add, map_mul]
      exact norm_mul_le_of_le (hc₀_le σ) (hc₀_le (.trans starRingAut σ))
    · have h_exp : ((ι.1 : ℝ) ^ (-D.localPrimeSumTotal ι.1)) ^ 2 =
          (exp (2 • (D.localPrimeSumTotal ι.1 * log ι.1)))⁻¹ := by
        rw [rpow_def_of_pos (mod_cast ι.1.2.pos), Real.exp_nsmul, ← inv_pow, ← Real.exp_neg,
          mul_neg, mul_comm]
      rw [← mul_div_assoc, map_div₀, norm_div, div_le_iff₀' (h_pos ι), ← div_le_iff₀ (exp_pos _),
        div_eq_mul_inv, ← h_exp]
      exact h_both ι
    · linarith [D.sum_localPrimeSumTotal_mul_log_le T hT]
  refine ((((heightLe_norm_trivialLift_sq hp).mul h_proj).mul
    ((hθ.height_le j q₂ 1 h_ram).pow 2)).mul h_pair).mono ?_ fun ι ↦ ?_
  · rw [directionAmount, sum_sub_distrib, Nat.cast_ofNat]
    linarith [(D.le_of_hasLogBound : D.x₁ ≤ D.denominatorBudget)]
  -- `‖φ‖²` is the product of the two pairings over the pairing of the projections.
  have h_ne : inner ℂ (Ξ ι) (φ ι) * inner ℂ (φ ι) (Ξ' ι) ≠ 0 := fun h ↦ by simpa [h] using h_pos ι
  have h_norm : inner ℂ ((ℂ ∙ φ ι).starProjection (Ξ ι)) ((ℂ ∙ φ ι).starProjection (Ξ' ι)) =
      inner ℂ (Ξ ι) (φ ι) * inner ℂ (φ ι) (Ξ' ι) / (‖φ ι‖ : ℂ) ^ 2 := by
    rw [inner_starProjection_left_eq_right,
      starProjection_eq_self_iff.2 (starProjection_apply_mem ..), starProjection_singleton,
      inner_smul_right]
    simp [field]
  have h_four : (p.ratio ((θ ι).powTwist j))⁻¹ =
      (((θ ι).powTwist j).normQ ^ (card (RankOneIndex p.z) - 1) : ℕ) *
        ((‖CriticalPair.trivialLift h_rank .one‖ : ℂ) ^ 2 *
          inner ℂ ((ℂ ∙ φ ι).starProjection (Ξ ι)) ((ℂ ∙ φ ι).starProjection (Ξ' ι)) *
          (ρ ι)⁻¹ ^ 2 * (ρ ι ^ 2 / (inner ℂ (Ξ ι) (φ ι) * inner ℂ (φ ι) (Ξ' ι)))) := by
    have h_value : (p.ratio ((θ ι).powTwist j))⁻¹ =
        (((θ ι).powTwist j).normQ ^ (card (RankOneIndex p.z) - 1) : ℕ) *
          ((‖CriticalPair.trivialLift h_rank .one‖ : ℂ) ^ 2 / (‖φ ι‖ : ℂ) ^ 2) := by
      have h_one : (TameChar.one : D.TameChar).normQ = 1 := by
        simp [TameChar.normQ, toAutChar_one_and_toTwist_one_and_Q_one]
      rw [ratio_eq_algPart_div h_rank, inv_div, algPart, algPart, h_one, Nat.cast_one, one_pow,
        div_one, div_div_eq_mul_div, Nat.cast_pow, mul_comm, mul_div_assoc]
    have hρι : ρ ι ≠ 0 := hρ ι
    rw [h_value, h_norm]
    generalize inner ℂ (Ξ ι) (φ ι) * inner ℂ (φ ι) (Ξ' ι) = pairings at h_ne
    field_simp
  -- The power of `N(Q)` is an integer, so it has norm at most one.
  refine (congrArg (‖ι.2 ·‖) h_four).trans_le ?_
  rw [map_mul, norm_mul, map_natCast]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_natCast_le_one ..)

/-- Let `1 ≤ j ≤ m`, and let `exchangePair j none = (ν_j, z_*)` be the pair made from the character
of the `j`-th lift, of tame part `D.chiMLocal ^ j`, at the point
`z_* = mainPairPoint = 7 (m / 2) + k / 2`, where `m = D.m` and `k = D.r + 1 - m`. For
`7 (m / 2) < z ≤ z_*` the pair `lowerPoint z = (ν_j, z)` is a main pair for `j`. -/
lemma isMainPair_lowerPoint_exchangePair_none (j : D.LiftIndex) {z : ℕ}
    (hz : z ∈ Ioc (7 * (D.m / 2)) D.mainPairPoint) :
      ((exchangePair j none).lowerPoint z).IsMainPair j := by
  set p : D.CriticalPair := (exchangePair j none).lowerPoint z
  have hz_mem : z ∈ Set.Ioc D.m D.r := by grind [mainPairPoint, ten_thousand_le_m]
  have h_point : p.z = z := by
    change 1 ⊔ z ⊓ D.mainPairPoint = z
    grind
  have h_card : card (RankOneIndex p.z) = 20 + (2 * p.z - 20) := by simp
  have h_weight (v : D.Φ) : p.negWeight v = D.liftWeight j v - (j + (D.t - 11 * D.m - 1) / 2) := rfl
  exact
    { hasLiftRank := by grind [ten_thousand_le_m]
      z_mem := by rwa [h_point]
      j_mem := j.2
      tamePart_eq := rfl
      negWeight_le v := by grind [ten_thousand_le_m]
      le_negWeight v := by grind [ten_thousand_le_m] }

/-- For every `z`, the pair `(exchangePair j i).lowerPoint z`, which has the same character as
`exchangePair j i`, is ramified: its tame part is non-trivial exactly at the chosen places. -/
lemma isRamified_lowerPoint_exchangePair (j : D.LiftIndex) (i : Option ℤˣ) (z : ℕ) :
    ((exchangePair j i).lowerPoint z).IsRamified := by
  obtain ⟨hj_pos : 1 ≤ j.val, hj_le : j.val ≤ D.m⟩ := j.2
  cases i with
  | none => exact chiMLocal_zpow_ne_one_iff_isChosen j (by omega) (by omega)
  | some s =>
    have h_abs : ((s : ℤ) * j).natAbs = j := by simp [Int.natAbs_mul]
    exact chiMLocal_zpow_ne_one_iff_isChosen (s * j) (by omega) (by omega)

/-- The Hecke value `heckeValueProd j ϑ` is the product, over the three pairs
`(ν_i, z_i) = exchangePair j i` for `i = none, 1, -1`, of `∏_{w ∈ S} q_w ^ (z_i ^ 2) ∏_{1 ≤ z ≤ z_i}
|L^S(z, (ν_i ϑ ^ s_i)⁻¹)|²`. Here `s_i = i.getD 1` is a sign, and `S` consists of the chosen places
and the places `ϑ.Q` of the twist `ϑ`. It equals the untwisted value `heckeValueProd j 1`, times
`ϑ.normQ ^ ∑ z_i ^ 2` (the product of the norms of the places of `ϑ.Q`), times the square of the
product of the ratios `ratio ϑ s_i = |L(z, (ν_i ϑ ^ s_i)⁻¹)| / |L(z, ν_i⁻¹)|`. These ratios are
taken for the pairs `lowerPoint z = (ν_i, z)` with `1 ≤ z ≤ z_i`. -/
lemma heckeValueProd_eq_mul_prod_ratio_sq (j : D.LiftIndex) (ϑ : D.Twist) :
    heckeValueProd j ϑ = ϑ.normQ ^ (∑ i : Option ℤˣ, (exchangePair j i).z ^ 2) *
      (∏ i : Option ℤˣ, ∏ z ∈ Icc 1 (exchangePair j i).z,
        ((exchangePair j i).lowerPoint z).ratio ϑ (i.getD 1)) ^ 2 * heckeValueProd j 1 := by
  have h_one : heckeValueProd j 1 = ∏ i : Option ℤˣ,
      (lValueProd {w : FinPlace D.E | D.IsChosen w} (exchangePair j i).character⁻¹
        (exchangePair j i).z : ℂ) := by
    simp [heckeValueProd, toAutChar_one_and_toTwist_one_and_Q_one]
  rw [h_one, heckeValueProd]
  simp only [lValueProd_eq_mul_prod_ratio_sq, prod_mul_distrib, prod_pow_eq_pow_sum, ← prod_pow]
  ring

/-- Let `heckeValueProd j ϑ` be the product of the squared `L`-values at `1 ≤ z ≤ z_i` of the three
pairs `(ν_i, z_i) = exchangePair j i`, twisted by `ϑ` or its inverse, with powers of the norms of
the omitted places. It is the untwisted value times a power `e` of the norm `ϑ.normQ` of the modulus
of `ϑ` and the square of a product of ratios `(ν, z).ratio ϑ s = |L(z, (ν ϑ ^ s)⁻¹)| / |L(z, ν⁻¹)|`.
Of these `k / 2` belong to main pairs `p a` for `j` (`IsMainPair`), with `s = 1`, and `5 m` to
ramified pairs `q b`, with signs `s b`. Here `m = D.m` is the number of lifts and `k = D.r + 1 - m`.
The exponent, the pairs and the signs do not depend on `ϑ`. -/
lemma exists_heckeValueProd_eq_mul_prod_ratio (j : D.LiftIndex) :
    ∃ (e : ℕ) (A : Finset ℕ) (B : Finset (Σ _ : Option ℤˣ, ℕ)) (p : ℕ → D.CriticalPair)
      (q : (Σ _ : Option ℤˣ, ℕ) → D.CriticalPair) (s : (Σ _ : Option ℤˣ, ℕ) → ℤˣ),
      2 * #A = D.k ∧
      #B = 5 * D.m ∧
      (∀ a ∈ A, (p a).IsMainPair j) ∧
      (∀ b : Σ _ : Option ℤˣ, ℕ, (q b).IsRamified) ∧
      ∀ ϑ : D.Twist, heckeValueProd j ϑ = ϑ.normQ ^ e *
        ((∏ a ∈ A, (p a).ratio ϑ) * ∏ b ∈ B, (q b).ratio ϑ (s b)) ^ 2 * heckeValueProd j 1 := by
  -- The factors of `exchangePair j none` with `7 (m / 2) < z ≤ mainPairPoint` are main pairs; `B`
  -- indexes the remaining factors.
  let B : Finset (Σ _ : Option ℤˣ, ℕ) :=
    univ.sigma fun i ↦ Ioc 0 (i.elim (7 * (D.m / 2)) D.signPoint)
  refine ⟨∑ i, (exchangePair j i).z ^ 2, Ioc (7 * (D.m / 2)) D.mainPairPoint, B,
    (exchangePair j none).lowerPoint, fun ⟨i, z⟩ ↦ (exchangePair j i).lowerPoint z, fun ⟨i, _⟩ ↦
      i.getD 1,
    ?_, ?_, fun z ↦ isMainPair_lowerPoint_exchangePair_none j,
    fun ⟨i, z⟩ ↦ isRamified_lowerPoint_exchangePair j i z, fun ϑ ↦ ?_⟩
  · simp [mainPairPoint, Nat.mul_div_cancel' D.k_even.two_dvd]
  · have h_card : #B = 7 * (D.m / 2) + (D.m + D.m / 2) := by simp [B, signPoint]
    obtain ⟨m', hm' : D.m = m' + m'⟩ := D.m_even
    omega
  · -- The two products together run over `1 ≤ z ≤ (exchangePair j i).z` for the three `i`.
    have range_eq (i : Option ℤˣ) :
        Icc 1 (exchangePair j i).z = Ioc 0 (i.elim D.mainPairPoint D.signPoint) := by
      cases i <;> rfl
    rw [heckeValueProd_eq_mul_prod_ratio_sq]
    congr 3
    simp only [B, Finset.prod_sigma, range_eq, mainPairPoint, Fintype.prod_option, Option.elim,
      Option.getD, ← prod_Ioc_consecutive _ zero_le le_self_add]
    ring

/-- Let `θ ι` be `m`-fold twists, one for each prime `l` and isomorphism `ι : ℂ ≃ ℚ̄_l`. Let them
form a regular family (`IsRegularFamily`): the modulus is prime to `l`, the inverse ratios of
`L`-values of ramified pairs have height at most the second cut-off `x₁ = D.x₁`, and the logarithmic
denominators of projections to lifts add up over `l` to at most `denominatorBudget`. Let
`1 ≤ j ≤ m`, and let `heckeValueProd j ϑ` be the product of the Hecke values `lValueProd` of the
three pairs `exchangePair j i`, twisted by `ϑ` or its inverse: the pair made from the character of
the `j`-th lift, and two flat pairs of tame parts `D.chiMLocal ^ (± j)` at the points `m` and
`m / 2`. Then the family over `ι` of the inverse ratios of its value at `(θ ι) ^ j` to its value at
`1` has height (`New.HeightLe`) at most `10 m x₁ + k (6 denominatorBudget - directionAmount)`. -/
theorem heightLe_inv_heckeValueProd_div {θ : PrimePadicIso → D.MFoldTwist}
    (hθ : D.IsRegularFamily θ) (j : D.LiftIndex) :
    HeightLe (10 * D.m * D.x₁ + D.k * (6 * D.denominatorBudget - D.directionAmount))
      fun ι : PrimePadicIso ↦ (heckeValueProd j ((θ ι).powTwist j) / heckeValueProd j 1)⁻¹ := by
  -- A main pair costs `6 denominatorBudget - directionAmount`, and a ramified pair costs `x₁`.
  obtain ⟨e, A, B, p, q, s, hA : 2 * #A = D.k, hB : #B = 5 * D.m,
      h_main : ∀ a ∈ A, (p a).IsMainPair j, h_ram : ∀ b, (q b).IsRamified, h_eq⟩ :=
    exists_heckeValueProd_eq_mul_prod_ratio j
  have h_height_main : HeightLe (∑ _a ∈ A, (6 * D.denominatorBudget - D.directionAmount))
      (∏ a ∈ A, fun ι ↦ ((p a).ratio ((θ ι).powTwist j))⁻¹) :=
    HeightLe.prod fun a ha ↦ heightLe_inv_ratio hθ j _ (h_main a ha)
  have h_height_ram : HeightLe (∑ _b ∈ B, D.x₁)
      (∏ b ∈ B, fun ι ↦ ((q b).ratio ((θ ι).powTwist j) (s b))⁻¹) :=
    HeightLe.prod fun b _ ↦ hθ.height_le j _ _ (h_ram b)
  refine hθ.heightLe_of_eq_zpow_mul ((h_height_main.mul h_height_ram).pow 2) (le_of_eq ?_)
    fun ι h_ne ↦ ⟨-e, ?_⟩
  · simp [← hA, hB]
    ring
  · have h_one : heckeValueProd j 1 ≠ 0 := fun h ↦ h_ne (by simp [h])
    rw [h_eq, mul_div_cancel_right₀ _ h_one,
      show ((θ ι).powTwist j).normQ = (θ ι).normQ from rfl]
    simp [mul_pow, mul_comm]

end New.Data

end
