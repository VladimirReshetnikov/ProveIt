import Lib.Adelic.AutomorphicForms.HeckeEigenforms
import Lib.Adelic.Landherr
import Lib.GaloisRep.BaseChange.GlobalRoot
import Lib.Shimura.TraceFormula.DefiniteTrace

/-!
# Twisted trace identity for a step E'/E of CM fields of prime degree

The main result is `New.twisted_trace_identity`. For a step `E'/E` (`New.IsStep`) of prime degree,
it compares a `σ`-twisted trace on forms over `E'` with a trace on forms over `E`, on the definite
unitary groups of `New.stdSpace`, for matching pairs of test functions. Both sides are expanded by
`New.Space.isSampleTotal_twisted_trace` as weighted sums over samples of pairs
(`New.IsSampleTotal`).

## Main definitions and results

* `New.IsSampleTotal`: a number `a` is a weighted sum of `F` over finitely many points, and the
  weighted number of moves from these points to each relevant point is `c`.
* `New.IsSampleTotal.mul_eq_mul_of_bijOn`: two such sums `a`, `b` with weights `c`, `d` satisfy
  `b * c = d * a` when a map between the point sets matches values and moves.
* `New.Weight.baseChange`: the weight of `E'` that has at each infinite place the data of `κ` at the
  place below.
* `New.exists_trace_mul_weightRep_eq_of_twistedNorm_eq`: the twisted character of `κ.baseChange` at
  `δ` is the character of `κ` at the norm of `δ`.

Notions from other files:
* `New.Space.forms V κ`: the forms of weight `κ` on a space `V`, smooth functions `ψ` on the finite
  adelic unitary group `Gf E n` (`U (1 : Matrix n n (𝔸f E))`; `U V.J` is the rational one) with
  `ψ (V.embFin γ * g) = ρ γ (ψ g)` for rational `γ`, where `ρ` is `V.weightRep κ.fst κ.snd` and
  `V.embFin` embeds the rational unitary group; `V.formTranslation κ` is right translation on them.
* `levelSpace π L`: the vectors fixed by `π k` for every `k ∈ L`.
* `New.IsOperatorOf π L T φ`: `T` is the Hecke operator of `φ` on the `L`-fixed vectors.
* `New.stdSpace`: the definite space `I_n`, the sum of `n` norms with its standard lattice.
* `New.twistedNorm τ p δ`: the product `δ * τ δ * ⋯ * τ^[p - 1] δ`.

## Relation to the literature

Known; see `Lib.GaloisRep.BaseChange.PrimeDegreeTransfer` for sources.
-/

/-! ## Double counting of moves between weighted samples of pairs -/

section MoveCounting

open Set Finsupp

/-- There are finitely many points `p i` with complex weights `w i` such that
`a = ∑ w i * F (p i)`, and `∑ w i * #(M (p i) y) = c` for every point `y` such that `F x ≠ 0`
whenever there is a move in `M x y`. Here `M x y` is thought of as the set of moves from `x` to
`y`, and `Set.ncard` is `0` on infinite sets. -/
def New.IsSampleTotal {P A : Type*} (M : P → P → Set A) (F : P → ℂ) (c a : ℂ) : Prop :=
  ∃ w : P →₀ ℂ,
    a = lift ℂ ℂ P F w ∧
    ∀ y : P, (∀ x : P, ∀ g ∈ M x y, F x ≠ 0) → lift ℂ ℂ P (fun x ↦ (M x y).ncard) w = c

/-- Double counting of moves. `IsSampleTotal M F c a` says that, for finitely many points `p i` with
complex weights `w i`, `a = ∑ w i * F (p i)` and `∑ w i * #(M (p i) y) = c` for every `y` such that
`F x ≠ 0` whenever `M x y` (the set of moves from `x` to `y`, with `#` equal to `0` if infinite) is
nonempty. Let `a`, `b` be such totals of `F`, `F'` with weights `c`, `d` for the moves `M`, `N`, and
suppose: `F` vanishes off `S`; `F' y = F x` when `x ∈ S` and `y` has a move to `m x`; and for each
`y` with `F' y ≠ 0`, some `z` and `J` map, for every `x`, the moves from `x` to `z` bijectively onto
the moves from `y` to `m x` (onto `∅` if `x ∉ S`). Then `b * c = d * a`. -/
lemma New.IsSampleTotal.mul_eq_mul_of_bijOn {P Q A B : Type*} {c d a b : ℂ} {M : P → P → Set A}
    {N : Q → Q → Set B} {F : P → ℂ} (F' : Q → ℂ) (h_tot : IsSampleTotal M F c a)
    (h_tot' : IsSampleTotal N F' d b) (m : P → Q) (S : Set P)
    (hF_supp : ∀ x : P, F x ≠ 0 → x ∈ S)
    (hF'_eq : ∀ x ∈ S, ∀ y : Q, ∀ g ∈ N y (m x), F' y = F x)
    (h_bij : ∀ y : Q, F' y ≠ 0 →
      ∃ (z : P) (J : A → B), ∀ x : P, BijOn J (M x z) {g ∈ N y (m x) | x ∈ S}) :
    b * c = d * a := by
  -- Count twice the moves from the points `y` of the second sample to the images `m x` of the
  -- first: summing over `x` first gives `b * c`, summing over `y` first gives `d * a`.
  obtain ⟨w, rfl, hw⟩ := h_tot
  obtain ⟨u, rfl, hu⟩ := h_tot'
  simp only [lift_apply, Finsupp.sum, smul_eq_mul] at hw hu ⊢
  -- If `F' y ≠ 0`, the moves from `y` are counted by the moves to the point `z` of `h_bij`.
  have sum_from (y : Q) :
      F' y * c = F' y * ∑ x ∈ w.support, w x * {g ∈ N y (m x) | x ∈ S}.ncard := by
    by_cases hy : F' y = 0
    · simp [hy]
    obtain ⟨z, J, hJ⟩ := h_bij y hy
    -- a move from `x` to `z` gives one from `y` to `m x` with `x ∈ S`, so `F x = F' y ≠ 0`
    have hF_ne_zero : ∀ x : P, ∀ g ∈ M x z, F x ≠ 0 := fun x g hg ↦ by
      obtain ⟨hg_move, hx_mem⟩ := (hJ x).mapsTo hg
      rwa [← hF'_eq x hx_mem y (J g) hg_move]
    simp only [← hw z hF_ne_zero, (hJ _).ncard_eq]
  -- If `F x ≠ 0`, then `F'` is nonzero at every point with a move to `m x`.
  have sum_to (x : P) : d * F x = F x * ∑ y ∈ u.support, u y * (N y (m x)).ncard := by
    by_cases hx : F x = 0
    · simp [hx]
    rw [← hu (m x) fun y g hg ↦ by rwa [hF'_eq x (hF_supp x hx) y g hg], mul_comm]
  -- The terms agree: a move from `y` to `m x`, `x ∈ S`, gives `F' y = F x`, and `F x = 0` off `S`.
  have term_eq (x : P) (y : Q) :
      F' y * {g ∈ N y (m x) | x ∈ S}.ncard = F x * (N y (m x)).ncard := by
    by_cases hx : x ∈ S
    · obtain h_empty | ⟨g, hg⟩ := (N y (m x)).eq_empty_or_nonempty
      · simp [h_empty]
      · simp [hx, hF'_eq x hx y g hg]
    · simp [hx, not_imp_comm.mp (hF_supp x) hx]
  calc
    _ = ∑ y ∈ u.support, u y * (F' y * c) := by simp only [Finset.sum_mul, mul_assoc]
    _ = ∑ y ∈ u.support, ∑ x ∈ w.support,
          w x * u y * (F' y * {g ∈ N y (m x) | x ∈ S}.ncard) := by
      simp only [sum_from, Finset.mul_sum, mul_assoc, mul_left_comm]
    _ = ∑ x ∈ w.support, ∑ y ∈ u.support, w x * u y * (F x * (N y (m x)).ncard) := by
      simp only [term_eq]
      exact Finset.sum_comm
    _ = ∑ x ∈ w.support, w x * (d * F x) := by
      simp only [sum_to, Finset.mul_sum, mul_assoc, mul_left_comm]
    _ = _ := by simp only [Finset.mul_sum, mul_left_comm]

end MoveCounting

/-!
## The twisted trace of a Hecke operator as a sum over a sample

The moves from a pair `(x, γ)` to a pair `(y, δ)` are the rational `g` with `y⁻¹ * j g * x ∈ K`
and `g⁻¹ * δ * τ g = γ`, where `j` is `V.embFin`.
-/

section TwistedTraceSum

open Subgroup LinearMap New.Variety DoubleCoset New.HasFiniteType Finset

variable {E n : Type} [Field E] [New.CMType E] [Fintype n] [DecidableEq n]
  (V : New.Space E n 1) (κ : New.Weight E)

/-- The twist `ψ ↦ s ∘ ψ ∘ σ⁻¹` maps forms of weight `κ` on `V` to forms. Here `σ` is an
automorphism of the finite adelic group with continuous inverse, `τ` an automorphism of the
rational unitary group with `V.embFin (τ γ) = σ (V.embFin γ)`, and `s` a linear map of the
coefficient space with `s * ρ γ = ρ (τ γ) * s` for `ρ = V.weightRep κ.fst κ.snd`. -/
private lemma New.Space.compLeft_comp_funLeft_mem_forms (σ : Gf E n ≃* Gf E n)
    (hσ_cont : Continuous σ.symm) (τ : U V.J ≃* U V.J)
    (hτ : ∀ γ : U V.J, V.embFin (τ γ) = σ (V.embFin γ))
    (s : (WeylIndex n κ.fst → ℂ) →ₗ[ℂ] WeylIndex n κ.fst → ℂ)
    (hs : ∀ γ : U V.J, s * V.weightRep κ.fst κ.snd γ = V.weightRep κ.fst κ.snd (τ γ) * s)
    {ψ : Gf E n → WeylIndex n κ.fst → ℂ} (hψ : ψ ∈ V.forms κ) :
    (s.compLeft (Gf E n) ∘ₗ funLeft ℂ (WeylIndex n κ.fst → ℂ) σ.symm) ψ ∈ V.forms κ := by
  obtain ⟨hψ_smooth, hψ_equivariant⟩ := hψ
  refine ⟨?_, ?_⟩
  · -- the twist is fixed by the preimage under `σ⁻¹` of the right stabiliser of `ψ`, which is open
    have h_stab : (rightStabilizer ψ).comap σ.symm.toMonoidHom ≤
        rightStabilizer ((s.compLeft (Gf E n) ∘ₗ funLeft ℂ (WeylIndex n κ.fst → ℂ) σ.symm) ψ) := by
      intro k (hk : ∀ g : Gf E n, ψ (g * σ.symm k) = ψ g)
      simp [hk]
    exact Subgroup.isOpen_mono h_stab (hσ_cont.isOpen_preimage _ hψ_smooth)
  · -- equivariance under `τ γ` follows from that of `ψ` under `γ`, by `hτ` and `hs`
    refine τ.toEquiv.forall_congr_right.mp fun γ g ↦ ?_
    simp_all [DFunLike.ext_iff]

/-- The twist `ψ ↦ s ∘ ψ ∘ σ⁻¹` of forms of weight `κ` (a map of `V.forms κ` by `h_forms`) maps
forms fixed by `L` to forms fixed by `L`, when the automorphism `σ` maps `L` onto itself. -/
private lemma New.Space.restrict_compLeft_comp_funLeft_mem_levelSpace {L : Subgroup (Gf E n)}
    (σ : Gf E n ≃* Gf E n) (hσ : L.comap σ = L)
    (s : (WeylIndex n κ.fst → ℂ) →ₗ[ℂ] WeylIndex n κ.fst → ℂ)
    (h_forms : ∀ x ∈ V.forms κ,
      (s.compLeft (Gf E n) ∘ₗ funLeft ℂ (WeylIndex n κ.fst → ℂ) σ.symm) x ∈ V.forms κ)
    {ψ : V.forms κ} (hψ : ψ ∈ levelSpace (V.formTranslation κ) L) :
    ((s.compLeft (Gf E n) ∘ₗ funLeft ℂ (WeylIndex n κ.fst → ℂ) σ.symm).restrict h_forms) ψ ∈
      levelSpace (V.formTranslation κ) L := by
  intro k
  -- `ψ` is fixed by `σ⁻¹ k ∈ L`, and the twist turns right translation by `σ⁻¹ k` into that by `k`
  have h_fixed (g : Gf E n) :
      (ψ : Gf E n → WeylIndex n κ.fst → ℂ) (g * σ.symm k) =
        (ψ : Gf E n → WeylIndex n κ.fst → ℂ) g := by
    simpa using congrFun (congrArg Subtype.val (hψ ⟨σ.symm k, hσ.le (by simp)⟩)) g
  ext g i
  simp [LinearMap.restrict, h_fixed]

open Classical in
/-- A weighted count of transporters. Let `L ≤ J` be subgroups of `Gf E n` of finite type for the
rational points `V.Γf`, and let `S g h` be finite sets with `#(S g h) = #(classAut V.Γf J g)` if `g`
and `h` lie in one double coset (`Γ g J = Γ h J`), and `0` otherwise. Then for every `x` the sum
over the double cosets `i` in `Γ \ G / L` of `#(S x i.out) / #(classAut V.Γf L i.out)` is the
index `[J : L]`. -/
private lemma New.Space.sum_inv_card_classAut_mul_card_eq_relIndex {L J : Subgroup (Gf E n)}
    [HasFiniteType V.Γf L] [HasFiniteType V.Γf J] (hJ : L ≤ J)
    (S : Gf E n → Gf E n → Finset (U V.J))
    (h_card : ∀ g h : Gf E n, #(S g h) =
      if DoubleCoset.mk V.Γf J g = DoubleCoset.mk V.Γf J h then Nat.card (classAut V.Γf J g) else 0)
    (x : Gf E n) :
    ∑ i : DoubleCoset.Quotient V.Γf L,
      (((Nat.card (classAut V.Γf L i.out) : ℚ)⁻¹ : ℚ) : ℂ) * #(S x i.out) = L.relIndex J := by
  -- The sum is the class sum of `#(S x ·)` at level `L`, which is `[J : L]` times that at level
  -- `J`; to the latter only the class of `x` contributes, with value `1`.
  have h_sum : classSum V.Γf L (fun y ↦ (#(S x y) : ℂ)) =
      (L.relIndex J : ℚ) • classSum V.Γf J fun y ↦ (#(S x y) : ℂ) :=
    classSum_eq_relIndex_smul hJ 1 (Subgroup.ext (by simp)) fun y ↦ by
      rw [h_card, h_card, out_eq', mul_one]
  -- `-mem_classAut` and `-MonoidHom.coe_range` keep `classAut` folded, and `↓` moves its order to
  -- the representative of the class of `x` before the sum is split
  have h_one : ∑ i : DoubleCoset.Quotient V.Γf J,
      (((Nat.card (classAut V.Γf J i.out) : ℚ)⁻¹ : ℚ) : ℂ) * #(S x i.out) = 1 := by
    simp [h_card, out_eq', ↓card_classAut_out x, -mem_classAut, -MonoidHom.coe_range]
  simp_rw [classSum, finsum_eq_sum_of_fintype, Rat.smul_def] at h_sum
  rw [h_sum, h_one]
  simp

/-- The `L`-fixed forms of weight `κ` on `V`, seen as functions on `Gf E n`, are the functions that
are equivariant for `ρ = V.weightRep κ.fst κ.snd` (`ψ (V.embFin γ * g) = ρ γ (ψ g)`) and right
invariant under the open subgroup `L`. The factor `Submodule.pi ∅ ⊥` (no vanishing condition) is
the form in which `New.trace_eq_weighted_sum` takes this space. -/
private lemma New.Space.range_domRestrict_levelSpace_eq_coindV_inf {L : Subgroup (Gf E n)}
    (hL_open : L.IsOpen) :
    LinearMap.range ((V.forms κ).subtype.domRestrict (levelSpace (V.formTranslation κ) L)) =
      (V.weightRep κ.fst κ.snd).coindV V.embFin ⊓ Submodule.pi (∅ : Set (Gf E n)) ⊥ ⊓
        levelSpace (rightRegular ℂ (Gf E n) (WeylIndex n κ.fst → ℂ)) L := by
  refine le_antisymm ?_ fun F hF ↦ ?_
  · rintro _ ⟨⟨⟨ψ, hψ_smooth, hψ_equivariant⟩, hψ_fixed⟩, rfl⟩
    exact ⟨⟨hψ_equivariant, by simp⟩, fun k ↦ congrArg Subtype.val (hψ_fixed k)⟩
  · obtain ⟨⟨hF_equivariant, _⟩, hF_fixed⟩ := hF
    exact ⟨⟨⟨F, mem_smoothFunctions_of_eigen _ hL_open hF_fixed, hF_equivariant⟩,
        fun k ↦ Subtype.ext (hF_fixed k)⟩, rfl⟩

/-- Twisted trace formula on a definite space `V`. Let `σ` be an automorphism of `Gf E n` with
continuous inverse, `L ≤ K ≤ stdLevel E n` with `L` open and `σ`-stable, `τ` a lift of `σ` to the
rational unitary group along `j = V.embFin`, and `s * ρ γ = ρ (τ γ) * s` for
`ρ = V.weightRep κ.fst κ.snd`. Then `ψ ↦ s ∘ ψ ∘ σ⁻¹` preserves forms and `L`-fixed forms, and for
some `c ≠ 0` the trace of each Hecke operator `T` of `φ` at level `L` composed with it is a sample
sum of weight `c` over pairs. -/
lemma New.Space.isSampleTotal_twisted_trace {K L : Subgroup (Gf E n)} (σ : Gf E n ≃* Gf E n)
    (hσ_cont : Continuous σ.symm) (hK : K ≤ stdLevel E n) (hL : L ≤ K) (hL_open : L.IsOpen)
    (hσ : L.comap σ = L) (τ : U V.J ≃* U V.J) :
    let j := V.embFin
    let ρ := V.weightRep κ.fst κ.snd
    (∀ γ : U V.J, j (τ γ) = σ (j γ)) →
    ∀ s : (WeylIndex n κ.fst → ℂ) →ₗ[ℂ] WeylIndex n κ.fst → ℂ,
      (∀ γ : U V.J, s * ρ γ = ρ (τ γ) * s) →
      ∃ c ≠ (0 : ℂ), ∃ (h : ∀ x ∈ V.forms κ,
        (s.compLeft (Gf E n) ∘ₗ funLeft ℂ (WeylIndex n κ.fst → ℂ) σ.symm) x ∈ V.forms κ)
        (h' : ∀ x ∈ levelSpace (V.formTranslation κ) L,
          ((s.compLeft (Gf E n) ∘ₗ funLeft ℂ (WeylIndex n κ.fst → ℂ) σ.symm).restrict h)
            x ∈ levelSpace (V.formTranslation κ) L),
        ∀ {φ : Gf E n → ℂ} {T : Module.End ℂ (levelSpace (V.formTranslation κ) L)},
        IsOperatorOf (V.formTranslation κ) L T φ →
        IsSampleTotal
          -- the moves from the pair `p` to the pair `q`
          (fun p q : Gf E n × U V.J ↦
            {g : U V.J | q.fst⁻¹ * j g * p.fst ∈ K ∧ g⁻¹ * q.snd * τ g = p.snd})
          -- the term of a pair
          (fun y : Gf E n × U V.J ↦
            φ (y.fst⁻¹ * j y.snd * σ y.fst) * (ρ y.snd * s).trace ℂ (WeylIndex n κ.fst → ℂ)) c
          -- the trace of `T` composed with `ψ ↦ s ∘ ψ ∘ σ⁻¹`
          ((T *
              ((s.compLeft (Gf E n) ∘ₗ funLeft ℂ (WeylIndex n κ.fst → ℂ) σ.symm).restrict
                h).restrict h').trace ℂ (levelSpace (V.formTranslation κ) L)) := by
  classical
  -- The twist preserves forms and `L`-fixed forms by the two lemmas above. By
  -- `trace_eq_weighted_sum` the trace is a sum over the classes `i` of `Γ \ G / L`, with weights
  -- `1 / #classAut`, and over `γ`. The pairs `(i.out, γ)` with nonzero term form the sample; the
  -- moves from it to a given pair are counted by transporters, whose weighted number is
  -- `c = [K : L]`.
  intro j ρ hτ s hs
  have hK_fin : HasFiniteType V.Γf K := V.hasFiniteType_of_isLevel.of_le hK (isOpen_mono hL hL_open)
  have hL_fin : HasFiniteType V.Γf L := hK_fin.of_le hL hL_open
  refine ⟨L.relIndex K, Nat.cast_ne_zero.2 (hK_fin.isCompact.relIndex_ne_zero hL_open),
    fun ψ hψ ↦ V.compLeft_comp_funLeft_mem_forms κ σ hσ_cont τ hτ s hs hψ,
    fun ψ hψ ↦ V.restrict_compLeft_comp_funLeft_mem_levelSpace κ σ hσ s _ hψ, ?_⟩
  rintro φ T ⟨a, rfl, hT⟩
  -- the transporter `S J g h` is the finite set of rational `γ` with `g⁻¹ * j γ * h ∈ J` (`hS`);
  -- it has `#(classAut V.Γf J g)` elements if `Γ g J = Γ h J` and is empty otherwise (`h_card`)
  have h_transporter (J : Subgroup (Gf E n)) [HasFiniteType V.Γf J] (g h : Gf E n) :
      ∃ S : Finset (U V.J), (∀ γ : U V.J, γ ∈ S ↔ V.embFin γ ∈ V.Γf ∧ g⁻¹ * V.embFin γ * h ∈ J) ∧
        #S = if DoubleCoset.mk V.Γf J g = DoubleCoset.mk V.Γf J h then
          Nat.card (classAut V.Γf J g) else 0 :=
    exists_transporter V.Γf Fact.out .rfl J g h
  choose S hS h_card using h_transporter
  let wt (i : DoubleCoset.Quotient V.Γf L) : ℂ := ((Nat.card (classAut V.Γf L i.out) : ℚ)⁻¹ : ℚ)
  -- `cosetFn L a` lives on finitely many cosets `q`, and each is met by finitely many `γ`
  have h_fin (x : Gf E n) :
      (fun γ : U V.J ↦ cosetFn L a (x⁻¹ * j γ * σ x) *
        (ρ γ * s).trace ℂ (WeylIndex n κ.fst → ℂ)).HasFiniteSupport := by
    refine .mul_left ((cosetFn L a).hasFiniteSupport.preimage' fun q _ ↦
      .ofFinset (S L (x * q.out) (σ x)) ?_) _
    simp [j, hS, mul_assoc, ← QuotientGroup.eq, eq_comm]
  refine ⟨∑ i, ∑ γ ∈ (h_fin i.out).toFinset, .single (i.out, γ) (wt i), ?_, ?_⟩
  · -- apply `trace_eq_weighted_sum` to the forms of level `L`, seen as functions on the group
    refine (trace_eq_weighted_sum (e := j) (ρ := ρ) (s := s) (D := ∅) (a := a)
      (domRestrict (Submodule.subtype _) _) (Subtype.val_injective.comp Subtype.val_injective)
      (V.range_domRestrict_levelSpace_eq_coindV_inf κ hL_open) (fun i ↦ i.out) wt
      (fun i g ↦ S L g i.out)
      -- the side condition stays inline, since it elaborates only against the expected type that
      -- `trace_eq_weighted_sum` supplies
      (by simp [j, hS, mul_assoc]) (by simp) (fun g _ ↦ ?_) σ hσ fun ψ ↦ ?_).2.trans ?_
    · -- at level `L` the weighted number of transporters is `1`
      simpa [wt] using V.sum_inv_card_classAut_mul_card_eq_relIndex le_rfl (S L) (h_card L) g
    · -- `T` acts on the `L`-fixed forms through the group ring element `a`
      have h_T_val (v : levelSpace (V.formTranslation κ) L) :
          ((T v : V.forms κ) : Gf E n → WeylIndex n κ.fst → ℂ) =
            ((V.formTranslation κ).asAlgebraHom a v : V.forms κ) :=
        congrArg Subtype.val (hT v)
      -- `using!`: the twist of `ψ` is `g ↦ s (ψ (σ⁻¹ g))` only by unfolding `restrict`
      simpa [-map_mul, asAlgebraHom_eq_sum_support] using! h_T_val _
    · -- reindex by `τ`, using `hτ` and `hs`
      have h_reindex (x : Gf E n) :
          ∑ᶠ γ : U V.J, cosetFn L a (x⁻¹ * j (τ γ) * σ x) *
              (ρ (τ γ) * s).trace ℂ (WeylIndex n κ.fst → ℂ) =
            ∑ γ ∈ (h_fin x).toFinset,
              cosetFn L a (x⁻¹ * j γ * σ x) * (ρ γ * s).trace ℂ (WeylIndex n κ.fst → ℂ) :=
        (finsum_comp _ τ.bijective).trans (finsum_eq_sum _ (h_fin x))
      simp [j, ρ, ← hτ, hs, h_reindex, mul_sum]
  · -- sort the transporter from `x` to `y` by the second coordinate `g⁻¹ * δ * τ g`
    rintro ⟨y, δ⟩ hy
    have h_fibre (x : Gf E n) : #(S K y x) =
        ∑ γ ∈ (h_fin x).toFinset, #{g ∈ S K y x | g⁻¹ * δ * τ g = γ} := by
      exact card_eq_sum_card_fiberwise fun g hg ↦ (h_fin x).mem_toFinset.2
        (hy (x, g⁻¹ * δ * τ g) g ⟨((hS K y x g).mp hg).right, rfl⟩)
    -- `↓`: `h_fibre` must rewrite the card before `← Set.ncard_coe_finset` turns it into an ncard
    calc _ = ∑ i, wt i * (#(S K y i.out) : ℂ) := by
          simp [j, hS, mul_sum, ← Set.ncard_coe_finset, ↓h_fibre]
      _ = L.relIndex K := V.sum_inv_card_classAut_mul_card_eq_relIndex hL (S K) (h_card K) y

end TwistedTraceSum

/-!
## Base change of weights and twisted characters at the norm

A weight `κ` (`New.Weight`) is a Young diagram `κ.fst` and a power `κ.snd` of the determinant at
each infinite place, and `New.Space.weightRep` is the representation of the rational unitary
group that it defines.
-/

section BaseChangeWeight

open NumberField Matrix ComplexEmbedding ComplexConjugate Finset Module Fin RingHom Equiv Function

variable {E E' n : Type} [Field E] [Field E'] [Algebra E E'] [IsGalois E E'] [Fintype n]
    {σ : Gal(E'/E)}

/-- The base change of a weight: at an infinite place of `E'`, the diagram and the power of the
determinant that `κ` has at the place of `E` below it. -/
noncomputable def New.Weight.baseChange (κ : Weight E) : Weight E' :=
  (fun u ↦ κ.1 (u.comap (algebraMap E E')), fun u ↦ κ.2 (u.comap (algebraMap E E')))

/-- Twisted characters of a base changed weight. For `E'/E` Galois of prime degree `p` with
compatible CM types and `σ ≠ 1` in its Galois group, let `ω` apply `σ` to entries and `ρ` be the
representation of the base change of `κ`. Some `s` satisfies `s * ρ δ = ρ (ω δ) * s`, and when the
twisted norm `δ * ω δ * ⋯ * ω^[p - 1] δ` is the image `j γ` of `γ` over `E`, the trace of `s * ρ δ`
is the character of `κ` at `γ`. -/
lemma New.exists_trace_mul_weightRep_eq_of_twistedNorm_eq [DecidableEq n] (hσ : σ ≠ 1)
    [hp : Fact (finrank E E').Prime] [CMType E] [hCM : CMTypeOver E E'] (κ : Weight E) :
    let j : U (1 : Matrix n n E) →* U (1 : Matrix n n E') :=
      U.map (algebraMap E E') (map_star_CM (algebraMap E E')) (map_one (algebraMap E E').mapMatrix)
    let ω : U (1 : Matrix n n E') →* U (1 : Matrix n n E') := U.mapEnd (map_star_CM σ)
    let ρ : Representation ℂ (U (stdSpace E' n).J) (WeylIndex n κ.baseChange.fst → ℂ) :=
      (stdSpace E' n).weightRep κ.baseChange.fst κ.baseChange.snd
    ∃ s : (WeylIndex n κ.baseChange.fst → ℂ) →ₗ[ℂ] WeylIndex n κ.baseChange.fst → ℂ,
      -- (a) `s` intertwines `ρ` and its twist by `σ`
      (∀ δ : U (stdSpace E' n).J, s * ρ δ = ρ (ω δ) * s) ∧
      -- (b) the twisted character at `δ` is the character of the weight at the norm of `δ`
      ∀ (δ : U (1 : Matrix n n E')) (γ : U (1 : Matrix n n E)),
        twistedNorm ω (Module.finrank E E') δ = j γ →
        (s * ρ δ).trace ℂ (WeylIndex n κ.baseChange.fst → ℂ) =
          ((stdSpace E n).weightRep κ.fst κ.snd γ).trace ℂ (WeylIndex n κ.fst → ℂ) := by
  -- The places of `E'` are pairs (power of `σ`, place of `E`), so `ρ` is the tensor product of the
  -- twists `G l` of the weight `κ` by `σ ^ l`. The operator `s` rotates the factors, and the trace
  -- of `s * ρ δ` is a sum over cycles, the trace of the product of the `G l δ`.
  obtain ⟨k, hE⟩ : ∃ k : ℕ, finrank E E' = k + 1 := Nat.exists_eq_add_one.2 hp.out.pos
  intro j ω ρ
  -- `φ v` extends `(Φ v).comp conj` to `E'`; so does `(Φ u).comp conj` for `u` above `v`.
  let φ (v : InfinitePlace E) : E' →+* ℂ := lift E' ((Φ v).comp conj)
  have h_agree (u : InfinitePlace E') : (φ (u.comap (algebraMap E E'))).comp (algebraMap E E') =
      ((Φ u).comp conj).comp (algebraMap E E') := by
    have hΦ : ∀ x : E, Φ u (algebraMap E E' x) = Φ (u.comap (algebraMap E E')) x := by
      simpa [RingHom.ext_iff] using hCM.eq_chosen_iff (Φ u)
    ext x
    simp [φ, hΦ, starRingEnd_apply (R := E), starRingEnd_apply (R := E')]
  -- Two embeddings that agree on `E` differ by a power of `σ`: `(Φ u).comp conj = φ v ∘ σ ^ i u`.
  have h_pow_bij : Bijective fun l : Fin (k + 1) ↦ σ ^ (l : ℕ) := by
    simpa [← hE] using bijective_pow_of_ne_one_of_prime_finrank hσ
  have h_exists (u : InfinitePlace E') : ∃ l : Fin (k + 1),
      (φ (u.comap (algebraMap E E'))).comp ((σ ^ (l : ℕ) : Gal(E'/E)) : E' →+* E') =
        (Φ u).comp conj :=
    (AlgEquiv.symm_bijective.comp h_pow_bij).surjective.exists.mp
      (exists_comp_symm_eq_of_comp_eq _ _ (h_agree u))
  choose i hi using h_exists
  -- `u ↦ (i u, v)` is injective, so bijective by counting: the infinite places are unramified.
  have h_unram : IsUnramifiedAtInfinitePlaces E E' := ⟨by simp [InfinitePlace.IsUnramified]⟩
  have h_bij : Bijective fun u ↦
      (⟨i u, u.comap (algebraMap E E')⟩ : Σ _ : Fin (k + 1), InfinitePlace E) := by
    refine (Nat.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩
    · -- equal pairs give `(Φ u).comp conj = (Φ u').comp conj` by `hi`; cancel `conj`, then `mk_Φ`
      intro u u' h_pair
      grind [mk_Φ, cancel_right, surjective]
    · simp [mul_comm, hE, h_unram.card_infinitePlace]
  let e : InfinitePlace E' ≃ Σ _ : Fin (k + 1), InfinitePlace E := ofBijective _ h_bij
  -- A basis index of `ρ` is a family of `k + 1` basis indices of the weight `κ`.
  let A : WeylIndex n (κ.baseChange : Weight E').fst ≃ (Fin (k + 1) → WeylIndex n κ.fst) :=
    .trans (.symm (.piCongrLeft' _ e.symm)) (.piCurry _)
  -- `G l` is the weight `κ` at the embeddings `φ v ∘ σ ^ l`.
  let G (l : ℕ) : GL n E' →* Matrix (WeylIndex n κ.fst) (WeylIndex n κ.fst) ℂ :=
    (weylRep κ.fst κ.snd).comp (.pi fun v ↦ GeneralLinearGroup.map ((φ v).comp (σ ^ l).toRingHom))
  have h_G_succ (l : ℕ) (δ : U (1 : Matrix n n E')) : G l (ω δ) = G (l + 1) δ := rfl
  have h_tensor (δ : U (1 : Matrix n n E')) :
      ρ δ = toLin' (of fun a b ↦ ∏ l : Fin (k + 1), G l δ (A a l) (A b l)) := by
    refine (LinearMap.ext (stdSpace_weightRep_apply δ)).trans (congrArg _ (ext ?_))
    -- Schur matrices and determinants are products over the places, reindexed by `e`; the two
    -- sides then agree entrywise by the definitions of `e`, `A` and `κ.baseChange`.
    simp [A.forall_congr_left, ← hi, G, weylRep, schur_apply_eq_prod (Φ := InfinitePlace _),
      prod_smul, ← Fintype.prod_sigma', ← e.prod_comp]
    exact fun _ _ ↦ rfl
  have h_norm (m : ℕ) (δ : U (1 : Matrix n n E')) :
      twistedNorm ω (m + 1) δ = δ * twistedNorm ω m (ω δ) := by simp [twistedNorm]
  -- Summing over the inner vertices of a cycle multiplies the matrices.
  have h_cycle (m : ℕ) (δ : U (1 : Matrix n n E'))
      (M : Matrix (WeylIndex n κ.fst) (WeylIndex n κ.fst) ℂ) :
      trace (M * G 0 ((twistedNorm ω m (ω δ) : U (1 : Matrix n n E')) : GL n E')) =
        ∑ x : Fin (m + 1) → WeylIndex n κ.fst,
          M (x (last m)) (x 0) * ∏ l : Fin m, G (l + 1) δ (x l.castSucc) (x l.succ) := by
    induction m generalizing δ M with
    | zero =>
      simp [twistedNorm, trace, reindex_equiv (consEquiv _), Fintype.sum_prod_type_right,
        univ_eq_empty]
    | succ m ih =>
      -- Use `ih` for `ω δ` and `M * G 0 (ω δ)`; by definition `G l (ω δ) = G (l + 1) δ`.
      simp [h_norm, ← (consEquiv fun _ : Fin (m + 2) ↦ _).sum_comp, ← mul_assoc, mul_apply, sum_mul,
        Fintype.sum_prod_type_right, prod_univ_succ, ih]
      rfl
  -- `s` permutes the basis by rotating the index `Fin (k + 1)`.
  refine ⟨(submatrix 1 (A.trans ((finRotate _).piCongrLeft' _)) A).toLin',
    fun (δ : U (1 : Matrix n n E')) ↦ ?_, fun δ γ h_norm_eq ↦ ?_⟩
  · -- Rotate the product; the last factor returns to the first because `σ ^ (k + 1) = 1`.
    simp_rw [h_tensor, End.mul_eq_comp, ← toLin'_mul, mul_submatrix_one, one_submatrix_mul]
    refine congrArg _ (ext fun a b ↦ (Equiv.prod_comp (finRotate _) _).symm.trans ?_)
    simp only [h_G_succ]
    simp [G, val_add, ← hE, ← IsGalois.card_aut_eq_finrank]
  · -- Both traces are the sum of `h_cycle` for `M = G 0 δ`.
    have h_char : ((stdSpace E n).weightRep κ.fst κ.snd γ).trace ℂ (WeylIndex n κ.fst → ℂ) =
        trace (G 0 (j γ)) := by
      simp [LinearMap.ext (g := toLin' _) (stdSpace_weightRep_apply γ), G, φ, j, U.map, weylRep,
        Units.smul_def, comp_def]
    -- by `h_norm_eq`, `j γ = δ * twistedNorm ω k (ω δ)`
    rw [h_char, ← h_norm_eq, hE, h_norm, Subgroup.coe_mul, (G 0).map_mul, h_cycle k δ (G 0 δ)]
    -- the trace of `s * ρ δ` unfolds to the same cycle sum
    simp_rw [h_tensor, End.mul_eq_comp, ← toLin'_mul, trace_toLin'_eq, one_submatrix_mul]
    simp [trace, ← A.symm.sum_comp, prod_univ_succ, ← cycleRange_last]

end BaseChangeWeight

/-!
## The twisted trace identity for matching pairs

Conventions: `New.galoisGf σ` is the action of `σ` on `New.Gf E' n`, `New.baseChangeGf` the
inclusion of `New.Gf E n` into `New.Gf E' n`, and `New.IsMatchingPair` the matching condition
between a function `f` over `E` and a function `φ` over `E'` (on `New.Gf E' n`, written `U 1`).
-/

section TwistedTraceIdentity

open Matrix Polynomial Module Function New U Space

attribute [local implicit_reducible] stdSpace

/-- Let `x` and `δ` be finite adelic unitary points over `E'`. The twisted norm (for the action
`galoisGf σ` of `σ`, with `[E' : E]` factors) of the twisted conjugate `x⁻¹ * δ * σ x` is the
conjugate `x⁻¹ * N δ * x` of the twisted norm `N δ` of `δ`. This uses `σ ^ [E' : E] = 1`. -/
lemma New.twistedNorm_inv_mul_mul_galoisGf {E E' n : Type*} [Field E] [CMType E] [Field E']
    [Algebra E E']
    [Fintype n] [DecidableEq n] {σ : Gal(E'/E)} [CMTypeOver E E'] [IsGalois E E'] (x δ : Gf E' n) :
    twistedNorm (galoisGf σ) (finrank E E') (x⁻¹ * δ * galoisGf σ x) =
      x⁻¹ * twistedNorm (galoisGf σ) (finrank E E') δ * x := by
  -- `galoisGf σ` applies `adeleMap σ` to the entries, so its `k`-th iterate applies
  -- `adeleMap σ ^ k`.
  have h_iter (k : ℕ) (y : Gf E' n) :
      ((galoisGf σ)^[k] y).val = y.val.map (adeleMap ↑σ ^ k) := by
    induction k generalizing y with
    | zero => rfl
    | succ k ih => exact ih (galoisGf σ y)
  refine twistedNorm_conj _ _ (Subtype.ext ?_) _
  rw [h_iter, adeleMap_pow_finrank_eq_one]
  rfl

/-- A global completion of a norm root `z` of the characteristic polynomial `P` of a rational
unitary `δ` over `E'`, when `σ` fixes `P`: for some rational `z₀` and adelic `b`,
`x = z₀ * σ b * z` is invertible at `e ν` for every rational `ν` of characteristic polynomial `P`,
and every root quotient `r` of `x` at `e ν` (`r * x(e ν)ᴴ = x(e ν)`) is one of `b` (`e` the
inclusion of rational into adelic points). -/
private lemma New.exists_isUnit_aeval_and_isRootQuotient_le {E E' n : Type} [Field E] [CMType E]
    [Field E'] [Algebra E E'] [Fintype n] [DecidableEq n] {σ : Gal(E'/E)} (hσ : σ ≠ 1)
    {μ : (𝔸f E)ˣ →* ℂˣ} [CMTypeOver E E'] [IsStep (E := E) E' μ] {δ : U (1 : Matrix n n E')}
    (h_fixed : σ • (δ : Matrix n n E').charpoly = (δ : Matrix n n E').charpoly)
    {z : (𝔸f E')[X]} (hz : IsNormRoot n (adeleMap σ) (finrank E E') 1 (kerCompNorm E' μ)
      ((δ : Matrix n n E').charpoly.map (algebraMap E' (𝔸f E'))) z) :
    let e : U (1 : Matrix n n E') →* Gf E' n :=
      U.map (algebraMap E' (𝔸f E')) (fun x : E' ↦ (star_algebraMap_finAdele x).symm)
        (map_one (algebraMap E' (𝔸f E')).mapMatrix)
    ∃ (z₀ : E'[X]) (b : (𝔸f E')[X]), ∀ ν : U (1 : Matrix n n E'),
      (ν : Matrix n n E').charpoly = (δ : Matrix n n E').charpoly →
        let x : (𝔸f E')[X] := z₀.map (algebraMap E' (𝔸f E')) * (b.map (adeleMap ↑σ) * z)
        IsUnit (aeval (e ν : Matrix n n (𝔸f E')) x) ∧
          IsRootQuotient (e ν) x ≤ IsRootQuotient (e ν) b := by
  intro e
  have hσ_pow : σ ^ finrank E E' = 1 := by simp [← IsGalois.card_aut_eq_finrank]
  obtain ⟨z₀, b, hb⟩ := exists_global_root Fact.out hσ_pow hσ ⟨δ, rfl⟩ h_fixed hz
  rw [mul_comm z] at hb
  refine ⟨z₀, b, fun ν hν ↦ hb (e ν) ?_⟩
  -- A unitary matrix is normal, so the radical of its characteristic polynomial kills it.
  exact (map_aeval_matrix _ _ _).symm.trans (by simp [← hν])

/-- Let `C` be a class of `σ`-fixed polynomials over `E'` with norm roots `z P` (`IsNormRoot`: among
other things, the twisted norm `z * σ z * ⋯` of `z P` has root quotient `g` at each adelic `g` of
characteristic polynomial `P`). To each rational `ν` with characteristic polynomial `q ν` in `C`
belong a rational `A ν` and an adelic `B ν`, compatible with conjugation, such that for `δ` with
`δ * ω ν = ν * δ` (`ω` the action of `σ`) a root quotient `r` of `z (q ν)` at `e ν`
(`r * z(e ν)ᴴ = z(e ν)`) makes `r⁻¹ * e δ` the twisted conjugate of `e (A ν * δ)` by `B ν`; `e`
includes rational into finite adelic unitary points, and `U 1` is the rational unitary group
`U (1 : Matrix n n E')`. -/
lemma New.exists_isRootQuotient_of_isNormRoot {E E' n : Type} [Field E] [CMType E] [Field E']
  [Algebra E E']
    [Fintype n] [DecidableEq n] {σ : Gal(E'/E)} (hσ : σ ≠ 1) {μ : (𝔸f E)ˣ →* ℂˣ} [CMTypeOver E E']
    [IsStep (E := E) E' μ] {C : E'[X] → Prop} {z : E'[X] → (𝔸f E')[X]}
    (hC : ∀ P : E'[X], C P → σ • P = P) (hz : ∀ P : E'[X], C P →
      IsNormRoot n (adeleMap σ) (finrank E E') 1 (kerCompNorm E' μ) (P.map (algebraMap E' (𝔸f E')))
        (z P)) :
    let e : U (1 : Matrix n n E') →* Gf E' n :=
      U.map (algebraMap E' (𝔸f E')) (fun x : E' ↦ (star_algebraMap_finAdele x).symm)
        (map_one (algebraMap E' (𝔸f E')).mapMatrix)
    let ω : U (1 : Matrix n n E') →* U (1 : Matrix n n E') := U.mapEnd (map_star_CM σ)
    let q (δ : U (1 : Matrix n n E')) : E'[X] := (δ : Matrix n n E').charpoly
    ∃ (A : U (1 : Matrix n n E') → U (1 : Matrix n n E')) (B : U (1 : Matrix n n E') → Gf E' n),
      (∀ {ν ν' : U (1 : Matrix n n E')} (g : U (1 : Matrix n n E')), C (q ν) → SemiconjBy g ν ν' →
        C (q ν') ∧ A ν' = g * A ν * g⁻¹ ∧ B ν' = e g * B ν * (e g)⁻¹) ∧
      ∀ {ν δ : U (1 : Matrix n n E')}, C (q ν) → SemiconjBy δ (ω ν) ν → ∃ r : Gf E' n,
        IsUnit (aeval (e ν : Matrix n n (𝔸f E')) (z (q ν))) ∧
        IsRootQuotient (e ν) (z (q ν)) r ∧
        r⁻¹ * e δ = (B ν)⁻¹ * e (A ν * δ) * galoisGf σ (B ν) := by
  intro e ω q
  have e_ω (δ : U 1) : e (ω δ) = galoisGf σ (e δ) := by
    simp +zetaDelta [U.map, Gf.val_ext_iff, Units.ext_iff, ← ext_iff]
  -- `exists_isUnit_aeval_and_isRootQuotient_le` completes `z P` to `x = z₀ * σ b * z P` with `z₀`
  -- rational and `x` invertible at `e ν` when `P = q ν`. Put `A ν = z₀(ν) / z₀(ν)ᴴ` and
  -- `B ν = x(ν) / x(ν)ᴴ`, the roots (`IsRootQuotient`) for `z₀` and `x`; `B ν` is also a root for
  -- `b`.
  have h_global (P : E'[X]) (hP : ∃ δ : U 1, q δ = P ∧ C (q δ)) :
      ∃ (z₀ : E'[X]) (b : (𝔸f E')[X]), ∀ ν : U 1, q ν = P →
        let x : (𝔸f E')[X] := z₀.map (algebraMap E' (𝔸f E')) * (b.map (adeleMap ↑σ) * z P)
        IsUnit (aeval (e ν : Matrix n n (𝔸f E')) x) ∧
          IsRootQuotient (e ν) x ≤ IsRootQuotient (e ν) b := by
    obtain ⟨δ, rfl, hδ⟩ := hP
    exact New.exists_isUnit_aeval_and_isRootQuotient_le hσ (hC _ hδ) (hz _ hδ)
  choose! z₀ b hb using h_global
  replace hb {ν : U 1} (hν_C : C (q ν)) := hb (q ν) ⟨ν, rfl, hν_C⟩ ν rfl
  -- `x(e ν)` is a product of commuting matrices, so each factor is invertible.
  have h_unit {ν : U 1} (hν_C : C (q ν)) :
      IsUnit (aeval (e ν : Matrix n n (𝔸f E')) (z₀ (q ν))) ∧
        IsUnit (aeval (e ν : Matrix n n (𝔸f E')) ((b (q ν)).map (adeleMap (σ : E' →+* E')))) ∧
        IsUnit (aeval (e ν : Matrix n n (𝔸f E')) (z (q ν))) := by
    simpa using (hb hν_C).left
  have h_unit_rat {ν : U 1} (hν_C : C (q ν)) : IsUnit (aeval (ν : Matrix n n E') (z₀ (q ν))) := by
    -- `e ν` is `ν` with `algebraMap E' (𝔸f E')` applied to the entries.
    refine isUnit_of_mapMatrix (algebraMap E' (𝔸f E')) ?_
    rw [RingHom.mapMatrix_apply, map_aeval_matrix]
    simpa [e, U.map] using (h_unit hν_C).left
  -- `A ν` and `B ν` are the unique roots for `z₀` at `ν` and for `x` at `e ν`.
  choose! A hA hA_uniq using fun ν (hν_C : C (q ν)) ↦ existsUnique_isRootQuotient (h_unit_rat hν_C)
  choose! B hB hB_uniq using fun ν (hν_C : C (q ν)) ↦ existsUnique_isRootQuotient (hb hν_C).left
  refine ⟨A, B, fun {ν ν'} g hν_C hg ↦ ?_, fun {ν δ} hν_C hν ↦ ?_⟩
  · -- Conjugate elements have the same `q`, and roots are unique.
    have hq : q ν = q ν' := by simp [q, ← mul_inv_eq_of_eq_mul hg]
    have hν'_C : C (q ν') := by rwa [← hq]
    refine ⟨hν'_C, (hA_uniq _ hν'_C _ ?_).symm, (hB_uniq _ hν'_C _ ?_).symm⟩
    · simpa [← hq] using isRootQuotient_conj hg.symm (hA ν hν_C)
    · simpa [← hq] using isRootQuotient_conj (hg.map e).symm (hB ν hν_C)
  · -- Roots multiply: the roots for the three factors of `x` have product `B ν`.
    obtain ⟨-, -, h_unit_z⟩ := h_unit hν_C
    obtain ⟨r, hr, -⟩ := existsUnique_isRootQuotient h_unit_z
    have h_comm : e ν * e δ = e δ * galoisGf σ (e ν) := by
      simpa only [map_mul, e_ω] using congrArg e hν.symm
    have h_σb :
        IsRootQuotient (e ν) ((b (q ν)).map (adeleMap ↑σ)) ↑(e δ * galoisGf σ (B ν) * (e δ)⁻¹) :=
      isRootQuotient_conj h_comm (isRootQuotient_map _ ((hb hν_C).right _ (hB ν hν_C)))
    have h_prod : e (A ν) * (e δ * galoisGf σ (B ν) * (e δ)⁻¹ * r) = B ν :=
      hB_uniq _ hν_C _ ((isRootQuotient_map _ (hA ν hν_C)).mul (h_σb.mul hr))
    refine ⟨r, h_unit_z, hr, ?_⟩
    rw [map_mul, mul_assoc, eq_inv_mul_iff_mul_eq]
    nth_rw 1 [← h_prod]
    group

section MatchingRoots

variable {E E' n : Type} [Field E] [CMType E] [Field E'] [Algebra E E'] [Fintype n] [DecidableEq n]
  [CMTypeOver E E']

/-- Facts about the maps between unitary points over `E` and `E'` in `New.twisted_trace_identity`:
`j` is base change of rational points from `E` to `E'`, `ω` the action of `σ` on rational points
over `E'`, `e` the inclusion of rational into finite adelic points. The maps `j` and `e` are
injective, the three maps are compatible with `σ` and with base change, Galois descent holds for
adelic and for rational points, and a rational cocycle of twisted norm one that splits adelically
splits (Hasse principle). -/
private structure New.IsBaseChangeMaps (σ : Gal(E'/E))
    (j : U (1 : Matrix n n E) →* U (1 : Matrix n n E'))
    (ω : U (1 : Matrix n n E') →* U (1 : Matrix n n E')) (e : U (1 : Matrix n n E') →* Gf E' n) :
    Prop where
  j_injective : Injective j
  e_injective : Injective e
  map_apply_eq_galoisGf (δ : U (1 : Matrix n n E')) : e (ω δ) = galoisGf σ (e δ)
  map_apply_eq_baseChangeGf (γ : U (1 : Matrix n n E)) :
    e (j γ) = baseChangeGf ((stdSpace E n).embFin γ)
  map_apply_eq_self (γ : U (1 : Matrix n n E)) : ω (j γ) = j γ
  galoisGf_baseChangeGf (g : Gf E n) : galoisGf σ (baseChangeGf g) = baseChangeGf g
  /-- Galois descent for finite adelic points. -/
  exists_baseChangeGf_eq (g : Gf E' n) : galoisGf σ g = g → ∃ k : Gf E n, baseChangeGf k = g
  /-- Galois descent for rational points. -/
  exists_j_eq (δ : U (1 : Matrix n n E')) : ω δ = δ → ∃ γ : U (1 : Matrix n n E), j γ = δ
  /-- The Hasse principle: a rational cocycle of twisted norm one that splits adelically splits. -/
  exists_ω_eq_inv_mul (s : U (1 : Matrix n n E')) (u : Gf E' n) :
    e s = u * (galoisGf σ u)⁻¹ → twistedNorm ω (finrank E E') s = 1 →
      ∃ g : U (1 : Matrix n n E'), ω g = s⁻¹ * g

/-- Facts about a matching pair `(f, φ)` used by the double counting in
`New.twisted_trace_identity`. `Good ν` marks the rational `ν` over `E'` whose characteristic
polynomial occurs in the matching condition, with a rational root quotient `A ν` and an adelic one
`B ν`. The fields: twisted invariance of `φ` under `K`, goodness at non-zero terms, compatibility
with conjugation, the twisted norm through `A ν` and `B ν`, and matching of values and of `K`. -/
private structure New.IsMatchingRoots (σ : Gal(E'/E)) (K : Subgroup (Gf E' n)) (f : Gf E n → ℂ)
    (φ : U (1 : Matrix n n (𝔸f E')) → ℂ) (j : U (1 : Matrix n n E) →* U (1 : Matrix n n E'))
    (ω : U (1 : Matrix n n E') →* U (1 : Matrix n n E')) (e : U (1 : Matrix n n E') →* Gf E' n)
    (Good : U (1 : Matrix n n E') → Prop) (A : U (1 : Matrix n n E') → U (1 : Matrix n n E'))
    (B : U (1 : Matrix n n E') → Gf E' n) : Prop where
  apply_inv_mul_mul_galoisGf (k : Gf E' n) (hk : k ∈ K) (δ : Gf E' n) :
    φ (k⁻¹ * δ * galoisGf σ k) = φ δ
  good_of_apply_ne_zero (x : Gf E n) (γ : U (1 : Matrix n n E)) :
    f (x⁻¹ * (stdSpace E n).embFin γ * x) ≠ 0 → Good (j γ)
  good_twistedNorm (x : Gf E' n) (δ : U (1 : Matrix n n E')) :
    φ (x⁻¹ * e δ * galoisGf σ x) ≠ 0 → Good (twistedNorm ω (finrank E E') δ)
  good_and_conj_of_semiconjBy {ν ν' : U (1 : Matrix n n E')} (g : U (1 : Matrix n n E')) :
    Good ν → SemiconjBy g ν ν' →
    Good ν' ∧ A ν' = g * A ν * g⁻¹ ∧ B ν' = e g * B ν * (e g)⁻¹
  map_twistedNorm_eq {ν δ : U (1 : Matrix n n E')} : Good ν → SemiconjBy δ (ω ν) ν →
    e (twistedNorm ω (finrank E E') δ) =
      e ν * ((B ν)⁻¹ * e (twistedNorm ω (finrank E E') (A ν * δ)) * B ν)
  exists_inv_mul_eq {ν δ : U (1 : Matrix n n E')} : Good ν → SemiconjBy δ (ω ν) ν →
    ∃ r : Gf E' n, r⁻¹ * e δ = (B ν)⁻¹ * e (A ν * δ) * galoisGf σ (B ν) ∧
      ∀ y : Gf E' n,
        (∀ g : Gf E n, baseChangeGf g = y⁻¹ * e ν * y →
          twistedNorm (galoisGf σ) (finrank E E') (y⁻¹ * r * y) = y⁻¹ * e ν * y →
          f g = φ (y⁻¹ * r * y)) ∧
        ∀ δ' : Gf E' n, twistedNorm (galoisGf σ) (finrank E E') δ' = y⁻¹ * e ν * y → φ δ' ≠ 0 →
          (y⁻¹ * r * y)⁻¹ * δ' ∈ K

variable {σ : Gal(E'/E)} {j : U (1 : Matrix n n E) →* U (1 : Matrix n n E')}
  {ω : U (1 : Matrix n n E') →* U (1 : Matrix n n E')} {e : U (1 : Matrix n n E') →* Gf E' n}
  {K : Subgroup (Gf E' n)} {f : Gf E n → ℂ} {φ : U (1 : Matrix n n (𝔸f E')) → ℂ}
  {Good : U (1 : Matrix n n E') → Prop} {A : U (1 : Matrix n n E') → U (1 : Matrix n n E')}
  {B : U (1 : Matrix n n E') → Gf E' n}

/-- If `δ * ω ν = ν * δ` for the action `ω` of `σ` on rational points over `E'`, then the
characteristic polynomial of `ν` is fixed by `σ`. -/
private lemma New.smul_charpoly_eq_of_semiconjBy {ν δ : U (1 : Matrix n n E')}
    (hν : SemiconjBy δ (U.mapEnd (map_star_CM σ) ν) ν) :
    σ • (ν : Matrix n n E').charpoly = (ν : Matrix n n E').charpoly := by
  -- `ω ν` is conjugate to `ν` by `δ`, and its matrix is that of `ν` with `σ` on the entries.
  have h_map : ((ν : Matrix n n E').map σ).charpoly = (ν : Matrix n n E').charpoly := by
    simpa [U.map, ← mul_assoc] using
      congrArg (fun g : U (1 : Matrix n n E') ↦ ((δ⁻¹ * g : U 1) : Matrix n n E').charpoly) hν.eq
  rwa [smul_eq_map, ← charpoly_map]

/-- The maps of `New.twisted_trace_identity` satisfy `IsBaseChangeMaps` for `σ ≠ 1` over a step
`E'/E`: base change `j` of rational points, the action `ω` of `σ` on rational points over `E'`, and
the inclusion `e` of rational into finite adelic points. -/
private lemma New.isBaseChangeMaps (μ : (𝔸f E)ˣ →* ℂˣ) [IsStep (E := E) E' μ] (hσ : σ ≠ 1) :
    let j : U (1 : Matrix n n E) →* U (1 : Matrix n n E') :=
      U.map (algebraMap E E') (map_star_CM (algebraMap E E')) (map_one (algebraMap E E').mapMatrix)
    let ω : U (1 : Matrix n n E') →* U (1 : Matrix n n E') := U.mapEnd (map_star_CM σ)
    let e : U (1 : Matrix n n E') →* Gf E' n :=
      U.map (algebraMap E' (𝔸f E')) (fun x : E' ↦ (star_algebraMap_finAdele x).symm)
        (map_one (algebraMap E' (𝔸f E')).mapMatrix)
    New.IsBaseChangeMaps σ j ω e := by
  intro j ω e
  have ⟨j_inj, e_inj, e_ω, e_j, ω_j, σ_bc⟩ :
      Injective j ∧ Injective e ∧ (∀ δ : U (1 : Matrix n n E'), e (ω δ) = galoisGf σ (e δ)) ∧
      (∀ γ : U (1 : Matrix n n E), e (j γ) = baseChangeGf ((stdSpace E n).embFin γ)) ∧
      (∀ γ : U (1 : Matrix n n E), ω (j γ) = j γ) ∧
      ∀ g : Gf E n, galoisGf σ (baseChangeGf g) = baseChangeGf g := by
    simp +zetaDelta [baseChangeGf, U.map, DFunLike.ext_iff, Gf.val_ext_iff, Units.ext_iff,
      ← ext_iff, Function.Injective, RingHom.comp]
  refine ⟨j_inj, e_inj, e_ω, e_j, ω_j, σ_bc, fun g hg ↦ ?_, fun δ hδ ↦ ?_,
    fun s u hs hN ↦ hasse_principle_coboundary hσ u hs hN⟩
  · -- Galois descent for adelic points, entry by entry.
    have h_entry (a b : n) : adeleMap (σ : E' →+* E') ((g : Matrix n n (𝔸f E')) a b) =
        (g : Matrix n n (𝔸f E')) a b :=
      congr_fun₂ (congrArg (fun h : Gf E' n ↦ (h : Matrix n n (𝔸f E'))) hg) a b
    have h_desc (a b : n) : (g : Matrix n n (𝔸f E')) a b ∈ (finAdeleIncl E E').range :=
      mem_range_finAdeleIncl_of_adeleMap_eq hσ (h_entry a b)
    choose M hM using h_desc
    obtain ⟨k, -, hk⟩ := mem_range_map (adeleMap_star (algebraMap E E')) (adeleMap_injective _)
      isUnit_one _ (M := M) (ext hM)
    exact ⟨k, hk⟩
  · -- Galois descent for rational points, entry by entry.
    have h_entry (a b : n) : σ ((δ : Matrix n n E') a b) = (δ : Matrix n n E') a b :=
      congr_fun₂ (congrArg (fun h : U (1 : Matrix n n E') ↦ (h : Matrix n n E')) hδ) a b
    have h_desc (a b : n) : (δ : Matrix n n E') a b ∈ (algebraMap E E').range :=
      mem_range_algebraMap_of_fixed_of_prime hσ (h_entry a b)
    choose M hM using h_desc
    obtain ⟨γ, -, hγ⟩ :=
      mem_range_map _ (algebraMap E E').injective isUnit_one _ (M := M) (ext hM)
    exact ⟨γ, hγ⟩

/-- The twisted norm for `galoisGf σ` of a twisted conjugate `x⁻¹ * e δ * σ x` of a rational point
`δ` over `E'` is the conjugate by `x` of `e` applied to the twisted norm of `δ` for `ω`. -/
private lemma New.IsBaseChangeMaps.twistedNorm_conj [IsGalois E E']
    (H : New.IsBaseChangeMaps σ j ω e) (x : Gf E' n) (δ : U (1 : Matrix n n E')) :
    twistedNorm (galoisGf σ) (finrank E E') (x⁻¹ * e δ * galoisGf σ x) =
      x⁻¹ * e (twistedNorm ω (finrank E E') δ) * x := by
  rw [map_twistedNorm e H.map_apply_eq_galoisGf, twistedNorm_inv_mul_mul_galoisGf]

/-- A rational point `δ` over `E'` and its twisted norm `ν` for `ω` satisfy `δ * ω ν = ν * δ`. -/
private lemma New.IsBaseChangeMaps.semiconjBy_twistedNorm [IsGalois E E']
    (H : New.IsBaseChangeMaps σ j ω e) (δ : U (1 : Matrix n n E')) :
    SemiconjBy δ (ω (twistedNorm ω (finrank E E') δ)) (twistedNorm ω (finrank E E') δ) := by
  apply H.e_injective
  -- Conjugate the twisted norm of `e δ` by `e δ` itself.
  have h_conj : e δ * twistedNorm (galoisGf σ) (finrank E E') ((e δ)⁻¹ * e δ * galoisGf σ (e δ)) =
      e δ * ((e δ)⁻¹ * e (twistedNorm ω (finrank E E') δ) * e δ) := by
    rw [H.twistedNorm_conj]
  simpa [← H.map_apply_eq_galoisGf, ← map_twistedNorm e H.map_apply_eq_galoisGf,
    map_twistedNorm ω (fun _ ↦ rfl), mul_assoc] using h_conj

/-- `(A ν)⁻¹` commutes with a good `ν`: take `g = ν' = ν` in
`IsMatchingRoots.good_and_conj_of_semiconjBy`. -/
private lemma New.IsMatchingRoots.commute_inv (R : New.IsMatchingRoots σ K f φ j ω e Good A B)
    {ν : U (1 : Matrix n n E')} (h_good : Good ν) : Commute (A ν)⁻¹ ν := by
  obtain ⟨-, hA, -⟩ := R.good_and_conj_of_semiconjBy ν h_good rfl
  exact Commute.inv_left (mul_eq_of_eq_mul_inv hA)

/-- For a good base change `j γ`, `(A (j γ))⁻¹ * ω (j γ) = j γ * (A (j γ))⁻¹` (`ω` fixes `j γ`). -/
private lemma New.IsMatchingRoots.semiconjBy_inv (R : New.IsMatchingRoots σ K f φ j ω e Good A B)
    (H : New.IsBaseChangeMaps σ j ω e) {γ : U (1 : Matrix n n E)} (h_good : Good (j γ)) :
    SemiconjBy (A (j γ))⁻¹ (ω (j γ)) (j γ) := by
  rw [H.map_apply_eq_self]
  exact R.commute_inv h_good

/-- `B ν` commutes with `e ν` for a good `ν`: take `g = ν' = ν` in
`IsMatchingRoots.good_and_conj_of_semiconjBy`. -/
private lemma New.IsMatchingRoots.commute_map (R : New.IsMatchingRoots σ K f φ j ω e Good A B)
    {ν : U (1 : Matrix n n E')} (h_good : Good ν) : Commute (B ν) (e ν) := by
  obtain ⟨-, -, hB⟩ := R.good_and_conj_of_semiconjBy ν h_good rfl
  exact mul_eq_of_eq_mul_inv hB

/-- For a good base change `j γ`, the twisted norm of `(A (j γ))⁻¹` is `j γ`. -/
private lemma New.IsMatchingRoots.twistedNorm_inv (R : New.IsMatchingRoots σ K f φ j ω e Good A B)
    (H : New.IsBaseChangeMaps σ j ω e) {γ : U (1 : Matrix n n E)} (h_good : Good (j γ)) :
    twistedNorm ω (finrank E E') (A (j γ))⁻¹ = j γ := by
  apply H.e_injective
  rw [R.map_twistedNorm_eq h_good (R.semiconjBy_inv H h_good)]
  simp [twistedNorm]

/-- For a good base change `j γ` and `x` over `E`, the value of `f` at `x⁻¹ * γ * x` is the value of
`φ` at the twisted conjugate of `e (A (j γ))⁻¹` by `y = (B (j γ))⁻¹ * baseChangeGf x`. -/
private lemma New.IsMatchingRoots.apply_inv_mul_embFin_mul_eq [IsGalois E E']
    (R : New.IsMatchingRoots σ K f φ j ω e Good A B) (H : New.IsBaseChangeMaps σ j ω e)
    (x : Gf E n) (γ : U (1 : Matrix n n E)) (h_good : Good (j γ)) :
    f (x⁻¹ * (stdSpace E n).embFin γ * x) =
      φ (((B (j γ))⁻¹ * baseChangeGf x)⁻¹ * e (A (j γ))⁻¹ *
        galoisGf σ ((B (j γ))⁻¹ * baseChangeGf x)) := by
  -- Take `δ = (A (j γ))⁻¹` in `exists_inv_mul_eq`; its twisted norm is `j γ`.
  have h_semi : SemiconjBy (A (j γ))⁻¹ (ω (j γ)) (j γ) := R.semiconjBy_inv H h_good
  obtain ⟨r, hrδ, h_match⟩ := R.exists_inv_mul_eq h_good h_semi
  have h_comm_B : Commute (B (j γ)) (e (j γ)) := R.commute_map h_good
  set y : Gf E' n := (B (j γ))⁻¹ * baseChangeGf x
  have hr_eq : r = e (A (j γ))⁻¹ * (galoisGf σ (B (j γ)))⁻¹ * B (j γ) := by
    simpa [eq_inv_mul_iff_mul_eq, eq_mul_inv_iff_mul_eq, mul_assoc] using congrArg Inv.inv hrδ
  have h_eq : y⁻¹ * r * y = y⁻¹ * e (A (j γ))⁻¹ * galoisGf σ y := by
    simp [y, hr_eq, H.galoisGf_baseChangeGf, mul_assoc]
  have h_norm : twistedNorm (galoisGf σ) (finrank E E') (y⁻¹ * r * y) = y⁻¹ * e (j γ) * y := by
    rw [h_eq, H.twistedNorm_conj, R.twistedNorm_inv H h_good]
  have h_bc : baseChangeGf (x⁻¹ * (stdSpace E n).embFin γ * x) = y⁻¹ * e (j γ) * y := by
    simp [y, ← H.map_apply_eq_baseChangeGf, h_comm_B.left_comm, mul_assoc]
  obtain ⟨h_value, -⟩ := h_match y
  rw [h_value _ h_bc h_norm, h_eq]

/-- For a matching pair `(f, φ)` (`IsMatchingPair`) over a step `E'/E`, with `e` the inclusion of
rational into finite adelic unitary points over `E'`, `ω` the action of `σ` on rational points
and `j` base change from `E` (`IsBaseChangeMaps`), there are a class `Good` of rational points and
root quotients `A`, `B` with the properties of `IsMatchingRoots`. -/
private lemma New.exists_isMatchingRoots (hσ : σ ≠ 1) {μ : (𝔸f E)ˣ →* ℂˣ} [IsStep (E := E) E' μ]
    (h_pair : IsMatchingPair (adeleMap_star σ) (finrank E E') 1 (kerCompNorm E' μ) baseChangeGf K f
      φ) :
    let e : U (1 : Matrix n n E') →* Gf E' n :=
      U.map (algebraMap E' (𝔸f E')) (fun x : E' ↦ (star_algebraMap_finAdele x).symm)
        (map_one (algebraMap E' (𝔸f E')).mapMatrix)
    let ω : U (1 : Matrix n n E') →* U (1 : Matrix n n E') := U.mapEnd (map_star_CM σ)
    ∀ _h_maps : New.IsBaseChangeMaps σ j ω e,
      ∃ (Good : U (1 : Matrix n n E') → Prop) (A : U (1 : Matrix n n E') → U (1 : Matrix n n E'))
        (B : U (1 : Matrix n n E') → Gf E' n), New.IsMatchingRoots σ K f φ j ω e Good A B := by
  intro e ω H
  obtain ⟨h_inv, h_pair⟩ := h_pair
  -- `C P`: the rational polynomial `P` is `σ`-fixed and is one of those that `IsMatchingPair`
  -- speaks of; `q δ` is the characteristic polynomial of a rational `δ`.
  let q (δ : U (1 : Matrix n n E')) : E'[X] := (δ : Matrix n n E').charpoly
  have charpoly_e (δ : U (1 : Matrix n n E')) :
      (e δ : Matrix n n (𝔸f E')).charpoly = (q δ).map (algebraMap E' (𝔸f E')) := charpoly_map _ _
  have charpoly_conj (x : Gf E' n) (ν : U (1 : Matrix n n E')) :
      ((x⁻¹ * e ν * x : Gf E' n) : Matrix n n (𝔸f E')).charpoly =
        (q ν).map (algebraMap E' (𝔸f E')) := by simp [charpoly_e]
  let supp : Set (Gf E' n) :=
    baseChangeGf '' support f ∪ twistedNorm (galoisGf σ) (finrank E E') '' support φ
  let C (P : E'[X]) : Prop := P.map (algebraMap E' (𝔸f E')) ∈
    (fun g : Gf E' n ↦ (g : Matrix n n (𝔸f E')).charpoly) '' supp ∧ σ • P = P
  have fixed_of_C (P : E'[X]) (hP : C P) : σ • P = P := hP.right
  have h_C {ν : U (1 : Matrix n n E')} (δ : U (1 : Matrix n n E')) (hν : SemiconjBy δ (ω ν) ν)
      (x : Gf E' n) (hx : x⁻¹ * e ν * x ∈ supp) : C (q ν) :=
    ⟨⟨x⁻¹ * e ν * x, hx, charpoly_conj x ν⟩, New.smul_charpoly_eq_of_semiconjBy hν⟩
  -- `z P` is the adelic polynomial that `IsMatchingPair` gives for `P`: a norm root (`hz`) whose
  -- root quotients match the values of `f` and `φ` (`hz_match`).
  have h_fixed (P : E'[X]) (hP : C P) :
      (P.map (algebraMap E' (𝔸f E'))).map (adeleMap (σ : E' →+* E')) =
        P.map (algebraMap E' (𝔸f E')) := by
    ext i
    simpa using congrArg (fun Q : E'[X] ↦ Q.coeff i) (fixed_of_C P hP)
  choose! z hz hz_match using fun (P : E'[X]) (hP : C P) ↦ h_pair _ hP.left (h_fixed P hP)
  -- `A ν` is a rational and `B ν` an adelic root quotient at `ν`.
  obtain ⟨A, B, h_conj, h_root⟩ := exists_isRootQuotient_of_isNormRoot hσ fixed_of_C hz
  refine ⟨fun ν ↦ C (q ν), A, B,
    { apply_inv_mul_mul_galoisGf := h_inv
      good_of_apply_ne_zero := fun x γ hf ↦ ?_
      good_twistedNorm := fun x δ hφ ↦ ?_
      good_and_conj_of_semiconjBy := h_conj
      map_twistedNorm_eq := fun {ν δ} hν_C hν ↦ ?_
      exists_inv_mul_eq := fun {ν δ} hν_C hν ↦ ?_ }⟩
  · -- `j γ` is fixed by `ω`, and `e (j γ)` is conjugate to the base change of `x⁻¹ * γ * x`.
    have h_mem : (baseChangeGf x)⁻¹ * e (j γ) * baseChangeGf x ∈ supp :=
      Or.inl ⟨x⁻¹ * (stdSpace E n).embFin γ * x, hf, by simp [H.map_apply_eq_baseChangeGf]⟩
    exact h_C 1 (by simp [H.map_apply_eq_self]) (baseChangeGf x) h_mem
  · have h_mem : x⁻¹ * e (twistedNorm ω (finrank E E') δ) * x ∈ supp :=
      Or.inr ⟨x⁻¹ * e δ * galoisGf σ x, hφ, H.twistedNorm_conj x δ⟩
    exact h_C δ (H.semiconjBy_twistedNorm δ) x h_mem
  · -- `IsRootQuotient.twistedNorm_eq_mul` splits off the root `r` for `z`, which contributes `e ν`
    -- to the norm.
    obtain ⟨r, h_unit, hr, hrδ⟩ := h_root hν_C hν
    obtain ⟨-, h_norm_root⟩ := hz (q ν) hν_C
    obtain ⟨-, h_root_norm⟩ := h_norm_root (e ν) (charpoly_e ν)
    have h_pol : IsRootQuotient (e ν)
        (twistedNorm (Polynomial.map (adeleMap ↑σ)) (finrank E E') (z (q ν))) (e ν) := by
      simpa using h_root_norm
    have h_comm : e ν * e δ = e δ * galoisGf σ (e ν) := by
      rw [← H.map_apply_eq_galoisGf, (hν.map e).eq]
    rw [← H.twistedNorm_conj, ← hrδ, map_twistedNorm e H.map_apply_eq_galoisGf]
    exact IsRootQuotient.twistedNorm_eq_mul h_pol h_comm hr h_unit
  · -- What `IsMatchingPair` says at a conjugate `y⁻¹ * e ν * y`, whose root for `z` is
    -- `y⁻¹ * r * y`.
    obtain ⟨r, -, hr, hrδ⟩ := h_root hν_C hν
    refine ⟨r, hrδ, fun y ↦ ?_⟩
    have hr_conj : IsRootQuotient (y⁻¹ * e ν * y) ((1 : 𝔸f E') • z (q ν))
        ((y⁻¹ * r * y : Gf E' n) : Matrix n n (𝔸f E')) := by
      simpa only [one_smul, inv_inv] using
        isRootQuotient_conj (mul_inv_cancel_right (y⁻¹ * e ν) y) hr
    exact hz_match _ hν_C _ _ (charpoly_conj y ν) hr_conj

/-- The bijection of moves in `New.twisted_trace_identity`. Let `m` send a pair `(y, γ)` over `E`
to the pair `((B (j γ))⁻¹ * y, (A (j γ))⁻¹)` over `E'`. For a pair `(x, δ)` over `E'` with
`φ (x⁻¹ * e δ * σ x) ≠ 0` there are a pair `z` over `E` and a map `J` on rational points such that,
for every pair `p` over `E`, `J` takes the moves from `p` to `z` bijectively onto the moves from
`(x, δ)` to `m p` (onto `∅` if `j p.2` is not good). A move over `E'` from `(x₀, γ)` to `(x₁, γ₁)`
is a rational `a` with `x₁⁻¹ * a * x₀ ∈ K` and `a⁻¹ * γ₁ * τ a = γ`; `hK_split` says that every
`s ∈ K` of twisted norm one splits in `K`. -/
private lemma New.IsMatchingRoots.exists_bijOn_of_ne_zero [IsGalois E E']
    (hK_split : ∀ s ∈ K,
      twistedNorm (galoisGf σ) (finrank E E') s = 1 → ∃ t ∈ K, galoisGf σ t = s⁻¹ * t)
    (H : New.IsBaseChangeMaps σ j ω e) (R : New.IsMatchingRoots σ K f φ j ω e Good A B)
    (τ : U (1 : Matrix n n E') ≃* U (1 : Matrix n n E'))
    (hτ : ∀ g : U (1 : Matrix n n E'), τ g = ω g)
    (m : Gf E n × U (1 : Matrix n n E) → Gf E' n × U (1 : Matrix n n E'))
    (hm : ∀ p : Gf E n × U (1 : Matrix n n E),
      m p = ((B (j p.snd))⁻¹ * baseChangeGf p.fst, (A (j p.snd))⁻¹))
    {x : Gf E' n} {δ : U (1 : Matrix n n E')} (hφ : φ (x⁻¹ * e δ * galoisGf σ x) ≠ 0) :
    ∃ (z : Gf E n × U (1 : Matrix n n E)) (J : U (1 : Matrix n n E) → U (1 : Matrix n n E')),
      ∀ p : Gf E n × U (1 : Matrix n n E),
        Set.BijOn J
          {a : U (1 : Matrix n n E) |
            z.fst⁻¹ * (stdSpace E n).embFin a * p.fst ∈ K.comap baseChangeGf ∧
              a⁻¹ * z.snd * a = p.snd}
          {g ∈ {g : U (1 : Matrix n n E') |
            (m p).fst⁻¹ * e g * x ∈ K ∧ g⁻¹ * (m p).snd * τ g = δ} | Good (j p.snd)} := by
  -- The twisted norm `ν` of `δ` is good, and the cocycle `A ν * δ` has twisted norm one.
  set ν : U (1 : Matrix n n E') := twistedNorm ω (finrank E E') δ with hν_def
  have hν : SemiconjBy δ (ω ν) ν := H.semiconjBy_twistedNorm δ
  have hν_good : Good ν := R.good_twistedNorm x δ hφ
  have norm_one : twistedNorm ω (finrank E E') (A ν * δ) = 1 := by
    apply H.e_injective
    simpa [inv_mul_eq_one, mul_assoc] using left_eq_mul.mp (R.map_twistedNorm_eq hν_good hν)
  -- A twisted conjugate of `A ν * δ` lies in `K`, by the matching condition at `x`.
  have mem_K : (B ν * x)⁻¹ * e (A ν * δ) * galoisGf σ (B ν * x) ∈ K := by
    obtain ⟨r, hrδ, h_match⟩ := R.exists_inv_mul_eq hν_good hν
    have h_eq : (x⁻¹ * r * x)⁻¹ * (x⁻¹ * e δ * galoisGf σ x) =
        (B ν * x)⁻¹ * e (A ν * δ) * galoisGf σ (B ν * x) :=
      calc _ = x⁻¹ * (r⁻¹ * e δ) * galoisGf σ x := by group
        _ = _ := by simp [hrδ, mul_assoc]
    simpa only [h_eq] using (h_match x).right _ (H.twistedNorm_conj x δ) hφ
  -- It splits in `K` by `hK_split`, hence adelically, hence rationally by the Hasse principle.
  obtain ⟨k, hk, hk_eq⟩ := hK_split _ mem_K <| by
    simpa [norm_one] using H.twistedNorm_conj (B ν * x) (A ν * δ)
  have h_split_ad : e (A ν * δ) = B ν * x * k * (galoisGf σ (B ν * x * k))⁻¹ := by
    rw [map_mul (galoisGf σ) (B ν * x) k, hk_eq]
    group
  obtain ⟨g, hg⟩ := H.exists_ω_eq_inv_mul (A ν * δ) (B ν * x * k) h_split_ad norm_one
  -- Twisting by `g` gives `σ`-fixed elements, which descend to a pair `(y, γ)` over `E`.
  obtain ⟨y, hy⟩ : ∃ y : Gf E n, baseChangeGf y = e g⁻¹ * B ν * x * k :=
    H.exists_baseChangeGf_eq _ (by simp [← H.map_apply_eq_galoisGf, hg, hk_eq, mul_assoc])
  obtain ⟨γ, hγ⟩ : ∃ γ : U (1 : Matrix n n E), j γ = g⁻¹ * ν * g := H.exists_j_eq _ <| by
    simp [eq_inv_mul_of_mul_eq hν, hg, ← (R.commute_inv hν_good).left_comm, mul_assoc]
  -- `a ↦ (g * j a)⁻¹` matches the moves from `p` to `(y, γ)` with those from `(x, δ)` to `m p`.
  refine ⟨(y, γ), fun a ↦ (g * j a)⁻¹, fun p ↦
    ⟨fun a ⟨ha_mem, ha_conj⟩ ↦ ?_, ?_, fun a ⟨⟨ha_mem, ha_conj⟩, hp_good⟩ ↦ ?_⟩⟩
  · -- Well defined: `(g * j a)⁻¹` conjugates `ν` to `j p.2`, and `A`, `B` follow the conjugation.
    have h_semi : SemiconjBy (g * j a)⁻¹ ν (j p.2) := by
      simp [SemiconjBy, ← ha_conj, hγ, mul_assoc]
    obtain ⟨hp_good, hA, hB⟩ := R.good_and_conj_of_semiconjBy (g * j a)⁻¹ hν_good h_semi
    refine ⟨⟨?_, ?_⟩, hp_good⟩
    · simpa [hm, hB, hy, H.map_apply_eq_baseChangeGf, mul_assoc] using inv_mem (mul_mem hk ha_mem)
    · simp [hm, hτ, hA, hg, H.map_apply_eq_self, mul_assoc]
  · simp [H.j_injective.eq_iff]
  · -- Surjective: `a` twists `(A (j p.2))⁻¹`, of twisted norm `j p.2`, to `δ`, so it conjugates
    -- `j p.2` to `ν`; then `(a * g)⁻¹` is `σ`-fixed and descends to a move `a'` over `E`.
    have ha_δ : a⁻¹ * (A (j p.2))⁻¹ * ω a = δ := by simpa only [hm, hτ] using ha_conj
    have h_semi : a⁻¹ * j p.2 = ν * a⁻¹ := H.e_injective <| by
      -- `-map_inv` with `e.map_inv a`: of the inverses under `e`, only that of `a` is pulled out.
      simp [hν_def, ← ha_δ, H.map_apply_eq_galoisGf, H.twistedNorm_conj, -map_inv, e.map_inv a,
        map_twistedNorm e H.map_apply_eq_galoisGf, R.twistedNorm_inv H hp_good]
    obtain ⟨-, hA, hB⟩ := R.good_and_conj_of_semiconjBy _ hp_good h_semi
    obtain ⟨a', ha'_j⟩ : ∃ a' : U (1 : Matrix n n E), j a' = (a * g)⁻¹ :=
      H.exists_j_eq _ (by simp [hg, ← ha_δ, hA, mul_assoc])
    refine ⟨a', ⟨?_, H.j_injective ?_⟩, by simp [ha'_j]⟩
    · simpa [hm, hB, hy, ← H.map_apply_eq_baseChangeGf, ha'_j, mul_assoc] using
        inv_mem (mul_mem ha_mem hk)
    · simp [ha'_j, hγ, ← h_semi, mul_assoc]

end MatchingRoots

/-- Twisted trace identity for a step `E'/E` (`IsStep`) and `σ ≠ 1` in its Galois group. Let
`L ≤ K ≤ stdLevel E' n` with `L` open and `σ`-stable, and let every `s ∈ K` of twisted norm one be
`t * (σ t)⁻¹` with `t ∈ K` (`hK_split`). Then for some `c ≠ 0`, an operator `t` on forms of weight
`κ.baseChange` over `E'` (a) turns translation by `g` into that by `σ g`, (b) keeps `L`-fixed forms,
and (c) has `tr (T' * t) = c * tr T` for Hecke operators `T'`, `T` of a matching pair `(φ, f)`. -/
lemma New.twisted_trace_identity {E E' n : Type} [Field E] [CMType E] [Field E'] [Algebra E E']
    [Fintype n] [DecidableEq n] {σ : Gal(E'/E)} (hσ : σ ≠ 1) {μ : (𝔸f E)ˣ →* ℂˣ} [CMTypeOver E E']
    [IsStep (E := E) E' μ] (κ : Weight E) {K L : Subgroup (Gf E' n)} (hK : K ≤ stdLevel E' n)
    (hL : L ≤ K) (hL_open : L.IsOpen) (hL_σ : L.comap (galoisGf σ) = L)
    (hK_split : ∀ s ∈ K,
      twistedNorm (galoisGf σ) (finrank E E') s = 1 → ∃ t ∈ K, galoisGf σ t = s⁻¹ * t) :
    ∃ c ≠ (0 : ℂ), ∃ t : End ℂ ((stdSpace E' n).forms κ.baseChange),
      -- (a) the operator `t` on forms over `E'` turns translation by `g` into translation by `σ g`
      (∀ (g : Gf E' n) (ψ : (stdSpace E' n).forms κ.baseChange),
        t ((stdSpace E' n).formTranslation κ.baseChange g ψ) =
          (stdSpace E' n).formTranslation κ.baseChange (galoisGf σ g) (t ψ)) ∧
      -- (b) `ht`: `t` preserves the `L`-fixed forms
      ∃ ht : ∀ x ∈ levelSpace ((stdSpace E' n).formTranslation κ.baseChange) L,
        t x ∈ levelSpace ((stdSpace E' n).formTranslation κ.baseChange) L,
        -- (c) for a matching pair of functions, the twisted trace is `c` times the trace
        ∀ (f : Gf E n → ℂ) (φ : U (1 : Matrix n n (𝔸f E')) → ℂ),
        IsMatchingPair (adeleMap_star σ) (finrank E E') 1 (kerCompNorm E' μ) baseChangeGf K f φ →
        ∀ (T : End ℂ (levelSpace ((stdSpace E n).formTranslation κ) (L.comap baseChangeGf)))
          (T' : End ℂ (levelSpace ((stdSpace E' n).formTranslation κ.baseChange) L)),
          IsOperatorOf ((stdSpace E n).formTranslation κ) (L.comap baseChangeGf) T f →
          IsOperatorOf ((stdSpace E' n).formTranslation κ.baseChange) L T' φ →
          (T' * t.restrict ht).trace ℂ
              (levelSpace ((stdSpace E' n).formTranslation κ.baseChange) L) =
            c * T.trace ℂ
              (levelSpace ((stdSpace E n).formTranslation κ) (L.comap baseChangeGf)) := by
  -- Both traces are weighted sums of orbital terms (`isSampleTotal_twisted_trace`), over pairs
  -- `(y, γ)` for `E` and `(x, δ)` for `E'`. A rational `A ν` and an adelic `B ν`, built from the
  -- roots in `IsMatchingPair`, send `(y, γ)` to a pair `(B⁻¹ y, A⁻¹)` with the same term, `A⁻¹`
  -- having twisted norm `j γ`. By `hK_split` and the Hasse principle every non-zero term over `E'`
  -- is reached up to a move; `IsSampleTotal.mul_eq_mul_of_bijOn` counts the moves.
  have h_wt := exists_trace_mul_weightRep_eq_of_twistedNorm_eq (n := n) hσ κ
  extract_lets j ω ρ at h_wt
  obtain ⟨s, hs, h_wt⟩ := h_wt
  -- `s` intertwines `ρ δ` with `ρ (ω δ)` (`hs`), and `tr (s * ρ δ)` is the character of weight `κ`
  -- at `γ` when `δ` has twisted norm `j γ` (`h_wt`).
  let e : U (1 : Matrix n n E') →* Gf E' n :=
    U.map (algebraMap E' (𝔸f E')) (fun x : E' ↦ (star_algebraMap_finAdele x).symm)
      (map_one (algebraMap E' (𝔸f E')).mapMatrix)
  have h_emb : (stdSpace E' n).embFin = e := by simp [e, U.map, DFunLike.ext_iff, Gf.val_ext_iff]
  have h_maps : New.IsBaseChangeMaps σ j ω e := New.isBaseChangeMaps μ hσ
  -- The trace formula over `E` (untwisted) and over `E'` (twisted by `σ`, as an automorphism).
  -- `τ` and `θ` are data built by tactics; `erw`: `simp` leaves `σ⁻¹` and `σ` composed as an
  -- unnamed identity ring hom, which `adeleMap_id` matches only up to unfolding.
  let τ : U 1 ≃* U 1 := by
    apply ω.toMulEquiv (mapEnd (map_star_CM ↑σ⁻¹)) <;> ext <;> simp [ω, U.map]
  let θ : Gf E' n ≃* Gf E' n := by
    apply (galoisGf σ).toMulEquiv (galoisGf σ⁻¹) <;> ext <;> simp [U.map, Gf.atPlace,
      RingHom.comp] <;> erw [adeleMap_id]
  have hK_E : K.comap baseChangeGf ≤ stdLevel E n := fun _ h ↦ baseChangeGf_mem_stdLevel.1 (hK h)
  obtain ⟨c, hc, h_forms, h_level, h_tr⟩ :=
    (stdSpace E n).isSampleTotal_twisted_trace κ 1 continuous_id hK_E (L.comap_mono hL)
      (hL_open.preimage continuous_baseChangeGf) rfl 1 (by simp) 1 (by simp)
  have h_tr'_of := (stdSpace E' n).isSampleTotal_twisted_trace κ.baseChange θ
    (continuous_map : Continuous (galoisGf σ⁻¹)) hK hL hL_open hL_σ τ
  rw [h_emb] at h_tr'_of
  obtain ⟨c', hc', ht, ht', h_tr'⟩ := h_tr'_of h_maps.map_apply_eq_galoisGf s hs
  refine ⟨c' / c, div_ne_zero hc' hc,
    (s.compLeft (Gf E' n) ∘ₗ LinearMap.funLeft ℂ (WeylIndex n κ.baseChange.1 → ℂ) θ.symm).restrict
      ht, fun g ψ ↦ ?_, ht', fun f φ h_pair T T' hT hT' ↦ ?_⟩
  · -- The operator precomposes with `σ⁻¹`, which turns translation by `g` into that by `σ g`.
    ext
    simp [show θ.symm (galoisGf σ g) = g from θ.symm_apply_apply g]
  rw [div_mul_eq_mul_div, eq_div_iff hc]
  obtain ⟨Good, A, B, h_roots : New.IsMatchingRoots σ K f φ j ω e Good A B⟩ :=
    New.exists_isMatchingRoots hσ h_pair h_maps
  -- `m` sends a pair over `E` to the pair over `E'` with the same term.
  let m (p : Gf E n × U (1 : Matrix n n E)) : Gf E' n × U (1 : Matrix n n E') :=
    ((B (j p.snd))⁻¹ * baseChangeGf p.fst, (A (j p.snd))⁻¹)
  let F (p : Gf E n × U 1) : ℂ := f (p.fst⁻¹ * (stdSpace E n).embFin p.snd * p.fst) *
    ((stdSpace E n).weightRep κ.1 κ.2 p.snd).trace ℂ _
  let F' (p : Gf E' n × U 1) : ℂ :=
    φ (p.fst⁻¹ * e p.snd * galoisGf σ p.fst) * (ρ p.snd * s).trace ℂ _
  refine IsSampleTotal.mul_eq_mul_of_bijOn (B := U 1) (F := F) F' (h_tr hT) (h_tr' hT') m
    {p | Good (j p.snd)} (fun p hp ↦ ?_) (fun p hp y g ⟨hk, hg⟩ ↦ ?_) fun (x, δ) hx ↦ ?_
  · -- A non-zero term over `E` has a good `j γ`.
    exact h_roots.good_of_apply_ne_zero p.fst p.snd (left_ne_zero_of_mul hp)
  · -- A move from `y` to `m p` keeps the value of `φ`, by twisted `K`-invariance, and the trace.
    have h_val : φ (y.fst⁻¹ * e y.snd * galoisGf σ y.fst) =
        f (p.fst⁻¹ * (stdSpace E n).embFin p.snd * p.fst) := by
      rw [h_roots.apply_inv_mul_embFin_mul_eq h_maps p.fst p.snd hp,
        ← h_roots.apply_inv_mul_mul_galoisGf _ hk ((m p).fst⁻¹ * _ * _)]
      simp [m, ← hg, h_maps.map_apply_eq_galoisGf, τ, mul_assoc]
    have h_trace :
        (ρ y.snd * s).trace ℂ _ = ((stdSpace E n).weightRep κ.1 κ.2 p.snd).trace ℂ _ := by
      simp [m, τ, ← hg, ← h_wt _ _ (h_roots.twistedNorm_inv h_maps hp), ← hs,
        (ρ g⁻¹).trace_mul_comm, s.trace_mul_comm, ← ρ.map_mul g, mul_assoc]
    simp only [F, F', h_val, h_trace]
  -- A non-zero term `(x, δ)` over `E'` is reached from a pair over `E`.
  exact h_roots.exists_bijOn_of_ne_zero hK_split h_maps τ (fun _ ↦ rfl) m (fun _ ↦ rfl)
    (left_ne_zero_of_mul hx)

end TwistedTraceIdentity
