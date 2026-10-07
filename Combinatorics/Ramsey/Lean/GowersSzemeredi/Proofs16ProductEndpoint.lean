import GowersSzemeredi.Proofs16Interpolation
import GowersSzemeredi.Proofs16CoordinateFaces

/-! Rigidity at the full-domain, unit-parameter product-property endpoint.
This retains the upstream hypothesis omitted by the false packaged Lemma 16.10.
It does not supply the general quantitative induction. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Saturation of the elementary N^3 bound forces preservation of every
additive quadruple. -/
theorem phiAdditiveCount_saturated {N : Nat} [NeZero N]
    (f : ZMod N → ZMod N)
    (h : N ^ 3 ≤ phiAdditiveCount Finset.univ f) :
    ∀ x y z, f x + f y = f z + f (x + y - z) := by
  classical
  let A := Finset.univ.filter (IsPhiAdditive Finset.univ f)
  let project : (Fin 4 → ZMod N) → (Fin 3 → ZMod N) := fun q i => q i.castSucc
  have hinj : Set.InjOn project A := by
    intro q hq r hr heq
    have hqadd := (Finset.mem_filter.mp hq).2.2.1
    have hradd := (Finset.mem_filter.mp hr).2.2.1
    have h0 : q 0 = r 0 := congrFun heq 0
    have h1 : q 1 = r 1 := congrFun heq 1
    have h2 : q 2 = r 2 := congrFun heq 2
    have h3 : q 3 = r 3 := by
      unfold IsAdditiveQuadruple at hqadd hradd
      rw [h0, h1, h2] at hqadd
      exact add_left_cancel (hqadd.symm.trans hradd)
    funext i
    fin_cases i <;> assumption
  have hcard : (A.image project).card = phiAdditiveCount Finset.univ f := by
    rw [Finset.card_image_of_injOn hinj]
    rfl
  have hall : A.image project = Finset.univ := by
    apply Finset.eq_univ_of_card
    apply Nat.le_antisymm (Finset.card_le_univ _)
    rw [hcard]
    simpa [ZMod.card] using h
  intro x y z
  have ht : ![x, y, z] ∈ A.image project := by rw [hall]; exact Finset.mem_univ _
  obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp ht
  have h0 : q 0 = x := congrFun heq 0
  have h1 : q 1 = y := congrFun heq 1
  have h2 : q 2 = z := congrFun heq 2
  have hqa := (Finset.mem_filter.mp hq).2
  have h3 : q 3 = x + y - z := by
    have hh := hqa.2.1
    unfold IsAdditiveQuadruple at hh
    rw [h0, h1, h2] at hh
    linear_combination -hh
  simpa only [h0, h1, h2, h3] using hqa.2.2

/-- A globally Freiman-affine map on a cyclic group has the usual affine
formula. No prime-modulus hypothesis is needed. -/
theorem linearOn_univ_of_additive_quadruples {N : Nat} [NeZero N]
    (f : ZMod N → ZMod N)
    (h : ∀ x y z, f x + f y = f z + f (x + y - z)) :
    LinearOn Finset.univ f := by
  let g : ZMod N →+ ZMod N := {
    toFun := fun x => f x - f 0
    map_zero' := sub_self _
    map_add' := by
      intro x y
      have hh := h x y 0
      simp only [sub_zero] at hh
      linear_combination -hh }
  have hg (x : ZMod N) : g x = x * g 1 := by
    have hh := g.map_nsmul x.val (1 : ZMod N)
    simpa only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val] using hh
  refine ⟨f 1 - f 0, f 0, fun x _ => ?_⟩
  have hh := hg x
  change f x - f 0 = x * (f 1 - f 0) at hh
  linear_combination hh

/-- At parameter one on the whole domain, every coordinate restriction
must preserve all additive quadruples, hence is globally affine. -/
theorem HasProductProperty.unit_coordinate_linear {N k : Nat} [NeZero N]
    {phi : Point N k → ZMod N}
    (h : HasProductProperty Finset.univ phi 1) (y : Point N k) (j : Fin k) :
    LinearOn Finset.univ (coordinateRestriction phi y j) := by
  classical
  have hh := h 1 j (fun _ => y) Finset.univ (fun _ => 1)
    (fun _ => zero_le_one) (fun _ _ _ => Finset.mem_univ _)
  have he : weightedSimultaneousAdditiveEnergy Finset.univ (fun _ => 1)
      (fun _ : Fin 1 => coordinateRestriction phi y j) =
      (phiAdditiveCount Finset.univ (coordinateRestriction phi y j) : Real) := by
    unfold weightedSimultaneousAdditiveEnergy phiAdditiveCount countWhere
    rw [Finset.filter_congr_decidable]
    simp [IsPhiAdditive, IsAdditiveQuadruple]
  rw [he] at hh
  have hN : (N : Real) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hn : (N : Real) ^ 3 ≤ phiAdditiveCount Finset.univ (coordinateRestriction phi y j) := by
    simpa [ZMod.card, hN, pow_succ, mul_assoc] using hh
  exact linearOn_univ_of_additive_quadruples _
    (phiAdditiveCount_saturated _ (by exact_mod_cast hn))

/-- Separately affine functions are multilinear. Two fixed anchors suffice
in every dimension, with no quantitative or box-cover hypotheses. -/
theorem isMultilinear_of_coordinate_linear {N k : Nat} [Fact N.Prime]
    (phi : Point N k → ZMod N)
    (h : ∀ y j, LinearOn Finset.univ (coordinateRestriction phi y j)) :
    IsMultilinear phi := by
  classical
  induction k with
  | zero =>
    refine ⟨fun _ => phi 0, fun x => ?_⟩
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  | succ k ih =>
    have hs (a : ZMod N) : IsMultilinear (fun x => phi (Fin.snoc x a)) := by
      apply ih
      intro y j
      have hh := h (Fin.snoc y a) j.castSucc
      have heq : coordinateRestriction (fun x => phi (Fin.snoc x a)) y j =
          coordinateRestriction phi (Fin.snoc y a) j.castSucc := by
        funext x
        unfold coordinateRestriction
        apply congrArg phi
        funext i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simp [replaceCoordinate, (Fin.castSucc_ne_last j).symm]
        · simp [replaceCoordinate, Function.update_apply, Fin.castSucc_inj]
      rw [heq]
      exact hh
    have hm := section16TwoAnchorLift_multilinear (1 : ZMod N) 0 (hs 1) (hs 0)
    have heq : phi = section16TwoAnchorLift 1 0
        (fun x => phi (Fin.snoc x 1)) (fun x => phi (Fin.snoc x 0)) := by
      funext z
      have hz := (h z (Fin.last k)).two_anchor_interpolation
        (Finset.mem_univ 1) (Finset.mem_univ 0) (Finset.mem_univ (z (Fin.last k)))
        (one_ne_zero : (1 : ZMod N) ≠ 0)
      have hr (a : ZMod N) : replaceCoordinate z (Fin.last k) a = Fin.snoc (Fin.init z) a := by
        funext i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simp [replaceCoordinate]
        · simp [replaceCoordinate, Fin.init]
      simpa [coordinateRestriction, hr, section16TwoAnchorLift] using hz
    rw [heq]
    exact hm

/-- The full-domain unit product property forces one global multilinear
graph, unlike the two insufficient packaged hypotheses of Lemma 16.10. -/
theorem HasProductProperty.unit_multilinear {N k : Nat} [NeZero N] [Fact N.Prime]
    {phi : Point N k → ZMod N} (h : HasProductProperty Finset.univ phi 1) :
    IsMultilinear phi :=
  isMultilinear_of_coordinate_linear phi h.unit_coordinate_linear

end LeanProofs.GowersSzemeredi
