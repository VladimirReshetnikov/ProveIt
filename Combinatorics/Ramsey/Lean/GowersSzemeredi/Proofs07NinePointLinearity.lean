import GowersSzemeredi.Proofs07ShortLinearity

/-! Affine interpolation from Freiman relations on at most nine consecutive
progression positions. Missing points are permitted in the domain.

`corollary_7_11_all_scales_modular` and `eight_modular_affine_partition` are in
`Proofs07NinePointLinearitySide`, outside the final route. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

private lemma freiman_index_interpolation {N : Nat} [Fact N.Prime]
    (A : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (hphi : FreimanHom 8 A phi) (s d : ZMod N)
    (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) (hca : c - a ≤ 8)
    (ha : s + a * d ∈ A) (hb : s + b * d ∈ A) (hc : s + c * d ∈ A) :
    ((c - a : Nat) : ZMod N) * phi (s + b * d) =
      ((b - a : Nat) : ZMod N) * phi (s + c * d) +
        ((c - b : Nat) : ZMod N) * phi (s + a * d) := by
  let S := Multiset.replicate (c - a) (s + b * d)
  let T := Multiset.replicate (b - a) (s + c * d) +
    Multiset.replicate (c - b) (s + a * d)
  have hS : ∀ ⦃x⦄, x ∈ S → x ∈ (A : Set (ZMod N)) := fun x hx => by
    rw [Multiset.eq_of_mem_replicate hx]
    exact hb
  have hT : ∀ ⦃x⦄, x ∈ T → x ∈ (A : Set (ZMod N)) := fun x hx => by
    rcases Multiset.mem_add.mp hx with hx | hx <;> rw [Multiset.eq_of_mem_replicate hx]
    exacts [hc, ha]
  have hcardT : T.card = c - a := by simp [T]; omega
  have hsum : S.sum = T.sum := by
    simp only [S, T, Multiset.sum_add, Multiset.sum_replicate, nsmul_eq_mul]
    push_cast [Nat.cast_sub (hab.trans hbc), Nat.cast_sub hab, Nat.cast_sub hbc]
    ring
  have h := (IsAddFreimanHom.mono hca hphi).map_sum_eq_map_sum hS hT
    (Multiset.card_replicate _ _) hcardT hsum
  simpa only [S, T, Multiset.map_replicate, Multiset.map_add, Multiset.sum_add,
    Multiset.sum_replicate, nsmul_eq_mul] using h

/-- An order-eight Freiman map on any subset of a proper progression of
length at most nine is affine on that subset. -/
theorem linearOn_nine_point_progression {N : Nat} [Fact N.Prime]
    (P : ModAP N) (A : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (hP : P.IsProper) (hlen : P.length ≤ 9) (hA : A ⊆ P.carrier)
    (hphi : FreimanHom 8 A phi) : LinearOn A phi := by
  by_cases htwo : A.card ≤ 2
  · exact linearOn_of_card_le_two A phi htwo
  -- the indices of the points of `A`, with their extremes `lo < hi`
  let I : Finset (Fin P.length) := Finset.univ.filter
    (fun i ↦ P.start + (i : Nat) * P.step ∈ A)
  have hAI : A ⊆ I.image fun i : Fin P.length ↦ P.start + (i : Nat) * P.step := fun x hx ↦ by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (hA hx)
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
  have hI : 1 < I.card := by
    have := (Finset.card_le_card hAI).trans Finset.card_image_le
    omega
  have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
  let lo := I.min' hIne
  let hi := I.max' hIne
  have hlt : lo < hi := Finset.min'_lt_max'_of_card I hI
  let x0 := P.start + (lo : Nat) * P.step
  let x1 := P.start + (hi : Nat) * P.step
  have hcard : (Finset.univ.image
      (fun i : Fin P.length ↦ P.start + (i : Nat) * P.step)).card =
      (Finset.univ : Finset (Fin P.length)).card := by
    simpa only [ModAP.IsProper, ModAP.carrier, Finset.card_univ, Fintype.card_fin] using hP
  have hne : x1 - x0 ≠ 0 := fun hz ↦ hlt.ne' (Finset.card_image_iff.mp hcard
    (Finset.mem_univ hi) (Finset.mem_univ lo) (sub_eq_zero.mp hz))
  -- the affine map through the two extreme points
  let a := (phi x1 - phi x0) / (x1 - x0)
  have ha : a * (x1 - x0) = phi x1 - phi x0 := div_mul_cancel₀ _ hne
  refine ⟨a, phi x0 - a * x0, fun x hx ↦ ?_⟩
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hA hx)
  have hiI : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  have hli : (lo : Nat) ≤ i := Finset.min'_le _ _ hiI
  have hih : (i : Nat) ≤ hi := Finset.le_max' _ _ hiI
  have hrel := freiman_index_interpolation A phi hphi P.start P.step lo i hi hli hih
    (by have := hi.isLt; omega) (Finset.mem_filter.mp (I.min'_mem hIne)).2 hx
    (Finset.mem_filter.mp (I.max'_mem hIne)).2
  push_cast [Nat.cast_sub (hli.trans hih), Nat.cast_sub hli, Nat.cast_sub hih] at hrel
  apply mul_left_cancel₀ hne
  dsimp only [x0, x1] at ha ⊢
  linear_combination P.step * hrel -
    (((i : Nat) : ZMod N) - ((lo : Nat) : ZMod N)) * P.step * ha

/-- Uniform upper bound for the one-map partition exponent. -/
theorem cor711_single_exponent_bounds {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    0 < cor711Exponent alpha 1 ∧ cor711Exponent alpha 1 ≤ 1 / 16384 := by
  unfold cor711Exponent
  rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
  norm_num
  constructor
  · positivity
  · simpa only [abs_of_pos hα] using hαone

end LeanProofs.GowersSzemeredi
