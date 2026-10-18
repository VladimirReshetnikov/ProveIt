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
  have hS : ∀ ⦃x⦄, x ∈ S → x ∈ (A : Set (ZMod N)) := by
    intro x hx
    have := (Multiset.mem_replicate.mp hx).2
    change x ∈ A
    rw [this]
    exact hb
  have hT : ∀ ⦃x⦄, x ∈ T → x ∈ (A : Set (ZMod N)) := by
    intro x hx
    rcases Multiset.mem_add.mp hx with hx | hx
    · have := (Multiset.mem_replicate.mp hx).2
      change x ∈ A
      rw [this]
      exact hc
    · have := (Multiset.mem_replicate.mp hx).2
      change x ∈ A
      rw [this]
      exact ha
  have hcardS : S.card = c - a := by simp [S]
  have hcardT : T.card = c - a := by simp [T]; omega
  have hsum : S.sum = T.sum := by
    simp only [S, T, Multiset.sum_add, Multiset.sum_replicate, nsmul_eq_mul]
    push_cast [Nat.cast_sub (hab.trans hbc), Nat.cast_sub hab, Nat.cast_sub hbc]
    ring
  have h := (IsAddFreimanHom.mono hca hphi).map_sum_eq_map_sum hS hT hcardS hcardT hsum
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
  let I : Finset (Fin P.length) := Finset.univ.filter
    (fun i ↦ P.start + (i : Nat) * P.step ∈ A)
  have hI : I.Nonempty := by
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hne
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hA hx)
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi ▸ hx⟩⟩
  let lo := I.min' hI
  let hi := I.max' hI
  have hlo : lo ∈ I := Finset.min'_mem _ _
  have hhi : hi ∈ I := Finset.max'_mem _ _
  have hloA : P.start + (lo : Nat) * P.step ∈ A := (Finset.mem_filter.mp hlo).2
  have hhiA : P.start + (hi : Nat) * P.step ∈ A := (Finset.mem_filter.mp hhi).2
  have hdistinct : lo ≠ hi := by
    intro heq
    have hsingle : A.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro x hx y hy
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hA hx)
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (hA hy)
      have hiI : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
      have hjI : j ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
      have hil : lo ≤ i := Finset.min'_le _ _ hiI
      have hih : i ≤ hi := Finset.le_max' _ _ hiI
      have hjl : lo ≤ j := Finset.min'_le _ _ hjI
      have hjh : j ≤ hi := Finset.le_max' _ _ hjI
      have hij : i = j := by omega
      rw [hij]
    omega
  have hcard : (Finset.univ.image
      (fun i : Fin P.length ↦ P.start + (i : Nat) * P.step)).card =
      (Finset.univ : Finset (Fin P.length)).card := by
    simpa only [ModAP.IsProper, ModAP.carrier, Finset.card_univ, Fintype.card_fin] using hP
  have hinj := Finset.card_image_iff.mp hcard
  have hne : P.start + (hi : Nat) * P.step -
      (P.start + (lo : Nat) * P.step) ≠ 0 := by
    intro hz
    have hh := hinj (Finset.mem_univ hi) (Finset.mem_univ lo) (sub_eq_zero.mp hz)
    exact hdistinct hh.symm
  let a := (phi (P.start + (hi : Nat) * P.step) -
    phi (P.start + (lo : Nat) * P.step)) /
    (P.start + (hi : Nat) * P.step - (P.start + (lo : Nat) * P.step))
  let b := phi (P.start + (lo : Nat) * P.step) -
    a * (P.start + (lo : Nat) * P.step)
  refine ⟨a, b, ?_⟩
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hA hx)
  have hiI : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  have hli : (lo : Nat) ≤ i := Finset.min'_le _ _ hiI
  have hih : (i : Nat) ≤ hi := Finset.le_max' _ _ hiI
  have hrel := freiman_index_interpolation A phi hphi P.start P.step lo i hi
    hli hih (by have := hi.isLt; omega) hloA hx hhiA
  push_cast [Nat.cast_sub (hli.trans hih), Nat.cast_sub hli, Nat.cast_sub hih] at hrel
  have ha : a * (P.start + (hi : Nat) * P.step -
      (P.start + (lo : Nat) * P.step)) =
      phi (P.start + (hi : Nat) * P.step) -
        phi (P.start + (lo : Nat) * P.step) := div_mul_cancel₀ _ hne
  apply mul_left_cancel₀ hne
  dsimp only [b]
  linear_combination P.step * hrel -
    (P.start + (i : Nat) * P.step - (P.start + (lo : Nat) * P.step)) * ha

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
