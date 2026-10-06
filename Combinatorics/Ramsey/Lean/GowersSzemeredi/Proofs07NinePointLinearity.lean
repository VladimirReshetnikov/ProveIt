import GowersSzemeredi.Proofs07ShortLinearity

/-! Affine interpolation from Freiman relations on at most nine consecutive
progression positions. Missing points are permitted in the domain. -/

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
  classical
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
  classical
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

/-- Eight- or nine-point affine cells cover every proper progression of
length at least sixty-four, retaining its nonzero step. -/
theorem eight_modular_affine_partition {N : Nat} [Fact N.Prime]
    (R : ModAP N) (A : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (hR : R.IsProper) (hstep : R.step != 0) (hlen : 64 ≤ R.length)
    (hphi : FreimanHom 8 A phi) {t : Real} (ht : t ≤ 8) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j ↦ (Q j).carrier) R.carrier ∧
      ∀ j, (Q j).step != 0 ∧ (Q j).IsProper ∧ t ≤ (Q j).length ∧
        LinearOn ((Q j).carrier.filter fun x ↦ x ∈ A) phi := by
  classical
  have hlinear (P : ModAP N) (hp : P.IsProper) (hlen : P.length ≤ 9) :
      LinearOn (P.carrier.filter fun x ↦ x ∈ A) phi := by
    apply linearOn_nine_point_progression P _ phi hp hlen (Finset.filter_subset _ _)
    exact IsAddFreimanHom.subset
      (fun x hx ↦ (Finset.mem_filter.mp hx).2) hphi (Set.mapsTo_univ _ _)
  let P := R.asBox
  have hP : P.IsProper := fun _ ↦ hR
  have hwidth : P.width = R.length := BaseCase.boxOne_width P
  have hLm : 8 * 8 ≤ P.width := by rw [hwidth]; omega
  let Q : Fin (P.width / 8) → ModAP N :=
    fun j ↦ (BaseCase.coarseChildBox P 8 j).axis 0
  have hproper (j : Fin (P.width / 8)) : (Q j).IsProper :=
    BaseCase.coarseChildBox_proper P hP 8 (by norm_num) hLm j 0
  have hlength (j : Fin (P.width / 8)) : 8 ≤ (Q j).length ∧ (Q j).length ≤ 9 := by
    dsimp only [Q, BaseCase.coarseChildBox, BaseCase.coarseChunkLength]
    split_ifs <;> omega
  refine ⟨P.width / 8, Q, ?_, ?_⟩
  · exact box_one_partition_axes P (fun j ↦ BaseCase.coarseChildBox P 8 j)
      (BaseCase.coarseChildBox_partition P hP 8 (by norm_num) hLm)
  · intro j
    refine ⟨hstep, hproper j, ?_, hlinear (Q j) (hproper j) (hlength j).2⟩
    exact ht.trans (by exact_mod_cast (hlength j).1)

/-- Uniform upper bound for the one-map partition exponent. -/
theorem cor711_single_exponent_bounds {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    0 < cor711Exponent alpha 1 ∧ cor711Exponent alpha 1 ≤ 1 / 16384 := by
  unfold cor711Exponent
  rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
  norm_num
  constructor
  · positivity
  · simpa only [abs_of_pos hα] using hαone

/-- The original real-power cell length is attainable at every scale over
a prime field. The proof combines the constant-radius construction with
short affine partitions, including missing points in each domain. -/
theorem corollary_7_11_all_scales_modular (N : Nat) [Fact N.Prime]
    (R : ModAP N) (A : Finset (ZMod N)) (phi : ZMod N → ZMod N) (alpha : Real)
    (hR : R.IsProper) (hstep : R.step != 0) (hl : 0 < R.length)
    (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (hA : A ⊆ R.carrier) (hdensity : alpha * R.length ≤ A.card)
    (hfreiman : FreimanHom 8 A phi) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j ↦ (Q j).carrier) R.carrier ∧
      (∀ j, (Q j).step != 0 ∧ (Q j).IsProper ∧
        (R.length : Real) ^ cor711Exponent alpha 1 ≤ (Q j).length ∧
        LinearOn ((Q j).carrier.filter fun x ↦ x ∈ A) phi) := by
  have he := cor711_single_exponent_bounds hα hαone
  by_cases hlarge : 8 ≤ (R.length : Real) ^ cor711Exponent alpha 1
  · exact corollary_7_11_constant_modular N R A phi alpha hR hl hα hαone hA hdensity
      hfreiman hlarge
  by_cases hlen : 64 ≤ R.length
  · exact eight_modular_affine_partition R A phi hR hstep hlen hfreiman (le_of_not_ge hlarge)
  have hsmall : (R.length : Real) ^ cor711Exponent alpha 1 ≤ 2 := by
    calc
      _ ≤ (64 : Real) ^ cor711Exponent alpha 1 :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (show R.length ≤ 64 by omega)) he.1.le
      _ = (2 : Real) ^ (6 * cor711Exponent alpha 1) := by
        rw [Real.rpow_mul (by norm_num)]
        norm_num
      _ ≤ (2 : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [he.2])
      _ = 2 := Real.rpow_one _
  exact short_modular_affine_partition R A phi hR hstep hfreiman hsmall
    (Real.rpow_le_self_of_one_le (by exact_mod_cast hl) (by linarith [he.2]))

end LeanProofs.GowersSzemeredi
