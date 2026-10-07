import GowersSzemeredi.Proofs16FiniteAlphabetBoxCover
import GowersSzemeredi.Proofs08AffineFrequencyProgression

/-! A balanced finite-alphabet word contradicts the graph and width
budgets of multiple multilinearity on the full box. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def alphabetFullBox (N k : Nat) : Box N k where
  axis := fun _ => modInterval N 0 N
  commonDiff := 1
  axis_step := fun _ => rfl

theorem alphabetFullBox_carrier (N k : Nat) [NeZero N] :
    (alphabetFullBox N k).carrier = Finset.univ := by
  classical
  ext x
  simp [alphabetFullBox, Box.carrier, modInterval_zero_modulus_carrier]

theorem alphabetFullBox_proper (N k : Nat) [NeZero N] : (alphabetFullBox N k).IsProper := by
  intro i
  change (modInterval N 0 N).carrier.card = N
  rw [modInterval_zero_modulus_carrier, Finset.card_univ, ZMod.card]

theorem alphabetFullBox_width (N k : Nat) : (alphabetFullBox N (k + 1)).width = N := by
  apply Nat.le_antisymm
  · exact (alphabetFullBox N (k + 1)).width_le_axis_length (Fin.last k)
  · exact Box.le_width_of_le_axis _ (Nat.succ_pos _) (fun _ => le_rfl)

theorem balanced_word_not_multiplyLinear {N k : Nat} [NeZero N] [Fact N.Prime]
    (S : Finset (ZMod N)) (f : ZMod N → ZMod N) (hf : ∀ y, f y ∈ S)
    (K L beta : Real) (hbeta : 0 ≤ beta)
    (hK : multipleQ (1 / 2) 1 (k + 1) ≤ K)
    (hL : L ≤ (N : Real) ^ multipleC (1 / 2) 1 (k + 1))
    (hbalanced : ∀ P : ModAP N, P.IsProper → L ≤ P.length →
      ∀ c : ZMod N, ((P.carrier.filter (fun y => f y = c)).card : Real) ≤ beta * P.length)
    (hsmall : K * beta ≤ 9 / 32) (hwidth : K * S.card ≤ L / 32) :
    ¬ MultiplyLinearFunction 1 1 Finset.univ (fun x : Point N (k + 1) => f (section16Last x)) := by
  classical
  intro h
  obtain ⟨M, q, H, Q, mu, hsub, hmass, hpart, hproper, hq, hsize, hmu, hcover⟩ :=
    h (1 / 2) (by norm_num) (by norm_num) (alphabetFullBox N (k + 1)) (alphabetFullBox_proper N (k + 1))
  simp only [inv_one, one_mul, Real.rpow_one] at hq hsize
  have hqK : (q : Real) ≤ K := hq.trans hK
  have haxis (j : Fin M) : L ≤ ((Q j).axis (Fin.last k)).length := by
    have hw := hsize j
    rw [alphabetFullBox_width] at hw
    have hh : ((Q j).width : Real) ≤ ((Q j).axis (Fin.last k)).length := by
      exact_mod_cast (Q j).width_le_axis_length (Fin.last k)
    exact hL.trans (hw.trans hh)
  have hbal (j : Fin M) (c : ZMod N) :
      ((((Q j).axis (Fin.last k)).carrier.filter (fun y => f y = c)).card : Real) ≤
        beta * ((Q j).axis (Fin.last k)).carrier.card := by
    rw [hproper j (Fin.last k)]
    exact hbalanced _ (hproper j (Fin.last k)) (haxis j) c
  have hw (j : Fin M) : (q : Real) * S.card ≤
      (((Q j).axis (Fin.last k)).carrier.card : Real) / 32 := by
    rw [hproper j (Fin.last k)]
    have hqS := mul_le_mul_of_nonneg_right hqK (Nat.cast_nonneg S.card)
    linarith only [hqS, hwidth, haxis j]
  have hcov : ∀ j x, x ∈ (Q j).carrier → x ∈ H →
      ∃ i : Fin q, f (section16Last x) = mu j i x := by
    intro j x hx hH
    apply hcover j x hx hH
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have hsm : (q : Real) * beta ≤ 9 / 32 :=
    (mul_le_mul_of_nonneg_right hqK hbeta).trans hsmall
  have hu := finiteAlphabet_box_partition_cover_bound (alphabetFullBox N (k + 1)) Q hpart S H f hf mu hmu
    beta hbeta hbal hsub hcov hsm hw
  have hp : (0 : Real) < (alphabetFullBox N (k + 1)).carrier.card := by
    rw [alphabetFullBox_carrier, Finset.card_univ]
    exact_mod_cast Fintype.card_pos
  nlinarith only [hu, hmass, hp]

end LeanProofs.GowersSzemeredi
