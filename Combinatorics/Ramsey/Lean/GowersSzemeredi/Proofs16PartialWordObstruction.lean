import GowersSzemeredi.Proofs16BalancedWordObstruction
import GowersSzemeredi.Proofs05BoxTransport

/-! A balanced word obstructs the source unit cover already on any nonempty
proper box contained in its partial domain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem balanced_word_not_multiplyLinear_on_box {N k : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (Point N (k + 1))) (P : Box N (k + 1))
    (hP : P.IsProper) (hPB : P.carrier ⊆ B) (hPnonempty : P.carrier.Nonempty)
    (S : Finset (ZMod N)) (f : ZMod N → ZMod N) (hf : ∀ y, f y ∈ S)
    (K L beta : Real) (hbeta : 0 ≤ beta)
    (hK : multipleQ (1 / 2) 1 (k + 1) ≤ K)
    (hL : L ≤ (P.width : Real) ^ multipleC (1 / 2) 1 (k + 1))
    (hbalanced : ∀ P : ModAP N, P.IsProper → L ≤ P.length →
      ∀ c : ZMod N, ((P.carrier.filter (fun y => f y = c)).card : Real) ≤ beta * P.length)
    (hsmall : K * beta ≤ 9 / 32) (hwidth : K * S.card ≤ L / 32) :
    ¬ MultiplyLinearFunction 1 1 B (fun x : Point N (k + 1) => f (section16Last x)) := by
  classical
  intro h
  obtain ⟨M, q, H, Q, mu, hsub, hmass, hpart, hproper, hq, hsize, hmu, hcover⟩ :=
    h (1 / 2) (by norm_num) (by norm_num) P hP
  simp only [inv_one, one_mul, Real.rpow_one] at hq hsize
  have hqK : (q : Real) ≤ K := hq.trans hK
  have haxis (j : Fin M) : L ≤ ((Q j).axis (Fin.last k)).length := by
    have hw := hsize j
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
    exact Finset.mem_image.mpr ⟨x, hPB (hsub hH), rfl⟩
  have hsm : (q : Real) * beta ≤ 9 / 32 :=
    (mul_le_mul_of_nonneg_right hqK hbeta).trans hsmall
  have hu := finiteAlphabet_box_partition_cover_bound P Q hpart S H f hf mu hmu
    beta hbeta hbal hsub hcov hsm hw
  have hp : (0 : Real) < P.carrier.card := by
    exact_mod_cast Finset.card_pos.mpr hPnonempty
  nlinarith only [hu, hmass, hp]


end LeanProofs.GowersSzemeredi
