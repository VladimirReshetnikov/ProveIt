import GowersSzemeredi.Proofs16CubeDensity

/-! # Quantitative domain-size inputs for Lemma 16.5 -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Choosing fifteen entries of an additive sixteen-tuple forces the index
of the remaining entry. A fibre cap therefore bounds the tuple count. -/
theorem domainAdditiveTupleCount_eight_le {N M : Nat}
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (hfibre : ∀ s, (D.fibre s).card ≤ M) :
    domainAdditiveTupleCount D 8 ≤ M * Fintype.card X ^ 15 := by
  classical
  let target (t : Fin 15 → X) : ZMod N :=
    (∑ i : Fin 15, if 8 ≤ i.val + 1 then D.index (t i) else 0) -
      ∑ i : Fin 15, if i.val + 1 < 8 then D.index (t i) else 0
  have hiff (a : X) (t : Fin 15 → X) :
      HasEqualHalfSums (k := 8) (fun i : Fin 16 => D.index (Fin.cons (α := fun _ : Fin 16 => X) a t i)) ↔ D.index a = target t := by
    unfold HasEqualHalfSums
    simp only [Finset.sum_filter]
    conv_lhs => lhs; rw [Fin.sum_univ_succ]
    conv_lhs => rhs; rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ]
    norm_num only [show (0 : Nat) < 8 by omega, show ¬ 8 ≤ (0 : Nat) by omega,
      ite_true, ite_false, zero_add]
    exact (eq_sub_iff_add_eq).symm
  have hone (t : Fin 15 → X) :
      (∑ a : X, if HasEqualHalfSums (k := 8) (fun i : Fin 16 => D.index (Fin.cons (α := fun _ : Fin 16 => X) a t i)) then 1 else 0) ≤ M := by
    simp_rw [hiff]
    simpa [MultifunctionDomain.fibre] using hfibre (target t)
  unfold domainAdditiveTupleCount countWhere
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← (Fin.consEquiv (fun _ : Fin 16 => X)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  calc
    _ ≤ ∑ _t : Fin 15 → X, M := Finset.sum_le_sum fun t _ => hone t
    _ = M * Fintype.card X ^ 15 := by simp [mul_comm]

/-- The fibre cap also bounds the entire domain. -/
theorem MultifunctionDomain.card_le_cap {N M : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (hfibre : ∀ s, (D.fibre s).card ≤ M) :
    Fintype.card X ≤ M * N := by
  classical
  have hsum : (∑ s : ZMod N, (D.fibre s).card) = Fintype.card X := by
    rw [Fintype.card]
    exact (Finset.card_eq_sum_card_fiberwise (s := Finset.univ)
      (t := Finset.univ) (f := D.index) (by simp)).symm
  rw [← hsum]
  calc
    _ ≤ ∑ _s : ZMod N, M := Finset.sum_le_sum fun s _ => hfibre s
    _ = M * N := by simp [mul_comm]

/-- A linear bound in the domain size, retaining the scale needed to turn
many arrangements into a lower bound for the number of cubes. -/
theorem domainAdditiveTupleCount_eight_linear_le {N M : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (hfibre : ∀ s, (D.fibre s).card ≤ M) :
    domainAdditiveTupleCount D 8 ≤ Fintype.card X * M ^ 15 * N ^ 14 := by
  have hX := D.card_le_cap hfibre
  calc
    _ ≤ M * Fintype.card X ^ 15 := domainAdditiveTupleCount_eight_le D hfibre
    _ = Fintype.card X * M * Fintype.card X ^ 14 := by ring
    _ ≤ Fintype.card X * M * (M * N) ^ 14 := by gcongr
    _ = Fintype.card X * M ^ 15 * N ^ 14 := by ring

/-- The lower arrangement threshold in Lemma 16.5 forces the required
lower density of its fixed-side cube domain. -/
theorem section16_cube_card_lower {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k) (a : Real)
    (hcount : a * (N : Real) ^ (16 * k + 15) ≤ section16ArrangementCountAtSide 8 B h) :
    a * (N : Real) ^ (k + 1) ≤ (section16CubeDomain B h).card := by
  have hupper := domainAdditiveTupleCount_eight_linear_le
    (section16CubeMultifunctionDomain B h) (section16CubeMultifunctionDomain_fibre_card_le B h)
  rw [section16_domainAdditiveTupleCount_eq_arrangementCountAtSide,
    section16CubeElement_card] at hupper
  have hupperR : (section16ArrangementCountAtSide 8 B h : Real) ≤
      (section16CubeDomain B h).card * (N : Real) ^ (15 * k + 14) := by
    have hr : (section16ArrangementCountAtSide 8 B h : Real) ≤
        (section16CubeDomain B h).card * ((N : Real) ^ k) ^ 15 * (N : Real) ^ 14 := by
      exact_mod_cast hupper
    convert hr using 1
    ring
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  apply (mul_le_mul_iff_left₀ (pow_pos hN (15 * k + 14))).mp
  calc
    (a * (N : Real) ^ (k + 1)) * (N : Real) ^ (15 * k + 14) =
        a * (N : Real) ^ (16 * k + 15) := by ring
    _ ≤ _ := hcount.trans hupperR

/-- Reparameterize a density lower bound as an exact density in the range
of Theorem 10.13. Dense domains use a sixfold fibre cap. -/
theorem domain_density_reparameterize (n : Real) (N M : Nat)
    (hN : 0 < N) (hM : 0 < M) (a : Real) (ha : 0 < a) (haSmall : a ≤ 1 / 36)
    (hlower : a * M * N ≤ n) (hupper : n ≤ (M : Real) * N) :
    ∃ L : Nat, M ≤ L ∧ L ≤ 6 * M ∧ 0 < L ∧
      ∃ alpha : Real, a ≤ alpha ∧ 0 < alpha ∧ alpha ≤ 1 / 6 ∧
        n = alpha * L * N := by
  have hNr : (0 : Real) < N := by exact_mod_cast hN
  have hMr : (0 : Real) < M := by exact_mod_cast hM
  let beta : Real := n / ((M : Real) * N)
  have hb : a ≤ beta := (le_div_iff₀ (mul_pos hMr hNr)).mpr (by simpa [mul_assoc] using hlower)
  have hbOne : beta ≤ 1 := (div_le_iff₀ (mul_pos hMr hNr)).mpr (by simpa using hupper)
  have heq : n = beta * M * N := by dsimp [beta]; field_simp
  by_cases hbSix : beta ≤ 1 / 6
  · exact ⟨M, le_rfl, by omega, hM, beta, hb, ha.trans_le hb, hbSix, heq⟩
  · refine ⟨6 * M, by omega, le_rfl, by omega, beta / 6, ?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
    · rw [heq]
      push_cast
      ring

end LeanProofs.GowersSzemeredi
