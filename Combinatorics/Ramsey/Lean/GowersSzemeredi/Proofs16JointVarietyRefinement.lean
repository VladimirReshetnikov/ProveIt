import GowersSzemeredi.Proofs16OscillationPartitionInst
import GowersSzemeredi.Proofs16VarietyTranslate
import GowersSzemeredi.Proofs16LiftAllScales

/-! Simultaneous refinement for translated local Freiman variety phases.

On a linear-stage cell, retain the mixed phases of exactly those varieties
whose deep translates meet the cell. Inactive phases are replaced by zero.
One simultaneous partition then controls every active variety, with a
polynomial dependence on the total number of mixed phases.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A translated local Freiman column is multilinear on any box whose
translated vertical range stays in the Freiman domain. -/
theorem freiman_shifted_column_multilinearOn {N : Nat} [NeZero N] [Fact N.Prime]
    {B : Finset (ZMod N)} {L : ZMod N → ZMod N} (hL : IsFreimanLinearOn B L)
    (C : Box N 2) (s t : ZMod N) (hC : ∀ x ∈ C.carrier, x 1 - t ∈ B) :
    MultilinearOn C.carrier (fun x => L (x 1 - t) * (x 0 - s)) := by
  let v : Point N 2 := ![s, t]
  have hy : ∀ x ∈ (C.translate (-v)).carrier, x 1 ∈ B := by
    intro x hx
    have hx' : x + v ∈ C.carrier := by
      have h := (Box.translate_mem_carrier (C.translate (-v)) v x).mpr hx
      simpa using h
    simpa [v] using hC (x + v) hx'
  obtain ⟨mu, hmu, hag⟩ := freiman_column_multilinearOn hL (C.translate (-v)) hy
  refine ⟨fun x => mu (x + -v), hmu.translate (-v), ?_⟩
  intro x hx
  have h := hag (x + -v) ((Box.translate_mem_carrier C (-v) x).mpr hx)
  simpa [v, sub_eq_add_neg] using h

/-- Simultaneous partition of the active local phases only. Inactive
phases need no multilinearity hypothesis and impose no diameter conclusion. -/
theorem masked_multilinear_diameter_partition {N : Nat} [NeZero N]
    {K : Real} {p : Nat} (hMD : MultilinearDiameterPartition K p)
    (q : Nat) (C : Box N 2) (hC : C.IsProper)
    (active : Fin q → Prop) (mu : Fin q → Point N 2 → ZMod N)
    (hmu : ∀ i, active i → MultilinearOn C.carrier (mu i))
    (H : Nat) (hH : 0 < H) (hK : K * ((q : Real) + 1) ≤ H)
    (hwide : H ^ (p * (q + 1)^8) ≤ C.width) :
    ∃ m : Nat, ∃ R : Fin m → Box N 2,
      IsBoxPartition R C ∧ (∀ j, (R j).IsProper) ∧
      (∀ j, (H : Real) ≤ (R j).width) ∧
      ∀ i, active i → ∀ j,
        diameterAtMostReal ((R j).carrier.image (mu i)) (4 / H * N) := by
  classical
  let f : Fin q → Point N 2 → ZMod N := fun i => if active i then mu i else fun _ => 0
  have hf : ∀ i, MultilinearOn C.carrier (f i) := by
    intro i
    by_cases h : active i
    · simpa [f, h] using hmu i h
    · exact ⟨fun _ => 0, isMultilinear_constant 0, by simp [f, h]⟩
  obtain ⟨m, R, hpart, hprop, hw, hdiam⟩ := hMD N q C hC f hf H hH hK hwide
  refine ⟨m, R, hpart, hprop, hw, ?_⟩
  intro i hi j
  simpa [f, hi, show (2 ^ 2 : Real) = 4 by norm_num] using hdiam i j

/-- One shared bilinear refinement handles a family of translated varieties.
Its phase count is `n*r`, rather than an iterated product of exponents. -/
theorem joint_variety_cell_refine {N n r : Nat} [NeZero N] [Fact N.Prime]
    (Gamma Psi : Fin n → Finset (ZMod N)) (L : Fin n → Fin r → ZMod N → ZMod N)
    (rho : Fin n → Real) (a b : Fin n → ZMod N) (hrho : ∀ i, 0 < rho i)
    (hL : ∀ i k, IsFreimanLinearOn (bohr (Psi i) (rho i)) (L i k))
    {K : Real} {p : Nat} (hMD : MultilinearDiameterPartition K p)
    (C : Box N 2) (hC : C.IsProper)
    (hgamma : ∀ i gamma, gamma ∈ Gamma i → ∀ x ∈ C.carrier, ∀ y ∈ C.carrier,
      (centeredAbs (gamma * y 0 - gamma * x 0) : Real) ≤ rho i / 4 * N)
    (hpsi : ∀ i psi, psi ∈ Psi i → ∀ x ∈ C.carrier, ∀ y ∈ C.carrier,
      (centeredAbs (psi * y 1 - psi * x 1) : Real) ≤ rho i / 4 * N)
    (H : Nat) (hH : 0 < H) (hK : K * ((n * r : Nat) + (1 : Real)) ≤ H)
    (hscale : ∀ i, 8 ≤ rho i * H)
    (hwide : H ^ (p * (n * r + 1)^8) ≤ C.width) :
    ∃ m : Nat, ∃ R : Fin m → Box N 2,
      IsBoxPartition R C ∧ (∀ j, (R j).IsProper) ∧
      (∀ j, (H : Real) ≤ (R j).width) ∧
      ∀ j i, CellGood
        (shiftPairs (bilinearBohrVariety (Gamma i) (Psi i) (L i) (rho i / 2)) (a i) (b i))
        (shiftPairs (bilinearBohrVariety (Gamma i) (Psi i) (L i) (rho i)) (a i) (b i)) (R j) := by
  classical
  let active : Fin n → Prop := fun i => ∃ x ∈ C.carrier,
    (x 0 - a i, x 1 - b i) ∈ bilinearBohrVariety (Gamma i) (Psi i) (L i) (rho i / 2)
  let e : Fin n × Fin r ≃ Fin (n * r) := finProdFinEquiv
  let mu : Fin (n * r) → Point N 2 → ZMod N := fun k x =>
    L (e.symm k).1 (e.symm k).2 (x 1 - b (e.symm k).1) * (x 0 - a (e.symm k).1)
  have hlocal : ∀ k, active (e.symm k).1 → MultilinearOn C.carrier (mu k) := by
    intro k hk
    obtain ⟨x0, hx0, hv⟩ := hk
    obtain ⟨_, hPsi, _⟩ := (mem_bilinearBohrVariety_iff _ _ _ _ _).mp hv
    apply freiman_shifted_column_multilinearOn (hL _ _) C _ _
    intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro psi hps
    have hd := hpsi (e.symm k).1 psi hps x0 hx0 x hx
    have heq : psi * (x 1 - b (e.symm k).1) - psi * (x0 1 - b (e.symm k).1) =
        psi * x 1 - psi * x0 1 := by ring
    have hd' : (centeredAbs (psi * (x 1 - b (e.symm k).1) -
        psi * (x0 1 - b (e.symm k).1)) : Real) ≤ rho (e.symm k).1 / 4 * N := by
      rw [heq]; exact hd
    have h := centeredAbs_le_of_close (hPsi psi hps) hd'
    exact h.trans (by nlinarith [mul_nonneg (hrho (e.symm k).1).le (Nat.cast_nonneg N)])
  obtain ⟨m, R, hpart, hprop, hw, hdiam⟩ :=
    masked_multilinear_diameter_partition hMD (n * r) C hC
      (fun k => active (e.symm k).1) mu hlocal H hH hK hwide
  refine ⟨m, R, hpart, hprop, hw, ?_⟩
  intro j i
  have hsub : (R j).carrier ⊆ C.carrier := IsPartition.cell_subset hpart j
  by_cases hi : active i
  swap
  · apply Or.inl
    intro x hx hV
    exact hi ⟨x, hsub hx, (mem_shiftPairs _ _ _ _).mp hV⟩
  let v : Point N 2 := ![a i, b i]
  have hback : ∀ x ∈ ((R j).translate (-v)).carrier, x + v ∈ (R j).carrier := by
    intro x hx
    have h := (Box.translate_mem_carrier ((R j).translate (-v)) v x).mpr hx
    simpa using h
  have hhalf : rho i / 4 * N ≤ rho i / 2 * N := by
    nlinarith [mul_nonneg (hrho i).le (Nat.cast_nonneg N)]
  have hsmall : (4 : Real) / H * N ≤ rho i / 2 * N := by
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
    rw [div_le_iff₀ (by exact_mod_cast hH : (0 : Real) < H)]
    nlinarith [hscale i]
  have hosc : SmallOscillation (Gamma i) (Psi i) (L i) (rho i / 2)
      (cellPairs ((R j).translate (-v))) := by
    intro u hu w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    have hxR := hback x hx
    have hyR := hback y hy
    refine ⟨?_, ?_, ?_⟩
    · intro gamma hg
      have h := hgamma i gamma hg (x + v) (hsub hxR) (y + v) (hsub hyR)
      have heq : gamma * (y + v) 0 - gamma * (x + v) 0 = gamma * y 0 - gamma * x 0 := by
        simp only [Pi.add_apply]; ring
      rw [heq] at h
      exact h.trans hhalf
    · intro psi hp
      have h := hpsi i psi hp (x + v) (hsub hxR) (y + v) (hsub hyR)
      have heq : psi * (y + v) 1 - psi * (x + v) 1 = psi * y 1 - psi * x 1 := by
        simp only [Pi.add_apply]; ring
      rw [heq] at h
      exact h.trans hhalf
    · intro k
      have hactive : active (e.symm (e (i, k))).1 := by simpa using hi
      have h := image_diam_sub_le (hdiam (e (i, k)) hactive j) hxR hyR
      have h' : (centeredAbs (L i k (y 1) * y 0 - L i k (x 1) * x 0) : Real) ≤
          (4 : Real) / H * N := by simpa only [mu, Equiv.symm_apply_apply, Pi.add_apply, v,
            Matrix.cons_val_zero, Matrix.cons_val_one, add_sub_cancel_right] using h
      exact h'.trans hsmall
  have hg := cellGood_of_small_oscillation ((R j).translate (-v)) (Or.inr hosc)
  have hshift := cellGood_translate hg (a i) (b i)
  simpa only [← show v = ![a i, b i] from rfl, Box.translate_neg'] using hshift

end LeanProofs.GowersSzemeredi
