import GowersSzemeredi.Proofs16CellOscillation
import GowersSzemeredi.Proofs05SimultaneousMultiaffinePartition

/-! Simultaneous polynomial-width oscillation partitions for variety phases.

When the mixed phases L_i(y)*x are multilinear on the parent box, the
simultaneous recurrence partitions all variety conditions at once, with
minimum cell width H and oscillation at most 4*N/H. The input threshold is
H^(p*(|Gamma|+|Psi|+r+1)^8). This proves a concrete case of the oscillation
input; Freiman linearity on a Bohr set alone is not asserted to supply the
parent-box multilinearity assumption.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Partition all variety conditions simultaneously on any parent box
where its mixed phases are multilinear. -/
theorem exists_polynomial_variety_oscillation_partition :
  ∃ (K : Real) (p : Nat), 2 ≤ K ∧ 0 < p ∧
  ∀ (N : Nat) [NeZero N] (Gamma Psi : Finset (ZMod N)) (r : Nat)
    (L : Fin r → ZMod N → ZMod N) (P : Box N 2), P.IsProper →
    (∀ i, MultilinearOn P.carrier (fun x : Point N 2 => L i (x 1) * x 0)) →
    ∀ H : Nat, 0 < H → K * ((Gamma.card + Psi.card + r : Nat) + 1 : Real) ≤ H →
      H ^ (p * (Gamma.card + Psi.card + r + 1) ^ 8) ≤ P.width →
      ∃ M : Nat, ∃ Q : Fin M → Box N 2,
        IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
        (∀ j, (H : Real) ≤ (Q j).width) ∧
        ∀ j, SmallOscillation Gamma Psi L (4 / (H : Real)) (cellPairs (Q j)) := by
  classical
  obtain ⟨K, p, hK, hp, hpartition⟩ := exists_simultaneous_multilinear_partition_bound 2 (by decide)
  refine ⟨K, p, hK, hp, ?_⟩
  intro N _ Gamma Psi r L P hP hL H hH hscale hsize
  let I := Gamma ⊕ (Psi ⊕ Fin r)
  let q := Gamma.card + Psi.card + r
  have hcard : Fintype.card I = q := by simp [I, q, Nat.add_assoc]
  let e : I ≃ Fin q := (Fintype.equivFin I).trans (finCongr hcard)
  let f : I → Point N 2 → ZMod N := Sum.elim
    (fun g x => g.val * x 0)
    (Sum.elim (fun g x => g.val * x 1) (fun i x => L i (x 1) * x 0))
  have hf (i : I) : MultilinearOn P.carrier (f i) := by
    rcases i with g | (g | i)
    · refine ⟨f (.inl g), ?_, fun _ _ => rfl⟩
      simpa [f] using isMultilinear_two (N := N) 0 g.val 0 0
    · refine ⟨f (.inr (.inl g)), ?_, fun _ _ => rfl⟩
      simpa [f] using isMultilinear_two (N := N) 0 0 g.val 0
    · exact hL i
  obtain ⟨M, Q, hpart, hproper, hw, hdiam⟩ := hpartition N q P hP
    (fun i => f (e.symm i)) (fun i => hf (e.symm i)) H hH hscale (by simpa [q] using hsize)
  have hdiff (i : I) (j : Fin M) (x y : Point N 2)
      (hx : x ∈ (Q j).carrier) (hy : y ∈ (Q j).carrier) :
      (centeredAbs (f i y - f i x) : Real) ≤ 4 / (H : Real) * N := by
    have h := (hdiam (e i) j).centeredAbs_sub_le
      (Finset.mem_image.mpr ⟨y, hy, rfl⟩) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    simpa only [Equiv.symm_apply_apply, show (2 : Real)^2 = 4 by norm_num] using h
  refine ⟨M, Q, hpart, hproper, hw, ?_⟩
  intro j a ha b hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  exact ⟨fun g hg => hdiff (.inl ⟨g, hg⟩) j x y hx hy,
    fun g hg => hdiff (.inr (.inl ⟨g, hg⟩)) j x y hx hy,
    fun i => hdiff (.inr (.inr i)) j x y hx hy⟩

/-- Globally affine coordinate functions supply the mixed-phase assumption. -/
theorem affine_variety_phases_multilinear {N r : Nat} [NeZero N] (a b : Fin r → ZMod N)
    (P : Box N 2) (i : Fin r) :
    MultilinearOn P.carrier (fun x : Point N 2 => (a i * x 1 + b i) * x 0) := by
  refine ⟨fun x => (a i * x 1 + b i) * x 0, ?_, fun _ _ => rfl⟩
  convert isMultilinear_two (N := N) 0 (b i) 0 (a i) using 1
  funext x
  ring

/-- The oscillation cells are good once H is at least 8/rho. -/
theorem cellGood_of_polynomial_oscillation {N H : Nat} [NeZero N]
    {Gamma Psi : Finset (ZMod N)} {r : Nat} {L : Fin r → ZMod N → ZMod N}
    {rho : Real} (hH : 0 < H) (hscale : 8 ≤ rho * H) (Q : Box N 2)
    (hosc : SmallOscillation Gamma Psi L (4 / (H : Real)) (cellPairs Q)) :
    CellGood (bilinearBohrVariety Gamma Psi L (rho / 2))
      (bilinearBohrVariety Gamma Psi L rho) Q := by
  have hHR : (0 : Real) < H := by exact_mod_cast hH
  have hbound : 4 / (H : Real) ≤ rho / 2 := (div_le_iff₀ hHR).mpr (by linarith)
  apply cellGood_of_small_oscillation Q
  right
  intro x hx y hy
  obtain ⟨hG, hP, hL⟩ := hosc x hx y hy
  have h := mul_le_mul_of_nonneg_right hbound (Nat.cast_nonneg N : (0 : Real) ≤ N)
  exact ⟨fun g hg => (hG g hg).trans h, fun g hg => (hP g hg).trans h,
    fun i => (hL i).trans h⟩

end LeanProofs.GowersSzemeredi
