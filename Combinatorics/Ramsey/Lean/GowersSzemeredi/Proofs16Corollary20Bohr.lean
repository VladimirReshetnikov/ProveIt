import GowersSzemeredi.Proofs16Corollary20Dense
import GowersSzemeredi.Proofs07BohrHom

/-! The dense order-eight selection pieces extend to Bohr neighborhoods
with a uniform radius and rank bound. This is an input to the remaining
bilinear Bohr structure argument, not that complete structure theorem. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem IsBHomomorphism.mono_neighborhood {N : Nat} {A B C : Finset (ZMod N)}
    {f : ZMod N → ZMod N} (h : IsBHomomorphism A B f) (hCB : C ⊆ B) :
    IsBHomomorphism A C f := by
  obtain ⟨psi, hpsi, hagree⟩ := h
  refine ⟨psi, ?_, fun x hx y hy hxy => hagree x hx y hy (hCB hxy)⟩
  exact IsAddFreimanHom.subset (fun _ hx => hCB hx) hpsi (fun _ _ => Set.mem_univ _)

/-- A lower density bound supplies uniform Bohr extension parameters. -/
theorem dense_freiman_eight_bohr_extension {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (f : ZMod N → ZMod N) {kappa : Real}
    (hk : 0 < kappa) (hmass : kappa * N ≤ A.card) (hF : FreimanHom 8 A f) :
    ∃ S : Finset (ZMod N), (S.card : Real) ≤ 16 * kappa^(-(2 : Real)) ∧
      IsBHomomorphism A (bohr S (kappa / (32 * Real.pi))) f := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let alpha : Real := (A.card : Real) / N
  have hka : kappa ≤ alpha := (le_div_iff₀ hN).mpr hmass
  have ha : 0 < alpha := hk.trans_le hka
  have hcard : (A.card : Real) = alpha * N := by dsimp only [alpha]; field_simp
  obtain ⟨hS, hB⟩ := lemma_7_8_holds N A f alpha ha hcard hF
  refine ⟨section7Spectrum A alpha, hS.trans ?_, hB.mono_neighborhood ?_⟩
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hk hka (by norm_num)) (by norm_num)
  · have hr : kappa / (32 * Real.pi) ≤ alpha / (32 * Real.pi) :=
      div_le_div_of_nonneg_right hka (by positivity)
    intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t ht => ?_⟩
    exact ((Finset.mem_filter.mp hx).2 t ht).trans
      (mul_le_mul_of_nonneg_right hr hN.le)

/-- The selection iteration supplies actual uniformly controlled Bohr
extensions for every dense piece, while keeping its bad-triple bound. -/
theorem corollary20_bohr_pieces_budget {N : Nat} [NeZero N] [Fact N.Prime]
    (U : ZMod N → Finset (ZMod N)) (h0 : ∀ x, (0 : ZMod N) ∈ U x)
    {K : Nat} (hK1 : 1 ≤ K) (hK : ∀ x, (U x).card ≤ K) {ε : Real} (hε : 0 < ε) :
    ∃ (m : Nat) (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N)
      (S : Fin m → Finset (ZMod N)),
      (m : Real) * corollary20Kappa ε K ≤ K - 1 ∧
      (∀ i, FreimanHom 8 (E i) (L i) ∧ corollary20Kappa ε K * N ≤ (E i).card ∧
        (∀ x ∈ E i, L i x ∈ U x) ∧
        ((S i).card : Real) ≤ 16 * (corollary20Kappa ε K)^(-(2 : Real)) ∧
        IsBHomomorphism (E i) (bohr (S i) (corollary20Kappa ε K / (32 * Real.pi))) (L i)) ∧
      ((Finset.univ.filter (IsBadTriple U E L)).card : Real) < ε * (N : Real)^3 := by
  classical
  obtain ⟨m, E, L, hm, hE, hbad⟩ := corollary20_dense_eight_budget U h0 hK1 hK hε
  have hk : 0 < corollary20Kappa ε K := by
    unfold corollary20Kappa
    have : (1 : Real) ≤ K := by exact_mod_cast hK1
    positivity
  choose S hS hB using fun i =>
    dense_freiman_eight_bohr_extension (E i) (L i) hk (hE i).2.1 (hE i).1
  exact ⟨m, E, L, S, hm, fun i =>
    ⟨(hE i).1, (hE i).2.1, (hE i).2.2, hS i, hB i⟩, hbad⟩

/-- Retain the original count interface as a consequence of the sharper budget. -/
theorem corollary20_bohr_pieces {N : Nat} [NeZero N] [Fact N.Prime]
    (U : ZMod N → Finset (ZMod N)) (h0 : ∀ x, (0 : ZMod N) ∈ U x)
    {K : Nat} (hK1 : 1 ≤ K) (hK : ∀ x, (U x).card ≤ K) {ε : Real} (hε : 0 < ε) :
    ∃ (m : Nat) (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N)
      (S : Fin m → Finset (ZMod N)),
      m ≤ ⌊(K : Real) / corollary20Kappa ε K⌋₊ + 1 ∧
      (∀ i, FreimanHom 8 (E i) (L i) ∧ corollary20Kappa ε K * N ≤ (E i).card ∧
        (∀ x ∈ E i, L i x ∈ U x) ∧
        ((S i).card : Real) ≤ 16 * (corollary20Kappa ε K)^(-(2 : Real)) ∧
        IsBHomomorphism (E i) (bohr (S i) (corollary20Kappa ε K / (32 * Real.pi))) (L i)) ∧
      ((Finset.univ.filter (IsBadTriple U E L)).card : Real) < ε * (N : Real)^3 := by
  obtain ⟨m, E, L, S, hm, hE, hbad⟩ := corollary20_bohr_pieces_budget U h0 hK1 hK hε
  have hk : 0 < corollary20Kappa ε K := by
    unfold corollary20Kappa
    have : (1 : Real) ≤ K := by exact_mod_cast hK1
    positivity
  have hmR : (m : Real) ≤ (K : Real) / corollary20Kappa ε K :=
    (le_div_iff₀ hk).mpr (by linarith)
  have hmNat : m ≤ ⌊(K : Real) / corollary20Kappa ε K⌋₊ :=
    (Nat.le_floor_iff (by positivity)).mpr hmR
  exact ⟨m, E, L, S, by omega, hE, hbad⟩

end LeanProofs.GowersSzemeredi
