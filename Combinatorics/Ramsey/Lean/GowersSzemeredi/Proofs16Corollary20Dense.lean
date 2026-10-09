import GowersSzemeredi.Proofs16Corollary20

/-! Preserve density, value membership, and order-eight Freiman structure
through the selection iteration. These are the inputs for Lemma 7.8. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
variable {N : Nat} [NeZero N]

/-- Retain the initial N covered zero values in the terminal potential.
Every selected piece keeps its density and order-eight structure, and
the number of pieces satisfies the sharper budget m*kappa ≤ K-1. -/
theorem corollary20_dense_eight_budget [Fact N.Prime] (U : ZMod N → Finset (ZMod N))
    (h0 : ∀ x, (0 : ZMod N) ∈ U x) {K : Nat} (hK1 : 1 ≤ K) (hK : ∀ x, (U x).card ≤ K)
    {ε : Real} (hε : 0 < ε) :
    ∃ (m : Nat) (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N),
      (m : Real) * corollary20Kappa ε K ≤ K - 1 ∧ (∀ i, FreimanHom 8 (E i) (L i) ∧ corollary20Kappa ε K * N ≤ (E i).card ∧
        ∀ x ∈ E i, L i x ∈ U x) ∧
      ((Finset.univ.filter (IsBadTriple U E L)).card : Real) < ε * (N : Real) ^ 3 := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hκ : 0 < corollary20Kappa ε K := by
    unfold corollary20Kappa
    have : (1 : Real) ≤ K := by exact_mod_cast hK1
    positivity
  -- the invariant after `s` steps
  have key : ∀ s : Nat, (∃ (m : Nat) (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N),
      m = s ∧ (∀ i, FreimanHom 8 (E i) (L i) ∧ corollary20Kappa ε K * N ≤ (E i).card ∧
        ∀ x ∈ E i, L i x ∈ U x) ∧
      (N : Real) + s * (corollary20Kappa ε K * N) ≤ covPotential U E L) ∨
      (∃ (m : Nat) (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N),
      m ≤ s ∧ (∀ i, FreimanHom 8 (E i) (L i) ∧ corollary20Kappa ε K * N ≤ (E i).card ∧
        ∀ x ∈ E i, L i x ∈ U x) ∧
      (N : Real) + m * (corollary20Kappa ε K * N) ≤ covPotential U E L ∧
      ((Finset.univ.filter (IsBadTriple U E L)).card : Real) < ε * (N : Real) ^ 3) := by
    intro s
    induction s with
    | zero =>
      refine Or.inl ⟨0, Fin.elim0, Fin.elim0, rfl, fun i => i.elim0, ?_⟩
      rw [covPotential_empty]
      simp
    | succ s ih =>
      rcases ih with ⟨m, E, L, hm, hF, hP⟩ | ⟨m, E, L, hm, hF, hP, hbad⟩
      · by_cases hbad : ((Finset.univ.filter (IsBadTriple U E L)).card : Real) < ε * (N : Real) ^ 3
        · exact Or.inr ⟨m, E, L, by omega, hF, by simpa [hm] using hP, hbad⟩
        · push Not at hbad
          obtain ⟨f, E', hnew, hcard, hF'⟩ := corollary20_step_eight U h0 hK1 hK E L hε hbad
          refine Or.inl ⟨m + 1, Fin.snoc E E', Fin.snoc L f, by omega, ?_, ?_⟩
          · intro i
            refine Fin.lastCases ?_ (fun j => ?_) i
            · simpa using (And.intro hF' (And.intro hcard (fun x hx => (hnew x hx).1)))
            · simpa using hF j
          · have hgrow := potential_snoc U E L E' f hnew
            have hgrowR : (covPotential U E L : Real) + E'.card ≤
                covPotential U (Fin.snoc E E' : Fin (m + 1) → Finset (ZMod N))
                  (Fin.snoc L f : Fin (m + 1) → ZMod N → ZMod N) := by exact_mod_cast hgrow
            push_cast
            linarith
      · exact Or.inr ⟨m, E, L, by omega, hF, hP, hbad⟩
  set s := ⌊(K : Real) / corollary20Kappa ε K⌋₊ + 1
  rcases key s with ⟨m, E, L, hm, hF, hP⟩ | hdone
  · exfalso
    have hle : (covPotential U E L : Real) ≤ K * N := by
      exact_mod_cast covPotential_le U h0 hK E L
    have hs : (K : Real) / corollary20Kappa ε K < s := by
      have := Nat.lt_floor_add_one ((K : Real) / corollary20Kappa ε K)
      simpa [s] using this
    have hsκ : (K : Real) < s * corollary20Kappa ε K := by
      rw [div_lt_iff₀ hκ] at hs
      linarith
    have : (s : Real) * (corollary20Kappa ε K * N) > K * N := by
      have := mul_lt_mul_of_pos_right hsκ hNR
      linarith
    linarith
  · obtain ⟨m, E, L, hm, hF, hP, hbad⟩ := hdone
    refine ⟨m, E, L, ?_, hF, hbad⟩
    have hle : (covPotential U E L : Real) ≤ K * N := by
      exact_mod_cast covPotential_le U h0 hK E L
    have hmul : ((m : Real) * corollary20Kappa ε K) * N ≤ ((K : Real) - 1) * N := by
      nlinarith only [hP, hle]
    exact (mul_le_mul_iff_left₀ hNR).mp hmul

/-- The previous count bound follows from the tighter potential budget. -/
theorem corollary20_dense_eight [Fact N.Prime] (U : ZMod N → Finset (ZMod N))
    (h0 : ∀ x, (0 : ZMod N) ∈ U x) {K : Nat} (hK1 : 1 ≤ K) (hK : ∀ x, (U x).card ≤ K)
    {ε : Real} (hε : 0 < ε) :
    ∃ (m : Nat) (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N),
      m ≤ ⌊(K : Real) / corollary20Kappa ε K⌋₊ + 1 ∧ (∀ i, FreimanHom 8 (E i) (L i) ∧ corollary20Kappa ε K * N ≤ (E i).card ∧
        ∀ x ∈ E i, L i x ∈ U x) ∧
      ((Finset.univ.filter (IsBadTriple U E L)).card : Real) < ε * (N : Real) ^ 3 := by
  obtain ⟨m, E, L, hm, hE, hbad⟩ := corollary20_dense_eight_budget U h0 hK1 hK hε
  have hk : 0 < corollary20Kappa ε K := by
    unfold corollary20Kappa
    have : (1 : Real) ≤ K := by exact_mod_cast hK1
    positivity
  have hmR : (m : Real) ≤ (K : Real) / corollary20Kappa ε K :=
    (le_div_iff₀ hk).mpr (by linarith)
  have hmNat : m ≤ ⌊(K : Real) / corollary20Kappa ε K⌋₊ :=
    (Nat.le_floor_iff (by positivity)).mpr hmR
  exact ⟨m, E, L, by omega, hE, hbad⟩

end LeanProofs.GowersSzemeredi
