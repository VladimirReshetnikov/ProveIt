import GowersSzemeredi.Proofs16AdaptiveGraphSchedule
import GowersSzemeredi.Proofs16TupleDensityLower

/-! Dense Bohr graphs with an accuracy chosen for the retained density.
The positive graph-density bound and all Fourier budgets are discharged. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Adaptive quasirandom refinement. The error e(D) and the retained density
alpha/Q^D refer to the same exact final state D. -/
theorem exists_adaptive_dense_graph {N Q H : Nat} [NeZero N] [NeZero Q] [NeZero H]
    [Fact N.Prime] {κ : Type*} [Fintype κ] (A : Finset (ZMod N × ZMod N))
    (W F Gamma : Finset (ZMod N)) (L : κ → ZMod N → ZMod N) (a : ZMod N)
    (e : Nat → Real) {sigma alpha eta : Real} (hsigma : 0 < sigma)
    (hsigmaMax : sigma ≤ 1 / (8 * Real.pi)) (ha : 0 < alpha)
    (heta : 0 < eta) (hetaQuarter : eta < 1 / 4)
    (he : ∀ d, 0 < e d ∧ e d ≤ (1 / ((4 * H : Nat) : Real)^
      (F.card + Fintype.card κ * Fintype.card κ + 2 * Fintype.card κ)) / 2)
    (hQ : 4 ≤ sigma * Q) (hH : (2 : Real)^(Fintype.card κ) ≤ eta * H)
    (hN : adaptiveGraphModulusBound e H
      (F.card + Fintype.card κ * Fintype.card κ + 2 * Fintype.card κ)
      Q (Fintype.card κ) (max Gamma.card F.card) ≤ N)
    (hW : W ⊆ bohr Gamma (sigma / 4))
    (hL : ∀ j, IsFreimanLinearOn (bohr Gamma sigma) (L j))
    (hzero : ∀ j, L j 0 = 0) (hcard : alpha * N ≤ W.card)
    (hgeom : tupleRowGeometry A W F L a eta) :
    let k := Fintype.card κ
    let m := F.card + k * k + 2 * k
    ∃ s : Nat, s ≤ k - Module.finrank (ZMod N) (relationSubmodule (bohr Gamma sigma) L) ∧
    let D := (adaptiveGraphState e H m Q k)^[s] (max Gamma.card F.card)
    let rho := eta / (2 : Real)^s
    ∃ (S V F' : Finset (ZMod N)) (a' : ZMod N) (delta : Real),
      Gamma ⊆ S ∧ S.card ≤ D ∧ F'.card ≤ D ∧
      bohr S sigma ⊆ bohr Gamma sigma ∧ bohr S (sigma / 4) ⊆ bohr Gamma (sigma / 4) ∧
      V.Nonempty ∧ V ⊆ bohr S (sigma / 4) ∧
      (alpha / (Q : Real)^D) * N ≤ V.card ∧ F ⊆ F' ∧ F'.card ≤ F.card + s * k ∧
      tupleRowGeometry A V F' L a' rho ∧
      (1 / ((4 * H : Nat) : Real)^m) / 2 ≤ delta ∧ delta ≤ 1 ∧
      boxSum (fun (x : ↥(bohr F' rho)) (y : ↥(bohr S (sigma / 4))) =>
        (if (x : ZMod N) ∈ bohr (Finset.univ.image fun j => L j y) (rho / 4)
          then (1 : Real) else 0) - delta) ≤
      (e D)^4 * ((bohr F' rho).card : Real)^2 * ((bohr S (sigma / 4)).card : Real)^2 := by
  let k := Fintype.card κ
  let m := F.card + k * k + 2 * k
  let d := max Gamma.card F.card
  let theta := fun d => (e d)^4 / 6
  let R := fun d => relationProfileCutoff ((e d)^4) H m
  let n := k - Module.finrank (ZMod N) (relationSubmodule (bohr Gamma sigma) L)
  have hQone : (1 : Real) ≤ Q := by exact_mod_cast NeZero.pos Q
  have hHone : (1 : Real) ≤ H := by exact_mod_cast NeZero.pos H
  have hbetaOne : 1 / ((4 * H : Nat) : Real)^m ≤ 1 := by
    have hbase : (1 : Real) ≤ (4 * H : Nat) := by push_cast; linarith
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ hbase)
  have hstart : (alpha / (Q : Real)^d) * N ≤ W.card :=
    (mul_le_mul_of_nonneg_right (div_le_self ha.le (one_le_pow₀ hQone)) (by positivity)).trans hcard
  have hrank : k ≤ Module.finrank (ZMod N) (relationSubmodule (bohr Gamma sigma) L) + n := by
    dsimp only [n]; omega
  obtain ⟨s, hs, S, V, F', a', hGS, hS, hFstate, hfull, hquarter, hVne, hV,
      hVcard, hFF', hFcard, hgeom', hbad⟩ :=
    adaptive_dense_relation_iteration A L theta R (fun d => by dsimp [theta]; exact div_pos (pow_pos (he d).1 _) (by norm_num))
      hsigma hsigmaMax ha hQ n d W F Gamma a eta heta.le
      (le_max_left _ _) (le_max_right _ _) hrank hW hL hstart hgeom
  let D := (adaptiveGraphState e H m Q k)^[s] d
  let rho := eta / (2 : Real)^s
  have hsk : s ≤ k := hs.trans (Nat.sub_le _ _)
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrhoLe : rho ≤ eta := div_le_self heta.le (one_le_pow₀ (by norm_num))
  have hrhoH : 1 ≤ rho * H := by
    have hp : (2 : Real)^s ≤ (2 : Real)^k := pow_le_pow_right₀ (by norm_num) hsk
    dsimp only [rho]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (by positivity)).mpr (by simpa only [one_mul] using hp.trans hH)
  have hfreq : Fintype.card ↥F' + 2 * Fintype.card κ ≤ m := by
    rw [Fintype.card_coe]
    have hskk := Nat.mul_le_mul_right k hsk
    change F'.card ≤ F.card + s * k at hFcard
    dsimp only [m]
    omega
  have hC : bohr S (sigma / 4) ⊆ bohr S sigma := bohr_mono_radius S (by linarith)
  have hCne : (bohr S (sigma / 4)).Nonempty := ⟨0, zero_mem_bohr S (by positivity)⟩
  have heOne : e D ≤ 1 := by have h := (he D).2; change e D ≤ (1 / ((4 * H : Nat) : Real)^m) / 2 at h; linarith
  have he4 : (e D)^4 ≤ 1 := by simpa using pow_le_pow_left₀ (he D).1.le heOne 4
  have hN' := adaptiveGraphModulusBound_spec e H m Q k d N s hsk hN
  obtain ⟨delta, hd0, hd1, hbox⟩ := tuple_bohr_quasirandom_explicit
    (Q := H) (fun i : ↥F' => (i : ZMod N)) (bohr S sigma) (bohr S (sigma / 4)) hC hCne
    L hzero m hrho.le (show 0 ≤ rho / 4 by positivity)
    (hrhoLe.trans_lt hetaQuarter) (show rho / 4 < 1 / 4 by linarith)
    (pow_pos (he D).1 _) he4 hN' hrhoH hfreq hbad.le
  have himage : Finset.univ.image (fun i : ↥F' => (i : ZMod N)) = F' := by ext x; simp
  rw [boxSum_finset_congr (congrArg (fun T => bohr T rho) himage)
    (fun x (y : ↥(bohr S (sigma / 4))) =>
      (if x ∈ bohr (Finset.univ.image fun j => L j y) (rho / 4) then (1 : Real) else 0) - delta)] at hbox
  rw [himage] at hbox
  have hcell : 1 ≤ rho / 4 * ((4 * H : Nat) : Real) := by push_cast; nlinarith only [hrhoH]
  have hd := tuple_bohr_density_lower (Q := 4 * H) F' (bohr S (sigma / 4)) hCne L m hrho.le
    (show rho / 4 ≤ rho by linarith) hcell (by rw [Fintype.card_coe] at hfreq; omega) (he D).1.le hbox
  refine ⟨s, hs, S, V, F', a', delta, hGS, hS, hFstate, hfull, hquarter, hVne, hV,
    hVcard, hFF', hFcard, hgeom', ?_, hd1, hbox⟩
  have h := (he D).2
  change e D ≤ (1 / ((4 * H : Nat) : Real)^m) / 2 at h
  linarith

end LeanProofs.GowersSzemeredi
