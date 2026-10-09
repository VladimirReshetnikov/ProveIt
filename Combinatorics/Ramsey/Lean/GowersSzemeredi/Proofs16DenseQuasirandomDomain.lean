import GowersSzemeredi.Proofs16DenseRelationIteration
import GowersSzemeredi.Proofs16ExplicitGraphCutoff

/-! A dense row configuration admits a dense refinement whose actual Bohr
graph has arbitrarily small prescribed box error. Both the relation
cutoff and the rank/density losses are explicit and independent of N. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Combine dense relation iteration with the explicit graph cutoff. The
quasirandomness conclusion is obtained rather than assumed. -/
theorem exists_dense_quasirandom_domain {N Q H : Nat} [NeZero N] [NeZero Q] [NeZero H]
    [Fact N.Prime] {κ : Type*} [Fintype κ] (A : Finset (ZMod N × ZMod N))
    (W F Gamma : Finset (ZMod N)) (L : κ → ZMod N → ZMod N) (a : ZMod N)
    {sigma alpha eta epsilon : Real} (hsigma : 0 < sigma)
    (hsigmaMax : sigma ≤ 1 / (8 * Real.pi)) (ha : 0 < alpha)
    (heta : 0 < eta) (hetaQuarter : eta < 1 / 4)
    (heps : 0 < epsilon) (hepsOne : epsilon ≤ 1)
    (hQ : 4 ≤ sigma * Q) (hH : (2 : Real)^(Fintype.card κ) ≤ eta * H)
    (hN : 1 / relationProfileSmoothing epsilon H
      (F.card + Fintype.card κ * Fintype.card κ + 2 * Fintype.card κ) ≤ N)
    (hW : W ⊆ bohr Gamma (sigma / 4))
    (hL : ∀ j, IsFreimanLinearOn (bohr Gamma sigma) (L j))
    (hzero : ∀ j, L j 0 = 0) (hcard : alpha * N ≤ W.card)
    (hgeom : tupleRowGeometry A W F L a eta) :
    let k := Fintype.card κ
    let m := F.card + k * k + 2 * k
    let R := relationProfileCutoff epsilon H m
    let n := k - Module.finrank (ZMod N) (relationSubmodule (bohr Gamma sigma) L)
    let D := (denseRelationBudget (epsilon / 6) R Q k)^[n] (max Gamma.card F.card)
    let rho := eta / (2 : Real)^n
    ∃ (S V F' : Finset (ZMod N)) (a' : ZMod N) (delta : Real),
      Gamma ⊆ S ∧ S.card ≤ D ∧
      bohr S sigma ⊆ bohr Gamma sigma ∧ bohr S (sigma / 4) ⊆ bohr Gamma (sigma / 4) ∧
      V.Nonempty ∧ V ⊆ bohr S (sigma / 4) ∧
      (alpha / (Q : Real)^(n * D)) * N ≤ V.card ∧
      F ⊆ F' ∧ F'.card ≤ F.card + n * k ∧
      tupleRowGeometry A V F' L a' rho ∧ 0 ≤ delta ∧ delta ≤ 1 ∧
      boxSum (fun (x : ↥(bohr F' rho)) (y : ↥(bohr S (sigma / 4))) =>
        (if (x : ZMod N) ∈ bohr (Finset.univ.image fun j => L j y) (rho / 4)
          then (1 : Real) else 0) - delta) ≤
      epsilon * ((bohr F' rho).card : Real)^2 * ((bohr S (sigma / 4)).card : Real)^2 := by
  let k := Fintype.card κ
  let m := F.card + k * k + 2 * k
  let R := relationProfileCutoff epsilon H m
  let n := k - Module.finrank (ZMod N) (relationSubmodule (bohr Gamma sigma) L)
  let rho := eta / (2 : Real)^n
  have hn : n ≤ k := Nat.sub_le _ _
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrhoLe : rho ≤ eta := div_le_self heta.le (one_le_pow₀ (by norm_num))
  have hrhoH : 1 ≤ rho * H := by
    have hp : (2 : Real)^n ≤ (2 : Real)^k := pow_le_pow_right₀ (by norm_num) hn
    have h := hp.trans hH
    dsimp only [rho]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (by positivity)).mpr (by simpa only [one_mul] using h)
  obtain ⟨S, V, F', a', hGS, hS, hfull, hquarter, hVne, hV, hVcard, hFF', hFcard, hgeom', hbad⟩ :=
    exists_dense_sparse_relation_domain A W F Gamma L a hsigma hsigmaMax
      (by positivity : 0 < epsilon / 6) ha heta.le hQ R hW hL hcard hgeom
  have hfreq : Fintype.card ↥F' + 2 * Fintype.card κ ≤ m := by
    rw [Fintype.card_coe]
    have hnk : n * k ≤ k * k := Nat.mul_le_mul_right k hn
    change F'.card ≤ F.card + n * k at hFcard
    dsimp only [m]
    omega
  have hC : bohr S (sigma / 4) ⊆ bohr S sigma := bohr_mono_radius S (by linarith)
  have hCne : (bohr S (sigma / 4)).Nonempty := ⟨0, zero_mem_bohr S (by positivity)⟩
  obtain ⟨delta, hd0, hd1, hbox⟩ := tuple_bohr_quasirandom_explicit
    (Q := H) (fun i : ↥F' => (i : ZMod N)) (bohr S sigma) (bohr S (sigma / 4)) hC hCne
    L hzero m hrho.le (show 0 ≤ rho / 4 by positivity)
    (hrhoLe.trans_lt hetaQuarter) (show rho / 4 < 1 / 4 by linarith)
    heps hepsOne hN hrhoH hfreq hbad.le
  have himage : Finset.univ.image (fun i : ↥F' => (i : ZMod N)) = F' := by ext x; simp
  rw [boxSum_finset_congr (congrArg (fun T => bohr T rho) himage)
    (fun x (y : ↥(bohr S (sigma / 4))) =>
      (if x ∈ bohr (Finset.univ.image fun j => L j y) (rho / 4) then (1 : Real) else 0) - delta)] at hbox
  rw [himage] at hbox
  exact ⟨S, V, F', a', delta, hGS, hS, hfull, hquarter, hVne, hV, hVcard,
    hFF', hFcard, hgeom', hd0, hd1, hbox⟩

end LeanProofs.GowersSzemeredi
