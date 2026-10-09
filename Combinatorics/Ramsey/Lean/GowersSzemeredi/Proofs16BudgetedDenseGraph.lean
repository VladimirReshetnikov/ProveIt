import GowersSzemeredi.Proofs16AdaptiveFillingError

/-! Dense quasirandom row geometry with the robust filling error budget
proved as a conclusion, using the actual retained ambient density. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The adaptive construction pays the robust seven-operator scalar budget
at its actual final density, without a fixed-point hypothesis. -/
theorem exists_budgeted_dense_graph {N Q H : Nat} [NeZero N] [NeZero Q] [NeZero H]
    [Fact N.Prime] {κ : Type*} [Fintype κ] (A : Finset (ZMod N × ZMod N))
    (W F Gamma : Finset (ZMod N)) (L : κ → ZMod N → ZMod N) (a : ZMod N)
    {sigma alpha eta : Real} (hsigma : 0 < sigma)
    (hsigmaMax : sigma ≤ 1 / (8 * Real.pi)) (ha : 0 < alpha)
    (heta : 0 < eta) (hetaQuarter : eta < 1 / 4)
    (hQ : 4 ≤ sigma * Q) (hH : (2 : Real)^(Fintype.card κ) ≤ eta * H)
    (hN : adaptiveGraphModulusBound
      (adaptiveFillingError alpha Q H
        (F.card + Fintype.card κ * Fintype.card κ + 2 * Fintype.card κ)) H
      (F.card + Fintype.card κ * Fintype.card κ + 2 * Fintype.card κ)
      Q (Fintype.card κ) (max Gamma.card F.card) ≤ N)
    (hW : W ⊆ bohr Gamma (sigma / 4))
    (hL : ∀ j, IsFreimanLinearOn (bohr Gamma sigma) (L j))
    (hzero : ∀ j, L j 0 = 0) (hcard : alpha * N ≤ W.card)
    (hgeom : tupleRowGeometry A W F L a eta) :
    let k := Fintype.card κ
    let m := F.card + k * k + 2 * k
    let e := adaptiveFillingError alpha Q H m
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
      (e D)^4 * ((bohr F' rho).card : Real)^2 * ((bohr S (sigma / 4)).card : Real)^2 ∧
      (4 : Real)^(m + 1) * (12 * e D) * ((4 * H : Nat) : Real)^m ≤
        (delta^3 * robustRepresentationDensity ((V.card : Real) / N) (bohr S (sigma / 4)))^2 := by
  let k := Fintype.card κ
  let m := F.card + k * k + 2 * k
  let e := adaptiveFillingError alpha Q H m
  obtain ⟨s, hs, S, V, F', a', delta, hGS, hS, hFstate, hfull, hquarter,
      hVne, hV, hVcard, hFF', hFcard, hgeom', hd, hd1, hbox⟩ :=
    exists_adaptive_dense_graph A W F Gamma L a e hsigma hsigmaMax ha heta hetaQuarter
      (fun d => adaptiveFillingError_pos_le ha Q H m d) hQ hH hN hW hL hzero hcard hgeom
  refine ⟨s, hs, S, V, F', a', delta, hGS, hS, hFstate, hfull, hquarter,
    hVne, hV, hVcard, hFF', hFcard, hgeom', hd, hd1, hbox, ?_⟩
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  apply adaptiveFillingError_robust_budget (bohr S (sigma / 4))
    ⟨0, zero_mem_bohr S (by positivity)⟩ ha Q H m _ _ hd
  exact (le_div_iff₀ hNpos).mpr hVcard

end LeanProofs.GowersSzemeredi
