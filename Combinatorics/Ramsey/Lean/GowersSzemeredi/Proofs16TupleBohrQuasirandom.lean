import GowersSzemeredi.Proofs16ScaledRelationProfile
import GowersSzemeredi.Proofs16PatternBohrDegrees
import GowersSzemeredi.Proofs16BohrLowerBound

/-! Quasirandomness for the exact fixed/variable Bohr graph, with no
rounded-radius or weak-regularity assumptions left in its interface. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Transport a box sum along equality of its finite left-vertex sets. -/
theorem boxSum_finset_congr {X Y : Type*} [Fintype Y] {S T : Finset X}
    (h : S = T) (f : X → Y → Real) :
    boxSum (fun (x : ↥S) y => f x y) = boxSum (fun (x : ↥T) y => f x y) := by
  subst T
  rfl

/-- The graph uses the prescribed Bohr radii exactly. Its analytic budgets
are expressed using only a frequency cap, cell count, and smoothing scale. -/
theorem tuple_bohr_quasirandom_scaled {N Q : Nat} [NeZero N] [NeZero Q] [Fact N.Prime]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (gamma : ι → ZMod N)
    (D C : Finset (ZMod N)) (hC : C ⊆ D) (hCne : C.Nonempty)
    (L : κ → ZMod N → ZMod N) (hzero : ∀ j, L j 0 = 0)
    (m R : Nat) {rho nu tau theta : Real}
    (hrho : 0 ≤ rho) (hnu : 0 ≤ nu) (htau : 0 < tau)
    (hrhoHalf : rho + tau < 1 / 2) (hnuHalf : nu + tau < 1 / 2)
    (hN : 1 ≤ tau * N) (hQ : 1 ≤ rho * Q)
    (hm : Fintype.card ι + 2 * Fintype.card κ ≤ m)
    (hR : 1 / tau^2 ≤ R + 1) (hsmall : 120 * m * tau ≤ 1 / (Q : Real)^m)
    (htheta : theta < 1)
    (hbad : ((boundedBadRelationPairs gamma D L C R).card : Real) ≤ theta * (C.card : Real)^2) :
    ∃ delta : Real, 0 ≤ delta ∧ delta ≤ 1 ∧
      boxSum (fun (x : ↥(bohr (Finset.univ.image gamma) rho)) (y : ↥C) =>
        (if (x : ZMod N) ∈ bohr (Finset.univ.image fun j => L j y) nu
          then (1 : Real) else 0) - delta) ≤
      3 * (480 * m * tau / (1 / (Q : Real)^m) + theta) *
        ((bohr (Finset.univ.image gamma) rho).card : Real)^2 * (C.card : Real)^2 := by
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hQpos : (0 : Real) < Q := by exact_mod_cast NeZero.pos Q
  have hQone : (1 : Real) ≤ Q := by exact_mod_cast NeZero.pos Q
  have hbeta : 0 < 1 / (Q : Real)^m := by positivity
  have hbetaOne : 1 / (Q : Real)^m ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ hQone)
  have hcard : (Finset.univ.image gamma).card ≤ m := by
    have h := Finset.card_image_le (s := Finset.univ) (f := gamma)
    rw [Finset.card_univ] at h
    omega
  have hbase : (1 / (Q : Real)^m) * N ≤ (bohr (Finset.univ.image gamma) rho).card := by
    have hlow : (N : Real) ≤ (Q : Real)^(Finset.univ.image gamma).card *
        (bohr (Finset.univ.image gamma) rho).card := by
      exact_mod_cast bohr_card_lower (Finset.univ.image gamma) Q hQ
    have hp : (Q : Real)^(Finset.univ.image gamma).card ≤ (Q : Real)^m := by
      exact_mod_cast Nat.pow_le_pow_right (NeZero.pos Q) hcard
    have h := hlow.trans (mul_le_mul_of_nonneg_right hp (by positivity))
    rw [one_div_mul_eq_div]
    exact (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using h)
  let a : ι → Nat := fun _ => ⌊rho * N⌋₊ + ⌊tau * N⌋₊
  let b : κ → Nat := fun _ => ⌊nu * N⌋₊ + ⌊tau * N⌋₊
  have hround (r : Real) (hr : 0 ≤ r) (h : r + tau < 1 / 2) :
      2 * (⌊r * N⌋₊ + ⌊tau * N⌋₊) < N := by
    have h1 := Nat.floor_le (show 0 ≤ r * N by positivity)
    have h2 := Nat.floor_le (show 0 ≤ tau * N by positivity)
    have h3 := mul_lt_mul_of_pos_right h hNpos
    have : (2 : Real) * (⌊r * N⌋₊ + ⌊tau * N⌋₊) < N := by nlinarith
    exact_mod_cast this
  have hm' : Fintype.card (ι ⊕ (κ ⊕ κ)) ≤ m := by simpa [Fintype.card_sum, two_mul, add_assoc] using hm
  have hsmall' : 120 * Fintype.card (ι ⊕ (κ ⊕ κ)) * tau ≤ 1 / (Q : Real)^m := by
    have h : (Fintype.card (ι ⊕ (κ ⊕ κ)) : Real) ≤ m := by exact_mod_cast hm'
    nlinarith
  have hbase' : (1 / (Q : Real)^m) * N ≤ (mixedBohr gamma (fun i => a i - ⌊tau * N⌋₊)).card := by
    simpa only [a, Nat.add_sub_cancel_right, mixedBohr_floor_tuple gamma hrho] using hbase
  obtain ⟨delta, hd0, hd1, hbox⟩ := sparse_relation_profile_scaled gamma D C hC hCne L hzero a b R
    htau (by linarith) hN hbeta hbetaOne hR hsmall' hbase'
    (fun _ => Nat.le_add_left _ _) (fun _ => Nat.le_add_left _ _)
    (fun _ => hround rho hrho hrhoHalf) (fun _ => hround nu hnu hnuHalf) htheta hbad
  have hdom : mixedBohr gamma (fun i => a i - ⌊tau * N⌋₊) =
      bohr (Finset.univ.image gamma) rho := by
    simp only [a, Nat.add_sub_cancel_right, mixedBohr_floor_tuple gamma hrho]
  rw [boxSum_finset_congr hdom (fun x (y : ↥C) =>
    (if x ∈ mixedBohr (fun j => L j y) (fun j => b j - ⌊tau * N⌋₊)
      then (1 : Real) else 0) - delta)] at hbox
  simp only [a, b, Nat.add_sub_cancel_right, mixedBohr_floor_tuple gamma hrho,
    mixedBohr_floor_tuple _ hnu] at hbox
  refine ⟨delta, hd0, hd1, hbox.trans ?_⟩
  gcongr

end LeanProofs.GowersSzemeredi
