import GowersSzemeredi.Proofs00Basics

/-! Declarations of `Proofs00Basics` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section

open scoped BigOperators Pointwise ZMod
open Finset

lemma restriction_mulLeft_range {N : Nat} [NeZero N] (h : ZMod N) :
    (AddMonoidHom.mulLeft h).range = AddSubgroup.zmultiples h := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rw [show x = (x.val : ZMod N) by
      exact (ZMod.natCast_zmod_val x).symm]
    simpa [mul_comm] using
      (AddSubgroup.intCast_mul_mem_zmultiples h (Int.ofNat x.val))
  · intro hz
    rw [AddSubgroup.mem_zmultiples_iff] at hz
    rcases hz with ⟨k, rfl⟩
    refine ⟨(k : ZMod N), ?_⟩
    change h * (k : ZMod N) = k • h
    rw [zsmul_eq_mul]
    exact mul_comm _ _

end

section

open scoped BigOperators Pointwise ZMod
open Finset

lemma restriction_mul_kernel_card {N : Nat} [NeZero N]
    (h : ZMod N) :
    Fintype.card {x : ZMod N // h * x = 0} = N.gcd h.val := by
  let f : ZMod N →+ ZMod N := AddMonoidHom.mulLeft h
  have hrange : Nat.card f.range = addOrderOf h := by
    rw [restriction_mulLeft_range h, Nat.card_zmultiples]
  have hcard : Nat.card f.ker * Nat.card f.range = Nat.card (ZMod N) := by
    rw [← AddSubgroup.index_ker f]
    exact f.ker.card_mul_index
  have hord : addOrderOf h = N / N.gcd h.val := by
    calc
      addOrderOf h = addOrderOf (h.val : ZMod N) := by
        rw [ZMod.natCast_zmod_val]
      _ = N / N.gcd h.val := ZMod.addOrderOf_coe h.val (NeZero.ne N)
  have hprod : Nat.card f.ker * (N / N.gcd h.val) = N := by
    rw [← hord, ← hrange]
    simpa using hcard
  have hgpos : 0 < N.gcd h.val :=
    Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne N))
  have hdiv : N.gcd h.val ∣ N := Nat.gcd_dvd_left _ _
  have hquotpos : 0 < N / N.gcd h.val :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdiv)
      hgpos
  have heq : N.gcd h.val * (N / N.gcd h.val) = N :=
    Nat.mul_div_cancel' hdiv
  have hker : Nat.card f.ker = N.gcd h.val :=
    Nat.eq_of_mul_eq_mul_right hquotpos (hprod.trans heq.symm)
  let e : {x : ZMod N // h * x = 0} ≃ f.ker :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun x ↦ by rfl)
  calc
    Fintype.card {x : ZMod N // h * x = 0} = Fintype.card f.ker :=
      Fintype.card_congr e
    _ = N.gcd h.val := by
      simpa [Nat.card_eq_fintype_card] using hker

end

section

open scoped BigOperators ZMod
open Finset

lemma cor58_sum_partition {X R : Type*} [DecidableEq X] {m : Nat}
    [AddCommMonoid R] (P : Fin m → Finset X) (S : Finset X)
    (hpartition : IsPartition P S) (g : X → R) :
    ∑ j, ∑ x ∈ P j, g x = ∑ x ∈ S, g x := by
  classical
  have hpair : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint P := by
    intro i _ j _ hij
    exact hpartition.2 i j (bne_iff_ne.mpr hij)
  have hunion : (Finset.univ : Finset (Fin m)).biUnion P = S := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact (hpartition.1 x).symm
  rw [show (∑ j, ∑ x ∈ P j, g x) =
      ∑ j ∈ (Finset.univ : Finset (Fin m)), ∑ x ∈ P j, g x by simp]
  rw [← Finset.sum_biUnion hpair, hunion]

end

section

open scoped BigOperators ZMod
open Finset

lemma cor25_density_bounds {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) : 0 ≤ density A ∧ density A ≤ 1 := by
  have hcard : A.card ≤ N := by
    calc
      A.card ≤ (Finset.univ : Finset (ZMod N)).card := A.card_le_univ
      _ = N := by simp
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  constructor
  · unfold density
    positivity
  · unfold density
    rw [div_le_one hN]
    exact_mod_cast hcard

end

section

open scoped BigOperators ZMod
open Finset

lemma fourier_indicator_norm_le_card' {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (r : ZMod N) :
    ‖fourier (indicator A) r‖ ≤ A.card := by
  exact fourier_indicator_norm_le_card A r

end

section

open scoped BigOperators ZMod
open Finset

lemma cor58_density_eq {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (delta : Real)
    (hcard : (A.card : Real) = delta * N) : density A = delta := by
  rw [density, hcard]
  exact mul_div_cancel_right₀ delta (by exact_mod_cast NeZero.ne N)

end

end LeanProofs.GowersSzemeredi
