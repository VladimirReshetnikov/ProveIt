import GowersSzemeredi.Proofs05QuadraticLocalization

/-! Simultaneous quadratic phase localization with an explicit finite budget. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def quadraticFamilyBudget : Nat → Nat → Nat
  | 0, U => U
  | q + 1, U => (2 * quadraticFamilyBudget q U) ^ 1024

theorem quadraticFamilyBudget_ge (q U : Nat) : U ≤ quadraticFamilyBudget q U := by
  induction q with
  | zero => rfl
  | succ q ih =>
    exact ih.trans ((Nat.le_mul_of_pos_left _ (by omega : 0 < 2)).trans
      (Nat.le_pow (by omega : 0 < 1024)))

theorem quadraticFamilyBudget_bound (q U : Nat) :
    4 * quadraticFamilyBudget q U ≤ (4 * U) ^ (1024 ^ q) := by
  induction q with
  | zero => simp [quadraticFamilyBudget]
  | succ q ih =>
    change 4 * (2 * quadraticFamilyBudget q U) ^ 1024 ≤ _
    calc
      _ ≤ 2 ^ 1024 * (2 * quadraticFamilyBudget q U) ^ 1024 :=
        Nat.mul_le_mul_right _ (show 2 ^ 2 ≤ 2 ^ 1024 from
          Nat.pow_le_pow_right (by omega) (by omega))
      _ = (4 * quadraticFamilyBudget q U) ^ 1024 := by rw [← mul_pow]; congr 1; ring
      _ ≤ ((4 * U) ^ (1024 ^ q)) ^ 1024 := Nat.pow_le_pow_left ih _
      _ = _ := by rw [← pow_mul, pow_succ]

theorem quadratic_family_phase_localization {N q : Nat} [NeZero N]
    (P : ModAP N) (phi : Fin q → ZMod N → ZMod N) (U : Nat)
    (hP : P.IsProper) (hphi : ∀ i, PolynomialOn 2 Finset.univ (phi i))
    (hU : 2 ≤ U) (hbudget : quadraticFamilyBudget q U ≤ P.length) :
    ∃ m : Nat, ∃ R : Fin m → ModAP N,
      IsPartition (fun j => (R j).carrier) P.carrier ∧
      ∀ j, (R j).IsProper ∧ U ≤ (R j).length ∧
        ∀ i, ∃ z : Complex, ‖z‖ = 1 ∧
          ∀ x, x ∈ (R j).carrier → ‖exponential (-(phi i x)) - z‖ ≤ 1 / (4 * U) := by
  induction q generalizing P with
  | zero =>
    exact ⟨1, fun _ => P, ⟨fun x => by simp, fun i j hij =>
      ((bne_iff_ne.mp hij) (Subsingleton.elim _ _)).elim⟩,
      fun _ => ⟨hP, hbudget, fun i => Fin.elim0 i⟩⟩
  | succ q ih =>
    -- localize `phi 0` at the budget of the remaining `q` phases, then refine every cell
    let V := quadraticFamilyBudget q U
    have hUV : U ≤ V := quadraticFamilyBudget_ge q U
    obtain ⟨M, C, z, hCpart, hC⟩ := thresholdFreePolynomialLocalization_two N P (phi 0) V hP
      (hphi 0) (hU.trans hUV) (show (2 * V) ^ 1024 ≤ P.length from hbudget)
    choose m R hpart hcells using fun i : Fin M =>
      ih (C i) (fun j => phi j.succ) (hC i).1 (fun j => hphi j.succ) (hC i).2.1
    let e := section5NatFlattenEquiv m
    refine ⟨∑ i, m i, (fun j => let v := e.symm j; R v.1 v.2), finsetPartition_flatten m
      (fun i => (C i).carrier) P.carrier (fun i j => (R i j).carrier) hCpart hpart, fun j => ?_⟩
    obtain ⟨hprop, hlen, hrest⟩ := hcells (e.symm j).1 (e.symm j).2
    refine ⟨hprop, hlen, fun i => Fin.cases ⟨z (e.symm j).1, (hC _).2.2.1, fun x hx =>
      ((hC _).2.2.2 x ((hpart _).cell_subset _ hx)).trans ?_⟩ hrest i⟩
    gcongr

end LeanProofs.GowersSzemeredi
