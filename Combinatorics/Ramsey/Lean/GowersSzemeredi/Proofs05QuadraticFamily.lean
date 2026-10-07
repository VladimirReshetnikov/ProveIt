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
  classical
  induction q generalizing P with
  | zero =>
    refine ⟨1, fun _ => P, ?_, ?_⟩
    · constructor
      · intro x; simp
      · intro i j hij; exact ((bne_iff_ne.mp hij) (Subsingleton.elim _ _)).elim
    · intro j
      exact ⟨hP, hbudget, fun i => Fin.elim0 i⟩
  | succ q ih =>
    let V := quadraticFamilyBudget q U
    have hUV : U ≤ V := quadraticFamilyBudget_ge q U
    have hV : 2 ≤ V := hU.trans hUV
    obtain ⟨M, C, z, hCpart, hC⟩ := thresholdFreePolynomialLocalization_two
      N P (phi 0) V hP (hphi 0) hV (by
        change (2 * V) ^ 1024 ≤ P.length
        exact hbudget)
    have hlocal (i : Fin M) := ih (C i) (fun j => phi j.succ)
      (hC i).1 (fun j => hphi j.succ) (hC i).2.1
    choose m R hpart hcells using hlocal
    let e := section5NatFlattenEquiv m
    refine ⟨∑ i, m i, (fun j => let v := e.symm j; R v.1 v.2), ?_, ?_⟩
    · exact finsetPartition_flatten m (fun i => (C i).carrier) P.carrier
        (fun i j => (R i j).carrier) hCpart hpart
    · intro j
      let v := e.symm j
      refine ⟨(hcells v.1 v.2).1, (hcells v.1 v.2).2.1, ?_⟩
      intro i
      refine Fin.cases ?_ (fun k => (hcells v.1 v.2).2.2 k) i
      refine ⟨z v.1, (hC v.1).2.2.1, ?_⟩
      intro x hx
      apply ((hC v.1).2.2.2 x ((hpart v.1).cell_subset v.2 hx)).trans
      apply one_div_le_one_div_of_le (by positivity : (0 : Real) < 4 * U)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hUV) (by norm_num)

end LeanProofs.GowersSzemeredi
