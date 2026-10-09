import GowersSzemeredi.Proofs16DualTestSelection

/-! One evaluation and character preserve a positive fraction of the
columns while detecting a positive fraction of the active local models. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def modelTestDensity (g d : Nat) (r : Real) : Real :=
  1/(4*(refinementCells (r/2) : Real)^(g+d))

theorem modelTestDensity_pos (g d : Nat) {r : Real} (hr : 0 < r) :
    0 < modelTestDensity g d r := by
  have hQ : 0 < refinementCells (r/2) := Nat.ceil_pos.mpr (by positivity)
  unfold modelTestDensity
  positivity

/-- All column-domain conditions are included in the counted test events. -/
theorem exists_model_test {J : Type*} {N g d : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N)) (I : Finset J) (Gamma : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (f : J → ZMod N → ZMod N)
    {rho r : Real} (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho)
    (hA : A.Nonempty) (hI : I.Nonempty) (hGamma : Gamma.card ≤ g)
    (hT : ∀ x ∈ A, (T x).card ≤ d)
    (hf : ∀ j ∈ I, IsFreimanLinearOn (bohr Gamma rho) (f j))
    (hf0 : ∀ j ∈ I, f j 0 = 0)
    (hne : ∀ j ∈ I, ∃ y ∈ bohr Gamma (refinementKernelRadius g d rho (r/2)), f j y ≠ 0)
    (hN : refinementKernelCap g d rho (r/2) < N) (h7 : 7 ≤ N) :
    ∃ y gamma : ZMod N, y ∈ bohr Gamma r ∧
      modelTestDensity g d r*A.card ≤ ((A.filter (fun x => y ∈ bohr (T x) r)).card : Real) ∧
      modelTestDensity g d r*I.card ≤ ((I.filter (fun j => Separates gamma (f j y))).card : Real) := by
  let M := (Finset.univ : Finset (ZMod N × ZMod N))
  let E := fun x (p : ZMod N × ZMod N) => p.1 ∈ bohr Gamma r ∧ p.1 ∈ bohr (T x) r
  let D := fun j (p : ZMod N × ZMod N) => Separates p.2 (f j p.1)
  have hcount : ∀ x ∈ A, ∀ j ∈ I, modelTestDensity g d r*M.card ≤
      ((M.filter (fun p => E x p ∧ D j p)).card : Real) := by
    intro x hx j hj
    have heq : M.filter (fun p => E x p ∧ D j p) =
        localSeparatingTests (bohr (Gamma ∪ T x) r) (f j) := by
      ext p
      simp [M,E,D,localSeparatingTests,bohr_union,and_assoc]
    rw [heq]
    have h := freiman_local_separating_tests Gamma (T x) (f j) hrho hr hrle hGamma (hT x hx)
      (hf j hj) (hf0 j hj) (hne j hj) hN h7
    convert h using 1
    simp only [M,modelTestDensity,Finset.card_univ,Fintype.card_prod,ZMod.card,Nat.cast_mul]
    ring
  obtain ⟨p,_,ha,hi⟩ := dual_test_selection A I M E D (beta := modelTestDensity g d r) hA hI Finset.univ_nonempty hcount
  have hpos : (0 : Real) < (A.filter (fun x => E x p)).card :=
    (mul_pos (modelTestDensity_pos g d hr) (show (0 : Real) < A.card by exact_mod_cast Finset.card_pos.mpr hA)).trans_le ha
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < (A.filter (fun x => E x p)).card by exact_mod_cast hpos)
  have hy : p.1 ∈ bohr Gamma r := (Finset.mem_filter.mp hx).2.1
  refine ⟨p.1,p.2,hy,?_,hi⟩
  simpa only [E,hy,true_and] using ha

end LeanProofs.GowersSzemeredi
