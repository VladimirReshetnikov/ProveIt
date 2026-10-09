import GowersSzemeredi.Proofs16ModelTestCells

/-! A quantitative refinement step decreases the active model set while
preserving the alternative between a zero relation and a surviving model. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def columnQuadValue {N : Nat} (L : ZMod N → ZMod N → ZMod N)
    (q : Fin 4 → ZMod N) (y : ZMod N) : ZMod N :=
  L (q 0) y-L (q 1) y+L (q 2) y-L (q 3) y

/-- Zero relations at `s` or a model comparison at the testing radius `r`.
The two radii are deliberately separate. -/
def ColumnQuadModelAlternatives {J : Type*} {N : Nat} [NeZero N]
    (A Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (s r : Real) (I : Finset J)
    (f : J → ZMod N → ZMod N) : Prop :=
  ∀ q : Fin 4 → ZMod N, (∀ i, q i ∈ A) → q 0-q 1+q 2-q 3 = 0 →
    (∀ y ∈ bohr Gamma s, (∀ i, y ∈ bohr (T (q i)) s) → columnQuadValue L q y = 0) ∨
      ∃ j ∈ I, ∀ y ∈ bohr Gamma r, (∀ i, y ∈ bohr (T (q i)) r) → columnQuadValue L q y = f j y

/-- One step retains at least `beta/10` of the columns and at most
`1-beta` of the active models, without losing the model alternatives. -/
theorem column_model_elimination_step {J : Type*} {N g d : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N)) (I : Finset J) (Gamma : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (f : J → ZMod N → ZMod N) {rho r s : Real}
    (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho)
    (hA : A.Nonempty) (hI : I.Nonempty) (hGamma : Gamma.card ≤ g)
    (hT : ∀ x ∈ A, (T x).card ≤ d)
    (hf : ∀ j ∈ I, IsFreimanLinearOn (bohr Gamma rho) (f j))
    (hf0 : ∀ j ∈ I, f j 0 = 0)
    (hne : ∀ j ∈ I, ∃ y ∈ bohr Gamma (refinementKernelRadius g d rho (r/2)), f j y ≠ 0)
    (hN : refinementKernelCap g d rho (r/2) < N) (h7 : 7 ≤ N)
    (hcover : ColumnQuadModelAlternatives A Gamma T L s r I f) :
    ∃ P ⊆ A, ∃ I' ⊆ I,
      modelTestDensity g d r/10*A.card ≤ (P.card : Real) ∧
      (I'.card : Real) ≤ (1-modelTestDensity g d r)*I.card ∧
      ColumnQuadModelAlternatives P Gamma T L s r I' f := by
  classical
  obtain ⟨P,y,gamma,hPA,hP,hy,hdom,hdet,havoid⟩ :=
    exists_model_test_cell A I Gamma T L f hrho hr hrle hA hI hGamma hT hf hf0 hne hN h7
  let I' := I.filter (fun j => ¬ Separates gamma (f j y))
  have hcount : (I'.card : Real) ≤ (1-modelTestDensity g d r)*I.card := by
    have hc := Finset.card_filter_add_card_filter_not (s := I) (fun j => Separates gamma (f j y))
    have hcR : ((I.filter (fun j => Separates gamma (f j y))).card : Real)+I'.card = I.card := by
      exact_mod_cast hc
    nlinarith only [hcR,hdet]
  refine ⟨P,hPA,I',Finset.filter_subset _ _,hP,hcount,?_⟩
  intro q hq hadd
  rcases hcover q (fun i => hPA (hq i)) hadd with hz | ⟨j,hj,hmodel⟩
  · exact Or.inl hz
  · apply Or.inr
    refine ⟨j,Finset.mem_filter.mpr ⟨hj,?_⟩,hmodel⟩
    intro hsep
    exact havoid (q 0) (hq 0) (q 1) (hq 1) (q 2) (hq 2) (q 3) (hq 3) j hj hsep
      (hmodel y hy (fun i => hdom _ (hq i)))

end LeanProofs.GowersSzemeredi
