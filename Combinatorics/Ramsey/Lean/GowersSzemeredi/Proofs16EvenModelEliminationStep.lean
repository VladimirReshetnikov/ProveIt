import GowersSzemeredi.Proofs16EvenModelCells

/-! Eliminate detected models from all alternating lists of a fixed even length. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def ColumnEvenModelAlternatives {J : Type*} {N : Nat} [NeZero N]
    (A Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (k : Nat) (s r : Real) (I : Finset J)
    (f : J → ZMod N → ZMod N) : Prop :=
  ∀ as : List (ZMod N), as.length = 2*k → (∀ x ∈ as, x ∈ A) → columnAnchorEval id as = 0 →
    (∀ y ∈ bohr Gamma s, (∀ x ∈ as, y ∈ bohr (T x) s) → columnAnchorEval (fun x => L x y) as = 0) ∨
      ∃ j ∈ I, ∀ y ∈ bohr Gamma r, (∀ x ∈ as, y ∈ bohr (T x) r) →
        columnAnchorEval (fun x => L x y) as = f j y

/-- One step retains at least `beta/(5*k)` of the columns and at most
`1-beta` of the active models, without losing the model alternatives. -/
theorem even_model_elimination_step {J : Type*} {N g d k : Nat} [NeZero N] [Fact N.Prime] [NeZero k]
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
    (hcover : ColumnEvenModelAlternatives A Gamma T L k s r I f) :
    ∃ P ⊆ A, ∃ I' ⊆ I,
      modelTestDensity g d r/(5*k)*A.card ≤ (P.card : Real) ∧
      (I'.card : Real) ≤ (1-modelTestDensity g d r)*I.card ∧
      ColumnEvenModelAlternatives P Gamma T L k s r I' f := by
  classical
  obtain ⟨P,y,gamma,hPA,hP,hy,hdom,hdet,havoid⟩ :=
    exists_even_model_test_cell (k := k) A I Gamma T L f hrho hr hrle hA hI hGamma hT hf hf0 hne hN h7
  let I' := I.filter (fun j => ¬ Separates gamma (f j y))
  have hcount : (I'.card : Real) ≤ (1-modelTestDensity g d r)*I.card := by
    have hc := Finset.card_filter_add_card_filter_not (s := I) (fun j => Separates gamma (f j y))
    have hcR : ((I.filter (fun j => Separates gamma (f j y))).card : Real)+I'.card = I.card := by
      exact_mod_cast hc
    nlinarith only [hcR,hdet]
  refine ⟨P,hPA,I',Finset.filter_subset _ _,hP,hcount,?_⟩
  intro as hlen has hadd
  rcases hcover as hlen (fun x hx => hPA (has x hx)) hadd with hz | ⟨j,hj,hmodel⟩
  · exact Or.inl hz
  · apply Or.inr
    refine ⟨j,Finset.mem_filter.mpr ⟨hj,?_⟩,hmodel⟩
    intro hsep
    exact havoid as hlen has j hj hsep
      (hmodel y hy (fun x hx => hdom x (has x hx)))

end LeanProofs.GowersSzemeredi
