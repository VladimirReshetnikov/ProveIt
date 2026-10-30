import DiophantineConsistency.PRAStageCodedChi
/-! One coded Σ₁ induction instance and its four-witness counterexample form. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAStageCodedInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRATermCompilation PRAStageCodedChi

/-- Drop χ's unused outer-v slot. -/
def chiInd {n : ℕ} (pred : Code (n+3)) : Semiproposition language 7 :=
  Rew.subst ![#0,#1,#2,#3,#4,#5,#6,.func (Code.zero 0) Fin.elim0] ▹ chiMatrix pred

def counterexample {n : ℕ} (pred : Code (n+3)) : Proposition language :=
  ∃⁰ ∃⁰ ∃⁰ ∀⁰ ∀⁰ ∀⁰ ∃⁰ chiInd pred

def inductionFormula {n : ℕ} (pred : Code (n+3)) : Proposition language :=
  ∼counterexample pred

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]

omit [Nonempty M] in
theorem modelChiInd {n : ℕ} (pred : Code (n+3)) (e : ℕ → M)
    (q w y x y₀ z c : M) : (chiInd pred).Eval ![q,w,y,x,y₀,z,c] e ↔
      let params := fun i : Fin n => e i.val
      let zero := Structure.func (L := language) (Code.zero 0) Fin.elim0
      let one := Structure.func (L := language) oneCode Fin.elim0
      let p := fun x y => Structure.func (L := language) pred (Fin.cases x (Fin.cases y (Fin.cases c params))) = one
      p zero y₀ ∧ (p x y → p (Structure.func (L := language) Code.succ (fun _ => x)) q) ∧ ¬p z w := by
  rw [chiInd, Semiformula.eval_substs]
  have hv : (Semiterm.val (L := language) ![q,w,y,x,y₀,z,c] e ∘
      ![#0,#1,#2,#3,#4,#5,#6,.func (Code.zero 0) Fin.elim0]) =
      ![q,w,y,x,y₀,z,c,Structure.func (L := language) (Code.zero 0) Fin.elim0] := by
    funext i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    change Structure.func (L := language) (Code.zero 0)
        (Semiterm.val ![q,w,y,x,y₀,z,c] e ∘ Fin.elim0) =
      Structure.func (L := language) (Code.zero 0) Fin.elim0
    congr 1
    exact Subsingleton.elim _ _
  rw [hv, modelChiMatrix]

/-- The coded counterexample's negation is exactly the familiar induction
principle for `∃y pred(x,y,c,params)=1` in arbitrary equality structures. -/
theorem modelInductionFormula {n : ℕ} (pred : Code (n+3)) (e : ℕ → M) :
    (inductionFormula pred).Eval ![] e ↔
      ∀ c z : M,
        let params := fun i : Fin n => e i.val
        let zero := Structure.func (L := language) (Code.zero 0) Fin.elim0
        let one := Structure.func (L := language) oneCode Fin.elim0
        let p := fun x y => Structure.func (L := language) pred (Fin.cases x (Fin.cases y (Fin.cases c params))) = one
        ((∃ y₀, p zero y₀) ∧ (∀ x, (∃ y, p x y) →
          ∃ q, p (Structure.func (L := language) Code.succ (fun _ => x)) q)) → ∃ w, p z w := by
  classical
  simp only [inductionFormula, LogicalConnective.HomClass.map_neg, counterexample,
    Semiformula.eval_ex, Semiformula.eval_all, modelChiInd]
  constructor
  · intro h c z hp
    by_contra hz
    obtain ⟨⟨y₀,hy₀⟩,hstep⟩ := hp
    apply h
    refine ⟨c,z,y₀,?_⟩
    intro x y w
    by_cases hxy : (Structure.func (L := language) pred (Fin.cases x (Fin.cases y
      (Fin.cases c (fun i : Fin n => e i.val))))) = Structure.func (L := language) oneCode Fin.elim0
    · obtain ⟨q,hq⟩ := hstep x ⟨y,hxy⟩
      exact ⟨q,hy₀,fun _ => hq,fun hw => hz ⟨w,hw⟩⟩
    · exact ⟨Classical.choice inferInstance,hy₀,fun hx => False.elim (hxy hx),fun hw => hz ⟨w,hw⟩⟩
  · intro hind ⟨c,z,y₀,hχ⟩
    let d : M := Classical.choice inferInstance
    have hbase := (hχ d d d).choose_spec.1
    have hstep : ∀ x, (∃ y, Structure.func (L := language) pred (Fin.cases x (Fin.cases y
        (Fin.cases c (fun i : Fin n => e i.val)))) = Structure.func (L := language) oneCode Fin.elim0) →
      ∃ q, Structure.func (L := language) pred (Fin.cases (Structure.func (L := language) Code.succ (fun _ => x))
        (Fin.cases q (Fin.cases c (fun i : Fin n => e i.val)))) = Structure.func (L := language) oneCode Fin.elim0 := by
      intro x ⟨y,hy⟩
      obtain ⟨q,_,hs,_⟩ := hχ x y d
      exact ⟨q,hs hy⟩
    obtain ⟨w,hw⟩ := hind c z ⟨⟨y₀,hbase⟩,hstep⟩
    obtain ⟨q,_,_,hn⟩ := hχ d d w
    exact hn hw
end models
end DiophantineConsistency.PRAStageCodedInduction
