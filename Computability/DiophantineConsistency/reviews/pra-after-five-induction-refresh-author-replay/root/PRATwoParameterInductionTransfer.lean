import DiophantineConsistency.PRAPairedInductionSemantics
import DiophantineConsistency.PRABoundedOneInduction
/-! Generic proof transfer for a bounded matrix with two free parameters.
The interface assumes the packing equivalence explicitly. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRATwoParameterInductionTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAOpenOneInduction PRABoundedOneInduction

def twoSigma (ψ : Semisentence language 4) : Semiproposition language 1 :=
  ∃⁰ (Rew.embSubsts ![#1,#0,&0,&1] ▹ ψ)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem modelTwoSigma (ψ : Semisentence language 4) (e : ℕ → M) (x : M) :
    (twoSigma ψ).Eval ![x] e ↔ ∃ y : M, ψ.Eval ![x,y,e 0,e 1] Empty.elim := by
  simp only [twoSigma, Semiformula.eval_ex, Semiformula.eval_rew]
  apply exists_congr
  intro y
  have hb : (Semiterm.val (L := language) ![y,x] e ∘
      Rew.embSubsts ![#1,#0,&0,&1] ∘ Semiterm.bvar) = ![x,y,e 0,e 1] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun l => ?_) k
    exact Fin.cases rfl (fun m => Fin.elim0 m) l
  have hf' : (Semiterm.val (L := language) ![y,x] e ∘
      Rew.embSubsts ![#1,#0,&0,&1] ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hb,hf']

local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Structure.Zero language M := ⟨by
  simp only [Semiterm.Operator.val, Semiterm.Operator.Zero.zero, Semiterm.val_func]
  have h : (Semiterm.val ![] Empty.elim ∘ (![] : Fin 0 → Semiterm language Empty 0)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [h]; rfl⟩
local instance : Structure.One language M := ⟨by
  simp only [Semiterm.Operator.val, Semiterm.Operator.One.one, Semiterm.val_func]
  have h : (Semiterm.val ![] Empty.elim ∘ (![] : Fin 0 → Semiterm language Empty 0)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [h]; rfl⟩
local instance : Structure.Add language M := ⟨fun _ _ => rfl⟩

theorem modelSuccInd (φ : Semiproposition language 1) (e : ℕ → M) :
    (succInd φ).Eval ![] e ↔
      (φ.Eval ![Structure.func (L := language) (Code.zero 0) Fin.elim0] e →
       (∀ x : M, φ.Eval ![x] e →
         φ.Eval ![Structure.func (L := language) Code.succ (fun _ => x)] e) →
       ∀ x : M, φ.Eval ![x] e) := by
  simp [succInd, Semiformula.eval_substs, Semiterm.Operator.numeral_zero,
    Semiterm.Operator.numeral_one, Structure.Zero.zero, Structure.One.one]
  change (φ.Eval ![(0 : M)] e →
    (∀ x : M, φ.Eval ![x] e → φ.Eval ![x+1] e) → ∀ x : M, φ.Eval ![x] e) ↔ _
  have hz : (0 : M) = Structure.func (L := language) (Code.zero 0) Fin.elim0 := rfl
  have hs (x : M) : x+1 = Structure.func (L := language) Code.succ (fun _ => x) := by
    change Structure.func (L := language) addCode
      ![x, Structure.func (L := language) oneCode Fin.elim0] = _
    exact modelAddOne x
  simp only [hz,hs]

theorem modelPackedInduction (ψ : Semisentence language 4) (packed : Semisentence language 3)
    (hpack : ∀ a b : M, ∃ t : M, ∀ x y : M,
      packed.Eval ![x,y,t] Empty.elim ↔ ψ.Eval ![x,y,a,b] Empty.elim)
    (h : M↓[language] ⊧ (succInd (openSigma packed)).univCl) :
    M↓[language] ⊧ (succInd (twoSigma ψ)).univCl := by
  simp only [models_iff, Semiformula.eval_univCl] at h ⊢
  intro e
  obtain ⟨t,ht⟩ := hpack (e 0) (e 1)
  let e' : ℕ → M := Function.update e 0 t
  have hc (x : M) : (openSigma packed).Eval ![x] e' ↔ (twoSigma ψ).Eval ![x] e := by
    rw [modelOpenSigma, modelTwoSigma]
    simp only [e', Function.update_self]
    exact exists_congr (ht x)
  have hi := (modelSuccInd _ e').mp (h e')
  apply (modelSuccInd _ e).mpr
  intro hb hs x
  apply (hc x).mp
  apply hi ((hc _).mpr hb)
  intro z hz
  exact (hc _).mpr (hs z ((hc z).mp hz))
end models

/-- Conditional on a model-uniform bounded packing certificate, eliminate
one Foundation Σ₁ induction instance with two free predicate parameters. -/
theorem PRA_proves_goal_of_two_parameter_induction
    (ψ : Semisentence language 4) (packed : Semisentence language 3)
    (hbounded : Hierarchy 𝚺 0 packed)
    (hpack : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ∀ a b : M, ∃ t : M, ∀ x y : M,
        packed.Eval ![x,y,t] Empty.elim ↔ ψ.Eval ![x,y,a,b] Empty.elim)
    (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : (PRA ∪ {(succInd (twoSigma ψ)).univCl}) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  have hp : (PRA ∪ {(succInd (openSigma packed)).univCl}) ⊢ (∃⁰ θ).univCl := by
    apply PRA_proof_of_model_axiom_replacement _ _ _ ?_ p
    intro M _ _ _ _ hpacked
    have horig := modelPackedInduction ψ packed (hpack M) hpacked
    constructor
    intro σ hσ
    simp only [Set.mem_singleton_iff] at hσ
    subst σ
    exact horig
  exact PRA_proves_goal_of_boundedSuccInd packed hbounded θ hθ hp
end DiophantineConsistency.PRATwoParameterInductionTransfer
