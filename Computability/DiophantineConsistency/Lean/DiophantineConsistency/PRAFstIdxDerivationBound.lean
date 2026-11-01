import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRAFstIdxWitnessBound
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic
/-! Bind the concrete first-index witness bound to the exact sigma graph of
Foundation's `derivationOf`. The separate bounded derivation/fixpoint
conjunct is an explicit hypothesis; this is not a bound for the full proof
predicate or the ZFC refutation sentence. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAFstIdxDerivationBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
/-- The actual argument permutation in `derivationOf` admits the same
local bound `d + 1` in every IOpen model. -/
theorem fstIdx_inline_succ (x p : V) :
    (Rew.subst (![#1,#0] : Fin 2 → ArithmeticSemiterm Empty 2) ▹ fstIdxDef.val).Evalb ![p,x] →
      (bnd (Rew.subst (![#1,#0] : Fin 2 → ArithmeticSemiterm Empty 2) ▹ fstIdxDef.val)).Evalb ![p,x,p+1] := by
  intro h
  have h' : fstIdxDef.val.Evalb ![x,p] := by
    simpa [fstIdxDef, pi₁Def, pairDef, subDef] using h
  have hb := PRAFstIdxWitnessBound.fstIdx_bnd_succ x p h'
  have ho₁ : ((“1 ≤ #1” : ArithmeticSemiformula Empty 3).neg).Open := Semiformula.open_neg.mpr (by simp)
  have ho₂ : ((“1 ≤ #2” : ArithmeticSemiformula Empty 3).neg).Open := Semiformula.open_neg.mpr (by simp)
  have ho₃ : ((“#1 < 1” : ArithmeticSemiformula Empty 3).neg).Open := Semiformula.open_neg.mpr (by simp)
  have ho₄ : ((“#2 < 1” : ArithmeticSemiformula Empty 3).neg).Open := Semiformula.open_neg.mpr (by simp)
  simp [fstIdxDef, pi₁Def, pairDef, subDef, Semiformula.bexsLTSucc,
    Semiformula.bexsLT, FirstOrder.bexs, bnd, bnd_open, Rew.subst, Rew.q] at hb ⊢
  simp [bnd_open _ ho₁, bnd_open _ ho₂, bnd_open _ ho₃, bnd_open _ ho₄] at hb ⊢
  exact hb

variable {L : Language} [L.Encodable] [L.LORDefinable] (T : Theory L) [T.Δ₁]
/-- The first-index occurrence is definitionally the first conjunct of
Foundation's actual sigma presentation for every theory with a Δ₁ axiom graph. -/
theorem derivationOf_sigma_shape :
    (derivationOf T).sigma.val =
      (Rew.subst (![#1,#0] : Fin 2 → ArithmeticSemiterm Empty 2) ▹ fstIdxDef.val) ⋏
      (Rew.subst (![#0] : Fin 1 → ArithmeticSemiterm Empty 2) ▹ (derivation T).sigma.val) := by
  rfl

/-- Bound the complete `derivationOf` sigma graph once its separate
bounded derivation/fixpoint conjunct and a common bound are supplied. -/
theorem derivationOf_bnd_of_local (d s w : V)
    (hw : d+1 ≤ w)
    (hfst : fstIdxDef.val.Evalb ![s,d])
    (hrest : (bnd (Rew.subst (![#0] : Fin 1 → ArithmeticSemiterm Empty 2) ▹
      (derivation T).sigma.val)).Evalb ![d,s,w]) :
    (bnd (derivationOf T).sigma.val).Evalb ![d,s,w] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have hin : (Rew.subst (![#1,#0] : Fin 2 → ArithmeticSemiterm Empty 2) ▹
      fstIdxDef.val).Evalb ![d,s] := by
    simp only [Semiformula.eval_rew]
    have hv : (Semiterm.val ![d,s] Empty.elim ∘
        (Rew.subst (![#1,#0] : Fin 2 → ArithmeticSemiterm Empty 2)) ∘ Semiterm.bvar) = ![s,d] := by
      funext i; revert i; simp [Fin.forall_fin_succ, Function.comp_def, Rew.subst]
    have hf : (Semiterm.val ![d,s] Empty.elim ∘
        (Rew.subst (![#1,#0] : Fin 2 → ArithmeticSemiterm Empty 2)) ∘ Semiterm.fvar) =
        (Empty.elim : Empty → V) := Subsingleton.elim _ _
    rw [hv,hf]
    exact hfst
  have hb := fstIdx_inline_succ s d hin
  have hm := eval_bnd_mono (Rew.subst (![#1,#0] : Fin 2 → ArithmeticSemiterm Empty 2) ▹
      fstIdxDef.val) ![d,s] (Empty.elim : Empty → V) hw (by simpa using hb)
  rw [derivationOf_sigma_shape T]
  simp only [bnd, LogicalConnective.HomClass.map_and]
  refine ⟨?_,hrest⟩
  simpa using hm
noncomputable def derivationBoundBody : ArithmeticSemisentence 3 :=
  ((“d s w. d + 1 ≤ w”) ⋏
    (Rew.subst (![#1,#0] : Fin 2 → ArithmeticSemiterm Empty 3) ▹ fstIdxDef.val) ⋏
    bnd (Rew.subst (![#0] : Fin 1 → ArithmeticSemiterm Empty 2) ▹ (derivation T).sigma.val)) 🡒
      bnd (derivationOf T).sigma.val

theorem derivationBoundBody_model (e : Fin 3 → V) :
    (derivationBoundBody T).Eval e Empty.elim := by
  simp only [derivationBoundBody, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_and]
  intro ⟨hw,hfst,hrest⟩
  have hv : ![e 0,e 1,e 2] = e := by funext i; revert i; simp [Fin.forall_fin_succ]
  rw [←hv] at hw hfst hrest ⊢
  have hw' : e 0+1 ≤ e 2 := by simpa using hw
  have hfst' : fstIdxDef.val.Evalb ![e 1,e 0] := by
    simp only [Semiformula.eval_rew] at hfst
    have he : (Semiterm.val ![e 0,e 1,e 2] Empty.elim ∘
        (Rew.subst (![#1,#0] : Fin 2 → ArithmeticSemiterm Empty 3)) ∘ Semiterm.bvar) = ![e 1,e 0] := by
      funext i; revert i; simp [Fin.forall_fin_succ, Function.comp_def, Rew.subst]
    have hf : (Semiterm.val ![e 0,e 1,e 2] Empty.elim ∘
        (Rew.subst (![#1,#0] : Fin 2 → ArithmeticSemiterm Empty 3)) ∘ Semiterm.fvar) =
        (Empty.elim : Empty → V) := Subsingleton.elim _ _
    rw [he,hf] at hfst
    exact hfst
  exact derivationOf_bnd_of_local T (e 0) (e 1) (e 2) hw' hfst' hrest

open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
section candidate
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- The exact conditional binding holds in every candidate-PRA model. -/
theorem candidate_derivationOf_bnd_of_local (d s w : M)
    (hw : ¬ Structure.rel (L := language) Language.ORing.Rel.lt ![w,d+1])
    (hfst : (Semiformula.lMap embedding fstIdxDef.val).Eval ![s,d] Empty.elim)
    (hrest : (Semiformula.lMap embedding
      (bnd (Rew.subst (![#0] : Fin 1 → ArithmeticSemiterm Empty 2) ▹
        (derivation T).sigma.val))).Eval ![d,s,w] Empty.elim) :
    (Semiformula.lMap embedding (bnd (derivationOf T).sigma.val)).Eval ![d,s,w] Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hw' : d+1 ≤ w := le_of_not_gt hw
  rw [Semiformula.eval_lMap] at hfst hrest ⊢
  rw [reduct_eq_standard] at hfst hrest ⊢
  exact derivationOf_bnd_of_local T d s w hw' hfst hrest
end candidate

noncomputable def derivationBoundSentence : Sentence language :=
  ∀⁰* Semiformula.lMap embedding (derivationBoundBody T)

/-- Candidate PRA proves the universally closed conditional binding for
Foundation's actual `derivationOf` sigma graph. -/
theorem candidate_proves_derivationBoundSentence : PRA ⊢ derivationBoundSentence T := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact derivationBoundBody_model T e
end DiophantineConsistency.PRAFstIdxDerivationBound
