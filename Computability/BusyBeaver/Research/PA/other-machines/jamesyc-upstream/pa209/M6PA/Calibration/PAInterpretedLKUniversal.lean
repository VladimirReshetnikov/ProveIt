module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedLKVariables
@[expose] public section

/-! Actual universal-rule transport with a fresh domain-guarded eigenvariable.
The original sequent is traversed constructively, without extracting a witness
from Prop-only multiset membership. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] formula value Ordinal.domain
set_option maxHeartbeats 800000

def interpretedShiftSupply (ps : List (SourceFormula 0)) (f : Nat → Term 0)
    {C : List Form} (h : ∀ p,p∈ps→ND.Proof C (∼formula p Fin.elim0 f))
    (q : SourceFormula 0) (hq : q∈ps.map Semiformula.shift) :
    ND.Proof (shifted C) (∼formula q Fin.elim0 (freshEnvironment f)) := by
  cases ps with
  | nil => exact False.elim (List.not_mem_nil hq)
  | cons p ps =>
    by_cases he : q=p.shift
    · subst q
      rw [interpretedSourceShift]
      simpa only [Semiformula.shift,Rewriting.shift,app_eq_rewAux,Semiformula.neg_eq,rew_neg]
        using shiftProof (h p (by simp))
    · exact interpretedShiftSupply ps f (fun p hp => h p (List.mem_cons_of_mem _ hp)) q
        ((List.mem_cons.mp hq).resolve_left he)

def interpretedRefutesAll {Γ : LK.Sequent Presentation.language}
    (tg : Γ.Traversal) (p : SourceFormula 1)
    (d : InterpretedRefutes (Rewriting.shifts Γ+⦃p.free⦄)) :
    InterpretedRefutes (Γ+⦃Semiformula.all p⦄) := by
  intro f C A H h
  have hn := h (Semiformula.all p) (by simp)
  have he : ND.Proof C (∃¹ (Ordinal.domain (.bvar 0) ⋏
      (formula p (bindEnv Fin.elim0) (shiftEnv f)).neg)) := by
    convert hn using 1 <;>
      (simp only [formula,Semiformula.neg_eq,Semiformula.neg,Semiformula.imp_eq,
        Semiformula.neg_neg] <;> rfl)
  apply exsElim he
  let body : Formula 1 := Ordinal.domain (.bvar 0) ⋏
    (formula p (bindEnv Fin.elim0) (shiftEnv f)).neg
  let b := body.free
  let D := b::shifted C
  have hb : ND.Proof D (Ordinal.domain (.fvar 0) ⋏
      (formula p (fun _ => .fvar 0) (freeShiftEnv f)).neg) := by
    have hh : ND.Proof D b := assumption (by simp [D])
    convert hh using 1
    simp only [b,body,Semiformula.free,Rewriting.free,app_eq_rewAux,
      Semiformula.rewAux,rew_neg,Ordinal.domain_rew,formula_rew]
    congr 2
    apply formula_env_ext
    · intro i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
    · intro i
      cases hf : f i with
      | bvar j => nomatch j
      | func fn _ => nomatch fn
      | fvar k => simp only [shiftEnv,freeShiftEnv,hf]; rfl
  have HD : DomainEnvironment D (freshEnvironment f) := H.fresh (andLeft hb)
  have out : ND.Proof D ⊥ := by
    apply d (freshEnvironment f) (A.shift.up b) HD
    intro q hq
    by_cases heq : q=p.free
    · subst q
      apply interpretedNegIntro
      let r := formula p.free Fin.elim0 (freshEnvironment f)
      have hr : ND.Proof (r::D) r := assumption (by simp)
      have hp := interpretedSourceFree p f ((A.shift.up b).up r) (HD.up r) hr
      exact contradiction hp (up (andRight hb) r)
    · have hs : q∈Rewriting.shifts Γ :=
        (Multiset.mem_add.mp hq).resolve_right (by simpa using heq)
      have hlist : q∈tg.toList.map Semiformula.shift := by
        simpa only [Rewriting.shifts,←tg.coe_toList,Multiset.map_coe,Multiset.mem_coe] using hs
      exact up (interpretedShiftSupply tg.toList f (fun r hr =>
        h r (Multiset.mem_add.mpr (Or.inl (by rw [←tg.coe_toList]; exact hr)))) q hlist) b
  exact out

#print axioms interpretedShiftSupply
#print axioms interpretedRefutesAll
end M6.PA.ForwardRelational
