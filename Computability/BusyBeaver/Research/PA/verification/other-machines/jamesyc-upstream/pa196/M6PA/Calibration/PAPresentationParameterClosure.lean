module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationFormulaCongruence
public import M6PA.Calibration.PAPresentationStepTheorem
@[expose] public section

/-! Actual finite proof operations for universally closed theory axioms with
arbitrary parameters. No completeness or Prop-to-proof witness extraction. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def closureIter (p : ND.Form) (m : Nat) : ND.Form :=
  ∀¹* Semiformula.rewAux (Rew.fixitr 0 m) p

theorem closureIter_zero (p : ND.Form) : closureIter p 0 = p := by
  simp only [closureIter,Rew.fixitr_zero,allClosure_zero]
  exact ReflectiveRewriting.id_app p
theorem closureIter_succ (p : ND.Form) (m : Nat) :
    closureIter p (m+1) = .all (Semiformula.rewAux Rew.fix (closureIter p m)) :=
  LawfulSyntacticRewriting.allClosure_fixitr p

theorem shift_closed (p : ND.Form) (hp : p.freeVariables = ∅) : p.shift = p := by
  apply Semiformula.rew_eq_self_of
  · intro i; exact Fin.elim0 i
  · intro i hi; exact False.elim (by simpa [Semiformula.FVar?,hp] using hi)

theorem shifted_closed (Γ : List ND.Form) (hc : ∀ p ∈ Γ, p.freeVariables = ∅) :
    ND.shifted Γ = Γ := by
  induction Γ with
  | nil => rfl
  | cons a Γ ih =>
      change a.shift :: ND.shifted Γ = a :: Γ
      rw [shift_closed a (hc a (by simp)),ih (by intro p hp; exact hc p (by simp [hp]))]

theorem free_fix_formula (p : ND.Form) :
    (Semiformula.rewAux Rew.fix p).free = p :=
  LawfulSyntacticRewriting.free_fix p

def ND.closeIter {Γ : List Form} {p : Form} (hc : ∀ q ∈ Γ,q.freeVariables = ∅)
    (d : Proof Γ p) : (m : Nat) → Proof Γ (closureIter p m)
  | 0 => d.cast (by rw [closureIter_zero])
  | m+1 => by
      have e := closeIter hc d m
      have ef : Proof (shifted Γ) (Semiformula.rewAux Rew.fix (closureIter p m)).free :=
        e.cast (by rw [shifted_closed Γ hc,free_fix_formula])
      exact (allIntro ef).cast (by rw [closureIter_succ]; rfl)

def ND.openIter {Γ : List Form} {p : Form} (hc : ∀ q ∈ Γ,q.freeVariables = ∅) :
    (m : Nat) → Proof Γ (closureIter p m) → Proof Γ p
  | 0,d => d.cast (by rw [closureIter_zero])
  | m+1,d => by
      have da : Proof Γ (.all (Semiformula.rewAux Rew.fix (closureIter p m))) :=
        d.cast (by rw [closureIter_succ])
      have ds : Proof (shifted Γ) (.all (Semiformula.rewAux Rew.fix (closureIter p m)).shift) :=
        (shiftProof da).cast (congrArg (fun q : Form => negatives (shifted Γ) + ⦃q⦄)
          (presentation_shift_all _))
      have e : Proof Γ (closureIter p m) :=
        (allElim _ (.fvar 0) ds).cast (by
          rw [shifted_closed Γ hc,open_shifted,free_fix_formula])
      exact openIter hc m e

def ND.closeParameters {Γ : List Form} {p : Form} (hc : ∀ q ∈ Γ,q.freeVariables = ∅)
    (d : Proof Γ p) : Proof Γ p.univCl' := closeIter hc d p.fvSup

def ND.openParameters {Γ : List Form} {p : Form} (hc : ∀ q ∈ Γ,q.freeVariables = ∅)
    (d : Proof Γ p.univCl') : Proof Γ p := openIter hc p.fvSup d

def ND.replaceContext {Δ : List Form} :
    (Γ : List Form) → {p : Form} → Proof Γ p →
      (∀ q ∈ Γ,Proof Δ q) → Proof Δ p
  | [],_,d,_ => weaken d (by simp)
  | q::Γ,p,d,hs =>
      mp (hs q (by simp))
        (replaceContext Γ (impIntro d) (fun r hr => hs r (List.mem_cons_of_mem _ hr)))

def closedContext (Γ : List ND.Form) := Γ.map Semiformula.univCl'

theorem closedContext_closed (Γ : List ND.Form) :
    ∀ q ∈ closedContext Γ,q.freeVariables = ∅ := by
  intro q hq
  rcases List.mem_map.mp hq with ⟨p,hp,rfl⟩
  simp

def ND.replaceByClosures {Γ : List Form} {p : Form} (d : Proof Γ p) :
    Proof (closedContext Γ) p :=
  replaceContext Γ d (fun q hq => openParameters (closedContext_closed Γ)
    (assumption (by exact List.mem_map.mpr ⟨q,hq,rfl⟩)))

theorem univCl_idempotent (p : ND.Form) : p.univCl'.univCl = p.univCl := by
  apply (Semiformula.coe_inj _ _).mp
  simp only [Semiformula.coe_univCl_eq_univCl',Semiformula.univCl'_univCl'_eq_univCl']

def ND.parameterTheoryProof {T : Theory language} {Γ : List Form} {p : Form}
    (d : Proof Γ p) (ht : ∀ q ∈ Γ,q.univCl ∈ T) : T.Proof p.univCl := by
  have hct : ∀ r ∈ closedContext Γ,r.univCl ∈ T := by
    intro r hr
    rcases List.mem_map.mp hr with ⟨q,hq,rfl⟩
    rw [univCl_idempotent]
    exact ht q hq
  have pp := closedTheoryProof (closeParameters (closedContext_closed Γ) (replaceByClosures d))
    (closedContext_closed Γ) (by simp) hct
  simpa only [univCl_idempotent] using pp

#print axioms ND.parameterTheoryProof
end M6.PA.Presentation
