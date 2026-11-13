module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateOrdinalRewriting
public import M6PA.Calibration.RelationalPredicateTemplateLiftLogic
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate.Ordinal
open FFL FFL.FirstOrder ND
def inductionBaseAt {Γ : List Form} (p : Formula 1) (a : Nat)
    (h : ND.Proof Γ (inductionBase p))
    (hd : ND.Proof Γ (domain (.fvar a))) (hz : ND.Proof Γ (zero (.fvar a))) :
    ND.Proof Γ (p/[.fvar a]) := by
  have hb : ND.Proof Γ ((domain (.fvar a) ⋏ zero (.fvar a)) 🡒 p/[.fvar a]) := by
    convert allElim _ (.fvar a) h using 1
    templateOrdinalSyntax
  exact mp (andIntro hd hz) hb

def inductionBaseShift {Γ : List Form} (p : Formula 1)
    (h : ND.Proof Γ (inductionBase p)) :
    ND.Proof (shifted Γ) (inductionBase p.shift) := by
  convert shiftProof h using 1
  simp only [inductionBase]
  templateOrdinalSyntax
  all_goals simp only [Rew.q_shift]

def inductionStepAt {Γ : List Form} (p : Formula 1) (a b : Nat)
    (h : ND.Proof Γ (inductionStep p))
    (ha : ND.Proof Γ (domain (.fvar a))) (hb : ND.Proof Γ (domain (.fvar b)))
    (hs : ND.Proof Γ (successor (.fvar a) (.fvar b)))
    (hp : ND.Proof Γ (p/[.fvar a])) : ND.Proof Γ (p/[.fvar b]) := by
  have hi : ND.Proof Γ ((domain (.fvar a) ⋏ (domain (.fvar b) ⋏
      (successor (.fvar a) (.fvar b) ⋏ p/[.fvar a]))) 🡒 p/[.fvar b]) := by
    convert allElim _ (.fvar b) (allElim _ (.fvar a) h) using 1
    simp only [inductionStep,traceProperty,successor,sourceIff]
    templateOrdinalSyntax
    try simp only [← Semiformula.neg_eq, Semiformula.rewAux_neg]
    repeat' rw [rewrite_compose]
    all_goals
      first
      | apply congrArg (fun ω : Rew sourceLanguage Nat 1 Nat 0 => (Semiformula.rewAux ω p).neg)
      | apply congrArg (fun ω : Rew sourceLanguage Nat 1 Nat 0 => Semiformula.rewAux ω p)
      ext i <;> simp [Rew.comp_app] <;> rfl
  exact mp (andIntro ha (andIntro hb (andIntro hs hp))) hi

def inductionStepShift {Γ : List Form} (p : Formula 1)
    (h : ND.Proof Γ (inductionStep p)) :
    ND.Proof (shifted Γ) (inductionStep p.shift) := by
  convert shiftProof h using 1
  simp only [inductionStep,traceProperty,successor,sourceIff]
  templateOrdinalSyntax
  try simp only [← Semiformula.neg_eq, Semiformula.rewAux_neg]
  repeat' rw [rewrite_compose]
  all_goals
    first
    | apply congrArg (fun ω : Rew sourceLanguage Nat 1 Nat 2 => (Semiformula.rewAux ω p).neg)
    | apply congrArg (fun ω : Rew sourceLanguage Nat 1 Nat 2 => Semiformula.rewAux ω p)
    ext i <;> simp [Rew.comp_app] <;> rfl


#print axioms inductionBaseAt
#print axioms inductionBaseShift
#print axioms inductionStepAt
#print axioms inductionStepShift
end M6.PA.RelationalPredicateTemplate.Ordinal
