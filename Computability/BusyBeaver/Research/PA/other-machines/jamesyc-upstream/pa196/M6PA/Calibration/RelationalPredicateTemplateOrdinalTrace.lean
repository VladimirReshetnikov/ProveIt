module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateOrdinalRewriting
public import M6PA.Calibration.RelationalPredicateTemplateLiftLogic
@[expose] public section
/-! Actual finite LK trace operations in the unary-predicate template language. -/
namespace M6.PA.RelationalPredicateTemplate.Ordinal
open FFL FFL.FirstOrder ND
def predicateTraceFromSeparation {Γ : List Form} (p : Formula 1) (s : Nat)
    (h : ND.Proof Γ (separationFormula p)) :
    ND.Proof Γ (predicateTraceExists p (.fvar s)) := by
  convert allElim _ (.fvar s) h using 1
  templateTraceSyntax
  have he : (Rew.subst ![(.fvar s : Term 0)]).q.q.comp
      (Rew.map (fun _ : Fin 1 => (0 : Fin 3)) id) =
      Rew.map (fun _ : Fin 1 => (0 : Fin 2)) id := by
    ext i <;> simp [Rew.comp_app]
  rw [he]
  finishTemplateSyntax

def predicateTraceAt {Γ : List Form} (p : Formula 1) (s c x : Nat)
    (h : ND.Proof Γ (predicateTrace p (.fvar s) (.fvar c))) :
    ND.Proof Γ (sourceIff (mem (.fvar c) (.fvar x))
      (mem (.fvar s) (.fvar x) ⋏ p/[.fvar x])) := by
  convert allElim _ (.fvar x) h using 1
  templateTraceSyntax
  have he : (Rew.subst ![(.fvar x : Term 0)]).comp
      (Rew.map (fun _ : Fin 1 => (0 : Fin 1)) id) = Rew.subst ![(.fvar x : Term 0)] := by
    ext i <;> simp [Rew.comp_app]
  rw [he]
  finishTemplateSyntax

def predicateTraceShift {Γ : List Form} (p : Formula 1) (s c : Nat)
    (h : ND.Proof Γ (predicateTrace p (.fvar s) (.fvar c))) :
    ND.Proof (shifted Γ) (predicateTrace p.shift (.fvar (s+1)) (.fvar (c+1))) := by
  convert shiftProof h using 1
  templateTraceSyntax
  have he : (Rew.shift : Rew sourceLanguage Nat 0 Nat 0).q.comp
      (Rew.map (fun _ : Fin 1 => (0 : Fin 1)) id) =
      (Rew.map (fun _ : Fin 1 => (0 : Fin 1)) id).comp Rew.shift := by
    ext i <;> simp [Rew.comp_app]
  rw [he]
  finishTemplateSyntax

theorem predicateTraceFree (p : Formula 1) (s : Nat) :
    (predicateTrace p (Rew.bShift (.fvar s : Term 0)) (.bvar 0)).free =
      predicateTrace p.shift (.fvar (s+1)) (.fvar 0) := by
  templateTraceSyntax
  have he : (Rew.free : Rew sourceLanguage Nat 1 Nat 0).q.comp
      (Rew.map (fun _ : Fin 1 => (0 : Fin 2)) id) =
      (Rew.map (fun _ : Fin 1 => (0 : Fin 1)) id).comp Rew.shift := by
    ext i <;> simp [Rew.comp_app]
  rw [he]
  finishTemplateSyntax

def predicateTraceSubset {Γ : List Form} (p : Formula 1) (s c : Nat)
    (h : ND.Proof Γ (predicateTrace p (.fvar s) (.fvar c))) :
    ND.Proof Γ (subset (.fvar c) (.fvar s)) := by
  apply allIntro
  have hi := predicateTraceAt p.shift (s+1) (c+1) 0 (predicateTraceShift p s c h)
  have hd : ND.Proof (shifted Γ)
      (mem (.fvar (c+1)) (.fvar 0) 🡒 mem (.fvar (s+1)) (.fvar 0)) :=
    impIntro (andLeft (mp (assumption (by simp)) (up (andLeft hi) _)))
  convert hd using 1 ; templateOrdinalSyntax


#print axioms predicateTraceFromSeparation
#print axioms predicateTraceAt
#print axioms predicateTraceShift
#print axioms predicateTraceFree
#print axioms predicateTraceSubset
end M6.PA.RelationalPredicateTemplate.Ordinal
