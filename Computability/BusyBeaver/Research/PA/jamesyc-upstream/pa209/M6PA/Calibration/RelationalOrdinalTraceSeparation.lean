module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrdinalInductionPredecessor
public import M6PA.Calibration.RelationalFormulaCongruence
@[expose] public section

/-! Parameter-preserving represented traces for arbitrary relational formulas.
The property may have arbitrary nested quantifiers and Nat free parameters. -/
namespace M6.PA.RelationalSource.Ordinal
open FFL FFL.FirstOrder ND

def traceProperty (p : Formula 1) (n : Nat) : Formula (n+1) :=
  Semiformula.rewAux (Rew.map (fun _ : Fin 1 => (0 : Fin (n+1))) id) p

def predicateTrace (p : Formula 1) (s c : Term n) : Formula n :=
  ∀¹ sourceIff (mem (Rew.bShift c) (.bvar 0))
    (mem (Rew.bShift s) (.bvar 0) ⋏ traceProperty p n)

def predicateTraceExists (p : Formula 1) (s : Term 0) : Formula 0 :=
  ∃¹ predicateTrace p (Rew.bShift s) (.bvar 0)

/-- Rewriting a trace property is computed on the single bound variable;
free parameters are left to the supplied capture-aware rewriting. -/
theorem tracePropertyRewrite {n m : Nat} (p : Formula 1)
    (ω : Rew language Nat (n+1) Nat m) :
    Semiformula.rewAux ω (traceProperty p n) =
      Semiformula.rewAux (ω.comp (Rew.map (fun _ : Fin 1 => (0 : Fin (n+1))) id)) p :=
  rewrite_compose p _ _

macro "traceSyntax" : tactic => `(tactic|
  (simp only [predicateTrace,predicateTraceExists,traceProperty,separationFormula,
    liftMember,sourceIff,sourceImply,memAtom,mem,eq,Semiformula.shift,Semiformula.free,
    Rewriting.shift,Rewriting.free,Rewriting.subst,app_eq_rewAux,
    Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
   try simp only [← Semiformula.neg_eq, Semiformula.rewAux_neg];
   repeat' rw [rewrite_compose]))

def predicateTraceFromSeparation {Γ : List Form} (p : Formula 1) (s : Nat)
    (h : ND.Proof Γ (separationFormula p)) :
    ND.Proof Γ (predicateTraceExists p (.fvar s)) := by
  convert allElim _ (.fvar s) h using 1
  traceSyntax
  have he : (Rew.subst ![(.fvar s : Term 0)]).q.q.comp
      (Rew.map (fun _ : Fin 1 => (0 : Fin 3)) id) =
      Rew.map (fun _ : Fin 1 => (0 : Fin 2)) id := by
    ext i <;> simp [Rew.comp_app]
  rw [he]
  finishSourceSyntax

def predicateTraceAt {Γ : List Form} (p : Formula 1) (s c x : Nat)
    (h : ND.Proof Γ (predicateTrace p (.fvar s) (.fvar c))) :
    ND.Proof Γ (sourceIff (mem (.fvar c) (.fvar x))
      (mem (.fvar s) (.fvar x) ⋏ p/[.fvar x])) := by
  convert allElim _ (.fvar x) h using 1
  traceSyntax
  have he : (Rew.subst ![(.fvar x : Term 0)]).comp
      (Rew.map (fun _ : Fin 1 => (0 : Fin 1)) id) = Rew.subst ![(.fvar x : Term 0)] := by
    ext i <;> simp [Rew.comp_app]
  rw [he]
  finishSourceSyntax

def predicateTraceShift {Γ : List Form} (p : Formula 1) (s c : Nat)
    (h : ND.Proof Γ (predicateTrace p (.fvar s) (.fvar c))) :
    ND.Proof (shifted Γ) (predicateTrace p.shift (.fvar (s+1)) (.fvar (c+1))) := by
  convert shiftProof h using 1
  traceSyntax
  have he : (Rew.shift : Rew language Nat 0 Nat 0).q.comp
      (Rew.map (fun _ : Fin 1 => (0 : Fin 1)) id) =
      (Rew.map (fun _ : Fin 1 => (0 : Fin 1)) id).comp Rew.shift := by
    ext i <;> simp [Rew.comp_app]
  rw [he]
  finishSourceSyntax

theorem predicateTraceFree (p : Formula 1) (s : Nat) :
    (predicateTrace p (Rew.bShift (.fvar s : Term 0)) (.bvar 0)).free =
      predicateTrace p.shift (.fvar (s+1)) (.fvar 0) := by
  traceSyntax
  have he : (Rew.free : Rew language Nat 1 Nat 0).q.comp
      (Rew.map (fun _ : Fin 1 => (0 : Fin 2)) id) =
      (Rew.map (fun _ : Fin 1 => (0 : Fin 1)) id).comp Rew.shift := by
    ext i <;> simp [Rew.comp_app]
  rw [he]
  finishSourceSyntax

def predicateTraceSubset {Γ : List Form} (p : Formula 1) (s c : Nat)
    (h : ND.Proof Γ (predicateTrace p (.fvar s) (.fvar c))) :
    ND.Proof Γ (subset (.fvar c) (.fvar s)) := by
  apply allIntro
  have hi := predicateTraceAt p.shift (s+1) (c+1) 0 (predicateTraceShift p s c h)
  have hd : ND.Proof (shifted Γ)
      (mem (.fvar (c+1)) (.fvar 0) 🡒 mem (.fvar (s+1)) (.fvar 0)) :=
    impIntro (andLeft (mp (assumption (by simp)) (up (andLeft hi) _)))
  convert hd using 1 ; ordinalSyntax

def predicateTraceDerivation (p : Formula 1) (s : Nat) :
    ND.Proof [separationFormula p] (predicateTraceExists p (.fvar s)) :=
  predicateTraceFromSeparation p s (assumption (by simp))

/-- Actual-basis supplier with allocator and finite LK budget explicit. -/
def predicateTraceSupplier (p : Formula 1) (s : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+3+depth p ≤ z)
    (hb : lo+lkBudget (predicateTraceDerivation p s) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code (predicateTraceExists p (.fvar s)) f lo z) := by
  apply compileContext [separationFormula p] (predicateTraceExists p (.fvar s))
    (predicateTraceDerivation p s) f lo z hlo hf hb
  intro q hq
  have he : q = separationFormula p := by simpa using hq
  subst q
  exact separationSupplier p f lo z hlo hf hz

#print axioms predicateTraceFromSeparation
#print axioms predicateTraceAt
#print axioms predicateTraceShift
#print axioms predicateTraceFree
#print axioms predicateTraceSubset
#print axioms predicateTraceSupplier
end M6.PA.RelationalSource.Ordinal
