module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionAtomic
public import M6PA.Calibration.PAForwardRelationalSubstitutionFormulaSyntax
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

/-- Both directions are actual proof transformers, uniformly in the context;
the final endpoint packages them as an ordinary ND conjunction of implications. -/
structure RealizedFormulaCompatible {n : Nat} (p : SourceFormula n) where
  forward : ∀ {k : Nat} (σ : Rew Presentation.language Nat n Nat k) {Γ : List Form},
    SubstitutionPremises Γ → ∀ (b : Fin k → Term 0) (f : Nat → Term 0)
      (c : Fin n → Term 0) (g : Nat → Term 0), FormulaRealization Γ σ b f c g p →
      ND.Proof Γ (formula (Semiformula.rewAux σ p) b f) → ND.Proof Γ (formula p c g)
  backward : ∀ {k : Nat} (σ : Rew Presentation.language Nat n Nat k) {Γ : List Form},
    SubstitutionPremises Γ → ∀ (b : Fin k → Term 0) (f : Nat → Term 0)
      (c : Fin n → Term 0) (g : Nat → Term 0), FormulaRealization Γ σ b f c g p →
      ND.Proof Γ (formula p c g) → ND.Proof Γ (formula (Semiformula.rewAux σ p) b f)

def realizedFormulaRel {n : Nat} (ts : Fin 2 → SourceTerm n) :
    RealizedFormulaCompatible (.rel .eq ts) where
  forward := by
    intro k σ Γ A b f c g H h
    exact realizedEqualityForward (ts 0) (ts 1) σ A b f c g
      (termRealizationFromOccurrences _ (fun v hv => H v (.rel 0 hv)))
      (termRealizationFromOccurrences _ (fun v hv => H v (.rel 1 hv))) h
  backward := by
    intro k σ Γ A b f c g H h
    exact realizedEqualityBackward (ts 0) (ts 1) σ A b f c g
      (termRealizationFromOccurrences _ (fun v hv => H v (.rel 0 hv)))
      (termRealizationFromOccurrences _ (fun v hv => H v (.rel 1 hv))) h

def realizedFormulaNrel {n : Nat} (ts : Fin 2 → SourceTerm n) :
    RealizedFormulaCompatible (.nrel .eq ts) where
  forward := by
    intro k σ Γ A b f c g H h
    apply byContradiction
    let q := (equal (ts 0) (ts 1) c g).neg.neg
    have ht := TermRealization.up (ts 0)
      (termRealizationFromOccurrences _ (fun v hv => H v (.nrel 0 hv))) q
    have hv := TermRealization.up (ts 1)
      (termRealizationFromOccurrences _ (fun v hv => H v (.nrel 1 hv))) q
    have hq : ND.Proof (q :: Γ) (equal (ts 0) (ts 1) c g) := by
      simpa only [q, Semiformula.neg_neg] using (assumption (List.mem_cons_self) : ND.Proof (q :: Γ) q)
    exact contradiction (realizedEqualityBackward _ _ σ (A.up q) b f c g ht hv hq) (up h q)
  backward := by
    intro k σ Γ A b f c g H h
    apply byContradiction
    let q := (equal (σ (ts 0)) (σ (ts 1)) b f).neg.neg
    have ht := TermRealization.up (ts 0)
      (termRealizationFromOccurrences _ (fun v hv => H v (.nrel 0 hv))) q
    have hv := TermRealization.up (ts 1)
      (termRealizationFromOccurrences _ (fun v hv => H v (.nrel 1 hv))) q
    have hq : ND.Proof (q :: Γ) (equal (σ (ts 0)) (σ (ts 1)) b f) := by
      simpa only [q, Semiformula.neg_neg] using (assumption (List.mem_cons_self) : ND.Proof (q :: Γ) q)
    exact contradiction (realizedEqualityForward _ _ σ (A.up q) b f c g ht hv hq) (up h q)

#print axioms realizedFormulaRel
#print axioms realizedFormulaNrel
end M6.PA.ForwardRelational
