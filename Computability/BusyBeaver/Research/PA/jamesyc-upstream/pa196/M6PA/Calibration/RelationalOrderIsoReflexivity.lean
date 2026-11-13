module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIdentityBijectionOrder
public import M6PA.Calibration.RelationalIdentitySupplier
@[expose] public section

/-! Reflexivity of the exact seven-clause existential order isomorphism on
ordinal representatives, via actual identity graphs rather than object equality. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def orderIsoFromExists {Γ : List Form} (E : FormulaEquality Γ) (a : Nat)
    (h : ND.Proof Γ (identityExists (.fvar a))) :
    ND.Proof Γ (orderIso (.fvar a) (.fvar a)) := by
  apply exsElim h
  let σ : Formula 1 := identityGraph (.bvar 0) (.fvar a)
  let C := σ.free :: shifted Γ
  have hg : ND.Proof C (identityGraph (.fvar 0) (.fvar (a+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> isoSyntax)
  have out := orderIsoFromIdentity (E.shifted.weaken (fun p hp => List.mem_cons_of_mem σ.free hp)) 0 (a+1) hg
  convert out using 1 <;> (dsimp [C,σ] <;> isoSyntax)

def identityAt {Γ : List Form} (a : Nat) (h : ND.Proof Γ identityStatement)
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a))) : ND.Proof Γ (identityExists (.fvar a)) := by
  have hh : ND.Proof Γ (Ordinal.domain (.fvar a) 🡒 identityExists (.fvar a)) := by
    convert allElim _ (.fvar a) h using 1 <;>
      ((try simp only [identityStatement,Ordinal.inductionConclusion,identityProperty]) <;> isoSyntax)
  exact mp ha hh

def orderIsoReflexivityStatement : Form :=
  ∀¹ (Ordinal.domain (.bvar 0) 🡒 orderIso (.bvar 0) (.bvar 0))

def orderIsoReflexivityProof {Γ : List Form} (E : FormulaEquality Γ)
    (h : ND.Proof Γ identityStatement) : ND.Proof Γ orderIsoReflexivityStatement := by
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have hs : ND.Proof (shifted Γ) identityStatement := by
    convert shiftProof h using 1 <;>
      ((try simp only [identityStatement,Ordinal.inductionConclusion,identityProperty]) <;> isoSyntax)
  have out := orderIsoFromExists (E.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)) 0
    (identityAt 0 (up hs d) hd)
  convert impIntro out using 1 <;> (dsimp [d] <;> (try simp only [orderIsoReflexivityStatement]) <;> isoSyntax)

def orderIsoReflexivityDerivation : ND.Proof identityAxioms orderIsoReflexivityStatement :=
  orderIsoReflexivityProof
    ⟨⟨assumption (by simp [identityAxioms]),assumption (by simp [identityAxioms]),
      assumption (by simp [identityAxioms])⟩,assumption (by simp [identityAxioms])⟩ identityDerivation

def orderIsoReflexivitySupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hsep : lo+3+depth (∼identityProperty) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget orderIsoReflexivityDerivation ≤ z) :
    NativeCalculus.ActualBasis.Proof (code orderIsoReflexivityStatement f lo z) :=
  compileContext identityAxioms _ orderIsoReflexivityDerivation f lo z hlo hf hbudget
    (identityAxiomSupplier f lo z hlo hf hz hsep hadj)

#print axioms orderIsoFromExists
#print axioms identityAt
#print axioms orderIsoReflexivityProof
#print axioms orderIsoReflexivityDerivation
#print axioms orderIsoReflexivitySupplier
end M6.PA.RelationalSource.PairGraph
