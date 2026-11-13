module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionBinary
@[expose] public section

/-! Constructive compatibility for substitution of an actual source term into
bound variable zero. The output relates arbitrary actual witnesses by order
isomorphism. It asserts neither syntactic equality nor canonical values. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph

def termSubstitutionCompatible {n : Nat} (t : SourceTerm (n+1)) :
    SubstitutionCompatible t :=
  match t with
  | .bvar i => Fin.cases substitutionBoundZero substitutionBoundTail i
  | .fvar i => substitutionFree i
  | .func .zero _ => fun u _ A b f a Hu _ ha r s hr hs =>
      substitutionZero u A b f a Hu (fun i => Fin.elim0 i) ha r s hr hs
  | .func .succ ts => fun u _ A b f a Hu Ht ha r s hr hs =>
      substitutionSuccessor (ts 0) (termSubstitutionCompatible (ts 0)) u A b f a Hu
        (Fin.cases (Ht 0) (fun i => Fin.elim0 i)) ha r s hr hs
  | .func .add ts => fun u _ A b f a Hu Ht ha r s hr hs =>
      substitutionBinary .addition (ts 0) (ts 1)
        (termSubstitutionCompatible (ts 0)) (termSubstitutionCompatible (ts 1)) u A b f a Hu
        (Fin.cases (Ht 0) (Fin.cases (Ht 1) (fun i => Fin.elim0 i))) ha r s hr hs
  | .func .mul ts => fun u _ A b f a Hu Ht ha r s hr hs =>
      substitutionBinary .multiplication (ts 0) (ts 1)
        (termSubstitutionCompatible (ts 0)) (termSubstitutionCompatible (ts 1)) u A b f a Hu
        (Fin.cases (Ht 0) (Fin.cases (Ht 1) (fun i => Fin.elim0 i))) ha r s hr hs

/-- Finite domain coverage suffices once the identity-graph existence premise is
paid. No totality hypothesis is needed here: all three actual values are given. -/
def sourceBoundSubstitutionValue {Γ : List Form} {n : Nat}
    (A : CoherencePremises Γ) (hidentity : ND.Proof Γ identityStatement)
    (t : SourceTerm (n+1)) (u : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (a : Term 0)
    (Hu : EnvironmentCoverage Γ b f u)
    (Ht : EnvironmentCoverage Γ (Fin.cases a b) f t)
    (ha : ND.Proof Γ (value u b f a))
    (r s : Term 0) (hr : ND.Proof Γ (value (singleBoundSubst u t) b f r))
    (hs : ND.Proof Γ (value t (Fin.cases a b) f s)) : ND.Proof Γ (orderIso r s) :=
  termSubstitutionCompatible t u A b f a
    (reflexiveIsoCoverage A.equality hidentity u b f Hu)
    (reflexiveIsoCoverage A.equality hidentity t (Fin.cases a b) f Ht) ha r s hr hs

#print axioms termSubstitutionCompatible
#print axioms sourceBoundSubstitutionValue
end M6.PA.ForwardRelational
