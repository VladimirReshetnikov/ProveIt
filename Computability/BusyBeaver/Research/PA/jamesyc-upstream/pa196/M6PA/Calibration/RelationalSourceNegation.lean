module
public import M6PA.Theory
public import M6PA.Calibration.RelationalSourceSyntax
public import M6PA.Calibration.ActualRelationalPointed
@[expose] public section

/-! Foundation's NNF negation is translated by finite actual-basis proofs,
including the relative falsum/truth codes. Not a semantic completeness step. -/
namespace M6.PA.NativeCalculus.ActualBasis

def Bi.symm {a b : Nat} (p : Bi a b) : Bi b a := ⟨p.2,p.1⟩
def Bi.trans {a b c : Nat} (p : Bi a b) (q : Bi b c) : Bi a c :=
  ⟨implicationCompose p.1 q.1,implicationCompose q.2 p.2⟩

def doubleNegationIntroduction (a : Nat) : Proof (wim a (wn (wn a))) := by
  let ha : Context [wn a,a] a := .assumption (by simp)
  let hn : Context [wn a,a] (wn a) := .assumption (by simp)
  exact (Context.mp ha hn).deduction.deduction.empty

def Bi.doubleNeg (a : Nat) : Bi a (wn (wn a)) :=
  ⟨doubleNegationIntroduction a,doubleNegationElimination a⟩

def false_not_true : Bi 1 (wn 0) := by
  let h : Context [wn 0] (wn 0) := .assumption (by simp)
  exact ⟨explosion (wn 0),(Context.mp (.closed truthProof) h).deduction.empty⟩

def true_not_false : Bi 0 (wn 1) :=
  ⟨.mp (identity 1) (Dominated.k (wn 1) 0),.mp truthProof (Dominated.k 0 (wn 1))⟩
end M6.PA.NativeCalculus.ActualBasis

namespace M6.PA.RelationalSource
open FFL FFL.FirstOrder NativeCalculus NativeCalculus.ActualBasis

def negationProof {ξ : Type} {n : Nat} (p : Semiformula language ξ n)
    (b : Fin n → Nat) (f : ξ → Nat) (lo z : Nat) :
    Bi (relationalCode z (toNamed (Semiformula.neg p) b f lo))
      (wn (relationalCode z (toNamed p b f lo))) :=
  match p with
  | .verum => false_not_true
  | .falsum => true_not_false
  | .rel _ _ => Bi.refl _
  | .nrel r ts => Bi.doubleNeg (relationalCode z (atomNamed r ts b f))
  | .and p q =>
    let a := relationalCode z (toNamed p b f lo)
    let bb := relationalCode z (toNamed q b f lo)
    let hp := (negationProof p b f lo z).neg.trans (Bi.doubleNeg a).symm
    (hp.imp (negationProof q b f lo z)).trans (Bi.doubleNeg (wim a (wn bb)))
  | .or p q =>
    let a := relationalCode z (toNamed p b f lo)
    let bb := relationalCode z (toNamed q b f lo)
    ((negationProof p b f lo z).and (negationProof q b f lo z)).trans
      (((Bi.refl (wn a)).imp (Bi.doubleNeg bb)).neg.symm)
  | .all p =>
    let a := relationalCode z (toNamed p (Fin.cases lo b) f (lo+1))
    (((negationProof p (Fin.cases lo b) f (lo+1) z).neg.trans
      (Bi.doubleNeg a).symm).all lo).neg
  | .exs p =>
    let a := relationalCode z (toNamed p (Fin.cases lo b) f (lo+1))
    ((negationProof p (Fin.cases lo b) f (lo+1) z).all lo).trans
      (Bi.doubleNeg (wal lo (wn a)))

#print axioms negationProof
end M6.PA.RelationalSource

