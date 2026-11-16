module
public import Std
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Max
@[expose] public section
/-!
# A 209-state Turing machine independent of Peano arithmetic

The table below specifies a binary machine on a two-way infinite tape. The
initial state and every initial tape cell are zero. The sole reachable halt
label is 215. The arithmetic sentence uses the same 418 transition rows.
`Provable PATheory` is ordinary first-order Peano arithmetic with full induction.
-/
namespace PalomarPA
/-- Stable explicit finite index: avoids module-wide sharing of automatically
extracted closed numeral-bound proofs when definitions are inlined. -/
def boundIndex {n : Nat} : Nat → Fin (n+1)
 | 0 => ⟨0, Nat.zero_lt_succ n⟩
 | i+1 => ⟨(i+1) % (n+1), Nat.mod_lt _ (Nat.zero_lt_succ n)⟩
@[simp] theorem boundIndex_zero {n : Nat} : boundIndex (n:=n) 0 = 0 := by
 apply Fin.ext
 simp [boundIndex]

inductive Term (ξ : Type) (n : Nat) where
  | bvar : Fin n → Term ξ n
  | fvar : ξ → Term ξ n
  | zero : Term ξ n
  | one : Term ξ n
  | add : Term ξ n → Term ξ n → Term ξ n
  | mul : Term ξ n → Term ξ n → Term ξ n
  deriving DecidableEq
inductive Formula (ξ : Type) : Nat → Type where
  | top {n} : Formula ξ n
  | bot {n} : Formula ξ n
  | eq {n} : Term ξ n → Term ξ n → Formula ξ n
  | ne {n} : Term ξ n → Term ξ n → Formula ξ n
  | lt {n} : Term ξ n → Term ξ n → Formula ξ n
  | nlt {n} : Term ξ n → Term ξ n → Formula ξ n
  | and {n} : Formula ξ n → Formula ξ n → Formula ξ n
  | or {n} : Formula ξ n → Formula ξ n → Formula ξ n
  | all {n} : Formula ξ (n+1) → Formula ξ n
  | ex {n} : Formula ξ (n+1) → Formula ξ n
  deriving DecidableEq
abbrev Sentence := Formula Empty 0

def Formula.neg : Formula ξ n → Formula ξ n
  | .top => .bot | .bot => .top
  | .eq t u => .ne t u | .ne t u => .eq t u
  | .lt t u => .nlt t u | .nlt t u => .lt t u
  | .and p q => .or p.neg q.neg
  | .or p q => .and p.neg q.neg
  | .all p => .ex p.neg | .ex p => .all p.neg

theorem Formula.neg_neg (p : Formula ξ n) : p.neg.neg = p := by
  induction p <;> simp_all [neg]

def Term.rename (b : Fin n → Fin m) (f : ξ → η) : Term ξ n → Term η m
  | .bvar i => .bvar (b i) | .fvar x => .fvar (f x)
  | .zero => .zero | .one => .one
  | .add t u => .add (t.rename b f) (u.rename b f)
  | .mul t u => .mul (t.rename b f) (u.rename b f)
def Term.rewrite (b : Fin n → Term η m) (f : ξ → Term η m) : Term ξ n → Term η m
  | .bvar i => b i | .fvar x => f x
  | .zero => .zero | .one => .one
  | .add t u => .add (t.rewrite b f) (u.rewrite b f)
  | .mul t u => .mul (t.rewrite b f) (u.rewrite b f)
def liftBound (b : Fin n → Term η m) : Fin (n+1) → Term η (m+1) :=
  Fin.cases (.bvar (boundIndex 0)) (fun i => (b i).rename Fin.succ id)
def Formula.rewrite (b : Fin n → Term η m) (f : ξ → Term η m) :
    Formula ξ n → Formula η m
  | .top => .top | .bot => .bot
  | .eq t u => .eq (t.rewrite b f) (u.rewrite b f)
  | .ne t u => .ne (t.rewrite b f) (u.rewrite b f)
  | .lt t u => .lt (t.rewrite b f) (u.rewrite b f)
  | .nlt t u => .nlt (t.rewrite b f) (u.rewrite b f)
  | .and p q => .and (p.rewrite b f) (q.rewrite b f)
  | .or p q => .or (p.rewrite b f) (q.rewrite b f)
  | .all p => .all (p.rewrite (liftBound b) (fun x => (f x).rename Fin.succ id))
  | .ex p => .ex (p.rewrite (liftBound b) (fun x => (f x).rename Fin.succ id))
def Formula.embed (p : Sentence) : Formula Nat 0 := p.rewrite Term.bvar Empty.elim
def Formula.shift (p : Formula Nat n) : Formula Nat n :=
  p.rewrite Term.bvar (fun x => .fvar (x+1))
def Formula.free (p : Formula Nat 1) : Formula Nat 0 :=
  p.rewrite (fun _ => .fvar 0) (fun x => .fvar (x+1))
def Formula.instantiate (p : Formula ξ 1) (t : Term ξ 0) : Formula ξ 0 :=
  p.rewrite (fun _ => t) Term.fvar
end PalomarPA
/-! Explicit finitary classical first-order sequent proof objects. The theory
parameter is not yet instantiated to PA: no arbitrary/opaque PA predicate is
being advertised as the final Challenge. -/
namespace PalomarPA
/-- Stable proof-calculus equality, independent of generated recursive compiler helpers. -/
noncomputable def calculusFormulaEq : DecidableEq (Formula Nat 0) := Classical.typeDecidableEq _
attribute [local instance] calculusFormulaEq
noncomputable section
abbrev Sequent := Finset (Formula Nat 0)
inductive Derivation (T : Sentence → Prop) : Sequent → Type where
  | closed (Γ) (p : Formula Nat 0) : p ∈ Γ → p.neg ∈ Γ → Derivation T Γ
  | axiom {Γ} (p : Sentence) : T p → p.embed ∈ Γ → Derivation T Γ
  | top {Γ} : Formula.top ∈ Γ → Derivation T Γ
  | and {Γ p q} : Formula.and p q ∈ Γ →
      Derivation T (insert p Γ) → Derivation T (insert q Γ) → Derivation T Γ
  | or {Γ p q} : Formula.or p q ∈ Γ →
      Derivation T (insert p (insert q Γ)) → Derivation T Γ
  | all {Γ} {p : Formula Nat 1} : Formula.all p ∈ Γ →
      Derivation T (insert p.free (Γ.image Formula.shift)) → Derivation T Γ
  | ex {Γ} {p : Formula Nat 1} : Formula.ex p ∈ Γ → (t : Term Nat 0) →
      Derivation T (insert (p.instantiate t) Γ) → Derivation T Γ
  | weaken {Δ Γ} : Derivation T Δ → Δ ⊆ Γ → Derivation T Γ
  | shift {Γ} : Derivation T Γ → Derivation T (Γ.image Formula.shift)
  | cut {Γ p} : Derivation T (insert p Γ) → Derivation T (insert p.neg Γ) → Derivation T Γ

def Provable (T : Sentence → Prop) (p : Sentence) : Prop :=
  Nonempty (Derivation T {p.embed})
end
end PalomarPA
namespace PalomarPA
/-- Finite ordered-ring PA-minus and equality axioms. No external theory predicate. -/
inductive BaseAxiom where
  | eqRefl | eqSymm | eqTrans | zeroExt | oneExt | addExt | mulExt | eqExt | ltExt
  | addZero | addAssoc | addComm | addEqOfLt | zeroLe | zeroLtOne | oneLeOfZeroLt
  | addLtAdd | mulZero | mulOne | mulAssoc | mulComm | mulLtMul | distr
  | ltIrrefl | ltTrans | ltTri
  deriving DecidableEq

def Formula.imp (p q : Formula ξ n) := Formula.or p.neg q

def BaseAxiom.formula : BaseAxiom → Sentence
  | .eqRefl => .all (.eq (.bvar (boundIndex 0)) (.bvar (boundIndex 0)))
  | .eqSymm => .all (.all (.imp (.eq (.bvar (boundIndex 1)) (.bvar (boundIndex 0))) (.eq (.bvar (boundIndex 0)) (.bvar (boundIndex 1)))))
  | .eqTrans => .all (.all (.all (.imp (.eq (.bvar (boundIndex 2)) (.bvar (boundIndex 1)))
      (.imp (.eq (.bvar (boundIndex 1)) (.bvar (boundIndex 0))) (.eq (.bvar (boundIndex 2)) (.bvar (boundIndex 0)))))))
  | .zeroExt => .imp .top (.eq .zero .zero)
  | .oneExt => .imp .top (.eq .one .one)
  | .addExt => .all (.all (.all (.all (.imp
      (.and (.eq (.bvar (boundIndex 0)) (.bvar (boundIndex 2))) (.and (.eq (.bvar (boundIndex 1)) (.bvar (boundIndex 3))) .top))
      (.eq (.add (.bvar (boundIndex 0)) (.bvar (boundIndex 1))) (.add (.bvar (boundIndex 2)) (.bvar (boundIndex 3))))))))
  | .mulExt => .all (.all (.all (.all (.imp
      (.and (.eq (.bvar (boundIndex 0)) (.bvar (boundIndex 2))) (.and (.eq (.bvar (boundIndex 1)) (.bvar (boundIndex 3))) .top))
      (.eq (.mul (.bvar (boundIndex 0)) (.bvar (boundIndex 1))) (.mul (.bvar (boundIndex 2)) (.bvar (boundIndex 3))))))))
  | .eqExt => .all (.all (.all (.all (.imp
      (.and (.eq (.bvar (boundIndex 0)) (.bvar (boundIndex 2))) (.and (.eq (.bvar (boundIndex 1)) (.bvar (boundIndex 3))) .top))
      (.imp (.eq (.bvar (boundIndex 0)) (.bvar (boundIndex 1))) (.eq (.bvar (boundIndex 2)) (.bvar (boundIndex 3))))))))
  | .ltExt => .all (.all (.all (.all (.imp
      (.and (.eq (.bvar (boundIndex 0)) (.bvar (boundIndex 2))) (.and (.eq (.bvar (boundIndex 1)) (.bvar (boundIndex 3))) .top))
      (.imp (.lt (.bvar (boundIndex 0)) (.bvar (boundIndex 1))) (.lt (.bvar (boundIndex 2)) (.bvar (boundIndex 3))))))))
  | .addZero => .all (.eq (.add (.bvar (boundIndex 0)) .zero) (.bvar (boundIndex 0)))
  | .addAssoc => .all (.all (.all (.eq (.add (.add (.bvar (boundIndex 2)) (.bvar (boundIndex 1))) (.bvar (boundIndex 0)))
      (.add (.bvar (boundIndex 2)) (.add (.bvar (boundIndex 1)) (.bvar (boundIndex 0)))))))
  | .addComm => .all (.all (.eq (.add (.bvar (boundIndex 1)) (.bvar (boundIndex 0))) (.add (.bvar (boundIndex 0)) (.bvar (boundIndex 1)))))
  | .addEqOfLt => .all (.all (.imp (.lt (.bvar (boundIndex 1)) (.bvar (boundIndex 0)))
      (.ex (.and (.lt (.bvar (boundIndex 0)) (.add (.bvar (boundIndex 1)) .one))
        (.eq (.add (.bvar (boundIndex 2)) (.bvar (boundIndex 0))) (.bvar (boundIndex 1)))))))
  | .zeroLe => .all (.or (.eq .zero (.bvar (boundIndex 0))) (.lt .zero (.bvar (boundIndex 0))))
  | .zeroLtOne => .lt .zero .one
  | .oneLeOfZeroLt => .all (.imp (.lt .zero (.bvar (boundIndex 0)))
      (.or (.eq .one (.bvar (boundIndex 0))) (.lt .one (.bvar (boundIndex 0)))))
  | .addLtAdd => .all (.all (.all (.imp (.lt (.bvar (boundIndex 2)) (.bvar (boundIndex 1)))
      (.lt (.add (.bvar (boundIndex 2)) (.bvar (boundIndex 0))) (.add (.bvar (boundIndex 1)) (.bvar (boundIndex 0)))))))
  | .mulZero => .all (.eq (.mul (.bvar (boundIndex 0)) .zero) .zero)
  | .mulOne => .all (.eq (.mul (.bvar (boundIndex 0)) .one) (.bvar (boundIndex 0)))
  | .mulAssoc => .all (.all (.all (.eq (.mul (.mul (.bvar (boundIndex 2)) (.bvar (boundIndex 1))) (.bvar (boundIndex 0)))
      (.mul (.bvar (boundIndex 2)) (.mul (.bvar (boundIndex 1)) (.bvar (boundIndex 0)))))))
  | .mulComm => .all (.all (.eq (.mul (.bvar (boundIndex 1)) (.bvar (boundIndex 0))) (.mul (.bvar (boundIndex 0)) (.bvar (boundIndex 1)))))
  | .mulLtMul => .all (.all (.all (.imp (.and (.lt (.bvar (boundIndex 2)) (.bvar (boundIndex 1))) (.lt .zero (.bvar (boundIndex 0))))
      (.lt (.mul (.bvar (boundIndex 2)) (.bvar (boundIndex 0))) (.mul (.bvar (boundIndex 1)) (.bvar (boundIndex 0)))))))
  | .distr => .all (.all (.all (.eq (.mul (.bvar (boundIndex 2)) (.add (.bvar (boundIndex 1)) (.bvar (boundIndex 0))))
      (.add (.mul (.bvar (boundIndex 2)) (.bvar (boundIndex 1))) (.mul (.bvar (boundIndex 2)) (.bvar (boundIndex 0)))))))
  | .ltIrrefl => .all (.nlt (.bvar (boundIndex 0)) (.bvar (boundIndex 0)))
  | .ltTrans => .all (.all (.all (.imp (.and (.lt (.bvar (boundIndex 2)) (.bvar (boundIndex 1))) (.lt (.bvar (boundIndex 1)) (.bvar (boundIndex 0))))
      (.lt (.bvar (boundIndex 2)) (.bvar (boundIndex 0))))) )
  | .ltTri => .all (.all (.or (.lt (.bvar (boundIndex 1)) (.bvar (boundIndex 0)))
      (.or (.eq (.bvar (boundIndex 1)) (.bvar (boundIndex 0))) (.lt (.bvar (boundIndex 0)) (.bvar (boundIndex 1))))))

/-- The usual successor-induction formula, before universally closing parameters. -/
def Formula.succInd (p : Formula Nat 1) : Formula Nat 0 :=
  .imp (p.instantiate .zero)
    (.imp (.all (.imp p (p.rewrite (fun _ => .add (.bvar (boundIndex 0)) .one) Term.fvar))) (.all p))

def Term.freeVariables : Term Nat n → Finset Nat
  | .bvar _ | .zero | .one => ∅
  | .fvar x => {x}
  | .add t u | .mul t u => t.freeVariables ∪ u.freeVariables

def Formula.freeVariables : Formula Nat n → Finset Nat
  | .top | .bot => ∅
  | .eq t u | .ne t u | .lt t u | .nlt t u => t.freeVariables ∪ u.freeVariables
  | .and p q | .or p q => p.freeVariables ∪ q.freeVariables
  | .all p | .ex p => p.freeVariables

def Formula.fvSup (p : Formula Nat n) : Nat :=
  p.freeVariables.max.recBotCoe 0 Nat.succ

def Formula.allClosure : {n : Nat} → Formula ξ n → Formula ξ 0
  | 0, p => p
  | _+1, p => allClosure (.all p)

/-- Capture exactly the finite range of free-variable indices, then bind it.
The unreachable out-of-range branch is zero, not a choice or an axiom. -/
def Formula.univCl (p : Formula Nat 0) : Sentence :=
  (p.rewrite Fin.elim0 (fun x => if h : x < p.fvSup then .bvar (Fin.natAdd 0 ⟨x,h⟩) else .zero)).allClosure

/-- Ordinary PA: finite arithmetic/equality axioms and all parameter-closed
successor-induction instances. This predicate is independent of Foundation. -/
inductive PATheory : Sentence → Prop where
  | base (a : BaseAxiom) : PATheory a.formula
  | induction (p : Formula Nat 1) : PATheory p.succInd.univCl
end PalomarPA
namespace PalomarPA.PrimitiveData
abbrev T := Term Empty
abbrev F := Formula Empty
def d0 (n:Nat):T n:=if h:0<n then .bvar ⟨0,h⟩ else .zero def d1 (n:Nat):T n:=if h:1<n then .bvar ⟨1,h⟩ else .zero def d2 (n:Nat):T n:=.one def d3 (n:Nat):T n:=.add (d1 n) (d2 n)
def d4 (n:Nat):F n:=.lt (d0 n) (d3 n) def d5 (n:Nat):T n:=if h:2<n then .bvar ⟨2,h⟩ else .zero def d6 (n:Nat):F n:=.lt (d5 n) (d0 n) def d7 (n:Nat):T n:=.mul (d0 n) (d0 n)
def d8 (n:Nat):T n:=.add (d7 n) (d5 n) def d9 (n:Nat):F n:=.eq (d1 n) (d8 n) def d10 (n:Nat):F n:=.and (d6 n) (d9 n) def d11 (n:Nat):F n:=.eq (d0 n) (d5 n)
def d12 (n:Nat):F n:=.lt (d0 n) (d5 n) def d13 (n:Nat):F n:=.or (d11 n) (d12 n) def d14 (n:Nat):T n:=.mul (d5 n) (d5 n) def d15 (n:Nat):T n:=.add (d14 n) (d5 n)
def d16 (n:Nat):T n:=.add (d15 n) (d0 n) def d17 (n:Nat):F n:=.eq (d1 n) (d16 n) def d18 (n:Nat):F n:=.and (d13 n) (d17 n) def d19 (n:Nat):F n:=.or (d10 n) (d18 n)
def d20 (n:Nat):T n:=if h:3<n then .bvar ⟨3,h⟩ else .zero def d21 (n:Nat):T n:=if h:4<n then .bvar ⟨4,h⟩ else .zero def d22 (n:Nat):F n:=.lt (d20 n) (d21 n) def d23 (n:Nat):T n:=.mul (d21 n) (d21 n)
def d24 (n:Nat):T n:=.add (d23 n) (d20 n) def d25 (n:Nat):F n:=.eq (d0 n) (d24 n) def d26 (n:Nat):F n:=.and (d22 n) (d25 n) def d27 (n:Nat):F n:=.eq (d21 n) (d20 n)
def d28 (n:Nat):F n:=.lt (d21 n) (d20 n) def d29 (n:Nat):F n:=.or (d27 n) (d28 n) def d30 (n:Nat):T n:=.mul (d20 n) (d20 n) def d31 (n:Nat):T n:=.add (d30 n) (d20 n)
def d32 (n:Nat):T n:=.add (d31 n) (d21 n) def d33 (n:Nat):F n:=.eq (d0 n) (d32 n) def d34 (n:Nat):F n:=.and (d29 n) (d33 n) def d35 (n:Nat):F n:=.or (d26 n) (d34 n)
def d36 (n:Nat):F n:=.and (d19 n) (d35 n) def d37 (n:Nat):F n:=.and (d4 n) (d36 n) def d38 (n:Nat):F n:=.ex (d37 (n+1)) def d39 (n:Nat):T n:=.add (d5 n) (d2 n)
def d40 (n:Nat):F n:=.lt (d0 n) (d39 n) def d41 (n:Nat):T n:=.zero def d42 (n:Nat):F n:=.eq (d1 n) (d41 n) def d43 (n:Nat):F n:=.eq (d0 n) (d2 n)
def d44 (n:Nat):F n:=.and (d42 n) (d43 n) def d45 (n:Nat):T n:=.mul (d2 n) (d1 n) def d46 (n:Nat):T n:=.mul (d45 n) (d1 n) def d47 (n:Nat):T n:=.mul (d46 n) (d1 n)
def d48 (n:Nat):T n:=.mul (d47 n) (d1 n) def d49 (n:Nat):T n:=.add (d48 n) (d2 n) def d50 (n:Nat):F n:=.lt (d0 n) (d49 n) def d51 (n:Nat):T n:=.mul (d2 n) (d5 n)
def d52 (n:Nat):T n:=.mul (d51 n) (d5 n) def d53 (n:Nat):T n:=.mul (d52 n) (d5 n) def d54 (n:Nat):T n:=.mul (d53 n) (d5 n) def d55 (n:Nat):T n:=.add (d54 n) (d2 n)
def d56 (n:Nat):F n:=.lt (d0 n) (d55 n) def d57 (n:Nat):T n:=.add (d2 n) (d2 n) def d58 (n:Nat):T n:=.add (d57 n) (d2 n) def d59 (n:Nat):T n:=.add (d58 n) (d2 n)
def d60 (n:Nat):F n:=.nlt (d41 n) (d59 n) def d61 (n:Nat):T n:=.mul (d59 n) (d0 n) def d62 (n:Nat):F n:=.eq (d61 n) (d5 n) def d63 (n:Nat):F n:=.lt (d61 n) (d5 n)
def d64 (n:Nat):F n:=.or (d62 n) (d63 n) def d65 (n:Nat):T n:=.add (d0 n) (d2 n) def d66 (n:Nat):T n:=.mul (d59 n) (d65 n) def d67 (n:Nat):F n:=.lt (d5 n) (d66 n)
def d68 (n:Nat):F n:=.and (d64 n) (d67 n) def d69 (n:Nat):F n:=.or (d60 n) (d68 n) def d70 (n:Nat):F n:=.ne (d59 n) (d41 n) def d71 (n:Nat):F n:=.eq (d0 n) (d41 n)
def d72 (n:Nat):F n:=.or (d70 n) (d71 n) def d73 (n:Nat):F n:=.and (d69 n) (d72 n) def d74 (n:Nat):F n:=.eq (d61 n) (d1 n) def d75 (n:Nat):F n:=.lt (d61 n) (d1 n)
def d76 (n:Nat):F n:=.or (d74 n) (d75 n) def d77 (n:Nat):F n:=.lt (d1 n) (d66 n) def d78 (n:Nat):F n:=.and (d76 n) (d77 n) def d79 (n:Nat):F n:=.or (d60 n) (d78 n)
def d80 (n:Nat):F n:=.and (d79 n) (d72 n) def d81 (n:Nat):F n:=.ne (d61 n) (d1 n) def d82 (n:Nat):F n:=.nlt (d61 n) (d1 n) def d83 (n:Nat):F n:=.and (d81 n) (d82 n)
def d84 (n:Nat):T n:=.add (d61 n) (d2 n) def d85 (n:Nat):F n:=.eq (d1 n) (d84 n) def d86 (n:Nat):F n:=.or (d83 n) (d85 n) def d87 (n:Nat):F n:=.nlt (d1 n) (d61 n)
def d88 (n:Nat):F n:=.eq (d2 n) (d41 n) def d89 (n:Nat):F n:=.or (d87 n) (d88 n) def d90 (n:Nat):F n:=.and (d86 n) (d89 n) def d91 (n:Nat):F n:=.and (d80 n) (d90 n)
def d92 (n:Nat):F n:=.and (d4 n) (d91 n) def d93 (n:Nat):F n:=.ex (d92 (n+1)) def d94 (n:Nat):F n:=.and (d73 n) (d93 n) def d95 (n:Nat):F n:=.and (d40 n) (d94 n)
def d96 (n:Nat):F n:=.ex (d95 (n+1)) def d97 (n:Nat):T n:=.add (d61 n) (d57 n) def d98 (n:Nat):F n:=.eq (d1 n) (d97 n) def d99 (n:Nat):F n:=.or (d83 n) (d98 n)
def d100 (n:Nat):F n:=.eq (d57 n) (d41 n) def d101 (n:Nat):F n:=.or (d87 n) (d100 n) def d102 (n:Nat):F n:=.and (d99 n) (d101 n) def d103 (n:Nat):F n:=.and (d80 n) (d102 n)
def d104 (n:Nat):F n:=.and (d4 n) (d103 n) def d105 (n:Nat):F n:=.ex (d104 (n+1)) def d106 (n:Nat):F n:=.and (d80 n) (d105 n) def d107 (n:Nat):F n:=.and (d4 n) (d106 n)
def d108 (n:Nat):F n:=.ex (d107 (n+1)) def d109 (n:Nat):F n:=.and (d96 n) (d108 n) def d110 (n:Nat):T n:=.add (d20 n) (d2 n) def d111 (n:Nat):F n:=.nlt (d0 n) (d110 n)
def d112 (n:Nat):F n:=.eq (d0 n) (d57 n) def d113 (n:Nat):F n:=.nlt (d41 n) (d0 n) def d114 (n:Nat):F n:=.lt (d2 n) (d0 n) def d115 (n:Nat):T n:=.mul (d1 n) (d0 n)
def d116 (n:Nat):F n:=.eq (d5 n) (d115 n) def d117 (n:Nat):F n:=.and (d40 n) (d116 n) def d118 (n:Nat):F n:=.ex (d117 (n+1)) def d119 (n:Nat):F n:=.nlt (d0 n) (d3 n)
def d120 (n:Nat):T n:=.mul (d57 n) (d0 n) def d121 (n:Nat):F n:=.ne (d1 n) (d120 n) def d122 (n:Nat):F n:=.or (d119 n) (d121 n) def d123 (n:Nat):F n:=.all (d122 (n+1))
def d124 (n:Nat):F n:=.and (d118 n) (d123 n) def d125 (n:Nat):F n:=.and (d114 n) (d124 n) def d126 (n:Nat):F n:=.and (d4 n) (d125 n) def d127 (n:Nat):F n:=.ex (d126 (n+1))
def d128 (n:Nat):F n:=.or (d113 n) (d127 n) def d129 (n:Nat):T n:=.mul (d57 n) (d1 n) def d130 (n:Nat):F n:=.nlt (d0 n) (d129 n) def d131 (n:Nat):F n:=.nlt (d41 n) (d2 n)
def d132 (n:Nat):T n:=.mul (d2 n) (d0 n) def d133 (n:Nat):F n:=.eq (d132 n) (d1 n) def d134 (n:Nat):F n:=.lt (d132 n) (d1 n) def d135 (n:Nat):F n:=.or (d133 n) (d134 n)
def d136 (n:Nat):T n:=.mul (d2 n) (d65 n) def d137 (n:Nat):F n:=.lt (d1 n) (d136 n) def d138 (n:Nat):F n:=.and (d135 n) (d137 n) def d139 (n:Nat):F n:=.or (d131 n) (d138 n)
def d140 (n:Nat):F n:=.ne (d2 n) (d41 n) def d141 (n:Nat):F n:=.or (d140 n) (d71 n) def d142 (n:Nat):F n:=.and (d139 n) (d141 n) def d143 (n:Nat):F n:=.and (d142 n) (d123 n)
def d144 (n:Nat):F n:=.and (d4 n) (d143 n) def d145 (n:Nat):F n:=.ex (d144 (n+1)) def d146 (n:Nat):F n:=.lt (d41 n) (d57 n) def d147 (n:Nat):F n:=.ne (d120 n) (d1 n)
def d148 (n:Nat):F n:=.nlt (d120 n) (d1 n) def d149 (n:Nat):F n:=.and (d147 n) (d148 n) def d150 (n:Nat):T n:=.mul (d57 n) (d65 n) def d151 (n:Nat):F n:=.nlt (d1 n) (d150 n)
def d152 (n:Nat):F n:=.or (d149 n) (d151 n) def d153 (n:Nat):F n:=.and (d146 n) (d152 n) def d154 (n:Nat):F n:=.ne (d0 n) (d41 n) def d155 (n:Nat):F n:=.and (d100 n) (d154 n)
def d156 (n:Nat):F n:=.or (d153 n) (d155 n) def d157 (n:Nat):F n:=.eq (d1 n) (d120 n) def d158 (n:Nat):F n:=.and (d4 n) (d157 n) def d159 (n:Nat):F n:=.ex (d158 (n+1))
def d160 (n:Nat):F n:=.or (d156 n) (d159 n) def d161 (n:Nat):F n:=.or (d119 n) (d160 n) def d162 (n:Nat):F n:=.all (d161 (n+1)) def d163 (n:Nat):F n:=.lt (d41 n) (d0 n)
def d164 (n:Nat):F n:=.nlt (d2 n) (d0 n) def d165 (n:Nat):F n:=.nlt (d0 n) (d39 n) def d166 (n:Nat):F n:=.ne (d5 n) (d115 n) def d167 (n:Nat):F n:=.or (d165 n) (d166 n)
def d168 (n:Nat):F n:=.all (d167 (n+1)) def d169 (n:Nat):F n:=.or (d168 n) (d159 n) def d170 (n:Nat):F n:=.or (d164 n) (d169 n) def d171 (n:Nat):F n:=.or (d119 n) (d170 n)
def d172 (n:Nat):F n:=.all (d171 (n+1)) def d173 (n:Nat):F n:=.and (d163 n) (d172 n) def d174 (n:Nat):F n:=.lt (d57 n) (d0 n) def d175 (n:Nat):F n:=.nlt (d41 n) (d1 n)
def d176 (n:Nat):F n:=.eq (d115 n) (d5 n) def d177 (n:Nat):F n:=.lt (d115 n) (d5 n) def d178 (n:Nat):F n:=.or (d176 n) (d177 n) def d179 (n:Nat):T n:=.mul (d1 n) (d65 n)
def d180 (n:Nat):F n:=.lt (d5 n) (d179 n) def d181 (n:Nat):F n:=.and (d178 n) (d180 n) def d182 (n:Nat):F n:=.or (d175 n) (d181 n) def d183 (n:Nat):F n:=.ne (d1 n) (d41 n)
def d184 (n:Nat):F n:=.or (d183 n) (d71 n) def d185 (n:Nat):F n:=.and (d182 n) (d184 n) def d186 (n:Nat):F n:=.and (d185 n) (d123 n) def d187 (n:Nat):F n:=.and (d40 n) (d186 n)
def d188 (n:Nat):F n:=.ex (d187 (n+1)) def d189 (n:Nat):F n:=.ne (d7 n) (d1 n) def d190 (n:Nat):F n:=.nlt (d7 n) (d1 n) def d191 (n:Nat):F n:=.and (d189 n) (d190 n)
def d192 (n:Nat):T n:=.mul (d65 n) (d65 n) def d193 (n:Nat):F n:=.nlt (d1 n) (d192 n) def d194 (n:Nat):F n:=.or (d191 n) (d193 n) def d195 (n:Nat):F n:=.lt (d41 n) (d1 n)
def d196 (n:Nat):F n:=.ne (d115 n) (d20 n) def d197 (n:Nat):F n:=.nlt (d115 n) (d20 n) def d198 (n:Nat):F n:=.and (d196 n) (d197 n) def d199 (n:Nat):F n:=.nlt (d20 n) (d179 n)
def d200 (n:Nat):F n:=.or (d198 n) (d199 n) def d201 (n:Nat):F n:=.and (d195 n) (d200 n) def d202 (n:Nat):F n:=.and (d42 n) (d154 n) def d203 (n:Nat):F n:=.or (d201 n) (d202 n)
def d204 (n:Nat):F n:=.or (d203 n) (d159 n) def d205 (n:Nat):F n:=.or (d111 n) (d204 n) def d206 (n:Nat):F n:=.all (d205 (n+1)) def d207 (n:Nat):F n:=.or (d189 n) (d206 n)
def d208 (n:Nat):F n:=.or (d194 n) (d207 n) def d209 (n:Nat):F n:=.or (d119 n) (d208 n) def d210 (n:Nat):F n:=.all (d209 (n+1)) def d211 (n:Nat):F n:=.and (d188 n) (d210 n)
def d212 (n:Nat):F n:=.eq (d7 n) (d1 n) def d213 (n:Nat):F n:=.lt (d7 n) (d1 n) def d214 (n:Nat):F n:=.or (d212 n) (d213 n) def d215 (n:Nat):F n:=.lt (d1 n) (d192 n)
def d216 (n:Nat):F n:=.and (d214 n) (d215 n) def d217 (n:Nat):F n:=.lt (d0 n) (d110 n) def d218 (n:Nat):F n:=.eq (d115 n) (d20 n) def d219 (n:Nat):F n:=.lt (d115 n) (d20 n)
def d220 (n:Nat):F n:=.or (d218 n) (d219 n) def d221 (n:Nat):F n:=.lt (d20 n) (d179 n) def d222 (n:Nat):F n:=.and (d220 n) (d221 n) def d223 (n:Nat):F n:=.or (d175 n) (d222 n)
def d224 (n:Nat):F n:=.and (d223 n) (d184 n) def d225 (n:Nat):F n:=.and (d224 n) (d123 n) def d226 (n:Nat):F n:=.and (d217 n) (d225 n) def d227 (n:Nat):F n:=.ex (d226 (n+1))
def d228 (n:Nat):F n:=.and (d212 n) (d227 n) def d229 (n:Nat):F n:=.and (d216 n) (d228 n) def d230 (n:Nat):F n:=.and (d4 n) (d229 n) def d231 (n:Nat):F n:=.ex (d230 (n+1))
def d232 (n:Nat):F n:=.ne (d115 n) (d5 n) def d233 (n:Nat):F n:=.nlt (d115 n) (d5 n) def d234 (n:Nat):F n:=.and (d232 n) (d233 n) def d235 (n:Nat):F n:=.nlt (d5 n) (d179 n)
def d236 (n:Nat):F n:=.or (d234 n) (d235 n) def d237 (n:Nat):F n:=.and (d195 n) (d236 n) def d238 (n:Nat):F n:=.or (d237 n) (d202 n) def d239 (n:Nat):F n:=.or (d238 n) (d159 n)
def d240 (n:Nat):F n:=.or (d165 n) (d239 n) def d241 (n:Nat):F n:=.all (d240 (n+1)) def d242 (n:Nat):F n:=.and (d231 n) (d241 n) def d243 (n:Nat):F n:=.or (d211 n) (d242 n)
def d244 (n:Nat):F n:=.and (d174 n) (d243 n) def d245 (n:Nat):F n:=.and (d173 n) (d244 n) def d246 (n:Nat):F n:=.and (d4 n) (d245 n) def d247 (n:Nat):F n:=.ex (d246 (n+1))
def d248 (n:Nat):F n:=.or (d162 n) (d247 n) def d249 (n:Nat):F n:=.or (d145 n) (d248 n) def d250 (n:Nat):F n:=.lt (d41 n) (d5 n) def d251 (n:Nat):T n:=.mul (d5 n) (d0 n)
def d252 (n:Nat):F n:=.ne (d251 n) (d1 n) def d253 (n:Nat):F n:=.nlt (d251 n) (d1 n) def d254 (n:Nat):F n:=.and (d252 n) (d253 n) def d255 (n:Nat):T n:=.mul (d5 n) (d65 n)
def d256 (n:Nat):F n:=.nlt (d1 n) (d255 n) def d257 (n:Nat):F n:=.or (d254 n) (d256 n) def d258 (n:Nat):F n:=.and (d250 n) (d257 n) def d259 (n:Nat):F n:=.eq (d5 n) (d41 n)
def d260 (n:Nat):F n:=.and (d259 n) (d154 n) def d261 (n:Nat):F n:=.or (d258 n) (d260 n) def d262 (n:Nat):F n:=.or (d261 n) (d159 n) def d263 (n:Nat):F n:=.or (d119 n) (d262 n)
def d264 (n:Nat):F n:=.all (d263 (n+1)) def d265 (n:Nat):F n:=.or (d249 n) (d264 n) def d266 (n:Nat):F n:=.or (d130 n) (d265 n) def d267 (n:Nat):F n:=.all (d266 (n+1))
def d268 (n:Nat):F n:=.or (d128 n) (d267 n) def d269 (n:Nat):T n:=.add (d21 n) (d2 n) def d270 (n:Nat):F n:=.lt (d0 n) (d269 n) def d271 (n:Nat):F n:=.nlt (d41 n) (d5 n)
def d272 (n:Nat):F n:=.eq (d251 n) (d21 n) def d273 (n:Nat):F n:=.lt (d251 n) (d21 n) def d274 (n:Nat):F n:=.or (d272 n) (d273 n) def d275 (n:Nat):F n:=.lt (d21 n) (d255 n)
def d276 (n:Nat):F n:=.and (d274 n) (d275 n) def d277 (n:Nat):F n:=.or (d271 n) (d276 n) def d278 (n:Nat):F n:=.ne (d5 n) (d41 n) def d279 (n:Nat):F n:=.or (d278 n) (d71 n)
def d280 (n:Nat):F n:=.and (d277 n) (d279 n) def d281 (n:Nat):F n:=.nlt (d41 n) (d20 n) def d282 (n:Nat):T n:=.mul (d20 n) (d0 n) def d283 (n:Nat):F n:=.eq (d282 n) (d1 n)
def d284 (n:Nat):F n:=.lt (d282 n) (d1 n) def d285 (n:Nat):F n:=.or (d283 n) (d284 n) def d286 (n:Nat):T n:=.mul (d20 n) (d65 n) def d287 (n:Nat):F n:=.lt (d1 n) (d286 n)
def d288 (n:Nat):F n:=.and (d285 n) (d287 n) def d289 (n:Nat):F n:=.or (d281 n) (d288 n) def d290 (n:Nat):F n:=.ne (d20 n) (d41 n) def d291 (n:Nat):F n:=.or (d290 n) (d71 n)
def d292 (n:Nat):F n:=.and (d289 n) (d291 n) def d293 (n:Nat):F n:=.ne (d282 n) (d1 n) def d294 (n:Nat):F n:=.nlt (d282 n) (d1 n) def d295 (n:Nat):F n:=.and (d293 n) (d294 n)
def d296 (n:Nat):T n:=.add (d282 n) (d5 n) def d297 (n:Nat):F n:=.eq (d1 n) (d296 n) def d298 (n:Nat):F n:=.or (d295 n) (d297 n) def d299 (n:Nat):F n:=.nlt (d1 n) (d282 n)
def d300 (n:Nat):F n:=.or (d299 n) (d259 n) def d301 (n:Nat):F n:=.and (d298 n) (d300 n) def d302 (n:Nat):F n:=.and (d292 n) (d301 n) def d303 (n:Nat):F n:=.and (d4 n) (d302 n)
def d304 (n:Nat):F n:=.ex (d303 (n+1)) def d305 (n:Nat):F n:=.and (d280 n) (d304 n) def d306 (n:Nat):F n:=.and (d270 n) (d305 n) def d307 (n:Nat):F n:=.ex (d306 (n+1))
def d308 (n:Nat):F n:=.nlt (d41 n) (d52 n) def d309 (n:Nat):T n:=.mul (d52 n) (d0 n) def d310 (n:Nat):F n:=.eq (d309 n) (d21 n) def d311 (n:Nat):F n:=.lt (d309 n) (d21 n)
def d312 (n:Nat):F n:=.or (d310 n) (d311 n) def d313 (n:Nat):T n:=.mul (d52 n) (d65 n) def d314 (n:Nat):F n:=.lt (d21 n) (d313 n) def d315 (n:Nat):F n:=.and (d312 n) (d314 n)
def d316 (n:Nat):F n:=.or (d308 n) (d315 n) def d317 (n:Nat):F n:=.ne (d52 n) (d41 n) def d318 (n:Nat):F n:=.or (d317 n) (d71 n) def d319 (n:Nat):F n:=.and (d316 n) (d318 n)
def d320 (n:Nat):T n:=.mul (d2 n) (d20 n) def d321 (n:Nat):T n:=.mul (d320 n) (d20 n) def d322 (n:Nat):F n:=.nlt (d41 n) (d321 n) def d323 (n:Nat):T n:=.mul (d321 n) (d0 n)
def d324 (n:Nat):F n:=.eq (d323 n) (d1 n) def d325 (n:Nat):F n:=.lt (d323 n) (d1 n) def d326 (n:Nat):F n:=.or (d324 n) (d325 n) def d327 (n:Nat):T n:=.mul (d321 n) (d65 n)
def d328 (n:Nat):F n:=.lt (d1 n) (d327 n) def d329 (n:Nat):F n:=.and (d326 n) (d328 n) def d330 (n:Nat):F n:=.or (d322 n) (d329 n) def d331 (n:Nat):F n:=.ne (d321 n) (d41 n)
def d332 (n:Nat):F n:=.or (d331 n) (d71 n) def d333 (n:Nat):F n:=.and (d330 n) (d332 n) def d334 (n:Nat):F n:=.ne (d323 n) (d1 n) def d335 (n:Nat):F n:=.nlt (d323 n) (d1 n)
def d336 (n:Nat):F n:=.and (d334 n) (d335 n) def d337 (n:Nat):T n:=.mul (d57 n) (d5 n) def d338 (n:Nat):T n:=.add (d323 n) (d337 n) def d339 (n:Nat):F n:=.eq (d1 n) (d338 n)
def d340 (n:Nat):F n:=.or (d336 n) (d339 n) def d341 (n:Nat):F n:=.nlt (d1 n) (d323 n) def d342 (n:Nat):F n:=.eq (d337 n) (d41 n) def d343 (n:Nat):F n:=.or (d341 n) (d342 n)
def d344 (n:Nat):F n:=.and (d340 n) (d343 n) def d345 (n:Nat):F n:=.and (d333 n) (d344 n) def d346 (n:Nat):F n:=.and (d4 n) (d345 n) def d347 (n:Nat):F n:=.ex (d346 (n+1))
def d348 (n:Nat):F n:=.and (d319 n) (d347 n) def d349 (n:Nat):F n:=.and (d270 n) (d348 n) def d350 (n:Nat):F n:=.ex (d349 (n+1)) def d351 (n:Nat):F n:=.and (d307 n) (d350 n)
def d352 (n:Nat):F n:=.and (d217 n) (d351 n) def d353 (n:Nat):F n:=.ex (d352 (n+1)) def d354 (n:Nat):F n:=.eq (d251 n) (d20 n) def d355 (n:Nat):F n:=.lt (d251 n) (d20 n)
def d356 (n:Nat):F n:=.or (d354 n) (d355 n) def d357 (n:Nat):F n:=.lt (d20 n) (d255 n) def d358 (n:Nat):F n:=.and (d356 n) (d357 n) def d359 (n:Nat):F n:=.or (d271 n) (d358 n)
def d360 (n:Nat):F n:=.and (d359 n) (d279 n) def d361 (n:Nat):F n:=.and (d360 n) (d304 n) def d362 (n:Nat):F n:=.and (d217 n) (d361 n) def d363 (n:Nat):F n:=.ex (d362 (n+1))
def d364 (n:Nat):F n:=.eq (d309 n) (d20 n) def d365 (n:Nat):F n:=.lt (d309 n) (d20 n) def d366 (n:Nat):F n:=.or (d364 n) (d365 n) def d367 (n:Nat):F n:=.lt (d20 n) (d313 n)
def d368 (n:Nat):F n:=.and (d366 n) (d367 n) def d369 (n:Nat):F n:=.or (d308 n) (d368 n) def d370 (n:Nat):F n:=.and (d369 n) (d318 n) def d371 (n:Nat):T n:=.add (d323 n) (d52 n)
def d372 (n:Nat):F n:=.eq (d1 n) (d371 n) def d373 (n:Nat):F n:=.or (d336 n) (d372 n) def d374 (n:Nat):F n:=.eq (d52 n) (d41 n) def d375 (n:Nat):F n:=.or (d341 n) (d374 n)
def d376 (n:Nat):F n:=.and (d373 n) (d375 n) def d377 (n:Nat):F n:=.and (d333 n) (d376 n) def d378 (n:Nat):F n:=.and (d4 n) (d377 n) def d379 (n:Nat):F n:=.ex (d378 (n+1))
def d380 (n:Nat):F n:=.and (d370 n) (d379 n) def d381 (n:Nat):F n:=.and (d217 n) (d380 n) def d382 (n:Nat):F n:=.ex (d381 (n+1)) def d383 (n:Nat):F n:=.and (d363 n) (d382 n)
def d384 (n:Nat):F n:=.and (d40 n) (d383 n) def d385 (n:Nat):F n:=.ex (d384 (n+1)) def d386 (n:Nat):F n:=.and (d353 n) (d385 n) def d387 (n:Nat):T n:=.add (d337 n) (d2 n)
def d388 (n:Nat):T n:=.add (d323 n) (d387 n) def d389 (n:Nat):F n:=.eq (d1 n) (d388 n) def d390 (n:Nat):F n:=.or (d336 n) (d389 n) def d391 (n:Nat):F n:=.eq (d387 n) (d41 n)
def d392 (n:Nat):F n:=.or (d341 n) (d391 n) def d393 (n:Nat):F n:=.and (d390 n) (d392 n) def d394 (n:Nat):F n:=.and (d333 n) (d393 n) def d395 (n:Nat):F n:=.and (d4 n) (d394 n)
def d396 (n:Nat):F n:=.ex (d395 (n+1)) def d397 (n:Nat):F n:=.and (d319 n) (d396 n) def d398 (n:Nat):F n:=.and (d270 n) (d397 n) def d399 (n:Nat):F n:=.ex (d398 (n+1))
def d400 (n:Nat):F n:=.and (d307 n) (d399 n) def d401 (n:Nat):F n:=.and (d217 n) (d400 n) def d402 (n:Nat):F n:=.ex (d401 (n+1)) def d403 (n:Nat):T n:=.mul (d57 n) (d52 n)
def d404 (n:Nat):T n:=.add (d323 n) (d403 n) def d405 (n:Nat):F n:=.eq (d1 n) (d404 n) def d406 (n:Nat):F n:=.or (d336 n) (d405 n) def d407 (n:Nat):F n:=.eq (d403 n) (d41 n)
def d408 (n:Nat):F n:=.or (d341 n) (d407 n) def d409 (n:Nat):F n:=.and (d406 n) (d408 n) def d410 (n:Nat):F n:=.and (d333 n) (d409 n) def d411 (n:Nat):F n:=.and (d4 n) (d410 n)
def d412 (n:Nat):F n:=.ex (d411 (n+1)) def d413 (n:Nat):F n:=.and (d370 n) (d412 n) def d414 (n:Nat):F n:=.and (d217 n) (d413 n) def d415 (n:Nat):F n:=.ex (d414 (n+1))
def d416 (n:Nat):F n:=.and (d363 n) (d415 n) def d417 (n:Nat):F n:=.and (d40 n) (d416 n) def d418 (n:Nat):F n:=.ex (d417 (n+1)) def d419 (n:Nat):F n:=.and (d402 n) (d418 n)
def d420 (n:Nat):F n:=.or (d386 n) (d419 n) def d421 (n:Nat):F n:=.or (d268 n) (d420 n) def d422 (n:Nat):F n:=.or (d112 n) (d421 n) def d423 (n:Nat):F n:=.or (d111 n) (d422 n)
def d424 (n:Nat):F n:=.all (d423 (n+1)) def d425 (n:Nat):T n:=.add (d321 n) (d2 n) def d426 (n:Nat):F n:=.lt (d0 n) (d425 n) def d427 (n:Nat):F n:=.ne (d0 n) (d57 n)
def d428 (n:Nat):F n:=.lt (d0 n) (d129 n) def d429 (n:Nat):F n:=.lt (d41 n) (d2 n) def d430 (n:Nat):F n:=.ne (d132 n) (d1 n) def d431 (n:Nat):F n:=.nlt (d132 n) (d1 n)
def d432 (n:Nat):F n:=.and (d430 n) (d431 n) def d433 (n:Nat):F n:=.nlt (d1 n) (d136 n) def d434 (n:Nat):F n:=.or (d432 n) (d433 n) def d435 (n:Nat):F n:=.and (d429 n) (d434 n)
def d436 (n:Nat):F n:=.and (d88 n) (d154 n) def d437 (n:Nat):F n:=.or (d435 n) (d436 n) def d438 (n:Nat):F n:=.or (d437 n) (d159 n) def d439 (n:Nat):F n:=.or (d119 n) (d438 n)
def d440 (n:Nat):F n:=.all (d439 (n+1)) def d441 (n:Nat):F n:=.nlt (d41 n) (d57 n) def d442 (n:Nat):F n:=.eq (d120 n) (d1 n) def d443 (n:Nat):F n:=.lt (d120 n) (d1 n)
def d444 (n:Nat):F n:=.or (d442 n) (d443 n) def d445 (n:Nat):F n:=.lt (d1 n) (d150 n) def d446 (n:Nat):F n:=.and (d444 n) (d445 n) def d447 (n:Nat):F n:=.or (d441 n) (d446 n)
def d448 (n:Nat):F n:=.ne (d57 n) (d41 n) def d449 (n:Nat):F n:=.or (d448 n) (d71 n) def d450 (n:Nat):F n:=.and (d447 n) (d449 n) def d451 (n:Nat):F n:=.and (d450 n) (d123 n)
def d452 (n:Nat):F n:=.and (d4 n) (d451 n) def d453 (n:Nat):F n:=.ex (d452 (n+1)) def d454 (n:Nat):F n:=.nlt (d57 n) (d0 n) def d455 (n:Nat):F n:=.or (d241 n) (d231 n)
def d456 (n:Nat):F n:=.or (d210 n) (d188 n) def d457 (n:Nat):F n:=.and (d455 n) (d456 n) def d458 (n:Nat):F n:=.or (d454 n) (d457 n) def d459 (n:Nat):F n:=.or (d128 n) (d458 n)
def d460 (n:Nat):F n:=.or (d119 n) (d459 n) def d461 (n:Nat):F n:=.all (d460 (n+1)) def d462 (n:Nat):F n:=.and (d453 n) (d461 n) def d463 (n:Nat):F n:=.and (d440 n) (d462 n)
def d464 (n:Nat):F n:=.eq (d251 n) (d1 n) def d465 (n:Nat):F n:=.lt (d251 n) (d1 n) def d466 (n:Nat):F n:=.or (d464 n) (d465 n) def d467 (n:Nat):F n:=.lt (d1 n) (d255 n)
def d468 (n:Nat):F n:=.and (d466 n) (d467 n) def d469 (n:Nat):F n:=.or (d271 n) (d468 n) def d470 (n:Nat):F n:=.and (d469 n) (d279 n) def d471 (n:Nat):F n:=.and (d470 n) (d123 n)
def d472 (n:Nat):F n:=.and (d4 n) (d471 n) def d473 (n:Nat):F n:=.ex (d472 (n+1)) def d474 (n:Nat):F n:=.and (d463 n) (d473 n) def d475 (n:Nat):F n:=.and (d428 n) (d474 n)
def d476 (n:Nat):F n:=.ex (d475 (n+1)) def d477 (n:Nat):F n:=.and (d173 n) (d476 n) def d478 (n:Nat):T n:=if h:6<n then .bvar ⟨6,h⟩ else .zero def d479 (n:Nat):T n:=.add (d251 n) (d478 n)
def d480 (n:Nat):F n:=.eq (d1 n) (d479 n) def d481 (n:Nat):F n:=.or (d254 n) (d480 n) def d482 (n:Nat):F n:=.nlt (d1 n) (d251 n) def d483 (n:Nat):F n:=.eq (d478 n) (d41 n)
def d484 (n:Nat):F n:=.or (d482 n) (d483 n) def d485 (n:Nat):F n:=.and (d481 n) (d484 n) def d486 (n:Nat):F n:=.and (d470 n) (d485 n) def d487 (n:Nat):F n:=.and (d4 n) (d486 n)
def d488 (n:Nat):F n:=.ex (d487 (n+1)) def d489 (n:Nat):F n:=.and (d224 n) (d488 n) def d490 (n:Nat):F n:=.and (d217 n) (d489 n) def d491 (n:Nat):F n:=.ex (d490 (n+1))
def d492 (n:Nat):T n:=if h:5<n then .bvar ⟨5,h⟩ else .zero def d493 (n:Nat):T n:=.add (d251 n) (d492 n) def d494 (n:Nat):F n:=.eq (d1 n) (d493 n) def d495 (n:Nat):F n:=.or (d254 n) (d494 n)
def d496 (n:Nat):F n:=.eq (d492 n) (d41 n) def d497 (n:Nat):F n:=.or (d482 n) (d496 n) def d498 (n:Nat):F n:=.and (d495 n) (d497 n) def d499 (n:Nat):F n:=.and (d470 n) (d498 n)
def d500 (n:Nat):F n:=.and (d4 n) (d499 n) def d501 (n:Nat):F n:=.ex (d500 (n+1)) def d502 (n:Nat):F n:=.and (d185 n) (d501 n) def d503 (n:Nat):F n:=.and (d40 n) (d502 n)
def d504 (n:Nat):F n:=.ex (d503 (n+1)) def d505 (n:Nat):F n:=.and (d491 n) (d504 n) def d506 (n:Nat):F n:=.and (d477 n) (d505 n) def d507 (n:Nat):F n:=.and (d427 n) (d506 n)
def d508 (n:Nat):F n:=.and (d426 n) (d507 n) def d509 (n:Nat):F n:=.ex (d508 (n+1)) def d510 (n:Nat):F n:=.and (d424 n) (d509 n) def d511 (n:Nat):F n:=.and (d109 n) (d510 n)
def d512 (n:Nat):F n:=.and (d56 n) (d511 n) def d513 (n:Nat):F n:=.ex (d512 (n+1)) def d514 (n:Nat):F n:=.and (d50 n) (d513 n) def d515 (n:Nat):F n:=.ex (d514 (n+1))
def d516 (n:Nat):F n:=.or (d44 n) (d515 n) def d517 (n:Nat):F n:=.and (d516 n) (d227 n) def d518 (n:Nat):F n:=.and (d40 n) (d517 n) def d519 (n:Nat):F n:=.ex (d518 (n+1))
def d520 (n:Nat):T n:=.add (d5 n) (d20 n) def d521 (n:Nat):T n:=.add (d520 n) (d2 n) def d522 (n:Nat):T n:=.mul (d2 n) (d521 n) def d523 (n:Nat):T n:=.mul (d522 n) (d521 n)
def d524 (n:Nat):T n:=.add (d523 n) (d2 n) def d525 (n:Nat):F n:=.lt (d0 n) (d524 n) def d526 (n:Nat):F n:=.lt (d5 n) (d20 n) def d527 (n:Nat):T n:=.add (d30 n) (d5 n)
def d528 (n:Nat):F n:=.eq (d0 n) (d527 n) def d529 (n:Nat):F n:=.and (d526 n) (d528 n) def d530 (n:Nat):F n:=.eq (d20 n) (d5 n) def d531 (n:Nat):F n:=.lt (d20 n) (d5 n)
def d532 (n:Nat):F n:=.or (d530 n) (d531 n) def d533 (n:Nat):T n:=.add (d15 n) (d20 n) def d534 (n:Nat):F n:=.eq (d0 n) (d533 n) def d535 (n:Nat):F n:=.and (d532 n) (d534 n)
def d536 (n:Nat):F n:=.or (d529 n) (d535 n) def d537 (n:Nat):F n:=.and (d536 n) (d519 n) def d538 (n:Nat):F n:=.and (d525 n) (d537 n) def d539 (n:Nat):F n:=.ex (d538 (n+1))
def d540 (n:Nat):F n:=.ne (d2 n) (d5 n) def d541 (n:Nat):F n:=.nlt (d2 n) (d5 n) def d542 (n:Nat):F n:=.and (d540 n) (d541 n) def d543 (n:Nat):T n:=.add (d2 n) (d0 n)
def d544 (n:Nat):F n:=.eq (d5 n) (d543 n) def d545 (n:Nat):F n:=.or (d542 n) (d544 n) def d546 (n:Nat):F n:=.nlt (d5 n) (d2 n) def d547 (n:Nat):F n:=.or (d546 n) (d71 n)
def d548 (n:Nat):F n:=.and (d545 n) (d547 n) def d549 (n:Nat):F n:=.and (d4 n) (d19 n) def d550 (n:Nat):F n:=.ex (d549 (n+1)) def d551 (n:Nat):F n:=.and (d548 n) (d550 n)
def d552 (n:Nat):F n:=.and (d40 n) (d551 n) def d553 (n:Nat):F n:=.ex (d552 (n+1)) def d554 (n:Nat):F n:=.eq (d20 n) (d8 n) def d555 (n:Nat):F n:=.and (d6 n) (d554 n)
def d556 (n:Nat):F n:=.eq (d20 n) (d16 n) def d557 (n:Nat):F n:=.and (d13 n) (d556 n) def d558 (n:Nat):F n:=.or (d555 n) (d557 n) def d559 (n:Nat):T n:=.mul (d1 n) (d1 n)
def d560 (n:Nat):T n:=.add (d559 n) (d41 n) def d561 (n:Nat):F n:=.eq (d0 n) (d560 n) def d562 (n:Nat):F n:=.and (d195 n) (d561 n) def d563 (n:Nat):F n:=.lt (d1 n) (d41 n)
def d564 (n:Nat):F n:=.or (d42 n) (d563 n) def d565 (n:Nat):T n:=.mul (d41 n) (d41 n) def d566 (n:Nat):T n:=.add (d565 n) (d41 n) def d567 (n:Nat):T n:=.add (d566 n) (d1 n)
def d568 (n:Nat):F n:=.eq (d0 n) (d567 n) def d569 (n:Nat):F n:=.and (d564 n) (d568 n) def d570 (n:Nat):F n:=.or (d562 n) (d569 n) def d571 (n:Nat):F n:=.and (d558 n) (d570 n)
def d572 (n:Nat):F n:=.and (d217 n) (d571 n) def d573 (n:Nat):F n:=.ex (d572 (n+1)) def d574 (n:Nat):F n:=.and (d553 n) (d573 n) def d575 (n:Nat):F n:=.and (d4 n) (d574 n)
def d576 (n:Nat):F n:=.ex (d575 (n+1)) def d577 (n:Nat):F n:=.and (d4 n) (d576 n) def d578 (n:Nat):F n:=.ex (d577 (n+1)) def d579 (n:Nat):F n:=.lt (d20 n) (d0 n)
def d580 (n:Nat):T n:=.add (d7 n) (d20 n) def d581 (n:Nat):F n:=.eq (d21 n) (d580 n) def d582 (n:Nat):F n:=.and (d579 n) (d581 n) def d583 (n:Nat):F n:=.eq (d0 n) (d20 n)
def d584 (n:Nat):F n:=.lt (d0 n) (d20 n) def d585 (n:Nat):F n:=.or (d583 n) (d584 n) def d586 (n:Nat):T n:=.add (d31 n) (d0 n) def d587 (n:Nat):F n:=.eq (d21 n) (d586 n)
def d588 (n:Nat):F n:=.and (d585 n) (d587 n) def d589 (n:Nat):F n:=.or (d582 n) (d588 n) def d590 (n:Nat):F n:=.lt (d39 n) (d1 n) def d591 (n:Nat):T n:=.add (d559 n) (d39 n)
def d592 (n:Nat):F n:=.eq (d0 n) (d591 n) def d593 (n:Nat):F n:=.and (d590 n) (d592 n) def d594 (n:Nat):F n:=.eq (d1 n) (d39 n) def d595 (n:Nat):F n:=.lt (d1 n) (d39 n)
def d596 (n:Nat):F n:=.or (d594 n) (d595 n) def d597 (n:Nat):T n:=.mul (d39 n) (d39 n) def d598 (n:Nat):T n:=.add (d597 n) (d39 n) def d599 (n:Nat):T n:=.add (d598 n) (d1 n)
def d600 (n:Nat):F n:=.eq (d0 n) (d599 n) def d601 (n:Nat):F n:=.and (d596 n) (d600 n) def d602 (n:Nat):F n:=.or (d593 n) (d601 n) def d603 (n:Nat):F n:=.and (d589 n) (d602 n)
def d604 (n:Nat):F n:=.and (d270 n) (d603 n) def d605 (n:Nat):F n:=.ex (d604 (n+1)) def d606 (n:Nat):F n:=.ne (d2 n) (d21 n) def d607 (n:Nat):F n:=.nlt (d2 n) (d21 n)
def d608 (n:Nat):F n:=.and (d606 n) (d607 n) def d609 (n:Nat):F n:=.eq (d21 n) (d543 n) def d610 (n:Nat):F n:=.or (d608 n) (d609 n) def d611 (n:Nat):F n:=.nlt (d21 n) (d2 n)
def d612 (n:Nat):F n:=.or (d611 n) (d71 n) def d613 (n:Nat):F n:=.and (d610 n) (d612 n) def d614 (n:Nat):T n:=.add (d14 n) (d0 n) def d615 (n:Nat):F n:=.eq (d1 n) (d614 n)
def d616 (n:Nat):F n:=.and (d12 n) (d615 n) def d617 (n:Nat):F n:=.eq (d5 n) (d0 n) def d618 (n:Nat):F n:=.or (d617 n) (d6 n) def d619 (n:Nat):T n:=.add (d7 n) (d0 n)
def d620 (n:Nat):T n:=.add (d619 n) (d5 n) def d621 (n:Nat):F n:=.eq (d1 n) (d620 n) def d622 (n:Nat):F n:=.and (d618 n) (d621 n) def d623 (n:Nat):F n:=.or (d616 n) (d622 n)
def d624 (n:Nat):F n:=.and (d4 n) (d623 n) def d625 (n:Nat):F n:=.ex (d624 (n+1)) def d626 (n:Nat):F n:=.and (d613 n) (d625 n) def d627 (n:Nat):F n:=.and (d270 n) (d626 n)
def d628 (n:Nat):F n:=.ex (d627 (n+1)) def d629 (n:Nat):F n:=.lt (d0 n) (d478 n) def d630 (n:Nat):T n:=.add (d30 n) (d21 n) def d631 (n:Nat):F n:=.eq (d0 n) (d630 n)
def d632 (n:Nat):F n:=.and (d28 n) (d631 n) def d633 (n:Nat):F n:=.eq (d20 n) (d21 n) def d634 (n:Nat):F n:=.or (d633 n) (d22 n) def d635 (n:Nat):T n:=.add (d23 n) (d21 n)
def d636 (n:Nat):T n:=.add (d635 n) (d20 n) def d637 (n:Nat):F n:=.eq (d0 n) (d636 n) def d638 (n:Nat):F n:=.and (d634 n) (d637 n) def d639 (n:Nat):F n:=.or (d632 n) (d638 n)
def d640 (n:Nat):F n:=.and (d19 n) (d639 n) def d641 (n:Nat):F n:=.and (d4 n) (d640 n) def d642 (n:Nat):F n:=.ex (d641 (n+1)) def d643 (n:Nat):T n:=if h:7<n then .bvar ⟨7,h⟩ else .zero
def d644 (n:Nat):T n:=.add (d643 n) (d2 n) def d645 (n:Nat):F n:=.lt (d0 n) (d644 n) def d646 (n:Nat):T n:=if h:8<n then .bvar ⟨8,h⟩ else .zero def d647 (n:Nat):T n:=.add (d646 n) (d2 n)
def d648 (n:Nat):F n:=.lt (d0 n) (d647 n) def d649 (n:Nat):F n:=.eq (d115 n) (d646 n) def d650 (n:Nat):F n:=.lt (d115 n) (d646 n) def d651 (n:Nat):F n:=.or (d649 n) (d650 n)
def d652 (n:Nat):F n:=.lt (d646 n) (d179 n) def d653 (n:Nat):F n:=.and (d651 n) (d652 n) def d654 (n:Nat):F n:=.or (d175 n) (d653 n) def d655 (n:Nat):F n:=.and (d654 n) (d184 n)
def d656 (n:Nat):F n:=.and (d655 n) (d123 n) def d657 (n:Nat):F n:=.and (d648 n) (d656 n) def d658 (n:Nat):F n:=.ex (d657 (n+1)) def d659 (n:Nat):F n:=.and (d516 n) (d658 n)
def d660 (n:Nat):F n:=.and (d645 n) (d659 n) def d661 (n:Nat):F n:=.ex (d660 (n+1)) def d662 (n:Nat):F n:=.and (d642 n) (d661 n) def d663 (n:Nat):F n:=.and (d629 n) (d662 n)
def d664 (n:Nat):F n:=.ex (d663 (n+1)) def d665 (n:Nat):F n:=.and (d628 n) (d664 n) def d666 (n:Nat):F n:=.and (d217 n) (d665 n) def d667 (n:Nat):F n:=.ex (d666 (n+1))
def d668 (n:Nat):F n:=.and (d605 n) (d667 n) def d669 (n:Nat):F n:=.and (d217 n) (d668 n) def d670 (n:Nat):F n:=.ex (d669 (n+1)) def d671 (n:Nat):F n:=.and (d40 n) (d670 n)
def d672 (n:Nat):F n:=.ex (d671 (n+1)) def d673 (n:Nat):F n:=.and (d4 n) (d672 n) def d674 (n:Nat):F n:=.ex (d673 (n+1)) def d675 (n:Nat):F n:=.or (d578 n) (d674 n)
def d676 (n:Nat):T n:=.add (d129 n) (d2 n) def d677 (n:Nat):F n:=.lt (d0 n) (d676 n) def d678 (n:Nat):T n:=.add (d1 n) (d5 n) def d679 (n:Nat):F n:=.nlt (d0 n) (d678 n)
def d680 (n:Nat):F n:=.ne (d0 n) (d2 n) def d681 (n:Nat):F n:=.or (d183 n) (d680 n) def d682 (n:Nat):F n:=.nlt (d0 n) (d49 n) def d683 (n:Nat):F n:=.nlt (d0 n) (d55 n)
def d684 (n:Nat):F n:=.lt (d41 n) (d59 n) def d685 (n:Nat):F n:=.ne (d61 n) (d5 n) def d686 (n:Nat):F n:=.nlt (d61 n) (d5 n) def d687 (n:Nat):F n:=.and (d685 n) (d686 n)
def d688 (n:Nat):F n:=.nlt (d5 n) (d66 n) def d689 (n:Nat):F n:=.or (d687 n) (d688 n) def d690 (n:Nat):F n:=.and (d684 n) (d689 n) def d691 (n:Nat):F n:=.eq (d59 n) (d41 n)
def d692 (n:Nat):F n:=.and (d691 n) (d154 n) def d693 (n:Nat):F n:=.or (d690 n) (d692 n) def d694 (n:Nat):F n:=.nlt (d1 n) (d66 n) def d695 (n:Nat):F n:=.or (d83 n) (d694 n)
def d696 (n:Nat):F n:=.and (d684 n) (d695 n) def d697 (n:Nat):F n:=.or (d696 n) (d692 n) def d698 (n:Nat):F n:=.ne (d1 n) (d84 n) def d699 (n:Nat):F n:=.and (d76 n) (d698 n)
def d700 (n:Nat):F n:=.lt (d1 n) (d61 n) def d701 (n:Nat):F n:=.and (d700 n) (d140 n) def d702 (n:Nat):F n:=.or (d699 n) (d701 n) def d703 (n:Nat):F n:=.or (d697 n) (d702 n)
def d704 (n:Nat):F n:=.or (d119 n) (d703 n) def d705 (n:Nat):F n:=.all (d704 (n+1)) def d706 (n:Nat):F n:=.or (d693 n) (d705 n) def d707 (n:Nat):F n:=.or (d165 n) (d706 n)
def d708 (n:Nat):F n:=.all (d707 (n+1)) def d709 (n:Nat):F n:=.ne (d1 n) (d97 n) def d710 (n:Nat):F n:=.and (d76 n) (d709 n) def d711 (n:Nat):F n:=.and (d700 n) (d448 n)
def d712 (n:Nat):F n:=.or (d710 n) (d711 n) def d713 (n:Nat):F n:=.or (d697 n) (d712 n) def d714 (n:Nat):F n:=.or (d119 n) (d713 n) def d715 (n:Nat):F n:=.all (d714 (n+1))
def d716 (n:Nat):F n:=.or (d697 n) (d715 n) def d717 (n:Nat):F n:=.or (d119 n) (d716 n) def d718 (n:Nat):F n:=.all (d717 (n+1)) def d719 (n:Nat):F n:=.or (d708 n) (d718 n)
def d720 (n:Nat):F n:=.nlt (d0 n) (d269 n) def d721 (n:Nat):F n:=.ne (d251 n) (d21 n) def d722 (n:Nat):F n:=.nlt (d251 n) (d21 n) def d723 (n:Nat):F n:=.and (d721 n) (d722 n)
def d724 (n:Nat):F n:=.nlt (d21 n) (d255 n) def d725 (n:Nat):F n:=.or (d723 n) (d724 n) def d726 (n:Nat):F n:=.and (d250 n) (d725 n) def d727 (n:Nat):F n:=.or (d726 n) (d260 n)
def d728 (n:Nat):F n:=.lt (d41 n) (d20 n) def d729 (n:Nat):F n:=.nlt (d1 n) (d286 n) def d730 (n:Nat):F n:=.or (d295 n) (d729 n) def d731 (n:Nat):F n:=.and (d728 n) (d730 n)
def d732 (n:Nat):F n:=.eq (d20 n) (d41 n) def d733 (n:Nat):F n:=.and (d732 n) (d154 n) def d734 (n:Nat):F n:=.or (d731 n) (d733 n) def d735 (n:Nat):F n:=.ne (d1 n) (d296 n)
def d736 (n:Nat):F n:=.and (d285 n) (d735 n) def d737 (n:Nat):F n:=.lt (d1 n) (d282 n) def d738 (n:Nat):F n:=.and (d737 n) (d278 n) def d739 (n:Nat):F n:=.or (d736 n) (d738 n)
def d740 (n:Nat):F n:=.or (d734 n) (d739 n) def d741 (n:Nat):F n:=.or (d119 n) (d740 n) def d742 (n:Nat):F n:=.all (d741 (n+1)) def d743 (n:Nat):F n:=.or (d727 n) (d742 n)
def d744 (n:Nat):F n:=.or (d720 n) (d743 n) def d745 (n:Nat):F n:=.all (d744 (n+1)) def d746 (n:Nat):F n:=.lt (d41 n) (d52 n) def d747 (n:Nat):F n:=.ne (d309 n) (d21 n)
def d748 (n:Nat):F n:=.nlt (d309 n) (d21 n) def d749 (n:Nat):F n:=.and (d747 n) (d748 n) def d750 (n:Nat):F n:=.nlt (d21 n) (d313 n) def d751 (n:Nat):F n:=.or (d749 n) (d750 n)
def d752 (n:Nat):F n:=.and (d746 n) (d751 n) def d753 (n:Nat):F n:=.and (d374 n) (d154 n) def d754 (n:Nat):F n:=.or (d752 n) (d753 n) def d755 (n:Nat):F n:=.lt (d41 n) (d321 n)
def d756 (n:Nat):F n:=.nlt (d1 n) (d327 n) def d757 (n:Nat):F n:=.or (d336 n) (d756 n) def d758 (n:Nat):F n:=.and (d755 n) (d757 n) def d759 (n:Nat):F n:=.eq (d321 n) (d41 n)
def d760 (n:Nat):F n:=.and (d759 n) (d154 n) def d761 (n:Nat):F n:=.or (d758 n) (d760 n) def d762 (n:Nat):F n:=.ne (d1 n) (d338 n) def d763 (n:Nat):F n:=.and (d326 n) (d762 n)
def d764 (n:Nat):F n:=.lt (d1 n) (d323 n) def d765 (n:Nat):F n:=.ne (d337 n) (d41 n) def d766 (n:Nat):F n:=.and (d764 n) (d765 n) def d767 (n:Nat):F n:=.or (d763 n) (d766 n)
def d768 (n:Nat):F n:=.or (d761 n) (d767 n) def d769 (n:Nat):F n:=.or (d119 n) (d768 n) def d770 (n:Nat):F n:=.all (d769 (n+1)) def d771 (n:Nat):F n:=.or (d754 n) (d770 n)
def d772 (n:Nat):F n:=.or (d720 n) (d771 n) def d773 (n:Nat):F n:=.all (d772 (n+1)) def d774 (n:Nat):F n:=.or (d745 n) (d773 n) def d775 (n:Nat):F n:=.or (d111 n) (d774 n)
def d776 (n:Nat):F n:=.all (d775 (n+1)) def d777 (n:Nat):F n:=.ne (d251 n) (d20 n) def d778 (n:Nat):F n:=.nlt (d251 n) (d20 n) def d779 (n:Nat):F n:=.and (d777 n) (d778 n)
def d780 (n:Nat):F n:=.nlt (d20 n) (d255 n) def d781 (n:Nat):F n:=.or (d779 n) (d780 n) def d782 (n:Nat):F n:=.and (d250 n) (d781 n) def d783 (n:Nat):F n:=.or (d782 n) (d260 n)
def d784 (n:Nat):F n:=.or (d783 n) (d742 n) def d785 (n:Nat):F n:=.or (d111 n) (d784 n) def d786 (n:Nat):F n:=.all (d785 (n+1)) def d787 (n:Nat):F n:=.ne (d309 n) (d20 n)
def d788 (n:Nat):F n:=.nlt (d309 n) (d20 n) def d789 (n:Nat):F n:=.and (d787 n) (d788 n) def d790 (n:Nat):F n:=.nlt (d20 n) (d313 n) def d791 (n:Nat):F n:=.or (d789 n) (d790 n)
def d792 (n:Nat):F n:=.and (d746 n) (d791 n) def d793 (n:Nat):F n:=.or (d792 n) (d753 n) def d794 (n:Nat):F n:=.ne (d1 n) (d371 n) def d795 (n:Nat):F n:=.and (d326 n) (d794 n)
def d796 (n:Nat):F n:=.and (d764 n) (d317 n) def d797 (n:Nat):F n:=.or (d795 n) (d796 n) def d798 (n:Nat):F n:=.or (d761 n) (d797 n) def d799 (n:Nat):F n:=.or (d119 n) (d798 n)
def d800 (n:Nat):F n:=.all (d799 (n+1)) def d801 (n:Nat):F n:=.or (d793 n) (d800 n) def d802 (n:Nat):F n:=.or (d111 n) (d801 n) def d803 (n:Nat):F n:=.all (d802 (n+1))
def d804 (n:Nat):F n:=.or (d786 n) (d803 n) def d805 (n:Nat):F n:=.or (d165 n) (d804 n) def d806 (n:Nat):F n:=.all (d805 (n+1)) def d807 (n:Nat):F n:=.or (d776 n) (d806 n)
def d808 (n:Nat):F n:=.ne (d1 n) (d388 n) def d809 (n:Nat):F n:=.and (d326 n) (d808 n) def d810 (n:Nat):F n:=.ne (d387 n) (d41 n) def d811 (n:Nat):F n:=.and (d764 n) (d810 n)
def d812 (n:Nat):F n:=.or (d809 n) (d811 n) def d813 (n:Nat):F n:=.or (d761 n) (d812 n) def d814 (n:Nat):F n:=.or (d119 n) (d813 n) def d815 (n:Nat):F n:=.all (d814 (n+1))
def d816 (n:Nat):F n:=.or (d754 n) (d815 n) def d817 (n:Nat):F n:=.or (d720 n) (d816 n) def d818 (n:Nat):F n:=.all (d817 (n+1)) def d819 (n:Nat):F n:=.or (d745 n) (d818 n)
def d820 (n:Nat):F n:=.or (d111 n) (d819 n) def d821 (n:Nat):F n:=.all (d820 (n+1)) def d822 (n:Nat):F n:=.ne (d1 n) (d404 n) def d823 (n:Nat):F n:=.and (d326 n) (d822 n)
def d824 (n:Nat):F n:=.ne (d403 n) (d41 n) def d825 (n:Nat):F n:=.and (d764 n) (d824 n) def d826 (n:Nat):F n:=.or (d823 n) (d825 n) def d827 (n:Nat):F n:=.or (d761 n) (d826 n)
def d828 (n:Nat):F n:=.or (d119 n) (d827 n) def d829 (n:Nat):F n:=.all (d828 (n+1)) def d830 (n:Nat):F n:=.or (d793 n) (d829 n) def d831 (n:Nat):F n:=.or (d111 n) (d830 n)
def d832 (n:Nat):F n:=.all (d831 (n+1)) def d833 (n:Nat):F n:=.or (d786 n) (d832 n) def d834 (n:Nat):F n:=.or (d165 n) (d833 n) def d835 (n:Nat):F n:=.all (d834 (n+1))
def d836 (n:Nat):F n:=.or (d821 n) (d835 n) def d837 (n:Nat):F n:=.and (d807 n) (d836 n) def d838 (n:Nat):F n:=.and (d477 n) (d837 n) def d839 (n:Nat):F n:=.and (d427 n) (d838 n)
def d840 (n:Nat):F n:=.and (d217 n) (d839 n) def d841 (n:Nat):F n:=.ex (d840 (n+1)) def d842 (n:Nat):F n:=.nlt (d0 n) (d425 n) def d843 (n:Nat):F n:=.ne (d1 n) (d479 n)
def d844 (n:Nat):F n:=.and (d466 n) (d843 n) def d845 (n:Nat):F n:=.lt (d1 n) (d251 n) def d846 (n:Nat):F n:=.ne (d478 n) (d41 n) def d847 (n:Nat):F n:=.and (d845 n) (d846 n)
def d848 (n:Nat):F n:=.or (d844 n) (d847 n) def d849 (n:Nat):F n:=.or (d261 n) (d848 n) def d850 (n:Nat):F n:=.or (d119 n) (d849 n) def d851 (n:Nat):F n:=.all (d850 (n+1))
def d852 (n:Nat):F n:=.or (d203 n) (d851 n) def d853 (n:Nat):F n:=.or (d111 n) (d852 n) def d854 (n:Nat):F n:=.all (d853 (n+1)) def d855 (n:Nat):F n:=.ne (d1 n) (d493 n)
def d856 (n:Nat):F n:=.and (d466 n) (d855 n) def d857 (n:Nat):F n:=.ne (d492 n) (d41 n) def d858 (n:Nat):F n:=.and (d845 n) (d857 n) def d859 (n:Nat):F n:=.or (d856 n) (d858 n)
def d860 (n:Nat):F n:=.or (d261 n) (d859 n) def d861 (n:Nat):F n:=.or (d119 n) (d860 n) def d862 (n:Nat):F n:=.all (d861 (n+1)) def d863 (n:Nat):F n:=.or (d238 n) (d862 n)
def d864 (n:Nat):F n:=.or (d165 n) (d863 n) def d865 (n:Nat):F n:=.all (d864 (n+1)) def d866 (n:Nat):F n:=.or (d854 n) (d865 n) def d867 (n:Nat):F n:=.or (d268 n) (d866 n)
def d868 (n:Nat):F n:=.or (d112 n) (d867 n) def d869 (n:Nat):F n:=.or (d842 n) (d868 n) def d870 (n:Nat):F n:=.all (d869 (n+1)) def d871 (n:Nat):F n:=.or (d841 n) (d870 n)
def d872 (n:Nat):F n:=.or (d719 n) (d871 n) def d873 (n:Nat):F n:=.or (d683 n) (d872 n) def d874 (n:Nat):F n:=.all (d873 (n+1)) def d875 (n:Nat):F n:=.or (d682 n) (d874 n)
def d876 (n:Nat):F n:=.all (d875 (n+1)) def d877 (n:Nat):F n:=.and (d681 n) (d876 n) def d878 (n:Nat):F n:=.or (d877 n) (d206 n) def d879 (n:Nat):F n:=.or (d165 n) (d878 n)
def d880 (n:Nat):F n:=.all (d879 (n+1)) def d881 (n:Nat):F n:=.lt (d0 n) (d21 n) def d882 (n:Nat):T n:=.add (d492 n) (d2 n) def d883 (n:Nat):F n:=.lt (d0 n) (d882 n)
def d884 (n:Nat):T n:=.add (d478 n) (d2 n) def d885 (n:Nat):F n:=.lt (d0 n) (d884 n) def d886 (n:Nat):F n:=.eq (d115 n) (d478 n) def d887 (n:Nat):F n:=.lt (d115 n) (d478 n)
def d888 (n:Nat):F n:=.or (d886 n) (d887 n) def d889 (n:Nat):F n:=.lt (d478 n) (d179 n) def d890 (n:Nat):F n:=.and (d888 n) (d889 n) def d891 (n:Nat):F n:=.or (d175 n) (d890 n)
def d892 (n:Nat):F n:=.and (d891 n) (d184 n) def d893 (n:Nat):F n:=.and (d892 n) (d123 n) def d894 (n:Nat):F n:=.and (d885 n) (d893 n) def d895 (n:Nat):F n:=.ex (d894 (n+1))
def d896 (n:Nat):F n:=.and (d516 n) (d895 n) def d897 (n:Nat):F n:=.and (d883 n) (d896 n) def d898 (n:Nat):F n:=.ex (d897 (n+1)) def d899 (n:Nat):F n:=.lt (d5 n) (d1 n)
def d900 (n:Nat):T n:=.add (d559 n) (d5 n) def d901 (n:Nat):F n:=.eq (d0 n) (d900 n) def d902 (n:Nat):F n:=.and (d899 n) (d901 n) def d903 (n:Nat):F n:=.eq (d1 n) (d5 n)
def d904 (n:Nat):F n:=.lt (d1 n) (d5 n) def d905 (n:Nat):F n:=.or (d903 n) (d904 n) def d906 (n:Nat):T n:=.add (d15 n) (d1 n) def d907 (n:Nat):F n:=.eq (d0 n) (d906 n)
def d908 (n:Nat):F n:=.and (d905 n) (d907 n) def d909 (n:Nat):F n:=.or (d902 n) (d908 n) def d910 (n:Nat):F n:=.and (d898 n) (d909 n) def d911 (n:Nat):F n:=.and (d881 n) (d910 n)
def d912 (n:Nat):F n:=.ex (d911 (n+1)) def d913 (n:Nat):F n:=.and (d584 n) (d912 n) def d914 (n:Nat):F n:=.ex (d913 (n+1)) def d915 (n:Nat):F n:=.or (d880 n) (d914 n)
def d916 (n:Nat):F n:=.nlt (d0 n) (d20 n) def d917 (n:Nat):F n:=.nlt (d0 n) (d21 n) def d918 (n:Nat):F n:=.nlt (d0 n) (d882 n) def d919 (n:Nat):F n:=.nlt (d0 n) (d884 n)
def d920 (n:Nat):F n:=.ne (d115 n) (d478 n) def d921 (n:Nat):F n:=.nlt (d115 n) (d478 n) def d922 (n:Nat):F n:=.and (d920 n) (d921 n) def d923 (n:Nat):F n:=.nlt (d478 n) (d179 n)
def d924 (n:Nat):F n:=.or (d922 n) (d923 n) def d925 (n:Nat):F n:=.and (d195 n) (d924 n) def d926 (n:Nat):F n:=.or (d925 n) (d202 n) def d927 (n:Nat):F n:=.or (d926 n) (d159 n)
def d928 (n:Nat):F n:=.or (d919 n) (d927 n) def d929 (n:Nat):F n:=.all (d928 (n+1)) def d930 (n:Nat):F n:=.or (d877 n) (d929 n) def d931 (n:Nat):F n:=.or (d918 n) (d930 n)
def d932 (n:Nat):F n:=.all (d931 (n+1)) def d933 (n:Nat):F n:=.nlt (d5 n) (d1 n) def d934 (n:Nat):F n:=.ne (d0 n) (d900 n) def d935 (n:Nat):F n:=.or (d933 n) (d934 n)
def d936 (n:Nat):F n:=.ne (d1 n) (d5 n) def d937 (n:Nat):F n:=.nlt (d1 n) (d5 n) def d938 (n:Nat):F n:=.and (d936 n) (d937 n) def d939 (n:Nat):F n:=.ne (d0 n) (d906 n)
def d940 (n:Nat):F n:=.or (d938 n) (d939 n) def d941 (n:Nat):F n:=.and (d935 n) (d940 n) def d942 (n:Nat):F n:=.or (d932 n) (d941 n) def d943 (n:Nat):F n:=.or (d917 n) (d942 n)
def d944 (n:Nat):F n:=.all (d943 (n+1)) def d945 (n:Nat):F n:=.or (d916 n) (d944 n) def d946 (n:Nat):F n:=.all (d945 (n+1)) def d947 (n:Nat):F n:=.or (d946 n) (d519 n)
def d948 (n:Nat):F n:=.and (d915 n) (d947 n) def d949 (n:Nat):F n:=.or (d679 n) (d948 n) def d950 (n:Nat):F n:=.all (d949 (n+1)) def d951 (n:Nat):F n:=.nlt (d0 n) (d1 n)
def d952 (n:Nat):T n:=.add (d5 n) (d1 n) def d953 (n:Nat):T n:=.add (d952 n) (d2 n) def d954 (n:Nat):T n:=.mul (d2 n) (d953 n) def d955 (n:Nat):T n:=.mul (d954 n) (d953 n)
def d956 (n:Nat):T n:=.add (d955 n) (d2 n) def d957 (n:Nat):F n:=.lt (d0 n) (d956 n) def d958 (n:Nat):F n:=.and (d909 n) (d898 n) def d959 (n:Nat):F n:=.and (d957 n) (d958 n)
def d960 (n:Nat):F n:=.ex (d959 (n+1)) def d961 (n:Nat):T n:=.add (d20 n) (d1 n) def d962 (n:Nat):T n:=.add (d961 n) (d2 n) def d963 (n:Nat):T n:=.mul (d2 n) (d962 n)
def d964 (n:Nat):T n:=.mul (d963 n) (d962 n) def d965 (n:Nat):T n:=.add (d964 n) (d2 n) def d966 (n:Nat):F n:=.nlt (d0 n) (d965 n) def d967 (n:Nat):F n:=.nlt (d20 n) (d1 n)
def d968 (n:Nat):T n:=.add (d559 n) (d20 n) def d969 (n:Nat):F n:=.ne (d0 n) (d968 n) def d970 (n:Nat):F n:=.or (d967 n) (d969 n) def d971 (n:Nat):F n:=.ne (d1 n) (d20 n)
def d972 (n:Nat):F n:=.nlt (d1 n) (d20 n) def d973 (n:Nat):F n:=.and (d971 n) (d972 n) def d974 (n:Nat):T n:=.add (d31 n) (d1 n) def d975 (n:Nat):F n:=.ne (d0 n) (d974 n)
def d976 (n:Nat):F n:=.or (d973 n) (d975 n) def d977 (n:Nat):F n:=.and (d970 n) (d976 n) def d978 (n:Nat):F n:=.nlt (d0 n) (d644 n) def d979 (n:Nat):F n:=.ne (d115 n) (d643 n)
def d980 (n:Nat):F n:=.nlt (d115 n) (d643 n) def d981 (n:Nat):F n:=.and (d979 n) (d980 n) def d982 (n:Nat):F n:=.nlt (d643 n) (d179 n) def d983 (n:Nat):F n:=.or (d981 n) (d982 n)
def d984 (n:Nat):F n:=.and (d195 n) (d983 n) def d985 (n:Nat):F n:=.or (d984 n) (d202 n) def d986 (n:Nat):F n:=.or (d985 n) (d159 n) def d987 (n:Nat):F n:=.or (d978 n) (d986 n)
def d988 (n:Nat):F n:=.all (d987 (n+1)) def d989 (n:Nat):F n:=.or (d877 n) (d988 n) def d990 (n:Nat):F n:=.or (d919 n) (d989 n) def d991 (n:Nat):F n:=.all (d990 (n+1))
def d992 (n:Nat):F n:=.or (d977 n) (d991 n) def d993 (n:Nat):F n:=.or (d966 n) (d992 n) def d994 (n:Nat):F n:=.all (d993 (n+1)) def d995 (n:Nat):F n:=.eq (d0 n) (d1 n)
def d996 (n:Nat):F n:=.or (d994 n) (d995 n) def d997 (n:Nat):F n:=.or (d917 n) (d996 n) def d998 (n:Nat):F n:=.all (d997 (n+1)) def d999 (n:Nat):F n:=.and (d960 n) (d998 n)
def d1000 (n:Nat):F n:=.and (d584 n) (d999 n) def d1001 (n:Nat):F n:=.ex (d1000 (n+1)) def d1002 (n:Nat):F n:=.or (d880 n) (d1001 n) def d1003 (n:Nat):F n:=.or (d951 n) (d1002 n)
def d1004 (n:Nat):F n:=.all (d1003 (n+1)) def d1005 (n:Nat):F n:=.and (d950 n) (d1004 n) def d1006 (n:Nat):F n:=.and (d677 n) (d1005 n) def d1007 (n:Nat):F n:=.ex (d1006 (n+1))
def d1008 (n:Nat):F n:=.eq (d65 n) (d2 n) def d1009 (n:Nat):F n:=.and (d42 n) (d1008 n) def d1010 (n:Nat):T n:=.mul (d2 n) (d3 n) def d1011 (n:Nat):T n:=.mul (d1010 n) (d3 n)
def d1012 (n:Nat):T n:=.mul (d1011 n) (d3 n) def d1013 (n:Nat):T n:=.mul (d1012 n) (d3 n) def d1014 (n:Nat):T n:=.add (d1013 n) (d2 n) def d1015 (n:Nat):F n:=.lt (d0 n) (d1014 n)
def d1016 (n:Nat):T n:=.mul (d2 n) (d39 n) def d1017 (n:Nat):T n:=.mul (d1016 n) (d39 n) def d1018 (n:Nat):T n:=.mul (d1017 n) (d39 n) def d1019 (n:Nat):T n:=.mul (d1018 n) (d39 n)
def d1020 (n:Nat):T n:=.add (d1019 n) (d2 n) def d1021 (n:Nat):F n:=.lt (d0 n) (d1020 n) def d1022 (n:Nat):T n:=.add (d110 n) (d2 n) def d1023 (n:Nat):F n:=.nlt (d0 n) (d1022 n)
def d1024 (n:Nat):F n:=.or (d1023 n) (d422 n) def d1025 (n:Nat):F n:=.all (d1024 (n+1)) def d1026 (n:Nat):T n:=.mul (d2 n) (d110 n) def d1027 (n:Nat):T n:=.mul (d1026 n) (d110 n)
def d1028 (n:Nat):T n:=.add (d1027 n) (d2 n) def d1029 (n:Nat):F n:=.lt (d0 n) (d1028 n) def d1030 (n:Nat):T n:=.add (d251 n) (d882 n) def d1031 (n:Nat):F n:=.eq (d1 n) (d1030 n)
def d1032 (n:Nat):F n:=.or (d254 n) (d1031 n) def d1033 (n:Nat):F n:=.eq (d882 n) (d41 n) def d1034 (n:Nat):F n:=.or (d482 n) (d1033 n) def d1035 (n:Nat):F n:=.and (d1032 n) (d1034 n)
def d1036 (n:Nat):F n:=.and (d470 n) (d1035 n) def d1037 (n:Nat):F n:=.and (d4 n) (d1036 n) def d1038 (n:Nat):F n:=.ex (d1037 (n+1)) def d1039 (n:Nat):F n:=.and (d185 n) (d1038 n)
def d1040 (n:Nat):F n:=.and (d40 n) (d1039 n) def d1041 (n:Nat):F n:=.ex (d1040 (n+1)) def d1042 (n:Nat):F n:=.and (d491 n) (d1041 n) def d1043 (n:Nat):F n:=.and (d477 n) (d1042 n)
def d1044 (n:Nat):F n:=.and (d427 n) (d1043 n) def d1045 (n:Nat):F n:=.and (d1029 n) (d1044 n) def d1046 (n:Nat):F n:=.ex (d1045 (n+1)) def d1047 (n:Nat):F n:=.and (d1025 n) (d1046 n)
def d1048 (n:Nat):F n:=.and (d109 n) (d1047 n) def d1049 (n:Nat):F n:=.and (d1021 n) (d1048 n) def d1050 (n:Nat):F n:=.ex (d1049 (n+1)) def d1051 (n:Nat):F n:=.and (d1015 n) (d1050 n)
def d1052 (n:Nat):F n:=.ex (d1051 (n+1)) def d1053 (n:Nat):F n:=.or (d1009 n) (d1052 n)
def pair3 : F 4 := d38 4
def member : F 2 := d519 2
def edge : F 3 := d539 3
def core : F 2 := d675 2
def mapping : F 1 := d1007 1
def domain : F 2 := d950 2
def under : F 2 := d1053 2
end PalomarPA.PrimitiveData
namespace PalomarPA
/-- Capture-avoiding instantiation of an explicitly supplied closed schema. -/
def substClosed (p : Formula Empty k) (v : Fin k → Term Empty n) : Formula Empty n :=
 p.rewrite v Empty.elim

def fixSuccTemplate (member coreSigma corePi : Formula Empty 2) : Formula Empty 3 :=
 let x : Term Empty 4 := .bvar (boundIndex 0)
 let u : Term Empty 4 := .bvar (boundIndex 1)
 let ih : Term Empty 4 := .bvar (boundIndex 2)
 let s : Term Empty 4 := .bvar (boundIndex 3)
 let mem := substClosed member (fun j => if j.val=0 then x else u)
 let cs := substClosed coreSigma (fun j => if j.val=0 then x else ih)
 let cp := substClosed corePi (fun j => if j.val=0 then x else ih)
 let le := Formula.or (.eq x s) (.lt x s)
 .all (.or (.nlt x (.add u (.add s .one)))
   (.and (.or mem.neg (.and le cs)) (.or (Formula.and le cp).neg mem)))

def fixZeroTemplate : Formula Empty 1 := .eq (.bvar (boundIndex 0)) .zero

def fixPointTemplate (member result : Formula Empty 2) : Formula Empty 1 :=
 .ex (.ex (.and
  (substClosed result (fun j => if j.val=0 then .bvar (boundIndex 0) else .bvar (boundIndex 1)))
  (substClosed member (fun j => if j.val=0 then .bvar (boundIndex 2) else .bvar (boundIndex 0)))))

def nthTemplate (pair3 : Formula Empty 4) (graph : Formula Empty 1) : Formula Empty 3 :=
 .ex (.and
  (substClosed pair3 (fun j => .bvar (boundIndex (match j.val with | 0 => 0 | 1 => 2 | 2 => 3 | _ => 1))))
  (substClosed graph (fun _ => .bvar (boundIndex 0))))
end PalomarPA
namespace PalomarPA
/-- Closed-schema application, with explicit argument order. -/
def prSub1 (p : Formula Empty 1) (a : Term Empty n) := substClosed p (fun _ => a)
def prSub2 (p : Formula Empty 2) (a b : Term Empty n) :=
 substClosed p (fun j => if j.val=0 then a else b)
def prSub3 (p : Formula Empty 3) (a b c : Term Empty n) :=
 substClosed p (fun j => if j.val=0 then a else if j.val=1 then b else c)
/-- PR sequence template for arity zero. `edge i s z` denotes the sequence edge.
All low-level HFS definitions are supplied formulas, not hidden predicates. -/
def prCSeqTemplate (zero seq : Formula Empty 1) (succ edge : Formula Empty 3)
 (length : Formula Empty 2) : Formula Empty 1 :=
 let two : Term Empty 2 := .add .one .one
 let initial : Formula Empty 1 := .ex (.and (.lt (.bvar (boundIndex 0)) (.bvar (boundIndex 1)))
  (.and (prSub1 zero (.bvar (boundIndex 0))) (prSub3 edge .zero (.bvar (boundIndex 1)) (.bvar (boundIndex 0)))))
 let guard : Formula Empty 2 := .ex (.and
  (.lt (.bvar (boundIndex 0)) (.add (.mul (.add .one .one) (.bvar (boundIndex 2))) .one))
  (.and (prSub2 length (.bvar (boundIndex 0)) (.bvar (boundIndex 2))) (.lt (.add (.bvar (boundIndex 1)) .one) (.bvar (boundIndex 0)))))
 let next : Formula Empty 3 := .ex (.and (.lt (.bvar (boundIndex 0)) (.bvar (boundIndex 3)))
  (.and (prSub3 succ (.bvar (boundIndex 0)) (.bvar (boundIndex 1)) (.bvar (boundIndex 2)))
   (prSub3 edge (.add (.bvar (boundIndex 2)) .one) (.bvar (boundIndex 3)) (.bvar (boundIndex 0)))))
 let recursion : Formula Empty 2 := .all (.or (.nlt (.bvar (boundIndex 0)) (.bvar (boundIndex 2)))
  (.or (prSub3 edge (.bvar (boundIndex 1)) (.bvar (boundIndex 2)) (.bvar (boundIndex 0))).neg next))
 .and (prSub1 seq (.bvar (boundIndex 0))) (.and initial
  (.all (.or (.nlt (.bvar (boundIndex 0)) (.mul two (.bvar (boundIndex 1)))) (.or guard.neg recursion))))
def prResultTemplate (cseq : Formula Empty 1) (edge : Formula Empty 3) : Formula Empty 2 :=
 .ex (.and (prSub1 cseq (.bvar (boundIndex 0))) (prSub3 edge (.bvar (boundIndex 2)) (.bvar (boundIndex 0)) (.bvar (boundIndex 1))))
end PalomarPA
namespace PalomarPA
/-- HFS mapping schema. Edge arguments are (relation,input,output). -/
def mappingTemplate (domain member : Formula Empty 2) (edge : Formula Empty 3) : Formula Empty 1 :=
 let unique : Formula Empty 4 := .all (.or (.nlt (.bvar (boundIndex 0)) (.bvar (boundIndex 4)))
  (.or (prSub3 edge (.bvar (boundIndex 4)) (.bvar (boundIndex 2)) (.bvar (boundIndex 0))).neg (.eq (.bvar (boundIndex 0)) (.bvar (boundIndex 1)))))
 let value : Formula Empty 3 := .ex (.and (.lt (.bvar (boundIndex 0)) (.bvar (boundIndex 3)))
  (.and (prSub3 edge (.bvar (boundIndex 3)) (.bvar (boundIndex 1)) (.bvar (boundIndex 0))) unique))
 let total : Formula Empty 2 := .all (.or (.nlt (.bvar (boundIndex 0)) (.bvar (boundIndex 1)))
  (.or (prSub2 member (.bvar (boundIndex 0)) (.bvar (boundIndex 1))).neg value))
 .ex (.and (.lt (.bvar (boundIndex 0)) (.add (.mul (.add .one .one) (.bvar (boundIndex 1))) .one))
  (.and (prSub2 domain (.bvar (boundIndex 0)) (.bvar (boundIndex 1))) total))
end PalomarPA
namespace PalomarPA
/-- Explicit bounded sequence predicate, parameterized by its lower-level graphs. -/
def seqTemplate (mapping : Formula Empty 1) (domain under : Formula Empty 2) : Formula Empty 1 :=
 .and (prSub1 mapping (.bvar (boundIndex 0)))
 (.ex (.and (.lt (.bvar (boundIndex 0)) (.add (.mul (.add .one .one) (.bvar (boundIndex 1))) .one))
  (.ex (.and (.lt (.bvar (boundIndex 0)) (.add (.mul (.add .one .one) (.bvar (boundIndex 2))) .one))
   (.and (prSub2 domain (.bvar (boundIndex 0)) (.bvar (boundIndex 2))) (prSub2 under (.bvar (boundIndex 0)) (.bvar (boundIndex 1))))))))
/-- Explicit length graph; invalid sequence inputs return zero. -/
def seqLengthTemplate (seq : Formula Empty 1) (domain under : Formula Empty 2) : Formula Empty 2 :=
 let valid := prSub1 seq (.bvar (boundIndex 1))
 .and (.or valid.neg
  (.ex (.and (.lt (.bvar (boundIndex 0)) (.add (.mul (.add .one .one) (.bvar (boundIndex 2))) .one))
   (.and (prSub2 domain (.bvar (boundIndex 0)) (.bvar (boundIndex 2))) (prSub2 under (.bvar (boundIndex 0)) (.bvar (boundIndex 1)))))))
  (.or valid.neg.neg (.eq (.bvar (boundIndex 0)) .zero))
end PalomarPA
namespace PalomarPA.ConstructedNth
/-- Every parameter of the generic HFS templates is instantiated by explicit
arithmetic syntax. No semantic predicate or opaque axiom is introduced. -/
def mapping : Formula Empty 1 := mappingTemplate PrimitiveData.domain PrimitiveData.member PrimitiveData.edge
def seq : Formula Empty 1 := seqTemplate mapping PrimitiveData.domain PrimitiveData.under
def length : Formula Empty 2 := seqLengthTemplate seq PrimitiveData.domain PrimitiveData.under
/-- PR edge arguments are (index,sequence,value), unlike memRel's
(sequence,index,value). The swap is explicit. -/
def edge : Formula Empty 3 := prSub3 PrimitiveData.edge (.bvar (boundIndex 1)) (.bvar (boundIndex 0)) (.bvar (boundIndex 2))
def succ : Formula Empty 3 := fixSuccTemplate PrimitiveData.member PrimitiveData.core PrimitiveData.core
def cseq : Formula Empty 1 := prCSeqTemplate fixZeroTemplate seq succ edge length
def result : Formula Empty 2 := prResultTemplate cseq edge
def graph : Formula Empty 1 := fixPointTemplate PrimitiveData.member result
def formula : Formula Empty 3 := nthTemplate PrimitiveData.pair3 graph
end PalomarPA.ConstructedNth
namespace PalomarPA
/-- Explicit Foundation-free HFS indexing formula, assembled from arithmetic
constructor data and fully instantiated syntax templates. -/
def nthFormula : Formula Empty 3 := ConstructedNth.formula
end PalomarPA
namespace PalomarPA

def Term.numeral : Nat → Term ξ n
  | 0 => .zero | 1 => .one | k+2 => .add (numeral (k+1)) .one

def rowFormula (src read write next : Nat) (right : Bool) : Formula Empty 6 :=
  let rightBody : Formula Empty 7 :=
    .and (.eq (.bvar (boundIndex 3)) (.add (.mul (.add .one .one) (.bvar (boundIndex 0))) (.numeral read))) <|
    .and (.eq (.bvar (boundIndex 5)) (.add (.mul (.add .one .one) (.bvar (boundIndex 2))) (.numeral write))) <|
    .eq (.bvar (boundIndex 6)) (.bvar (boundIndex 0))
  let leftBody : Formula Empty 9 :=
    .and (.or (.eq (.bvar (boundIndex 0)) .zero) (.eq (.bvar (boundIndex 0)) .one)) <|
    .and (.eq (.bvar (boundIndex 4)) (.add (.mul (.add .one .one) (.bvar (boundIndex 1))) (.bvar (boundIndex 0)))) <|
    .and (.eq (.bvar (boundIndex 5)) (.add (.mul (.add .one .one) (.bvar (boundIndex 2))) (.numeral read))) <|
    .and (.eq (.bvar (boundIndex 7)) (.bvar (boundIndex 1))) <|
    .eq (.bvar (boundIndex 8)) (.add (.mul (.add .one .one)
      (.add (.mul (.add .one .one) (.bvar (boundIndex 2))) (.numeral write))) (.bvar (boundIndex 0)))
  .and (.eq (.bvar (boundIndex 0)) (.numeral src)) <|
  .and (.eq (.bvar (boundIndex 3)) (.numeral next)) <|
  if right then .ex rightBody else .ex (.ex (.ex leftBody))

/-- Application of the explicit sequence-accessor formula to its three terms. -/
def nthAt (v s i : Term Empty n) : Formula Empty n :=
  nthFormula.rewrite (fun j => if j.val=0 then v else if j.val=1 then s else i) Empty.elim

/-- Exact four-sequence-witness, six-register-step halting sentence schema. -/
def traceFormula (step : Formula Empty 6) : Sentence :=
  let body : Formula Empty 11 :=
    .and (nthAt (.bvar (boundIndex 5)) (.bvar (boundIndex 9)) (.bvar (boundIndex 6))) <|
    .and (nthAt (.bvar (boundIndex 4)) (.bvar (boundIndex 8)) (.bvar (boundIndex 6))) <|
    .and (nthAt (.bvar (boundIndex 3)) (.bvar (boundIndex 7)) (.bvar (boundIndex 6))) <|
    .and (nthAt (.bvar (boundIndex 2)) (.bvar (boundIndex 9)) (.add (.bvar (boundIndex 6)) .one)) <|
    .and (nthAt (.bvar (boundIndex 1)) (.bvar (boundIndex 8)) (.add (.bvar (boundIndex 6)) .one)) <|
    .and (nthAt (.bvar (boundIndex 0)) (.bvar (boundIndex 7)) (.add (.bvar (boundIndex 6)) .one)) <|
    step.rewrite (fun j => .bvar (boundIndex (5-j.val))) Empty.elim
  let timeBody : Formula Empty 5 :=
    .or (.nlt (.bvar (boundIndex 0)) (.bvar (boundIndex 4))) (.ex (.ex (.ex (.ex (.ex (.ex body))))))
  let startBody : Formula Empty 4 :=
    .and (nthAt .zero (.bvar (boundIndex 2)) .zero) <|
    .and (nthAt .zero (.bvar (boundIndex 1)) .zero) <|
    .and (nthAt .zero (.bvar (boundIndex 0)) .zero) <|
    .and (nthAt (.numeral 215) (.bvar (boundIndex 2)) (.bvar (boundIndex 3))) (.all timeBody)
  .ex (.ex (.ex (.ex startBody)))
end PalomarPA
namespace PalomarPA
set_option maxRecDepth 100000
abbrev RowSpec := Nat × Nat × Nat × Nat × Bool
/-- All418 active rows of the exact append-one M6 arithmetic machine. -/
def m6Rows : List RowSpec := [
(0,0,1,1,true),(0,1,1,64,true),(1,0,1,91,true),(1,1,1,1,true),
(2,0,0,2,false),(2,1,1,3,false),(3,0,0,4,false),(3,1,1,3,false),
(4,0,0,6,false),(4,1,1,3,false),(5,0,1,7,true),(5,1,0,5,false),
(6,0,0,10,false),(6,1,1,3,false),(7,0,0,7,true),(7,1,0,11,true),
(8,0,0,83,true),(8,1,1,186,true),(9,0,0,15,true),(9,1,1,14,true),
(10,0,0,16,false),(10,1,1,3,false),(11,0,0,17,false),(11,1,0,11,true),
(12,0,0,27,false),(12,1,1,19,true),(13,0,0,20,true),(13,1,1,21,true),
(14,0,0,88,false),(14,1,1,32,false),(15,0,0,12,false),(15,1,0,23,true),
(16,0,0,24,false),(16,1,1,3,false),(17,0,1,2,false),(17,1,0,2,false),
(18,0,0,25,true),(18,1,0,33,true),(19,0,0,93,true),(19,1,0,104,false),
(20,0,0,29,true),(20,1,1,30,true),(21,0,0,31,true),(21,1,1,32,true),
(22,0,0,25,true),(22,1,0,60,true),(23,0,0,34,true),(23,1,1,23,true),
(24,0,0,35,false),(24,1,1,3,false),(25,0,0,36,false),(25,1,0,1,true),
(26,0,0,37,true),(26,1,1,26,true),(27,0,0,177,true),(27,1,1,42,true),
(28,0,0,39,true),(28,1,0,40,false),(29,0,0,41,true),(29,1,1,42,true),
(30,0,0,43,true),(30,1,1,44,true),(31,0,0,45,true),(31,1,1,46,true),
(32,0,0,22,true),(32,1,1,47,true),(33,0,0,48,true),(33,1,1,33,true),
(34,0,0,33,true),(34,1,1,34,true),(35,0,0,74,false),(35,1,1,3,false),
(36,0,1,36,true),(36,1,1,2,false),(37,0,0,51,true),(37,1,1,37,true),
(38,0,0,29,true),(38,1,1,21,true),(39,0,0,12,false),(39,1,0,37,true),
(40,0,0,5,false),(40,1,1,54,false),(41,0,0,25,true),(41,1,0,26,true),
(42,0,0,14,true),(42,1,0,17,false),(43,0,0,56,true),(43,1,1,57,true),
(44,0,0,58,true),(44,1,1,59,true),(45,0,0,25,true),(45,1,0,55,true),
(46,0,0,61,true),(46,1,1,62,true),(47,0,0,63,true),(47,1,0,17,false),
(48,0,0,26,true),(48,1,1,48,true),(49,0,0,36,false),(49,1,0,64,true),
(51,0,0,17,true),(51,1,1,51,true),(52,0,0,145,true),(52,1,1,141,true),
(53,0,0,68,true),(53,1,1,69,true),(54,0,0,40,false),(54,1,1,54,false),
(55,0,0,23,true),(55,1,1,55,true),(56,0,0,12,false),(56,1,0,51,true),
(57,0,0,61,true),(57,1,0,17,false),(58,0,0,70,true),(58,1,1,71,true),
(59,0,0,62,true),(59,1,1,72,true),(60,0,0,55,true),(60,1,1,60,true),
(61,0,0,49,true),(61,1,0,26,true),(62,0,0,29,false),(62,1,1,73,false),
(63,0,0,116,false),(63,1,1,31,false),(64,0,0,0,true),(64,1,1,64,true),
(65,0,0,96,true),(65,1,1,147,true),(66,0,1,180,true),(66,1,1,54,false),
(67,0,0,142,true),(67,1,1,143,true),(68,0,0,76,true),(68,1,1,215,true),
(69,0,0,192,false),(69,1,1,32,true),(70,0,0,41,true),(70,1,1,63,true),
(71,0,0,88,false),(71,1,1,77,true),(72,0,0,56,true),(72,1,1,78,false),
(73,0,0,79,true),(73,1,1,80,true),(74,0,0,74,true),(74,1,1,81,true),
(75,0,0,143,false),(75,1,1,139,false),(76,0,0,84,true),(76,1,1,85,true),
(77,0,0,88,true),(77,1,1,131,false),(78,0,0,107,false),(78,1,1,57,true),
(79,0,0,49,true),(79,1,0,34,true),(80,0,0,90,true),(80,1,0,42,false),
(81,0,0,53,true),(81,1,1,211,true),(82,0,0,95,true),(82,1,1,13,true),
(83,0,0,87,true),(83,1,1,96,true),(84,0,0,202,true),(84,1,1,22,true),
(85,0,0,115,true),(85,1,1,99,true),(86,0,0,147,true),(86,1,1,112,true),
(87,0,0,101,true),(87,1,1,102,true),(88,0,0,79,true),(88,1,1,78,true),
(89,0,0,100,true),(89,1,1,170,true),(90,0,0,104,true),(90,1,1,105,true),
(91,0,0,66,true),(91,1,0,1,true),(92,0,0,28,true),(92,1,1,106,true),
(93,0,0,98,true),(93,1,1,97,true),(94,0,1,109,false),(94,1,1,94,false),
(95,0,0,20,true),(95,1,1,110,true),(96,0,0,61,true),(96,1,1,61,true),
(97,0,0,163,true),(97,1,1,153,true),(98,0,0,27,false),(98,1,1,111,true),
(99,0,0,104,true),(99,1,0,203,false),(100,0,0,116,true),(100,1,1,117,true),
(101,0,0,72,true),(101,1,1,59,true),(102,0,0,58,true),(102,1,1,118,true),
(103,0,0,22,true),(103,1,1,119,true),(104,0,0,22,true),(104,1,0,11,false),
(105,0,0,62,true),(105,1,1,42,true),(106,0,0,120,true),(106,1,1,9,true),
(107,0,0,100,true),(107,1,1,121,true),(108,0,0,87,true),(108,1,1,169,true),
(109,0,0,203,false),(109,1,0,94,false),(110,0,0,123,true),(110,1,1,103,true),
(111,0,0,75,true),(111,1,1,114,true),(112,0,0,108,true),(112,1,1,177,true),
(113,0,0,146,true),(113,1,1,144,true),(114,0,0,137,true),(114,1,1,134,true),
(115,0,0,130,false),(115,1,0,2,false),(116,0,0,39,true),(116,1,1,73,true),
(117,0,0,62,true),(117,1,1,131,true),(118,0,0,62,true),(118,1,1,132,true),
(119,0,0,71,true),(119,1,0,17,false),(120,0,0,15,true),(120,1,1,131,true),
(121,0,0,22,true),(121,1,1,133,true),(123,0,0,135,true),(123,1,1,21,false),
(124,0,0,129,true),(124,1,1,176,true),(125,0,0,159,true),(125,1,1,200,true),
(126,0,0,75,true),(126,1,1,172,true),(127,0,0,128,true),(127,1,0,203,false),
(128,0,0,125,true),(128,1,1,136,true),(129,0,0,13,true),(129,1,1,139,true),
(130,0,0,31,true),(130,1,1,70,true),(131,0,0,39,true),(131,1,1,123,false),
(132,0,0,175,true),(132,1,0,17,false),(133,0,0,151,true),(133,1,0,17,false),
(134,0,0,148,true),(134,1,1,127,true),(135,0,0,25,true),(135,1,0,48,true),
(136,0,0,146,true),(136,1,1,152,true),(137,0,0,153,true),(137,1,1,156,true),
(138,0,0,95,true),(138,1,1,155,true),(139,0,0,171,true),(139,1,1,162,true),
(140,0,0,13,true),(140,1,1,155,true),(141,0,0,87,true),(141,1,1,162,false),
(142,0,0,87,true),(142,1,1,154,true),(143,0,0,149,false),(143,1,1,159,false),
(144,0,0,83,true),(144,1,1,87,true),(145,0,0,155,true),(145,1,1,13,true),
(146,0,0,82,true),(146,1,1,141,true),(147,0,0,67,false),(147,1,1,139,false),
(148,0,0,188,true),(148,1,1,165,true),(149,0,0,155,true),(149,1,1,113,true),
(151,0,0,49,true),(151,1,0,33,true),(152,0,0,174,true),(152,1,1,206,true),
(153,0,0,212,false),(153,1,1,95,true),(154,0,0,164,true),(154,1,1,175,true),
(155,0,0,20,true),(155,1,1,166,true),(156,0,0,191,true),(156,1,1,183,true),
(158,0,0,124,true),(158,1,1,160,true),(159,0,0,96,true),(159,1,1,158,true),
(160,0,0,8,false),(160,1,1,140,true),(161,0,0,147,true),(161,1,1,169,true),
(162,0,0,144,true),(162,1,1,168,true),(163,0,0,192,true),(163,1,1,29,true),
(164,0,0,153,true),(164,1,1,141,true),(165,0,0,67,true),(165,1,1,144,true),
(166,0,0,177,true),(166,1,1,121,true),(167,0,0,143,true),(167,1,1,161,true),
(168,0,0,75,true),(168,1,1,61,true),(169,0,0,143,true),(169,1,1,87,true),
(170,0,0,103,true),(170,1,1,95,true),(171,0,0,138,true),(171,1,1,83,true),
(172,0,0,171,true),(172,1,1,75,true),(173,0,0,92,true),(173,1,1,107,true),
(174,0,0,149,true),(174,1,1,184,true),(175,0,0,96,true),(175,1,1,209,false),
(176,0,0,164,true),(176,1,1,52,true),(177,0,0,18,true),(177,1,1,130,false),
(178,0,0,76,true),(178,1,1,115,true),(179,0,0,105,true),(179,1,1,123,true),
(180,0,1,40,false),(180,1,1,109,false),(181,0,0,167,true),(181,1,1,13,true),
(182,0,0,185,true),(182,1,1,190,true),(183,0,0,138,true),(183,1,1,194,true),
(184,0,0,195,true),(184,1,1,210,true),(185,0,0,197,true),(185,1,1,198,true),
(186,0,0,153,true),(186,1,1,187,true),(187,0,0,75,true),(187,1,1,181,true),
(188,0,0,65,true),(188,1,1,8,true),(189,0,0,147,true),(189,1,1,126,true),
(190,0,0,86,true),(190,1,1,199,true),(191,0,0,69,true),(191,1,1,201,true),
(192,0,0,89,true),(192,1,1,87,true),(193,0,0,173,true),(193,1,1,213,true),
(194,0,0,160,true),(194,1,1,204,true),(195,0,0,145,true),(195,1,1,146,true),
(196,0,0,179,true),(196,1,1,178,true),(197,0,0,155,true),(197,1,1,208,true),
(198,0,0,209,true),(198,1,1,108,true),(199,0,0,178,true),(199,1,1,196,true),
(200,0,0,189,true),(200,1,1,167,true),(201,0,0,87,true),(201,1,1,192,true),
(202,0,0,45,true),(202,1,1,99,true),(203,0,0,5,false),(203,1,0,203,false),
(204,0,0,141,true),(204,1,1,142,true),(206,0,0,207,true),(206,1,1,182,true),
(207,0,0,141,true),(207,1,1,52,true),(208,0,0,108,true),(208,1,1,108,true),
(209,0,0,83,true),(209,1,1,210,true),(210,0,0,155,true),(210,1,1,52,true),
(211,0,0,193,true),(211,1,1,62,true),(212,0,0,152,false),(212,1,1,178,true),
(213,0,0,12,true),(213,1,1,38,true)
]
def rowOfSpec (r : RowSpec) : Formula Empty 6 := rowFormula r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2
def disjoinRows : List RowSpec → Formula Empty 6
  | [] => .bot | r::rs => .or (rowOfSpec r) (disjoinRows rs)
def m6Step : Formula Empty 6 := disjoinRows m6Rows
def m6Halting : Sentence := traceFormula m6Step
def m6Nonhalting : Sentence := m6Halting.neg
theorem m6Rows_count : m6Rows.length=418 := by decide
end PalomarPA
namespace PalomarPA
/-- Ordinary PA proves neither exact-M6 nonhalting nor positive halting. -/
theorem m6_two_sided_independence :
 (¬ Provable PATheory m6Nonhalting) ∧ (¬ Provable PATheory m6Halting) := by
 sorry
end PalomarPA

namespace PalomarPA

/-- Look up the transition for a state and the bit under the head. -/
def machineRow (q : Nat) (b : Bool) : Option (Bool × Bool × Nat) :=
  m6Rows.findSome? fun (src, read, write, next, right) =>
    if src = q ∧ read = b.toNat then some (write != 0, right, next) else none

/-- A configuration stores the state and the two sides of the tape, nearest
cell first. The right list starts at the head. Missing cells contain zero. -/
structure TapeConfig where
  state : Nat
  left : List Bool
  right : List Bool

/-- Remove the redundant zeros at the far end of a tape side. -/
def trimTape : List Bool → List Bool
  | [] => []
  | b :: rest => if b = false ∧ trimTape rest = [] then [] else b :: trimTape rest

/-- Read and write at the head, then move one cell. A missing row ends the run. -/
def machineStep (c : TapeConfig) : Option TapeConfig :=
  match machineRow c.state (c.right.headD false) with
  | none => none
  | some (w, true, q) => some ⟨q, trimTape (w :: c.left), trimTape c.right.tail⟩
  | some (w, false, q) =>
    some ⟨q, trimTape c.left.tail, trimTape (c.left.headD false :: w :: c.right.tail)⟩

/-- Execute exactly the indicated number of steps, if they exist. -/
def machineRun : Nat → TapeConfig → Option TapeConfig
  | 0, c => some c
  | n + 1, c => (machineStep c).bind (machineRun n)

/-- The blank tape, with the machine in state zero. -/
def blank : TapeConfig := ⟨0, [], []⟩


/-- No finite run from state zero on a blank tape reaches a terminal configuration. -/
theorem m6_machine_nonhalting : ¬ ∃ n c, machineRun n blank = some c ∧ machineStep c = none := by
  sorry

end PalomarPA
