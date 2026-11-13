module
public import Std
@[expose] public section
/-! Foundation-free arithmetic syntax, intended to be inlined into the final
Challenge. This component by itself makes no PA-independence claim. -/
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
