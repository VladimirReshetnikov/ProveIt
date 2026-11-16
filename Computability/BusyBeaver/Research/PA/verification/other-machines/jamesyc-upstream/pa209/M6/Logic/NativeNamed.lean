module
public import M6.Logic.NativeCalculus
@[expose] public section

/-! Literal named-formula syntax from NumericSyntax238.v at the same pinned
upstream. This extraction retains only the pure named syntax, encoding and semantics;
the Foundation interpretation and PA proof schemas are deliberately omitted. Code1 encodes self-membership, not logical falsity. -/
namespace M6.PA.NativeCalculus

inductive Named where
  | truth
  | imp (antecedent consequent : Named)
  | neg (body : Named)
  | mem (container member : Nat)
  | eq (left right : Nat)
  | all (name : Nat) (body : Named)
  deriving DecidableEq

def Named.encode : Named → Nat
  | .truth => 0
  | .imp p q => wim p.encode q.encode
  | .neg p => wn p.encode
  | .mem a b => wel a b
  | .eq a b => weq a b
  | .all a p => wal a p.encode

/-- Named semantics: quantifiers update exactly their bound label. -/
def Named.eval {V : Type u} (R E : V → V → Prop) : Named → (Nat → V) → Prop
  | .truth, _ => True
  | .imp p q, env => p.eval R E env → q.eval R E env
  | .neg p, env => ¬ p.eval R E env
  | .mem a b, env => R (env a) (env b)
  | .eq a b, env => E (env a) (env b)
  | .all a p, env => ∀ x, p.eval R E (fun v => if v = a then x else env v)

def namedRho2 (a : Nat) (p q : Named) : Named :=
  .imp (.all a (.imp p q)) (.imp (.all a p) (.all a q))

theorem namedRho2_encode (a : Nat) (p q : Named) :
    (namedRho2 a p q).encode = rho2 a p.encode q.encode := rfl

end M6.PA.NativeCalculus
