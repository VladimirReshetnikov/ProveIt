/- Lean 4.32.0. This standalone fragment uses only Init. Its only induction
   rule for object proofs is induction on a single equation. -/
import Init

namespace FiniteWords

/-- `n` is the induction variable; `a` and `b` are numerical parameters. -/
inductive T where
  | n | a | b | zero | one
  | succ : T → T
  | add : T → T → T
  | mul : T → T → T
  | pow : T → T → T
  | words : T → T → T → T
  deriving Repr, DecidableEq


def sub (u : T) : T → T
  | .n => u
  | .a => .a
  | .b => .b
  | .zero => .zero
  | .one => .one
  | .succ x => .succ (sub u x)
  | .add x y => .add (sub u x) (sub u y)
  | .mul x y => .mul (sub u x) (sub u y)
  | .pow x y => .pow (sub u x) (sub u y)
  | .words x y k => .words (sub u x) (sub u y) (sub u k)

/-- Equational derivations with a single possible induction hypothesis.
    The distributive law is an admitted *derived rule* of this fragment:
    it is an existing iPRA semiring lemma. All other arithmetic rules below
    are defining equations or equality rules. -/
inductive Der : Option (T × T) → T → T → Prop where
  | hyp {x y} : H = some (x,y) → Der H x y
  | refl (x) : Der H x x
  | sym {x y} : Der H x y → Der H y x
  | trans {x y z} : Der H x y → Der H y z → Der H x z
  | mulCong {x y u v} : Der H x y → Der H u v → Der H (.mul x u) (.mul y v)
  | distrib (x y z) : Der H (.mul z (.add x y)) (.add (.mul z x) (.mul z y))
  | pzero (x) : Der H (.pow x .zero) .one
  | pstep (x k) : Der H (.pow x (.succ k)) (.mul (.pow x k) x)
  | wzero (x y) : Der H (.words x y .zero) .one
  | wstep (x y k) : Der H (.words x y (.succ k))
      (.add (.mul (.words x y k) x) (.mul (.words x y k) y))
  | inductionEq {x y : T} : Der none (sub .zero x) (sub .zero y) →
      Der (some (x,y)) (sub (.succ .n) x) (sub (.succ .n) y) → Der H x y

def lhs : T := .words .a .b .n
def rhs : T := .pow (.add .a .b) .n

/-- A uniform proof object. It does not inspect or bound the numerical inputs. -/
theorem wordCertificate : Der none lhs rhs := by
  apply Der.inductionEq
  · exact .trans (.wzero _ _) (.sym (.pzero _))
  · exact .trans (.wstep _ _ _) (.trans (.sym (.distrib _ _ _))
      (.trans (.mulCong (.hyp rfl) (.refl _)) (.sym (.pstep _ _))))

/-- Choose a last letter from either of the two disjoint labelled alphabets. -/
def wordCount (A B : Nat) : Nat → Nat
  | 0 => 1
  | k+1 => wordCount A B k * A + wordCount A B k * B

def val (k A B : Nat) : T → Nat
  | .n => k
  | .a => A
  | .b => B
  | .zero => 0
  | .one => 1
  | .succ x => val k A B x + 1
  | .add x y => val k A B x + val k A B y
  | .mul x y => val k A B x * val k A B y
  | .pow x y => val k A B x ^ val k A B y
  | .words x y z => wordCount (val k A B x) (val k A B y) (val k A B z)

theorem sub_val (u x : T) (k A B : Nat) :
    val k A B (sub u x) = val (val k A B u) A B x := by
  induction x <;> simp_all [sub, val]

def Holds (H : Option (T × T)) (k A B : Nat) : Prop :=
  match H with
  | none => True
  | some (l,r) => val k A B l = val k A B r

/-- Semantic audit of every rule, independent of the external ProveIt library. -/
theorem sound {H x y} (d : Der H x y) :
    ∀ k A B, Holds H k A B → val k A B x = val k A B y := by
  induction d with
  | hyp h => intro k A B hH; subst_vars; exact hH
  | refl => intros; rfl
  | sym _ ih => intro k A B h; exact (ih k A B h).symm
  | trans _ _ h₁ h₂ => intro k A B h; exact (h₁ k A B h).trans (h₂ k A B h)
  | mulCong _ _ h₁ h₂ => intro k A B h; simp only [val, h₁ k A B h, h₂ k A B h]
  | distrib => intros; exact Nat.mul_add _ _ _
  | pzero => intros; rfl
  | pstep => intros; rfl
  | wzero => intros; rfl
  | wstep => intros; rfl
  | inductionEq _ _ base step =>
    intro k A B hH
    clear hH
    induction k with
    | zero => simpa only [sub_val, val] using base 0 A B trivial
    | succ k ih => simpa only [sub_val, val] using step k A B ih

theorem countAll (k A B : Nat) : wordCount A B k = (A + B)^k :=
  sound wordCertificate k A B trivial

#print axioms wordCertificate
#print axioms countAll

end FiniteWords
