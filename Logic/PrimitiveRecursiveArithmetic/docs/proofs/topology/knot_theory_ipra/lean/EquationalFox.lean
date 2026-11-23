import Std

/- A small deep embedding of an additive equational fragment of iPRA.
   The positivity/naturality sort is the object sort, not Lean Nat.
   Universal closure of the finitely many free variables is understood.
   The inductions below are object inferences on a single equation. -/
namespace EquationalFox

inductive T where
  | v (i : Nat)
  | z
  | s (a : T)
  | add (a b : T)
  deriving DecidableEq

def sub (σ : Nat → T) : T → T
  | .v i => σ i
  | .z => .z
  | .s x => .s (sub σ x)
  | .add x y => .add (sub σ x) (sub σ y)

def put0 (a : T) : Nat → T
  | 0 => a
  | k+1 => .v (k+1)

inductive D : List (T × T) → T → T → Prop where
  | hyp {Γ a b} : (a,b) ∈ Γ → D Γ a b
  | refl {Γ} (a) : D Γ a a
  | symm {Γ a b} : D Γ a b → D Γ b a
  | trans {Γ a b c} : D Γ a b → D Γ b c → D Γ a c
  | succCong {Γ a b} : D Γ a b → D Γ (.s a) (.s b)
  | plusCong {Γ a b c d} : D Γ a b → D Γ c d → D Γ (.add a c) (.add b d)
  | zeroR {Γ} (a) : D Γ (.add a .z) a
  | succR {Γ} (a b) : D Γ (.add a (.s b)) (.s (.add a b))
  | useClosed {Γ a b} (h : D [] a b) (σ : Nat → T) :
      D Γ (sub σ a) (sub σ b)
  | inductionEq (a b : T)
      (base : D [] (sub (put0 .z) a) (sub (put0 .z) b))
      (step : D [(a,b)] (sub (put0 (.s (.v 0))) a) (sub (put0 (.s (.v 0))) b)) :
      D [] a b

private abbrev i := T.v 0
private abbrev j := T.v 1
private abbrev k := T.v 2

theorem zeroLschema : D [] (.add .z i) i := by
  apply D.inductionEq
  · exact .zeroR _
  · exact .trans (.succR _ _) (.succCong (.hyp (by simp [sub, i])))

theorem succLschema : D [] (.add (.s j) i) (.s (.add j i)) := by
  apply D.inductionEq
  · exact .trans (.zeroR _) (.symm (.succCong (.zeroR _)))
  · exact .trans (.succR _ _) (.trans (.succCong (.hyp (by simp [sub, put0, i, j])))
      (.symm (.succCong (.succR _ _))))

theorem succLeft {Γ} (a b : T) : D Γ (.add (.s a) b) (.s (.add a b)) :=
  .useClosed succLschema (fun n => if n == 0 then b else a)

theorem commSchema : D [] (.add j i) (.add i j) := by
  apply D.inductionEq
  · exact .trans (.zeroR _) (.symm (.useClosed zeroLschema (fun _ => j)))
  · exact .trans (.succR _ _) (.trans (.succCong (.hyp (by simp [sub, put0, i, j])))
      (.symm (succLeft _ _)))

theorem assocSchema : D [] (.add (.add k j) i) (.add k (.add j i)) := by
  apply D.inductionEq
  · exact .trans (.zeroR _) (.symm (.plusCong (.refl _) (.zeroR _)))
  · exact .trans (.succR _ _) (.trans (.succCong (.hyp (by simp [sub, put0, i, j, k])))
      (.trans (.symm (.succR _ _)) (.symm (.plusCong (.refl _) (.succR _ _)))))

private def rel : Setoid T where
  r := D []
  iseqv := ⟨D.refl, D.symm, D.trans⟩

private abbrev Q := Quotient rel
private def mk (a : T) : Q := Quotient.mk rel a

private instance : Add Q where
  add a b := Quotient.liftOn₂ a b (fun x y => mk (.add x y))
    (fun _ _ _ _ hx hy => Quotient.sound (D.plusCong hx hy))

private theorem mkAdd (a b : T) : mk (.add a b) = mk a + mk b := rfl

private instance : Std.Associative (α := Q) (· + ·) where
  assoc a b c := Quotient.inductionOn₃ a b c fun x y w =>
    Quotient.sound (D.useClosed assocSchema
      (fun n => if n == 0 then w else if n == 1 then y else x))

private instance : Std.Commutative (α := Q) (· + ·) where
  comm a b := Quotient.inductionOn₂ a b fun x y =>
    Quotient.sound (D.useClosed commSchema (fun n => if n == 0 then y else x))

structure Z where
  p : T
  n : T

def fox (x y : Z) : Z :=
  ⟨.add (.add y.p y.p) x.n, .add (.add y.n y.n) x.p⟩

def ZEq (x y : Z) : Prop := D [] (.add x.p y.n) (.add y.p x.n)

private theorem finish {a b : T} (h : mk a = mk b) : D [] a b :=
  Quotient.exact h

theorem foxIdempotent (x : Z) : ZEq (fox x x) x := by
  unfold ZEq fox
  apply finish
  simp only [mkAdd]
  ac_rfl

theorem foxInvolutive (x y : Z) : ZEq (fox (fox x y) y) x := by
  unfold ZEq fox
  apply finish
  simp only [mkAdd]
  ac_rfl

theorem foxTriangle (x y z : Z) :
    ZEq (fox (fox x y) z) (fox (fox x z) (fox y z)) := by
  unfold ZEq fox
  apply finish
  simp only [mkAdd]
  ac_rfl

#print axioms foxTriangle

end EquationalFox
