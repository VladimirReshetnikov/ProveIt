import DiophantineConsistency.ArithmeticRepresentation
import DiophantineConsistency.ReifyPRCode

/-! Computational regression checks for explicit syntax, witness indexing,
primitive recursion, and supported proof transports. -/

open DiophantineConsistency

set_option maxRecDepth 65536

private def three : GraphRep (σ := Fin 0) (fun _ => 3) := GraphRep.constant 3
private def four : GraphRep (σ := Fin 0) (fun _ => 4) := GraphRep.constant 4

example : (GraphRep.add three four).expression.eval
    (natAssignment (fun _ => 7) (fun i => if i.val = 0 then 3 else 4)) = 0 := by decide

example : (GraphRep.mul three four).expression.eval
    (natAssignment (fun _ => 12) (fun i => if i.val = 0 then 3 else 4)) = 0 := by decide

example : (ArithmeticRep.modEq (0 : Fin 3) 1 2).expression.eval
    (natAssignment (fun i => if i.val = 0 then 5 else if i.val = 1 then 2 else 3)
      (fun i => if i.val = 0 then 0 else 1)) = 0 := by decide

example : (ArithmeticRep.modEq (0 : Fin 3) 1 2).expression.eval
    (natAssignment (fun i => if i.val = 2 then 0 else 5) (fun _ => 0)) = 0 := by decide

private def successor : PRCode.Realizes (fun v : List.Vector ℕ 1 => v.head.succ) :=
  prcode% Nat.Primrec'.succ

private def constantThree : PRCode.Realizes (fun _ : List.Vector ℕ 2 => 3) :=
  prcode% (Nat.Primrec'.const (n := 2) 3)

private def headCode : PRCode.Realizes (fun v : List.Vector ℕ 1 => v.head) :=
  prcode% (Nat.Primrec'.head (n := 0))

private def countFrom :=
  prcode% (Nat.Primrec'.prec (Nat.Primrec'.get (0 : Fin 1))
    (Nat.Primrec'.comp (fun _ : Fin 1 => fun v : List.Vector ℕ 3 => v.get 1)
      Nat.Primrec'.succ (fun _ => Nat.Primrec'.get 1)))

private def multiplication : PRCode.Realizes
    (fun v : List.Vector ℕ 2 => v.head * v.tail.head) :=
  prcode% Nat.Primrec'.mul

example : successor.val.eval (List.Vector.ofFn (fun _ => 4)) = 5 := by decide
example : constantThree.val.eval (List.Vector.ofFn (fun _ => 100)) = 3 := by decide
example : headCode.val.eval (List.Vector.ofFn (fun _ => 42)) = 42 := by decide
example : countFrom.val.eval
    (List.Vector.ofFn (fun i => if i.val = 0 then 4 else 7)) = 11 := by decide
example : multiplication.val.eval
    (List.Vector.ofFn (fun i => if i.val = 0 then 6 else 7)) = 42 := by decide

-- The extractor deliberately rejects arbitrary proof parameters.
example {f : List.Vector ℕ 1 → ℕ} (_h : Nat.Primrec' f) : True := by
  fail_if_success let _ := prcode% _h
  trivial

private def swapPair := scalar_prcode% (Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left)

example (x y : ℕ) : swapPair.val.eval (Nat.pair x y) = Nat.pair y x := by
  simpa using swapPair.property (Nat.pair x y)

private def incrementLeft := scalar_prcode% (Nat.Primrec.comp Nat.Primrec.succ Nat.Primrec.left)

example : incrementLeft.val = .comp .succ .left := rfl

example (x y : ℕ) : incrementLeft.val.eval (Nat.pair x y) = x.succ := by
  simpa using incrementLeft.property (Nat.pair x y)

example {f : ℕ → ℕ} (_h : Nat.Primrec f) : True := by
  fail_if_success let _ := scalar_prcode% _h
  trivial
