import DiophantineConsistency.ArithmeticFiniteSwitch

open DiophantineConsistency ScalarPRCode DirectScalar ArithmeticFiniteSwitch
private def bodies (k : Nat) : R (fun n => k+n) := add (constant k) identity
private def selected := program (fun k n => k+n) bodies 3
example (n : Nat) : selected.val.eval n=value 3 (fun k n => k+n) n := selected.property n
#eval selected.val.eval (Nat.pair 0 4)==4
#eval selected.val.eval (Nat.pair 2 4)==6
#eval selected.val.eval (Nat.pair 3 4)==0
#eval selected.val.eval (Nat.pair 9 4)==0
#print axioms value
#print axioms program
