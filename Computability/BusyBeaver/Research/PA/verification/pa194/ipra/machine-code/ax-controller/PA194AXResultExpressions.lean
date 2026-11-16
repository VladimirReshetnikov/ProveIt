import PA194AXSymbolic

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194AXResultExpressions
open M6.Source.AXSymbolic

def one : Expr := .succ .zero
def all (a b : Expr) : Expr := .succ (.succ (.im b a))
def neg (a : Expr) : Expr := .im a one
def ex (a b : Expr) : Expr := neg (all a (neg b))
def mem (a b : Expr) : Expr := .succ (.im a b)
def equal (a b : Expr) : Expr := .succ (.succ (.succ (.im a b)))
def both (p q : Expr) : Expr := neg (.im p (neg q))
def membership (a b c : Expr) : Expr :=
  .im (mem a b) (all c (mem a b))
def point (b c : Expr) : Expr := .im c (mem c b)
def separate (a b c : Expr) : Expr :=
  all b (both (.im (mem a b) (point b c)) (.im (mem c b) c))
def separationTail (a b c : Expr) : Expr :=
  all c (.im (separate a b c) (neg (point b c)))
def bundle (a b c : Expr) : Expr := neg (.im (membership a b c) (separationTail a b c))

def heads (d a h d₀ h₀ t : Expr) : List Expr := [
  .im a (all a a),
  .im (all d a) (.im (all d (.im a h)) (all d h)),
  ex d (equal h d),
  .im (equal h d) (.im (mem a h) (mem a d)),
  .im (mem h d) (.im (equal h a) (mem a d)),
  .im (all d (all a h)) (all a (all d h)),
  .im (ex d (all d h)) h,
  .im (.im (.im h d₀) d) (.im (.im d h) (.im a h)),
  all d₀ h₀,
  t]

def result : Store :=
  let t := Expr.atom 0
  let a := Expr.atom 1
  let d₀ := Expr.atom 2
  let h₀ := Expr.atom 3
  let d := Expr.add d₀ (.atom 5)
  let h := Expr.add h₀ (.atom 4)
  ⟨bundle h d a, a, d, h, [], heads d a h d₀ h₀ t⟩

theorem expectedResult : PA194AXSymbolic.result = result := by decide +kernel

#print axioms expectedResult
end PA194AXResultExpressions
