import PresburgerArithmetic.Syntax

namespace PresburgerArithmetic

abbrev Clause := List Atom
abbrev DNF := List Clause

namespace Atom

def negate : Atom → Atom
  | .le t => .le ((t.neg.add (.const (-1))))
  | .dvd d hd t => .ndvd d hd t
  | .ndvd d hd t => .dvd d hd t

@[simp] theorem eval_negate (a : Atom) (xs : List Int) :
    a.negate.eval xs = !a.eval xs := by
  cases a with
  | le t =>
      by_cases h : 0 ≤ t.eval xs
      · simp [negate, eval, h]
        omega
      · simp [negate, eval, h]
        omega
  | dvd d hd t => simp [negate, eval]
  | ndvd d hd t => simp [negate, eval]

end Atom

namespace DNF

def cross (p q : DNF) : DNF :=
  p.flatMap fun c => q.map fun d => c ++ d

def ofPolarity : Bool → QF → DNF
  | true, .truth => [[]]
  | false, .truth => []
  | true, .falsity => []
  | false, .falsity => [[]]
  | true, .atom a => [[a]]
  | false, .atom a => [[a.negate]]
  | true, .and p q => cross (ofPolarity true p) (ofPolarity true q)
  | false, .and p q => ofPolarity false p ++ ofPolarity false q
  | true, .or p q => ofPolarity true p ++ ofPolarity true q
  | false, .or p q => cross (ofPolarity false p) (ofPolarity false q)
  | b, .not p => ofPolarity (!b) p

def evalClause (c : Clause) (xs : List Int) : Bool :=
  c.all fun a => a.eval xs

def eval (p : DNF) (xs : List Int) : Bool :=
  p.any fun c => evalClause c xs

@[simp] theorem evalClause_append (c d : Clause) (xs : List Int) :
    evalClause (c ++ d) xs = (evalClause c xs && evalClause d xs) := by
  simp [evalClause, List.all_append]

theorem eval_cross (p q : DNF) (xs : List Int) :
    eval (cross p q) xs = (eval p xs && eval q xs) := by
  have eval_map_append (c : Clause) :
      (q.map fun d => c ++ d).any (fun d => evalClause d xs) =
        (evalClause c xs && eval q xs) := by
    induction q with
    | nil => simp [eval]
    | cons d ds ih =>
        simp only [List.map_cons, List.any_cons, evalClause_append, ih, eval]
        cases evalClause c xs <;> cases evalClause d xs <;> simp
  induction p with
  | nil => simp [cross, eval]
  | cons c cs ih =>
      change eval ((q.map fun d => c ++ d) ++ cross cs q) xs = _
      simp only [eval, List.any_append]
      change ((q.map fun d => c ++ d).any (fun d => evalClause d xs) ||
        eval (cross cs q) xs) = _
      rw [ih]
      rw [eval_map_append]
      change (evalClause c xs && eval q xs || eval cs xs && eval q xs) =
        ((evalClause c xs || eval cs xs) && eval q xs)
      cases evalClause c xs <;> cases eval cs xs <;> cases eval q xs <;> rfl

@[simp] theorem eval_append (p q : DNF) (xs : List Int) :
    eval (p ++ q) xs = (eval p xs || eval q xs) := by
  simp [eval, List.any_append]

theorem eval_ofPolarity (b : Bool) (p : QF) (xs : List Int) :
    eval (ofPolarity b p) xs = if b then p.eval xs else !p.eval xs := by
  induction p generalizing b with
  | truth => cases b <;> rfl
  | falsity => cases b <;> rfl
  | atom a => cases b <;> simp [ofPolarity, eval, evalClause, Atom.eval_negate, QF.eval]
  | and p q ihp ihq =>
      cases b <;> simp [ofPolarity, eval_cross, ihp, ihq, QF.eval]
  | or p q ihp ihq =>
      cases b <;> simp [ofPolarity, eval_cross, ihp, ihq, QF.eval]
  | not p ih =>
      cases b <;> simp [ofPolarity, ih, QF.eval]

def toQF (p : DNF) : QF :=
  .disjunction (p.map QF.conjunction)

@[simp] theorem eval_toQF (p : DNF) (xs : List Int) :
    (toQF p).eval xs = eval p xs := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
      change ((QF.conjunction c).eval xs || (toQF cs).eval xs) = _
      rw [ih]
      simp [eval, evalClause]

end DNF

end PresburgerArithmetic
