module
public import PACore
public import Mathlib.Tactic.FinCases
public import Foundation.FirstOrder.Syntax.Classical.Rew
@[expose] public section
namespace PalomarPA
open FFL FFL.FirstOrder

def Term.toFoundation : Term ξ n → Semiterm ℒₒᵣ ξ n
  | .bvar i => .bvar i
  | .fvar x => .fvar x
  | .zero => .func .zero Fin.elim0
  | .one => .func .one Fin.elim0
  | .add t u => .func .add ![t.toFoundation,u.toFoundation]
  | .mul t u => .func .mul ![t.toFoundation,u.toFoundation]

def Term.fromFoundation : Semiterm ℒₒᵣ ξ n → Term ξ n
  | .bvar i => .bvar i
  | .fvar x => .fvar x
  | .func .zero _ => .zero
  | .func .one _ => .one
  | .func .add ts => .add (fromFoundation (ts 0)) (fromFoundation (ts 1))
  | .func .mul ts => .mul (fromFoundation (ts 0)) (fromFoundation (ts 1))

@[simp] theorem Term.from_to (t : Term ξ n) : fromFoundation t.toFoundation = t := by
  induction t <;> simp_all [toFoundation,fromFoundation]

@[simp] theorem Term.to_from (t : Semiterm ℒₒᵣ ξ n) :
    (fromFoundation t).toFoundation = t := by
  induction t with
  | bvar => rfl
  | fvar => rfl
  | @func arity f ts ih =>
    cases f <;> simp only [fromFoundation,toFoundation]
    all_goals congr 1; funext i
    all_goals fin_cases i <;> simp [ih]

def Formula.toFoundation : Formula ξ n → Semiformula ℒₒᵣ ξ n
  | .top => .verum | .bot => .falsum
  | .eq t u => .rel .eq ![t.toFoundation,u.toFoundation]
  | .ne t u => .nrel .eq ![t.toFoundation,u.toFoundation]
  | .lt t u => .rel .lt ![t.toFoundation,u.toFoundation]
  | .nlt t u => .nrel .lt ![t.toFoundation,u.toFoundation]
  | .and p q => .and p.toFoundation q.toFoundation
  | .or p q => .or p.toFoundation q.toFoundation
  | .all p => .all p.toFoundation | .ex p => .exs p.toFoundation

def Formula.fromFoundation : Semiformula ℒₒᵣ ξ n → Formula ξ n
  | .verum => .top | .falsum => .bot
  | .rel .eq ts => .eq (Term.fromFoundation (ts 0)) (Term.fromFoundation (ts 1))
  | .nrel .eq ts => .ne (Term.fromFoundation (ts 0)) (Term.fromFoundation (ts 1))
  | .rel .lt ts => .lt (Term.fromFoundation (ts 0)) (Term.fromFoundation (ts 1))
  | .nrel .lt ts => .nlt (Term.fromFoundation (ts 0)) (Term.fromFoundation (ts 1))
  | .and p q => .and (fromFoundation p) (fromFoundation q)
  | .or p q => .or (fromFoundation p) (fromFoundation q)
  | .all p => .all (fromFoundation p) | .exs p => .ex (fromFoundation p)

@[simp] theorem Formula.from_to (p : Formula ξ n) : fromFoundation p.toFoundation = p := by
  induction p <;> simp_all [toFoundation,fromFoundation]

@[simp] theorem Formula.to_from (p : Semiformula ℒₒᵣ ξ n) :
    (fromFoundation p).toFoundation = p := by
  induction p with
  | verum => rfl
  | falsum => rfl
  | @rel n k r ts =>
    cases r <;> simp only [fromFoundation,toFoundation]
    all_goals congr 1; funext i; fin_cases i <;> simp
  | @nrel n k r ts =>
    cases r <;> simp only [fromFoundation,toFoundation]
    all_goals congr 1; funext i; fin_cases i <;> simp
  | and p q ihp ihq => simp [fromFoundation,toFoundation,ihp,ihq]
  | or p q ihp ihq => simp [fromFoundation,toFoundation,ihp,ihq]
  | all p ih => simp [fromFoundation,toFoundation,ih]
  | exs p ih => simp [fromFoundation,toFoundation,ih]

@[simp] theorem Formula.to_neg (p : Formula ξ n) :
    p.neg.toFoundation = Semiformula.neg p.toFoundation := by
  induction p <;> simp_all [Formula.neg,toFoundation,Semiformula.neg]

@[simp] theorem Term.to_rename (t : Term ξ n) (b : Fin n → Fin m) (f : ξ → η) :
    (t.rename b f).toFoundation = Rew.map b f t.toFoundation := by
  induction t <;> simp_all [rename,toFoundation]
  all_goals funext i; exact Fin.elim0 i

@[simp] theorem Term.to_rewrite (t : Term ξ n)
    (b : Fin n → Term η m) (f : ξ → Term η m) :
    (t.rewrite b f).toFoundation =
      Rew.bind (fun i => (b i).toFoundation) (fun x => (f x).toFoundation) t.toFoundation := by
  induction t <;> simp_all [rewrite,toFoundation]
  all_goals funext i; exact Fin.elim0 i

private theorem bind_lift (b : Fin n → Term η m) (f : ξ → Term η m) :
    Rew.bind (fun i => (liftBound b i).toFoundation)
      (fun x => ((f x).rename Fin.succ id).toFoundation) =
      (Rew.bind (fun i => (b i).toFoundation) (fun x => (f x).toFoundation)).q := by
  apply Rew.ext
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [liftBound,Term.toFoundation]
    · simp [liftBound,Rew.bShift]
  · intro x
    simp [Rew.bShift]

@[simp] theorem Formula.to_rewrite (p : Formula ξ n)
    (b : Fin n → Term η m) (f : ξ → Term η m) :
    (p.rewrite b f).toFoundation =
      Semiformula.rewAux
        (Rew.bind (fun i => (b i).toFoundation) (fun x => (f x).toFoundation)) p.toFoundation := by
  induction p generalizing m with
  | top => rfl
  | bot => rfl
  | eq t u | ne t u | lt t u | nlt t u =>
    simp only [rewrite,toFoundation,Semiformula.rewAux,Term.to_rewrite]
    congr 1; funext i; fin_cases i <;> rfl
  | and p q ihp ihq =>
    change Semiformula.and _ _ = Semiformula.and _ _
    congr 1 <;> apply_assumption
  | or p q ihp ihq =>
    change Semiformula.or _ _ = Semiformula.or _ _
    congr 1 <;> apply_assumption
  | all p ih =>
    change Semiformula.all _ = Semiformula.all _
    congr 1
    rw [ih,bind_lift]
  | ex p ih =>
    change Semiformula.exs _ = Semiformula.exs _
    congr 1
    rw [ih,bind_lift]

#print axioms Formula.to_rewrite
#print axioms Formula.to_from
#print axioms Formula.from_to
end PalomarPA
