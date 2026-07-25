import PAFiniteBasisReduction.FiniteBetaCoding

/-!
# A fixed first-order evaluator for standard Skolem programs

This file is the syntactic half of the arithmetized evaluator used by the
proper-cut construction.  Program nodes are decoded by the polynomial pairing
from `FiniteSkolemCut`; Skolem nodes dispatch over the already checked finite
enumeration of rank-bounded formulas.  In particular, the evaluator never
interprets a Goedel code for PA syntax.

The beta code is a table indexed by standard polynomial program codes.  A row
contains the value of that program.  Child rows are read through the fixed
term-parametric beta relation from `PAHF.PASyntax`.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

universe u v

namespace FiniteSkolemCut
namespace ProgramTrace

/-! ## Polynomial decoding terms -/

/-- Object-language counterpart of `Program.pairCode`. -/
def pairTerm (a b : PA.Term) : PA.Term :=
  PA.Term.add (PA.Term.mul (PA.Term.add a b) (PA.Term.add a b)) a

/-- Object-language counterpart of the positive node code. -/
def nodeTerm (a b : PA.Term) : PA.Term :=
  PA.Term.succ (pairTerm a b)

/-- Object-language counterpart of `Program.listCode`. -/
def listTerm : List PA.Term → PA.Term
  | [] => PA.Term.zero
  | x :: xs => nodeTerm x (listTerm xs)

@[simp] theorem eval_pairTerm {alpha : Type u} (M : PA.PreModel alpha)
    (e : Nat → alpha) (a b : PA.Term) :
    PA.Term.eval M e (pairTerm a b) =
      M.add
        (M.mul
          (M.add (PA.Term.eval M e a) (PA.Term.eval M e b))
          (M.add (PA.Term.eval M e a) (PA.Term.eval M e b)))
        (PA.Term.eval M e a) := by
  rfl

@[simp] theorem eval_nodeTerm {alpha : Type u} (M : PA.PreModel alpha)
    (e : Nat → alpha) (a b : PA.Term) :
    PA.Term.eval M e (nodeTerm a b) =
      M.succ
        (M.add
          (M.mul
            (M.add (PA.Term.eval M e a) (PA.Term.eval M e b))
            (M.add (PA.Term.eval M e a) (PA.Term.eval M e b)))
          (PA.Term.eval M e a)) := by
  rfl

/-! ## Finite logical folds and simultaneous witness blocks -/

/-- Right-associated finite conjunction; the empty conjunction is `0 = 0`. -/
def conjunction : List PA.Formula → PA.Formula
  | [] => PA.Formula.eq PA.Term.zero PA.Term.zero
  | phi :: rest => PA.Formula.and phi (conjunction rest)

/-- Right-associated finite disjunction; the empty disjunction is false. -/
def disjunction : List PA.Formula → PA.Formula
  | [] => PA.Formula.bot
  | phi :: rest => PA.Formula.or phi (disjunction rest)

/-- Prefix a formula by a standard finite block of existential binders. -/
def existsN : Nat → PA.Formula → PA.Formula
  | 0, phi => phi
  | n + 1, phi => PA.Formula.ex (existsN n phi)

/-- Environment obtained after installing `n` simultaneous witness slots.
Slot zero is the innermost witness. -/
def slotEnv {alpha : Type u} (n : Nat) (slots : Fin n → alpha)
    (e : Nat → alpha) : Nat → alpha :=
  fun i => if hi : i < n then slots ⟨i, hi⟩ else e (i - n)

@[simp] theorem slotEnv_of_lt {alpha : Type u} {n i : Nat}
    (slots : Fin n → alpha) (e : Nat → alpha) (hi : i < n) :
    slotEnv n slots e i = slots ⟨i, hi⟩ := by
  simp [slotEnv, hi]

@[simp] theorem slotEnv_of_not_lt {alpha : Type u} {n i : Nat}
    (slots : Fin n → alpha) (e : Nat → alpha) (hi : ¬i < n) :
    slotEnv n slots e i = e (i - n) := by
  simp [slotEnv, hi]

/-- Supply a simultaneous block of existential witnesses by specifying the
final de Bruijn slots. -/
theorem sat_existsN_of_slots {alpha : Type u} (M : PA.PreModel alpha)
    (n : Nat) (phi : PA.Formula) (slots : Fin n → alpha)
    (e : Nat → alpha)
    (h : PA.Formula.Sat M (slotEnv n slots e) phi) :
    PA.Formula.Sat M e (existsN n phi) := by
  induction n generalizing e with
  | zero =>
      have henv : slotEnv 0 slots e = e := by
        funext i
        simp [slotEnv]
      rw [henv] at h
      simpa [existsN] using h
  | succ n ih =>
      simp only [existsN, PA.Formula.Sat]
      let last : alpha := slots ⟨n, Nat.lt_succ_self n⟩
      let initial : Fin n → alpha := fun i =>
        slots ⟨i, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩
      refine ⟨last, ih (e := scons last e) initial ?_⟩
      have henv : slotEnv n initial (scons last e) =
          slotEnv (n + 1) slots e := by
        funext i
        by_cases hi : i < n
        · have hi' : i < n + 1 := by omega
          rw [slotEnv_of_lt initial (scons last e) hi]
          rw [slotEnv_of_lt slots e hi']
        · by_cases hin : i = n
          · subst i
            have hn' : n < n + 1 := Nat.lt_succ_self n
            rw [slotEnv_of_not_lt initial (scons last e) hi]
            rw [slotEnv_of_lt slots e hn']
            simp [last, scons]
          · have hni : n < i := by omega
            have hnot : ¬i < n + 1 := by omega
            rw [slotEnv_of_not_lt initial (scons last e) hi]
            rw [slotEnv_of_not_lt slots e hnot]
            have heq : i - n = (i - (n + 1)) + 1 := by omega
            rw [heq]
            rfl
      rw [henv]
      simpa only [Nat.succ_eq_add_one] using h

@[simp] theorem sat_conjunction {alpha : Type u} (M : PA.PreModel alpha)
    (e : Nat → alpha) (fs : List PA.Formula) :
    PA.Formula.Sat M e (conjunction fs) ↔
      ∀ phi ∈ fs, PA.Formula.Sat M e phi := by
  induction fs with
  | nil => simp [conjunction, PA.Formula.Sat]
  | cons phi fs ih => simp [conjunction, PA.Formula.Sat, ih]

@[simp] theorem sat_disjunction {alpha : Type u} (M : PA.PreModel alpha)
    (e : Nat → alpha) (fs : List PA.Formula) :
    PA.Formula.Sat M e (disjunction fs) ↔
      ∃ phi ∈ fs, PA.Formula.Sat M e phi := by
  induction fs with
  | nil => simp [disjunction, PA.Formula.Sat]
  | cons phi fs ih => simp [disjunction, PA.Formula.Sat, ih]

/-! ## Fixed child slots -/

/-- Shift an ambient term across a block of `n` fresh witnesses. -/
def liftTerm (n : Nat) (t : PA.Term) : PA.Term :=
  PA.Term.rename (fun i => i + n) t

@[simp] theorem eval_liftTerm_slotEnv {alpha : Type u}
    (M : PA.PreModel alpha) (n : Nat) (slots : Fin n → alpha)
    (e : Nat → alpha) (t : PA.Term) :
    PA.Term.eval M (slotEnv n slots e) (liftTerm n t) =
      PA.Term.eval M e t := by
  rw [liftTerm, PA.Term.eval_rename]
  apply PA.Term.eval_ext M t
  intro i
  have hnot : ¬ i + n < n := by omega
  rw [slotEnv_of_not_lt slots e hnot]
  congr
  omega

/-- In a Skolem branch, slot `2*i` is the value of child `i`. -/
def argumentValueTerm (i : Nat) : PA.Term := PA.Term.var (2 * i)

/-- In a Skolem branch, slot `2*i+1` is the code of child `i`. -/
def argumentCodeTerm (i : Nat) : PA.Term := PA.Term.var (2 * i + 1)

/-- Interleave child values and child codes in the witness block. -/
def argumentSlots {alpha : Type u} {rank : Nat}
    (values codes : Fin rank → alpha) : Fin (2 * rank) → alpha :=
  fun j =>
    let i : Fin rank := ⟨j.val / 2, by omega⟩
    if j.val % 2 = 0 then values i else codes i

@[simp] theorem argumentSlots_value {alpha : Type u} {rank : Nat}
    (values codes : Fin rank → alpha) (i : Fin rank) :
    argumentSlots values codes ⟨2 * i.val, by omega⟩ = values i := by
  simp [argumentSlots]

@[simp] theorem argumentSlots_code {alpha : Type u} {rank : Nat}
    (values codes : Fin rank → alpha) (i : Fin rank) :
    argumentSlots values codes ⟨2 * i.val + 1, by omega⟩ = codes i := by
  simp [argumentSlots]
  congr
  omega

@[simp] theorem eval_argumentValueTerm_slots {alpha : Type u}
    (M : PA.PreModel alpha) {rank : Nat}
    (values codes : Fin rank → alpha) (e : Nat → alpha)
    (i : Fin rank) :
    PA.Term.eval M (slotEnv (2 * rank) (argumentSlots values codes) e)
        (argumentValueTerm i) = values i := by
  simp [argumentValueTerm, PA.Term.eval]

@[simp] theorem eval_argumentCodeTerm_slots {alpha : Type u}
    (M : PA.PreModel alpha) {rank : Nat}
    (values codes : Fin rank → alpha) (e : Nat → alpha)
    (i : Fin rank) :
    PA.Term.eval M (slotEnv (2 * rank) (argumentSlots values codes) e)
        (argumentCodeTerm i) = codes i := by
  simp only [argumentCodeTerm, PA.Term.eval]
  rw [slotEnv_of_lt (argumentSlots values codes) e (by omega)]
  exact argumentSlots_code values codes i

/-- The fixed-length list-code term assembled from the child-code slots. -/
def argumentVectorTerm (rank : Nat) : PA.Term :=
  listTerm (List.ofFn (fun i : Fin rank => argumentCodeTerm i))

theorem eval_listTerm_map_congr {alpha : Type u} {beta : Type v}
    (M : PA.PreModel alpha) (xs : List beta)
    (left right : beta → PA.Term) (e e' : Nat → alpha)
    (h : ∀ x ∈ xs,
      PA.Term.eval M e (left x) = PA.Term.eval M e' (right x)) :
    PA.Term.eval M e (listTerm (xs.map left)) =
      PA.Term.eval M e' (listTerm (xs.map right)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, listTerm, eval_nodeTerm]
      rw [h x (by simp), ih]
      intro y hy
      exact h y (by simp [hy])

@[simp] theorem eval_argumentVectorTerm_slots {alpha : Type u}
    (M : PA.PreModel alpha) {rank : Nat}
    (values : Fin rank → alpha) (terms : Fin rank → PA.Term)
    (slotTail termEnv : Nat → alpha) :
    PA.Term.eval M
        (slotEnv (2 * rank)
          (argumentSlots values (fun i => PA.Term.eval M termEnv (terms i)))
          slotTail)
        (argumentVectorTerm rank) =
      PA.Term.eval M termEnv (listTerm (List.ofFn terms)) := by
  let indices := List.ofFn (fun i : Fin rank => i)
  have h := eval_listTerm_map_congr M indices
    (fun i => argumentCodeTerm i) terms
    (slotEnv (2 * rank)
      (argumentSlots values (fun i => PA.Term.eval M termEnv (terms i)))
      slotTail)
    termEnv (by
      intro (i : Fin rank) hi
      exact eval_argumentCodeTerm_slots M values
        (fun i => PA.Term.eval M termEnv (terms i)) slotTail i)
  simpa [indices, argumentVectorTerm, List.map_ofFn,
    Function.comp_def] using h

/-- Substitution which installs a proposed output and the fixed finite tuple
of argument values in a selector graph.  Irrelevant tail slots are zero. -/
def graphSubst (rank : Nat) (out : PA.Term)
    (args : Fin rank → PA.Term) : Nat → PA.Term
  | 0 => out
  | i + 1 => if hi : i < rank then args ⟨i, hi⟩ else PA.Term.zero

/-- Instantiate a selector graph with term-valued output and arguments. -/
def graphAt (rank : Nat) (graph : PA.Formula) (out : PA.Term)
    (args : Fin rank → PA.Term) : PA.Formula :=
  PA.Formula.subst (graphSubst rank out args) graph

@[simp] theorem sat_graphAt {alpha : Type u} (M : PA.PreModel alpha)
    (rank : Nat) (graph : PA.Formula) (out : PA.Term)
    (args : Fin rank → PA.Term) (e : Nat → alpha) :
    PA.Formula.Sat M e (graphAt rank graph out args) ↔
      PA.Formula.Sat M
        (scons (PA.Term.eval M e out)
          (boundedEnv M rank (fun i => PA.Term.eval M e (args i))))
        graph := by
  rw [graphAt, PA.Formula.Sat_subst]
  apply PA.Formula.Sat_ext M graph
  intro i
  cases i with
  | zero => rfl
  | succ i =>
      by_cases hi : i < rank
      · simp [graphSubst, boundedEnv, hi, scons]
      · simp [graphSubst, boundedEnv, hi, scons, PA.Term.eval]

/-! ## The seven row cases -/

/-- The distinguished-generator row. -/
def starCase (code value star : PA.Term) : PA.Formula :=
  PA.Formula.and
    (PA.Formula.eq code
      (nodeTerm (PA.Term.numeral 0) (PA.Term.numeral 0)))
    (PA.Formula.eq value star)

/-- The arithmetic-zero row. -/
def zeroCase (code value : PA.Term) : PA.Formula :=
  PA.Formula.and
    (PA.Formula.eq code
      (nodeTerm (PA.Term.numeral 1) (PA.Term.numeral 0)))
    (PA.Formula.eq value PA.Term.zero)

/-- A unary row.  The two witnesses are, from inner to outer, the child value
and child code. -/
def succCase (code value betaCode betaStep : PA.Term) : PA.Formula :=
  existsN 2 <|
    conjunction
      [PA.Formula.eq (liftTerm 2 code)
        (nodeTerm (PA.Term.numeral 2) (argumentCodeTerm 0)),
       PA.Formula.ltTermAt (argumentCodeTerm 0) (liftTerm 2 code),
       PA.Formula.betaTermTermAt (argumentValueTerm 0)
        (liftTerm 2 betaCode) (liftTerm 2 betaStep)
        (argumentCodeTerm 0),
       PA.Formula.eq (liftTerm 2 value)
        (PA.Term.succ (argumentValueTerm 0))]

/-- A binary arithmetic row, shared by addition and multiplication. -/
def binaryCase (tag : Nat) (op : PA.Term → PA.Term → PA.Term)
    (code value betaCode betaStep : PA.Term) : PA.Formula :=
  existsN 4 <|
    conjunction
      [PA.Formula.eq (liftTerm 4 code)
        (nodeTerm (PA.Term.numeral tag)
          (nodeTerm (argumentCodeTerm 0) (argumentCodeTerm 1))),
       PA.Formula.ltTermAt (argumentCodeTerm 0) (liftTerm 4 code),
       PA.Formula.ltTermAt (argumentCodeTerm 1) (liftTerm 4 code),
       PA.Formula.betaTermTermAt (argumentValueTerm 0)
        (liftTerm 4 betaCode) (liftTerm 4 betaStep)
        (argumentCodeTerm 0),
       PA.Formula.betaTermTermAt (argumentValueTerm 1)
        (liftTerm 4 betaCode) (liftTerm 4 betaStep)
        (argumentCodeTerm 1),
       PA.Formula.eq (liftTerm 4 value)
        (op (argumentValueTerm 0) (argumentValueTerm 1))]

theorem sat_succCase_of {alpha : Type u} (M : PA.PreModel alpha)
    (code value betaCode betaStep childTerm : PA.Term)
    (childValue : alpha) (e : Nat → alpha)
    (hcode : PA.Term.eval M e code = PA.Term.eval M e
      (nodeTerm (PA.Term.numeral 2) childTerm))
    (hbound : RawLt M (PA.Term.eval M e childTerm)
      (PA.Term.eval M e code))
    (hlookup : RawBetaEntry M childValue
      (PA.Term.eval M e betaCode) (PA.Term.eval M e betaStep)
      (PA.Term.eval M e childTerm))
    (hvalue : PA.Term.eval M e value = M.succ childValue) :
    PA.Formula.Sat M e (succCase code value betaCode betaStep) := by
  let values : Fin 1 → alpha := fun _ => childValue
  let terms : Fin 1 → PA.Term := fun _ => childTerm
  let slots : Fin 2 → alpha :=
    argumentSlots values (fun i => PA.Term.eval M e (terms i))
  have hslotValue : PA.Term.eval M (slotEnv 2 slots e)
      (argumentValueTerm 0) = childValue := by
    change slotEnv 2 slots e 0 = childValue
    rw [slotEnv_of_lt slots e (by omega)]
    simp [slots, values, terms, argumentSlots]
  have hslotCode : PA.Term.eval M (slotEnv 2 slots e)
      (argumentCodeTerm 0) = PA.Term.eval M e childTerm := by
    change slotEnv 2 slots e 1 = PA.Term.eval M e childTerm
    rw [slotEnv_of_lt slots e (by omega)]
    simp [slots, values, terms, argumentSlots]
  apply sat_existsN_of_slots M 2 _ slots e
  rw [sat_conjunction]
  intro phi hphi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hphi
  rcases hphi with rfl | rfl | rfl | rfl
  · simp only [PA.Formula.Sat, eval_liftTerm_slotEnv]
    simp only [eval_nodeTerm, PA.Term.eval_numeral]
    rw [hslotCode]
    simpa only [eval_nodeTerm, PA.Term.eval_numeral] using hcode
  · rw [sat_ltTermAt_iff_raw]
    simp only [eval_liftTerm_slotEnv]
    rw [hslotCode]
    exact hbound
  · rw [sat_betaTermTermAt_iff_raw]
    simp only [eval_liftTerm_slotEnv]
    rw [hslotValue, hslotCode]
    exact hlookup
  · simp only [PA.Formula.Sat, eval_liftTerm_slotEnv, PA.Term.eval]
    rw [hslotValue]
    exact hvalue

theorem sat_binaryCase_of {alpha : Type u} (M : PA.PreModel alpha)
    (tag : Nat) (op : PA.Term → PA.Term → PA.Term)
    (opValue : alpha → alpha → alpha)
    (code value betaCode betaStep leftTerm rightTerm : PA.Term)
    (leftValue rightValue : alpha) (e : Nat → alpha)
    (hop : ∀ (e' : Nat → alpha) (a b : PA.Term),
      PA.Term.eval M e' (op a b) =
        opValue (PA.Term.eval M e' a) (PA.Term.eval M e' b))
    (hcode : PA.Term.eval M e code = PA.Term.eval M e
      (nodeTerm (PA.Term.numeral tag)
        (nodeTerm leftTerm rightTerm)))
    (hleftBound : RawLt M (PA.Term.eval M e leftTerm)
      (PA.Term.eval M e code))
    (hrightBound : RawLt M (PA.Term.eval M e rightTerm)
      (PA.Term.eval M e code))
    (hleft : RawBetaEntry M leftValue
      (PA.Term.eval M e betaCode) (PA.Term.eval M e betaStep)
      (PA.Term.eval M e leftTerm))
    (hright : RawBetaEntry M rightValue
      (PA.Term.eval M e betaCode) (PA.Term.eval M e betaStep)
      (PA.Term.eval M e rightTerm))
    (hvalue : PA.Term.eval M e value = opValue leftValue rightValue) :
    PA.Formula.Sat M e
      (binaryCase tag op code value betaCode betaStep) := by
  let values : Fin 2 → alpha := fun i =>
    if i.val = 0 then leftValue else rightValue
  let terms : Fin 2 → PA.Term := fun i =>
    if i.val = 0 then leftTerm else rightTerm
  let slots : Fin 4 → alpha :=
    argumentSlots values (fun i => PA.Term.eval M e (terms i))
  have hslotValue0 : PA.Term.eval M (slotEnv 4 slots e)
      (argumentValueTerm 0) = leftValue := by
    change slotEnv 4 slots e 0 = leftValue
    rw [slotEnv_of_lt slots e (by omega)]
    simp [slots, values, terms, argumentSlots]
  have hslotCode0 : PA.Term.eval M (slotEnv 4 slots e)
      (argumentCodeTerm 0) = PA.Term.eval M e leftTerm := by
    change slotEnv 4 slots e 1 = PA.Term.eval M e leftTerm
    rw [slotEnv_of_lt slots e (by omega)]
    simp [slots, values, terms, argumentSlots]
  have hslotValue1 : PA.Term.eval M (slotEnv 4 slots e)
      (argumentValueTerm 1) = rightValue := by
    change slotEnv 4 slots e 2 = rightValue
    rw [slotEnv_of_lt slots e (by omega)]
    simp [slots, values, terms, argumentSlots]
  have hslotCode1 : PA.Term.eval M (slotEnv 4 slots e)
      (argumentCodeTerm 1) = PA.Term.eval M e rightTerm := by
    change slotEnv 4 slots e 3 = PA.Term.eval M e rightTerm
    rw [slotEnv_of_lt slots e (by omega)]
    have h := argumentSlots_code values
      (fun i => PA.Term.eval M e (terms i)) (⟨1, by omega⟩ : Fin 2)
    simpa [slots, terms] using h
  apply sat_existsN_of_slots M 4 _ slots e
  rw [sat_conjunction]
  intro phi hphi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hphi
  rcases hphi with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PA.Formula.Sat, eval_liftTerm_slotEnv]
    simp only [eval_nodeTerm, PA.Term.eval_numeral]
    rw [hslotCode0, hslotCode1]
    simpa only [eval_nodeTerm, PA.Term.eval_numeral] using hcode
  · rw [sat_ltTermAt_iff_raw]
    simp only [eval_liftTerm_slotEnv]
    rw [hslotCode0]
    exact hleftBound
  · rw [sat_ltTermAt_iff_raw]
    simp only [eval_liftTerm_slotEnv]
    rw [hslotCode1]
    exact hrightBound
  · rw [sat_betaTermTermAt_iff_raw]
    simp only [eval_liftTerm_slotEnv]
    rw [hslotValue0, hslotCode0]
    exact hleft
  · rw [sat_betaTermTermAt_iff_raw]
    simp only [eval_liftTerm_slotEnv]
    rw [hslotValue1, hslotCode1]
    exact hright
  · simp only [PA.Formula.Sat, eval_liftTerm_slotEnv]
    rw [hop]
    rw [hslotValue0, hslotValue1]
    exact hvalue

/-- One formula-index branch of an existential or universal Skolem row. -/
def skolemBranch (rank tag : Nat) (graph : PA.Formula)
    (formulaIndex : Nat) (code value betaCode betaStep : PA.Term) :
    PA.Formula :=
  let width := 2 * rank
  existsN width <|
    conjunction
      [PA.Formula.eq (liftTerm width code)
        (nodeTerm (PA.Term.numeral tag)
          (nodeTerm (PA.Term.numeral formulaIndex)
            (argumentVectorTerm rank))),
       conjunction (List.ofFn (fun i : Fin rank =>
         PA.Formula.ltTermAt (argumentCodeTerm i)
           (liftTerm width code))),
       conjunction (List.ofFn (fun i : Fin rank =>
         PA.Formula.betaTermTermAt (argumentValueTerm i)
           (liftTerm width betaCode) (liftTerm width betaStep)
           (argumentCodeTerm i))),
       graphAt rank graph (liftTerm width value)
         (fun i => argumentValueTerm i)]

/-- Semantic constructor for one fixed formula-index branch. -/
theorem sat_skolemBranch_of_slots {alpha : Type u}
    (M : PA.PreModel alpha) (rank tag : Nat) (graph : PA.Formula)
    (formulaIndex : Nat) (code value betaCode betaStep : PA.Term)
    (e : Nat → alpha) (values : Fin rank → alpha)
    (terms : Fin rank → PA.Term)
    (hcode : PA.Term.eval M e code =
      PA.Term.eval M e
        (nodeTerm (PA.Term.numeral tag)
          (nodeTerm (PA.Term.numeral formulaIndex)
            (listTerm (List.ofFn terms)))))
    (hbounds : ∀ i : Fin rank,
      RawLt M (PA.Term.eval M e (terms i)) (PA.Term.eval M e code))
    (hlookup : ∀ i : Fin rank,
      RawBetaEntry M (values i)
        (PA.Term.eval M e betaCode) (PA.Term.eval M e betaStep)
        (PA.Term.eval M e (terms i)))
    (hgraph : PA.Formula.Sat M
      (scons (PA.Term.eval M e value) (boundedEnv M rank values)) graph) :
    PA.Formula.Sat M e
      (skolemBranch rank tag graph formulaIndex
        code value betaCode betaStep) := by
  let slots : Fin (2 * rank) → alpha :=
    argumentSlots values (fun i => PA.Term.eval M e (terms i))
  apply sat_existsN_of_slots M (2 * rank) _ slots e
  rw [sat_conjunction]
  intro phi hphi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hphi
  rcases hphi with rfl | rfl | rfl | rfl
  · simp only [PA.Formula.Sat, eval_liftTerm_slotEnv]
    dsimp [slots]
    simp only [eval_nodeTerm]
    rw [eval_argumentVectorTerm_slots]
    simpa only [eval_nodeTerm, PA.Term.eval_numeral] using hcode
  · rw [sat_conjunction]
    intro entry hentry
    rcases (List.mem_ofFn.mp hentry) with ⟨i, rfl⟩
    rw [sat_ltTermAt_iff_raw]
    simp only [eval_liftTerm_slotEnv]
    simpa [slots] using hbounds i
  · rw [sat_conjunction]
    intro entry hentry
    rcases (List.mem_ofFn.mp hentry) with ⟨i, rfl⟩
    rw [sat_betaTermTermAt_iff_raw]
    simpa [slots] using hlookup i
  · rw [sat_graphAt]
    simpa [slots] using hgraph

/-- Formula bodies admitted by a genuine existential Skolem constructor. -/
def exBodies (rank : Nat) : List PA.Formula :=
  (formulasOfRankAtMost rank).filter
    (fun body => formulaRank (PA.Formula.ex body) ≤ rank)

/-- Formula bodies admitted by a genuine universal Skolem constructor. -/
def allBodies (rank : Nat) : List PA.Formula :=
  (formulasOfRankAtMost rank).filter
    (fun body => formulaRank (PA.Formula.all body) ≤ rank)

/-- Finite dispatch for existential Skolem nodes. -/
def exSkolemCase (rank : Nat)
    (code value betaCode betaStep : PA.Term) : PA.Formula :=
  disjunction ((exBodies rank).map (fun body =>
    skolemBranch rank 5 (leastDefaultGraph body)
      (Program.formulaIndex rank body) code value betaCode betaStep))

/-- Finite dispatch for universal-counterexample nodes. -/
def allSkolemCase (rank : Nat)
    (code value betaCode betaStep : PA.Term) : PA.Formula :=
  disjunction ((allBodies rank).map (fun body =>
    skolemBranch rank 6 (leastCounterexampleGraph body)
      (Program.formulaIndex rank body) code value betaCode betaStep))

/-- The finite disjunction of the seven genuine program constructors. -/
def programCases (rank : Nat) (code value betaCode betaStep star : PA.Term) :
    PA.Formula :=
  disjunction
    [starCase code value star,
     zeroCase code value,
     succCase code value betaCode betaStep,
     binaryCase 3 PA.Term.add code value betaCode betaStep,
     binaryCase 4 PA.Term.mul code value betaCode betaStep,
     exSkolemCase rank code value betaCode betaStep,
     allSkolemCase rank code value betaCode betaStep]

/-- No value satisfies a genuine constructor case for this code.  Crucially,
the negation quantifies the proposed output; guarding the default by
`not (programCases code value)` would make a valid nonzero row coexist with a
spurious zero row. -/
def noProgramCase (rank : Nat) (code betaCode betaStep star : PA.Term) :
    PA.Formula :=
  PA.Formula.imp
    (PA.Formula.ex
      (programCases rank (liftTerm 1 code) (PA.Term.var 0)
        (liftTerm 1 betaCode) (liftTerm 1 betaStep) (liftTerm 1 star)))
    PA.Formula.bot

@[simp] theorem sat_noProgramCase_iff {alpha : Type u}
    (M : PA.PreModel alpha) (rank : Nat)
    (code betaCode betaStep star : PA.Term) (e : Nat → alpha) :
    PA.Formula.Sat M e (noProgramCase rank code betaCode betaStep star) ↔
      ¬∃ value : alpha,
        PA.Formula.Sat M (scons value e)
          (programCases rank (liftTerm 1 code) (PA.Term.var 0)
            (liftTerm 1 betaCode) (liftTerm 1 betaStep)
            (liftTerm 1 star)) := by
  rfl

/-- One fixed, total evaluator row for programs of the displayed rank.
Codes with no genuine output receive value zero.  This totalization lets a
beta table be indexed by every number through the target code without adding
junk constructors to `Program`. -/
def programStep (rank : Nat) (code value betaCode betaStep star : PA.Term) :
    PA.Formula :=
  let cases := programCases rank code value betaCode betaStep star
  PA.Formula.or cases
    (PA.Formula.and (noProgramCase rank code betaCode betaStep star)
      (PA.Formula.eq value PA.Term.zero))

@[simp] theorem sat_programStep_iff {alpha : Type u}
    (M : PA.PreModel alpha) (rank : Nat)
    (code value betaCode betaStep star : PA.Term) (e : Nat → alpha) :
    PA.Formula.Sat M e
        (programStep rank code value betaCode betaStep star) ↔
      (PA.Formula.Sat M e
          (programCases rank code value betaCode betaStep star) ∨
        (PA.Formula.Sat M e
            (noProgramCase rank code betaCode betaStep star) ∧
          PA.Term.eval M e value = M.zero)) := by
  rfl

/-- A closed polynomial term mirroring `Program.code` constructor by
constructor. -/
def programCodeTerm : Program rank → PA.Term
  | .star => nodeTerm (PA.Term.numeral 0) (PA.Term.numeral 0)
  | .zero => nodeTerm (PA.Term.numeral 1) (PA.Term.numeral 0)
  | .succ p => nodeTerm (PA.Term.numeral 2) (programCodeTerm p)
  | .add p q => nodeTerm (PA.Term.numeral 3)
      (nodeTerm (programCodeTerm p) (programCodeTerm q))
  | .mul p q => nodeTerm (PA.Term.numeral 4)
      (nodeTerm (programCodeTerm p) (programCodeTerm q))
  | .exSkolem body _ args => nodeTerm (PA.Term.numeral 5)
      (nodeTerm (PA.Term.numeral (Program.formulaIndex rank body))
        (listTerm (List.ofFn (fun i => programCodeTerm (args i)))))
  | .allSkolem body _ args => nodeTerm (PA.Term.numeral 6)
      (nodeTerm (PA.Term.numeral (Program.formulaIndex rank body))
        (listTerm (List.ofFn (fun i => programCodeTerm (args i)))))

/-- Environment used by the standard-row correctness theorem. -/
noncomputable def programRowEnv {alpha : Type u} {M : PA.PreModel alpha}
    (S : CanonicalSelectors M) (star betaCode betaStep : alpha)
    (p : Program rank) (e : Nat → alpha) : Nat → alpha :=
  scons (Program.eval M S star p)
    (scons betaCode (scons betaStep (scons star e)))

/-- Every genuine standard program satisfies its corresponding finite row
case, provided the beta table contains all immediate children. -/
theorem sat_programCases_of_program {alpha : Type u}
    {M : PA.PreModel alpha}
    (S : CanonicalSelectors M) (star betaCode betaStep : alpha)
    (p : Program rank) (e : Nat → alpha)
    (hlookup : ∀ q : Program rank, Program.code q < Program.code p →
      RawBetaEntry M (Program.eval M S star q) betaCode betaStep
        (PA.Term.eval M (programRowEnv S star betaCode betaStep p e)
          (programCodeTerm q)))
    (hcodeLt : ∀ q : Program rank, Program.code q < Program.code p →
      RawLt M
        (PA.Term.eval M (programRowEnv S star betaCode betaStep p e)
          (programCodeTerm q))
        (PA.Term.eval M (programRowEnv S star betaCode betaStep p e)
          (programCodeTerm p))) :
    PA.Formula.Sat M (programRowEnv S star betaCode betaStep p e)
      (programCases rank (programCodeTerm p)
        (PA.Term.var 0) (PA.Term.var 1) (PA.Term.var 2)
        (PA.Term.var 3)) := by
  rw [programCases, sat_disjunction]
  cases p with
  | star =>
      refine ⟨starCase (programCodeTerm (.star : Program rank))
        (PA.Term.var 0) (PA.Term.var 3), by simp, ?_⟩
      simp [starCase, programRowEnv, programCodeTerm,
        Program.eval, PA.Formula.Sat, PA.Term.eval, scons]
  | zero =>
      refine ⟨zeroCase (programCodeTerm (.zero : Program rank))
        (PA.Term.var 0), by simp, ?_⟩
      simp [zeroCase, programRowEnv, programCodeTerm,
        Program.eval, PA.Formula.Sat, PA.Term.eval, scons]
  | succ q =>
      refine ⟨succCase (programCodeTerm (.succ q))
        (PA.Term.var 0) (PA.Term.var 1) (PA.Term.var 2), by simp, ?_⟩
      apply sat_succCase_of M
        (programCodeTerm (.succ q)) (PA.Term.var 0)
        (PA.Term.var 1) (PA.Term.var 2) (programCodeTerm q)
        (Program.eval M S star q)
        (programRowEnv S star betaCode betaStep (.succ q) e)
      · rfl
      · exact hcodeLt q (Program.code_succ_child_lt q)
      · have h := hlookup q (Program.code_succ_child_lt q)
        simpa [programRowEnv, PA.Term.eval, scons] using h
      · rfl
  | add left right =>
      refine ⟨binaryCase 3 PA.Term.add (programCodeTerm (.add left right))
        (PA.Term.var 0) (PA.Term.var 1) (PA.Term.var 2), by simp, ?_⟩
      apply sat_binaryCase_of M 3 PA.Term.add M.add
        (programCodeTerm (.add left right)) (PA.Term.var 0)
        (PA.Term.var 1) (PA.Term.var 2)
        (programCodeTerm left) (programCodeTerm right)
        (Program.eval M S star left) (Program.eval M S star right)
        (programRowEnv S star betaCode betaStep (.add left right) e)
      · intro e' a b
        rfl
      · rfl
      · exact hcodeLt left (Program.code_add_left_lt left right)
      · exact hcodeLt right (Program.code_add_right_lt left right)
      · have h := hlookup left (Program.code_add_left_lt left right)
        simpa [programRowEnv, PA.Term.eval, scons] using h
      · have h := hlookup right (Program.code_add_right_lt left right)
        simpa [programRowEnv, PA.Term.eval, scons] using h
      · rfl
  | mul left right =>
      refine ⟨binaryCase 4 PA.Term.mul (programCodeTerm (.mul left right))
        (PA.Term.var 0) (PA.Term.var 1) (PA.Term.var 2), by simp, ?_⟩
      apply sat_binaryCase_of M 4 PA.Term.mul M.mul
        (programCodeTerm (.mul left right)) (PA.Term.var 0)
        (PA.Term.var 1) (PA.Term.var 2)
        (programCodeTerm left) (programCodeTerm right)
        (Program.eval M S star left) (Program.eval M S star right)
        (programRowEnv S star betaCode betaStep (.mul left right) e)
      · intro e' a b
        rfl
      · rfl
      · exact hcodeLt left (Program.code_mul_left_lt left right)
      · exact hcodeLt right (Program.code_mul_right_lt left right)
      · have h := hlookup left (Program.code_mul_left_lt left right)
        simpa [programRowEnv, PA.Term.eval, scons] using h
      · have h := hlookup right (Program.code_mul_right_lt left right)
        simpa [programRowEnv, PA.Term.eval, scons] using h
      · rfl
  | exSkolem body hRank args =>
      let node : Program rank := .exSkolem body hRank args
      refine ⟨exSkolemCase rank (programCodeTerm node)
        (PA.Term.var 0) (PA.Term.var 1) (PA.Term.var 2), by simp [node], ?_⟩
      rw [exSkolemCase, sat_disjunction]
      have hBodyRank : formulaRank body ≤ rank := by
        simp only [formulaRank] at hRank
        omega
      have hBodyMem : body ∈ exBodies rank := by
        simp [exBodies, (mem_formulasOfRankAtMost rank body).mpr hBodyRank,
          hRank]
      refine ⟨skolemBranch rank 5 (leastDefaultGraph body)
        (Program.formulaIndex rank body) (programCodeTerm node)
        (PA.Term.var 0) (PA.Term.var 1) (PA.Term.var 2),
        List.mem_map.mpr ⟨body, hBodyMem, rfl⟩, ?_⟩
      apply sat_skolemBranch_of_slots M rank 5 (leastDefaultGraph body)
        (Program.formulaIndex rank body) (programCodeTerm node)
        (PA.Term.var 0) (PA.Term.var 1) (PA.Term.var 2)
        (programRowEnv S star betaCode betaStep node e)
        (fun i => Program.eval M S star (args i))
        (fun i => programCodeTerm (args i))
      · rfl
      · intro i
        exact hcodeLt (args i) (Program.code_ex_child_lt body hRank args i)
      · intro i
        have h := hlookup (args i) (Program.code_ex_child_lt body hRank args i)
        simpa [programRowEnv, PA.Term.eval, scons] using h
      · simpa [node, programRowEnv, Program.argsEnv,
          PA.Term.eval, scons] using
          (Program.eval_exSkolem_graph M S star body hRank args)
  | allSkolem body hRank args =>
      let node : Program rank := .allSkolem body hRank args
      refine ⟨allSkolemCase rank (programCodeTerm node)
        (PA.Term.var 0) (PA.Term.var 1) (PA.Term.var 2), by simp [node], ?_⟩
      rw [allSkolemCase, sat_disjunction]
      have hBodyRank : formulaRank body ≤ rank := by
        simp only [formulaRank] at hRank
        omega
      have hBodyMem : body ∈ allBodies rank := by
        simp [allBodies, (mem_formulasOfRankAtMost rank body).mpr hBodyRank,
          hRank]
      refine ⟨skolemBranch rank 6 (leastCounterexampleGraph body)
        (Program.formulaIndex rank body) (programCodeTerm node)
        (PA.Term.var 0) (PA.Term.var 1) (PA.Term.var 2),
        List.mem_map.mpr ⟨body, hBodyMem, rfl⟩, ?_⟩
      apply sat_skolemBranch_of_slots M rank 6
        (leastCounterexampleGraph body) (Program.formulaIndex rank body)
        (programCodeTerm node) (PA.Term.var 0) (PA.Term.var 1)
        (PA.Term.var 2) (programRowEnv S star betaCode betaStep node e)
        (fun i => Program.eval M S star (args i))
        (fun i => programCodeTerm (args i))
      · rfl
      · intro i
        exact hcodeLt (args i) (Program.code_all_child_lt body hRank args i)
      · intro i
        have h := hlookup (args i) (Program.code_all_child_lt body hRank args i)
        simpa [programRowEnv, PA.Term.eval, scons] using h
      · simpa [node, programRowEnv, Program.argsEnv,
          PA.Term.eval, scons] using
          (Program.eval_allSkolem_graph M S star body hRank args)

/-! ## The fixed beta-table evaluator -/

/-- A beta table evaluates `code` to `value` and every row through `code`
satisfies the fixed program-step relation. -/
def evaluator (rank : Nat) (code value star : PA.Term) : PA.Formula :=
  PA.Formula.ex (PA.Formula.ex
    (PA.Formula.and
      (PA.Formula.betaTermTermAt
        (liftTerm 2 value) (PA.Term.var 1) (PA.Term.var 0)
        (liftTerm 2 code))
      (PA.Formula.all
        (PA.Formula.imp
          (PA.Formula.leTermAt (PA.Term.var 0) (liftTerm 3 code))
          (PA.Formula.ex
            (PA.Formula.and
              (PA.Formula.betaTermTermAt
                (PA.Term.var 0) (PA.Term.var 3) (PA.Term.var 2)
                (PA.Term.var 1))
              (programStep rank (PA.Term.var 1) (PA.Term.var 0)
                (PA.Term.var 3) (PA.Term.var 2)
                (liftTerm 4 star))))))))

/-! ## PA normalization of the external codes -/

/-- Polynomial pairing preserves PA-provable equality with standard
numerals. -/
theorem bprov_pairTerm_normalize {a b : Nat} {s t : PA.Term}
    (hs : PA.Formula.BProv PA.Formula.Ax_s []
      (PA.Formula.eq s (PA.Term.numeral a)))
    (ht : PA.Formula.BProv PA.Formula.Ax_s []
      (PA.Formula.eq t (PA.Term.numeral b))) :
    PA.Formula.BProv PA.Formula.Ax_s []
      (PA.Formula.eq (pairTerm s t)
        (PA.Term.numeral (Program.pairCode a b))) := by
  have hsum0 := PA.Formula.BProv_eq_congr_add hs ht
  have hsum1 := PA.Formula.BProv_Ax_s_addNumerals (G := []) a b
  have hsum : PA.Formula.BProv PA.Formula.Ax_s []
      (PA.Formula.eq (PA.Term.add s t) (PA.Term.numeral (a + b))) :=
    PA.Formula.BProv_eqTrans hsum0 hsum1
  have hsquare0 := PA.Formula.BProv_eq_congr_mul hsum hsum
  have hsquare1 := PA.Formula.BProv_Ax_s_mulNumerals (G := []) (a + b) (a + b)
  have hsquare : PA.Formula.BProv PA.Formula.Ax_s []
      (PA.Formula.eq
        (PA.Term.mul (PA.Term.add s t) (PA.Term.add s t))
        (PA.Term.numeral ((a + b) * (a + b)))) :=
    PA.Formula.BProv_eqTrans hsquare0 hsquare1
  have hout0 := PA.Formula.BProv_eq_congr_add hsquare hs
  have hout1 := PA.Formula.BProv_Ax_s_addNumerals (G := [])
    ((a + b) * (a + b)) a
  have hout := PA.Formula.BProv_eqTrans hout0 hout1
  simpa [pairTerm, Program.pairCode] using hout

/-- Positive-node formation preserves PA-provable equality with standard
numerals. -/
theorem bprov_nodeTerm_normalize {a b : Nat} {s t : PA.Term}
    (hs : PA.Formula.BProv PA.Formula.Ax_s []
      (PA.Formula.eq s (PA.Term.numeral a)))
    (ht : PA.Formula.BProv PA.Formula.Ax_s []
      (PA.Formula.eq t (PA.Term.numeral b))) :
    PA.Formula.BProv PA.Formula.Ax_s []
      (PA.Formula.eq (nodeTerm s t)
        (PA.Term.numeral (Program.nodeCode a b))) := by
  have h := PA.Formula.BProv_eq_congr_succ
    (bprov_pairTerm_normalize hs ht)
  simpa [nodeTerm, Program.nodeCode, PA.Term.numeral_succ] using h

/-- Normalize a list-code term whose fields individually normalize. -/
theorem bprov_listTerm_map_normalize {beta : Type}
    (xs : List beta) (term : beta → PA.Term) (value : beta → Nat)
    (h : ∀ x ∈ xs, PA.Formula.BProv PA.Formula.Ax_s []
      (PA.Formula.eq (term x) (PA.Term.numeral (value x)))) :
    PA.Formula.BProv PA.Formula.Ax_s []
      (PA.Formula.eq (listTerm (xs.map term))
        (PA.Term.numeral (Program.listCode (xs.map value)))) := by
  induction xs with
  | nil =>
      simpa [listTerm, Program.listCode, PA.Term.numeral] using
        (PA.Formula.BProv_eqRefl (B := PA.Formula.Ax_s) (G := [])
          PA.Term.zero)
  | cons x xs ih =>
      simp only [List.map_cons, listTerm, Program.listCode]
      apply bprov_nodeTerm_normalize
      · exact h x (by simp)
      · apply ih
        intro y hy
        exact h y (by simp [hy])

/-- Every closed structural program-code term denotes the corresponding
external standard polynomial code in every model of PA.  The derivation is
itself a kernel-checked PA derivation. -/
theorem bprov_programCodeTerm (p : Program rank) :
    PA.Formula.BProv PA.Formula.Ax_s []
      (PA.Formula.eq (programCodeTerm p)
        (PA.Term.numeral (Program.code p))) := by
  induction p with
  | star =>
      exact bprov_nodeTerm_normalize
        (PA.Formula.BProv_eqRefl (PA.Term.numeral 0))
        (PA.Formula.BProv_eqRefl (PA.Term.numeral 0))
  | zero =>
      exact bprov_nodeTerm_normalize
        (PA.Formula.BProv_eqRefl (PA.Term.numeral 1))
        (PA.Formula.BProv_eqRefl (PA.Term.numeral 0))
  | succ p ih =>
      exact bprov_nodeTerm_normalize
        (PA.Formula.BProv_eqRefl (PA.Term.numeral 2)) ih
  | add p q ihp ihq =>
      exact bprov_nodeTerm_normalize
        (PA.Formula.BProv_eqRefl (PA.Term.numeral 3))
        (bprov_nodeTerm_normalize ihp ihq)
  | mul p q ihp ihq =>
      exact bprov_nodeTerm_normalize
        (PA.Formula.BProv_eqRefl (PA.Term.numeral 4))
        (bprov_nodeTerm_normalize ihp ihq)
  | exSkolem body hRank args ih =>
      apply bprov_nodeTerm_normalize
      · exact PA.Formula.BProv_eqRefl (PA.Term.numeral 5)
      · apply bprov_nodeTerm_normalize
        · exact PA.Formula.BProv_eqRefl
            (PA.Term.numeral (Program.formulaIndex rank body))
        · simpa [List.map_ofFn, Function.comp_def,
              Program.vectorCode] using
            (bprov_listTerm_map_normalize
              (List.ofFn (fun i : Fin rank => i))
              (fun i => programCodeTerm (args i))
              (fun i => Program.code (args i))
              (by
                intro i hi
                exact ih i))
  | allSkolem body hRank args ih =>
      apply bprov_nodeTerm_normalize
      · exact PA.Formula.BProv_eqRefl (PA.Term.numeral 6)
      · apply bprov_nodeTerm_normalize
        · exact PA.Formula.BProv_eqRefl
            (PA.Term.numeral (Program.formulaIndex rank body))
        · simpa [List.map_ofFn, Function.comp_def,
              Program.vectorCode] using
            (bprov_listTerm_map_normalize
              (List.ofFn (fun i : Fin rank => i))
              (fun i => programCodeTerm (args i))
              (fun i => Program.code (args i))
              (by
                intro i hi
                exact ih i))

/-- Semantic standard-code theorem obtained from PA soundness. -/
theorem eval_programCodeTerm_eq_numeral {alpha : Type u}
    {M : PA.PreModel alpha} (hPA : RawPASatisfies M)
    (p : Program rank) (e : Nat → alpha) :
    PA.Term.eval M e (programCodeTerm p) =
      PA.Term.numeralValue M (Program.code p) := by
  have hsat := sat_of_bprov_axs hPA (bprov_programCodeTerm p) e
  simpa [PA.Formula.Sat, PA.Term.eval_numeral] using hsat

/-- Standard-numeral form of `sat_programCases_of_program`, matching the
indices supplied by `finite_vector_beta_code`. -/
theorem sat_programCases_of_standard_table {alpha : Type u}
    {M : PA.PreModel alpha} (hPA : RawPASatisfies M)
    (S : CanonicalSelectors M) (star betaCode betaStep : alpha)
    (p : Program rank) (e : Nat → alpha)
    (hlookup : ∀ q : Program rank, Program.code q < Program.code p →
      RawBetaEntry M (Program.eval M S star q) betaCode betaStep
        (PA.Term.numeralValue M (Program.code q))) :
    PA.Formula.Sat M (programRowEnv S star betaCode betaStep p e)
      (programCases rank (programCodeTerm p)
        (PA.Term.var 0) (PA.Term.var 1) (PA.Term.var 2)
        (PA.Term.var 3)) := by
  apply sat_programCases_of_program S star betaCode betaStep p e
  intro q hq
  rw [eval_programCodeTerm_eq_numeral hPA q
    (programRowEnv S star betaCode betaStep p e)]
  exact hlookup q hq
  intro q hq
  rw [eval_programCodeTerm_eq_numeral hPA q
      (programRowEnv S star betaCode betaStep p e),
    eval_programCodeTerm_eq_numeral hPA p
      (programRowEnv S star betaCode betaStep p e)]
  exact rawLt_numeralValue_of_lt hPA hq

/-- A genuine standard program therefore satisfies the totalized row
relation through its genuine-case disjunct. -/
theorem sat_programStep_of_standard_table {alpha : Type u}
    {M : PA.PreModel alpha} (hPA : RawPASatisfies M)
    (S : CanonicalSelectors M) (star betaCode betaStep : alpha)
    (p : Program rank) (e : Nat → alpha)
    (hlookup : ∀ q : Program rank, Program.code q < Program.code p →
      RawBetaEntry M (Program.eval M S star q) betaCode betaStep
        (PA.Term.numeralValue M (Program.code q))) :
    PA.Formula.Sat M (programRowEnv S star betaCode betaStep p e)
      (programStep rank (programCodeTerm p)
        (PA.Term.var 0) (PA.Term.var 1) (PA.Term.var 2)
        (PA.Term.var 3)) := by
  apply Or.inl
  exact sat_programCases_of_standard_table hPA S star betaCode betaStep
    p e hlookup

end ProgramTrace
end FiniteSkolemCut

end PAFiniteBasisReduction
end LeanProofs
