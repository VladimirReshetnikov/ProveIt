import DiophantineConsistency.ObjectOmegaSemiring
import Mathlib.Logic.ExistsUnique
import Mathlib.Logic.Function.Iterate

/-! # Definable iteration over the entire internal omega

The supplied operation includes an actual graph formula and its semantic
specification on every internal natural input. No external Realizes proof
is transferred to an arbitrary model by this interface.
-/

namespace DiophantineConsistency.ObjectNaturalIteration

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency ObjectArithmetic ObjectOmegaSemiring

set_option maxRecDepth 16000

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- An operation on all internal naturals, with its exact definable graph.
The two distinguished graph slots are output0 and input1; the remaining
slots read the supplied parameter environment. -/
structure Operation (H : ZFAxioms mem) where
  toFun : Natural H → Natural H
  graph : Form
  parameters : Nat → V
  graph_spec : ∀ (x : Natural H) (y : V),
    relOf mem graph parameters y x.val ↔ y = (toFun x).val

variable (H : ZFAxioms mem)

/-- A genuine total operation on the ambient universe, with empty default
on arguments outside the model's own omega. -/
noncomputable def totalize (op : Operation H) (x : V) : V := by
  classical
  exact if hx : mem x (omegaV H) then (op.toFun ⟨x,hx⟩).val else vempty H

theorem totalize_nat (op : Operation H) (x : Natural H) :
    totalize H op x.val = (op.toFun x).val := by
  simp only [totalize,dif_pos x.property]

theorem totalize_nonnat (op : Operation H) {x : V} (hx : ¬mem x (omegaV H)) :
    totalize H op x = vempty H := by simp only [totalize,dif_neg hx]

/-- The actual guarded graph formula for the totalized operation. -/
def totalizeForm (f : Form) : Form :=
  fOr (fAnd (fNatF 1) f) (fAnd (fNot (fNatF 1)) (fEmptyF 0))

theorem totalizeForm_spec (op : Operation H) (y x : V) :
    relOf mem (totalizeForm op.graph) op.parameters y x ↔ y = totalize H op x := by
  change ((Sat mem (scons y (scons x op.parameters)) (fNatF 1) ∧
      relOf mem op.graph op.parameters y x) ∨
    (¬Sat mem (scons y (scons x op.parameters)) (fNatF 1) ∧
      Sat mem (scons y (scons x op.parameters)) (fEmptyF 0))) ↔ _
  rw [fNatF_spec H _ 1,fEmptyF_spec H _ 0]
  change ((mem x (omegaV H) ∧ relOf mem op.graph op.parameters y x) ∨
    (¬mem x (omegaV H) ∧ y=vempty H)) ↔ _
  by_cases hx : mem x (omegaV H)
  · simp only [hx,true_and,not_true_eq_false,false_and,or_false]
    simpa only [totalize_nat H op ⟨x,hx⟩] using op.graph_spec ⟨x,hx⟩ y
  · simp only [hx,false_and,not_false_eq_true,true_and,false_or,totalize_nonnat H op hx]

/-- A seed and stage relation. Its stages are internal naturals by definition. -/
def IterRel (op : Operation H) (a n z : V) : Prop := ThetaG H (totalize H op) a z n

/-- The graph of iteration. Parameters for the step formula start at caller
slot off; introducing omega shifts that block by exactly one. -/
def iterationForm (f : Form) (z n a off : Nat) : Form :=
  fEx (fAnd (isOmegaForm 0)
    (fThetaG (totalizeForm f) (z+1) (n+1) (a+1) 0 (off+1)))

theorem iterationForm_spec (op : Operation H) (ee : Nat → V) (z n a off : Nat)
    (hoff : ∀ k, ee (k+off)=op.parameters k) :
    Sat mem ee (iterationForm op.graph z n a off) ↔ IterRel H op (ee a) (ee n) (ee z) := by
  constructor
  · rintro ⟨w,hw,h⟩
    have hw' : w=omegaV H := (isOmegaForm_spec H (scons w ee) 0).mp hw
    exact (fThetaG_spec H (totalizeForm op.graph) op.parameters (totalize H op)
      (totalizeForm_spec H op) (ee a) (scons w ee) (z+1) (n+1) (a+1) 0 (off+1)
      (fun k => hoff k) rfl hw').mp h
  · intro h
    refine ⟨omegaV H,(isOmegaForm_spec H _ 0).mpr rfl,?_⟩
    exact (fThetaG_spec H (totalizeForm op.graph) op.parameters (totalize H op)
      (totalizeForm_spec H op) (ee a) (scons (omegaV H) ee) (z+1) (n+1) (a+1) 0 (off+1)
      (fun k => hoff k) rfl rfl).mpr h

theorem iterRel_total (op : Operation H) (a : V) {n : V} (hn : mem n (omegaV H)) :
    ∃ z, IterRel H op a n z :=
  thetaG_total H (totalizeForm op.graph) op.parameters (totalize H op)
    (totalizeForm_spec H op) a n hn

theorem iterRel_unique (op : Operation H) {a n z z' : V}
    (h : IterRel H op a n z) (h' : IterRel H op a n z') : z=z' :=
  thetaG_unique H (totalize H op) a h h'

theorem iterRel_zero (op : Operation H) (a : V) : IterRel H op a (vempty H) a :=
  thetaG_zero H (totalize H op) a

theorem iterRel_succ (op : Operation H) {a n z : V} (h : IterRel H op a n z) :
    IterRel H op a (vsucc H n) (totalize H op z) :=
  thetaG_succ H (totalize H op) a h.1 h

private def stageNaturalForm (f : Form) : Form :=
  fAll (fImp (iterationForm f 0 1 2 3) (fNatF 0))

private theorem stageNaturalForm_spec (op : Operation H) (n a : V) :
    Sat mem (scons n (scons a op.parameters)) (stageNaturalForm op.graph) ↔
      ∀ z, IterRel H op a n z → mem z (omegaV H) := by
  constructor
  · intro h z hz
    exact (fNatF_spec H _ 0).mp
      (h z ((iterationForm_spec H op _ 0 1 2 3 (fun _ => rfl)).mpr hz))
  · intro h z hz
    exact (fNatF_spec H _ 0).mpr
      (h z ((iterationForm_spec H op _ 0 1 2 3 (fun _ => rfl)).mp hz))

/-- Closure under every internal number of iterations. The induction
predicate is an actual Form, and omega_ind ranges over the entire omega. -/
theorem iterRel_result_nat (op : Operation H) {a n z : V}
    (ha : mem a (omegaV H)) (h : IterRel H op a n z) : mem z (omegaV H) := by
  have hind : ∀ k, mem k (omegaV H) →
      Sat mem (scons k (scons a op.parameters)) (stageNaturalForm op.graph) := by
    apply omega_ind H (stageNaturalForm op.graph) (scons a op.parameters)
    · apply (stageNaturalForm_spec H op (vempty H) a).mpr
      intro z hz
      rw [iterRel_unique H op hz (iterRel_zero H op a)]
      exact ha
    · intro k hk ih
      apply (stageNaturalForm_spec H op (vsucc H k) a).mpr
      intro z hz
      obtain ⟨y,hy⟩ := iterRel_total H op a hk
      have hyNat := (stageNaturalForm_spec H op k a).mp ih y hy
      rw [iterRel_unique H op hz (iterRel_succ H op hy),
        totalize_nat H op ⟨y,hyNat⟩]
      exact (op.toFun ⟨y,hyNat⟩).property
  exact (stageNaturalForm_spec H op n a).mp (hind n h.1) z h

/-- A set-theoretic function value, obtained by definable replacement. -/
noncomputable def iterationValue (op : Operation H) (a n : V) : V :=
  applyV H (recFun H (totalizeForm op.graph) op.parameters (totalize H op)
    (totalizeForm_spec H op) a) n

theorem iterationValue_spec (op : Operation H) (a : V) {n : V}
    (hn : mem n (omegaV H)) : IterRel H op a n (iterationValue H op a n) :=
  recFun_apply_theta H (totalizeForm op.graph) op.parameters (totalize H op)
    (totalizeForm_spec H op) a hn

theorem iterationValue_zero (op : Operation H) (a : V) :
    iterationValue H op a (vempty H)=a :=
  iterRel_unique H op (iterationValue_spec H op a (vempty_in_omega H)) (iterRel_zero H op a)

theorem iterationValue_succ (op : Operation H) (a : V) {n : V}
    (hn : mem n (omegaV H)) :
    iterationValue H op a (vsucc H n)=totalize H op (iterationValue H op a n) :=
  iterRel_unique H op (iterationValue_spec H op a (omega_succ H n hn))
    (iterRel_succ H op (iterationValue_spec H op a hn))

noncomputable def successor (n : Natural H) : Natural H :=
  ⟨vsucc H n.val,omega_succ H n.val n.property⟩

/-- The resulting endofunction has all of internal omega as its length domain. -/
noncomputable def iterate (op : Operation H) (a n : Natural H) : Natural H :=
  ⟨iterationValue H op a.val n.val,
    iterRel_result_nat H op a.property (iterationValue_spec H op a.val n.property)⟩

theorem iterate_spec (op : Operation H) (a n : Natural H) :
    IterRel H op a.val n.val (iterate H op a n).val := iterationValue_spec H op _ n.property

theorem iterate_unique (op : Operation H) (a n z : Natural H) :
    IterRel H op a.val n.val z.val ↔ z=iterate H op a n := by
  constructor
  · intro h
    exact Subtype.ext (iterRel_unique H op h (iterate_spec H op a n))
  · rintro rfl
    exact iterate_spec H op a n

theorem iterate_total_unique (op : Operation H) (a n : Natural H) :
    ∃! z : Natural H, IterRel H op a.val n.val z.val :=
  ⟨iterate H op a n,iterate_spec H op a n,
    fun z hz => (iterate_unique H op a n z).mp hz⟩

theorem iterate_zero (op : Operation H) (a : Natural H) : iterate H op a 0=a :=
  Subtype.ext (iterationValue_zero H op a.val)

theorem iterate_succ (op : Operation H) (a n : Natural H) :
    iterate H op a (successor H n)=op.toFun (iterate H op a n) := by
  apply Subtype.ext
  change iterationValue H op a.val (vsucc H n.val)=_
  rw [iterationValue_succ H op a.val n.property]
  exact totalize_nat H op (iterate H op a n)

theorem successor_numeral (k : ℕ) : successor H (k : Natural H)=(k+1 : ℕ) := by
  apply Subtype.ext
  change vsucc H (natV H k)=natV H (k+1)
  exact (natV_succ H k).symm

/-- Compatibility at standard lengths, with an arbitrary internal seed.
Only this numeral-compatibility theorem uses external Nat induction. -/
theorem iterate_numeral (op : Operation H) (a : Natural H) (k : ℕ) :
    iterate H op a (k : Natural H)=op.toFun^[k] a := by
  induction k with
  | zero => exact iterate_zero H op a
  | succ k ih =>
    rw [show ((k+1 : ℕ) : Natural H)=successor H (k : Natural H) from (successor_numeral H k).symm,
      iterate_succ,ih,Function.iterate_succ_apply']

end DiophantineConsistency.ObjectNaturalIteration
