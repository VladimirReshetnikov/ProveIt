import BusyBeaver.ZFC.ArithmeticControlFile
import BusyBeaver.ZFC.ControlCatalogue
import BusyBeaver.ZFC.ArithmeticControlBisim
import BusyBeaver.ZFC.Permutation252Frame

set_option autoImplicit false

/-!
# The represented control interpreter of a decoder tree

For a decoder tree `t` with `n` instruction leaves, its control catalogue
(false-first leaf order), fixed `Σ₀` opcode/register/successor tables built
from compact binary constants, one represented step on the nine-register file
of `ArithmeticControlFile`, and the represented run at every internal time of an
`IΣ₁` model. Successor paths are resolved by the descent rank of
`ControlCatalogue`. `spec` states the step in the catalogue-generic form used by
`ArithmeticControlBisim`, for every tree without missing subtrees.

The opcode convention, live encoding and physical register map `physOf` are
those of the Codex lane's Prog254 interpreter `ArithmeticControlStep254`, whose
construction this module generalizes from one fixed tree to every tree.
-/

namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlTree

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open RegisterPath RMBisim ControlCatalogue ArithmeticCantor
open ArithmeticControlFile

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-! ## Compact constant lookups -/

/-- Least-significant-first binary constant (one recursive child per bit). -/
def binaryTerm : List Bool → Semiterm.Const ℒₒᵣ
  | [] => op(0)
  | b :: bs => op(+).comp ![
      op(*).comp ![op(+).comp ![op(1),op(1)],binaryTerm bs],
      if b then op(1) else op(0)]

def bitsNat : List Bool → Nat
  | [] => 0
  | b :: bs => 2 * bitsNat bs + if b then 1 else 0

def natBits (n : Nat) : List Bool :=
  if n = 0 then [] else decide (n % 2 = 1) :: natBits (n / 2)
termination_by n
decreasing_by omega

theorem bitsNat_natBits (n : Nat) : bitsNat (natBits n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; rw [natBits, if_pos rfl]; rfl
    · rw [natBits, if_neg hn, bitsNat, ih (n / 2) (by omega)]
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega

structure LRow where
  key : List Bool
  zeroValue : List Bool
  positiveValue : List Bool

def compactRows : Nat → List (Nat × Nat) → List LRow
  | _, [] => []
  | first, row :: rows =>
      ⟨natBits (first+1), natBits row.1, natBits row.2⟩ :: compactRows (first+1) rows

section Lookup

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

noncomputable def binaryValue : List Bool → V
  | [] => 0
  | b :: bs => 2 * binaryValue bs + if b then 1 else 0

theorem binaryTerm_val (bs : List Bool) :
    (binaryTerm bs).val (![] : Fin 0 → V) = binaryValue bs := by
  have ht : (1+1 : V) = 2 := by ring
  induction bs with
  | nil => exact Structure.Zero.zero (L := ℒₒᵣ) (M := V)
  | cons b bs ih =>
    cases b <;>
      simp [binaryTerm, binaryValue, Semiterm.Operator.val_comp, Matrix.fun_eq_vec_two, ih, ht]

theorem binaryValue_cast (bs : List Bool) : binaryValue (V := V) bs = (bitsNat bs : V) := by
  induction bs with
  | nil => simp [binaryValue, bitsNat]
  | cons b bs ih => cases b <;> simp [binaryValue, bitsNat, ih]

theorem binaryValue_natBits (n : Nat) : binaryValue (V := V) (natBits n) = (n : V) := by
  rw [binaryValue_cast, bitsNat_natBits]

noncomputable def lookupValue : List LRow → V → V → V
  | [], _, _ => 0
  | row :: rows, q, branch =>
    if q = binaryValue row.key then
      if branch = 0 then binaryValue row.zeroValue else binaryValue row.positiveValue
    else lookupValue rows q branch

def lookupDef : List LRow → 𝚺₀.Semisentence 3
  | [] => .mkSigma “out q branch. out = 0”
  | row :: rows => .mkSigma
    “out q branch.
      ((q = !!(binaryTerm row.key)) ∧
        ((branch = 0 ∧ out = !!(binaryTerm row.zeroValue)) ∨
         (branch ≠ 0 ∧ out = !!(binaryTerm row.positiveValue)))) ∨
      ((q ≠ !!(binaryTerm row.key)) ∧ !(lookupDef rows) out q branch)”

instance lookup_defined (rows : List LRow) :
    𝚺₀-Function₂[V] (lookupValue rows) via lookupDef rows := by
  induction rows with
  | nil => exact .mk fun e => by simp [lookupDef, lookupValue]
  | cons row rows ih =>
    refine .mk fun e => ?_
    classical
    by_cases hq : e 1 = binaryValue row.key
    · by_cases hb : e 2 = 0 <;> simp [lookupDef, lookupValue, ih.iff, binaryTerm_val, hq, hb]
    · simp [lookupDef, lookupValue, ih.iff, binaryTerm_val, hq]

theorem compact_lookup_at (rows : List (Nat × Nat)) (first i : Nat) (hi : i < rows.length)
    (branch : V) :
    lookupValue (compactRows first rows) ((first+i+1 : Nat) : V) branch =
      if branch = 0 then ((rows[i]'hi).1 : V) else ((rows[i]'hi).2 : V) := by
  induction rows generalizing first i with
  | nil => simp at hi
  | cons row rows ih =>
    classical
    cases i with
    | zero =>
      simp only [compactRows, lookupValue, binaryValue_natBits, Nat.add_zero, if_true,
        List.getElem_cons_zero]
    | succ i =>
      have hlt : ((first+1 : Nat) : V) < ((first+(i+1)+1 : Nat) : V) :=
        (Nat.cast_lt (α := V)).mpr (by omega)
      have hne : ((first+(i+1)+1 : Nat) : V) ≠ ((first+1 : Nat) : V) := ne_of_gt hlt
      simp only [compactRows, lookupValue, binaryValue_natBits, if_neg hne,
        List.getElem_cons_succ]
      have hi' : i < rows.length := Nat.lt_of_succ_lt_succ (by
        simpa only [List.length_cons] using hi)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (first+1) i hi'

theorem compact_lookup_supported (rows : List (Nat × Nat)) (first : Nat) (q branch : V)
    (hn : lookupValue (compactRows first rows) q branch ≠ 0) :
    ∃ i, i < rows.length ∧ q = ((first+i+1 : Nat) : V) := by
  induction rows generalizing first with
  | nil => simp [compactRows, lookupValue] at hn
  | cons row rows ih =>
    classical
    by_cases hq : q = ((first+1 : Nat) : V)
    · exact ⟨0, by simp, by simpa using hq⟩
    · have hq' : q ≠ binaryValue (natBits (first+1)) := by rwa [binaryValue_natBits]
      obtain ⟨i, hi, he⟩ := ih (first+1) (by
        simpa only [compactRows, lookupValue, if_neg hq'] using hn)
      exact ⟨i+1, by simpa using hi, by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he⟩

end Lookup

/-! ## The catalogue of a tree -/

section Catalogue

variable (t : Tree) (n : Nat)

/-- Structural list access. -/
def nth : List (List Bool × Edge) → Nat → Option (List Bool × Edge)
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, k+1 => nth xs k

theorem nth_eq (l : List (List Bool × Edge)) (i : Nat) : nth l i = l[i]? := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i <;> simp [nth, ih]

/-- Leaf `i` (total; the default is never used in range). -/
def source (i : Nat) : List Bool × Edge := (nth (leafEntries t) i).getD ([], .halt)

def edgeOpcode : Edge → Nat
  | .node _ => 0
  | .inc _ => 1
  | .decnz _ => 2
  | .brk _ | .cont _ => 3
  | .halt => 4

def outgoingPathOf (P : List Bool) (e : Edge) (positive : Bool) : List Bool :=
  match e with
  | .node _ | .halt => P
  | .inc _ => incPath P
  | .decnz _ => if positive then incPath P else breakPath 1 P
  | .brk k => breakPath k P
  | .cont k => continuePath k P

def registerOf (e : Edge) : Nat :=
  match e with
  | .inc r | .decnz r => Permutation252Frame.physOf r
  | _ => 0

theorem physOf_lt (r : Nat) : Permutation252Frame.physOf r < 9 := by
  unfold Permutation252Frame.physOf
  split <;> omega

theorem registerOf_lt (e : Edge) : registerOf e < 9 := by
  cases e <;> simp only [registerOf] <;> first | exact physOf_lt _ | omega

/-- Successor control number of a leaf (zero only for halt and decoder nodes). -/
def successorOf (P : List Bool) (e : Edge) (positive : Bool) : Nat :=
  match e with
  | .node _ | .halt => 0
  | _ => crank (annotate t) (outgoingPathOf P e positive) + 1

def rowOf (entry : List Bool × Edge) : ArithmeticControlBisim.Row :=
  ⟨edgeOpcode entry.2, ⟨registerOf entry.2, registerOf_lt _⟩,
    successorOf t entry.1 entry.2 false, successorOf t entry.1 entry.2 true⟩

/-- Fast external row table: control number `c` is leaf `c - 1`. -/
def rows (c : Nat) : Option ArithmeticControlBisim.Row :=
  if c = 0 then none else (BT.ofList ((leafEntries t).map (rowOf t))).get (c - 1)

def sourceOpcode (i : Fin n) : Nat := edgeOpcode (source t i).2
def sourceRegister (i : Fin n) : Nat := registerOf (source t i).2
def successorNumber (i : Fin n) (positive : Bool) : Nat :=
  successorOf t (source t i).1 (source t i).2 positive

theorem rows_some (hlen : (leafEntries t).length = n) (c : Nat)
    (row : ArithmeticControlBisim.Row) (h : rows t c = some row) :
    ∃ i : Fin n, c = i.val + 1 ∧ row = rowOf t (source t i) := by
  unfold rows at h
  split_ifs at h with hc
  rw [BT.get_ofList, List.getElem?_map] at h
  have hlt : c - 1 < (leafEntries t).length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at h
    cases h
  rw [List.getElem?_eq_getElem hlt] at h
  have hi : c - 1 < n := hlen ▸ hlt
  refine ⟨⟨c - 1, hi⟩, by simp only; omega, ?_⟩
  simp only [Option.map_some, Option.some.injEq] at h
  simp only [source, nth_eq, List.getElem?_eq_getElem hlt, Option.getD_some]
  exact h.symm

end Catalogue

/-! ## The represented tables and step -/

section Arithmetic

variable (t : Tree) (n : Nat)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

def fieldRows (zero positive : Fin n → Nat) : List (Nat × Nat) :=
  List.ofFn (fun i : Fin n => (zero i, positive i))

noncomputable def fieldValue (zero positive : Fin n → Nat) (q branch : V) : V :=
  lookupValue (compactRows 0 (fieldRows n zero positive)) q branch

def fieldDef (zero positive : Fin n → Nat) : 𝚺₀.Semisentence 3 :=
  lookupDef (compactRows 0 (fieldRows n zero positive))

instance field_defined (zero positive : Fin n → Nat) :
    𝚺₀-Function₂[V] (fieldValue n zero positive) via fieldDef n zero positive :=
  lookup_defined _

theorem fieldValue_at (zero positive : Fin n → Nat) (i : Fin n) (branch : V) :
    fieldValue n zero positive ((i.val + 1 : Nat) : V) branch =
      if branch = 0 then (zero i : V) else (positive i : V) := by
  have h := compact_lookup_at (V := V) (fieldRows n zero positive) 0 i.val
    (by simpa only [fieldRows, List.length_ofFn] using i.isLt) branch
  rw [fieldValue]
  simpa only [fieldRows, List.getElem_ofFn, Nat.zero_add, Fin.eta] using h

noncomputable def opcodeValue (q : V) : V := fieldValue n (sourceOpcode t n) (sourceOpcode t n) q 0
def opcodeDef : 𝚺₀.Semisentence 2 := .mkSigma
  “output control. !(fieldDef n (sourceOpcode t n) (sourceOpcode t n)) output control 0”
instance opcode_defined : 𝚺₀-Function₁[V] (opcodeValue t n) via opcodeDef t n :=
  .mk fun e => by
    simp [opcodeDef, opcodeValue, (field_defined n (sourceOpcode t n) (sourceOpcode t n)).iff]

noncomputable def registerKeyValue (q : V) : V :=
  fieldValue n (sourceRegister t n) (sourceRegister t n) q 0
def registerKeyDef : 𝚺₀.Semisentence 2 := .mkSigma
  “out q. !(fieldDef n (sourceRegister t n) (sourceRegister t n)) out q 0”
instance registerKey_defined : 𝚺₀-Function₁[V] (registerKeyValue t n) via registerKeyDef t n :=
  .mk fun e => by
    simp [registerKeyDef, registerKeyValue,
      (field_defined n (sourceRegister t n) (sourceRegister t n)).iff]

noncomputable def nextValue (q branch : V) : V :=
  fieldValue n (fun i => successorNumber t n i false) (fun i => successorNumber t n i true) q branch
def nextDef : 𝚺₀.Semisentence 3 :=
  fieldDef n (fun i => successorNumber t n i false) (fun i => successorNumber t n i true)
instance next_defined : 𝚺₀-Function₂[V] (nextValue t n) via nextDef t n := field_defined n _ _

theorem opcodeValue_at (i : Fin n) :
    opcodeValue t n ((i.val + 1 : Nat) : V) = (sourceOpcode t n i : V) := by
  simp only [opcodeValue, fieldValue_at, ite_self]

theorem registerKey_at (i : Fin n) :
    registerKeyValue t n ((i.val + 1 : Nat) : V) = (sourceRegister t n i : V) := by
  simp only [registerKeyValue, fieldValue_at, ite_self]

theorem next_at (i : Fin n) (branch : V) : nextValue t n ((i.val + 1 : Nat) : V) branch =
    if branch = 0 then (successorNumber t n i false : V) else (successorNumber t n i true : V) :=
  fieldValue_at n _ _ i branch

/-- One represented step; opcode conventions as in `ArithmeticControlStep254`. -/
noncomputable def transitionValue (control file : V) : V :=
  if opcodeValue t n control = 1 ∨ opcodeValue t n control = 2 ∨ opcodeValue t n control = 3 then
    liveValue (nextValue t n control (selectedValue file (registerKeyValue t n control)))
      (effectValue (opcodeValue t n control) (registerKeyValue t n control) file)
  else 0

def transitionDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out control file. ∃ opcode, !(opcodeDef t n) opcode control ∧
    ∃ index, !(registerKeyDef t n) index control ∧
    ∃ selected, !selectedDef selected file index ∧
    (((opcode = 1 ∨ opcode = 2 ∨ opcode = 3) ∧
       ∃ next, !(nextDef t n) next control selected ∧
       ∃ nextFile, !effectDef nextFile opcode index file ∧
       !liveDef out next nextFile) ∨
     (opcode ≠ 1 ∧ opcode ≠ 2 ∧ opcode ≠ 3 ∧ out = 0))”

instance transition_defined :
    𝚺₁-Function₂[V] (transitionValue t n) via transitionDef t n := .mk fun e => by
  classical
  by_cases h1 : opcodeValue t n (e 1) = 1
  · simp [transitionDef, transitionValue, h1, (opcode_defined t n).iff,
      (registerKey_defined t n).iff, (next_defined t n).iff, effect_defined.iff,
      live_defined.iff, selected_defined.iff]
  · by_cases h2 : opcodeValue t n (e 1) = 2
    · simp [transitionDef, transitionValue, h2, (opcode_defined t n).iff,
        (registerKey_defined t n).iff, (next_defined t n).iff, effect_defined.iff,
        live_defined.iff, selected_defined.iff]
    · by_cases h3 : opcodeValue t n (e 1) = 3
      · simp [transitionDef, transitionValue, h3, (opcode_defined t n).iff,
          (registerKey_defined t n).iff, (next_defined t n).iff, effect_defined.iff,
          live_defined.iff, selected_defined.iff]
      · simp [transitionDef, transitionValue, h1, h2, h3, (opcode_defined t n).iff,
          (registerKey_defined t n).iff, selected_defined.iff]

noncomputable def stepValue (state : V) : V :=
  if state = 0 then 0 else transitionValue t n (controlValue state) (fileCodeValue state)

def stepDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out state. (state = 0 ∧ out = 0) ∨
    (state ≠ 0 ∧ ∃ control, !controlDef control state ∧
      ∃ file, !fileCodeDef file state ∧ !(transitionDef t n) out control file)”

instance step_defined : 𝚺₁-Function₁[V] (stepValue t n) via stepDef t n := .mk fun e => by
  classical
  by_cases hs : e 1 = 0 <;>
    simp [stepDef, stepValue, hs, control_defined.iff, fileCode_defined.iff,
      (transition_defined t n).iff]

@[simp] theorem step_zero : stepValue t n (0 : V) = 0 := by simp [stepValue]

theorem step_live (q file : V) :
    stepValue t n (liveValue q file) = transitionValue t n q file := by
  simp [stepValue]

end Arithmetic

/-! ## The represented run -/

section Run

variable (t : Tree) (n : Nat)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def zeroDef : 𝚺₁.Semisentence 2 := .mkSigma “out initial. out = initial”
def succDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index initial. !(stepDef t n) out previous”
def blueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := succDef t n
noncomputable def construction : PR.Construction V (blueprint t n) where
  zero parameters := parameters 0
  succ _ _ previous := stepValue t n previous
  zero_defined := .mk fun e => by simp [blueprint, zeroDef]
  succ_defined := .mk fun e => by simp [blueprint, succDef, (step_defined t n).iff]

noncomputable def controlRun (time initial : V) : V :=
  (construction t n).result ![initial] time
def controlRunDef : 𝚺₁.Semisentence 3 := (blueprint t n).resultDef

instance controlRun_defined :
    𝚺₁-Function₂[V] (controlRun t n) via controlRunDef t n := .mk fun e => by
  have he : (fun i : Fin 1 => e i.succ.succ) = ![e 2] := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have h := (construction t n (V := V)).result_defined.df e
  change (blueprint t n).resultDef.val.Evalb e ↔
    e 0 = (construction t n).result (fun i : Fin 1 => e i.succ.succ) (e 1) at h
  rw [he] at h
  change (blueprint t n).resultDef.val.Evalb e ↔ e 0 = (construction t n).result ![e 2] (e 1)
  exact h

instance controlRun_definable : 𝚺₁-Function₂[V] (controlRun t n) :=
  (controlRun_defined t n).to_definable

@[simp] theorem controlRun_zero (initial : V) : controlRun t n 0 initial = initial := by
  simp [controlRun, construction]

@[simp] theorem controlRun_succ (time initial : V) :
    controlRun t n (time+1) initial = stepValue t n (controlRun t n time initial) := by
  simp [controlRun, PR.Construction.result_succ, construction]

theorem controlRun_add (firstTime secondTime initial : V) :
    controlRun t n (firstTime+secondTime) initial =
      controlRun t n secondTime (controlRun t n firstTime initial) := by
  induction secondTime using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ secondTime ih => rw [← add_assoc, controlRun_succ, controlRun_succ, ih]

@[simp] theorem controlRun_halted (time : V) : controlRun t n time 0 = 0 := by
  induction time using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact controlRun_zero t n 0
  case succ time ih => rw [controlRun_succ, ih, step_zero]

theorem controlRun_one (x : V) : controlRun t n 1 x = stepValue t n x := by
  simpa using controlRun_succ t n (0 : V) x

end Run

/-! ## The catalogue-generic step equation -/

section Spec

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Register write in the generic interface. -/
noncomputable def write (p : Fin 9) (v x : V) : V := writeValue (p.val : V) v x

theorem file_ext (x y : V) (h : ∀ i, regValue x i = regValue y i) : x = y := by
  rw [← file_reg x, ← file_reg y]
  exact congrArg fileValue (funext h)

theorem reg_write_same (p : Fin 9) (v x : V) : regValue (write p v x) p = v := by
  simp [write]

theorem reg_write_other (p q : Fin 9) (v x : V) (h : p ≠ q) :
    regValue (write p v x) q = regValue x q := by
  have hn : (p.val : V) ≠ (q.val : V) := by
    intro he; exact h (Fin.ext (by simpa only [Nat.cast_inj] using he))
  simp [write, hn]

theorem write_same (p : Fin 9) (x : V) : write p (regValue x p) x = x := by
  apply file_ext
  intro q
  by_cases h : p = q
  · subst h; exact reg_write_same _ _ _
  · exact reg_write_other _ _ _ _ h

theorem cast_eq_one_iff (k : Nat) : ((k : Nat) : V) = 1 ↔ k = 1 := by
  rw [← Nat.cast_one, Nat.cast_inj]

theorem cast_eq_two_iff (k : Nat) : ((k : Nat) : V) = 2 ↔ k = 2 := by
  rw [show (2 : V) = ((2 : Nat) : V) by simp, Nat.cast_inj]

theorem cast_eq_three_iff (k : Nat) : ((k : Nat) : V) = 3 ↔ k = 3 := by
  rw [show (3 : V) = ((3 : Nat) : V) by simp, Nat.cast_inj]

/-- The unfolded transition at a known catalogue row. -/
theorem transition_generic (row : ArithmeticControlBisim.Row) (o k : V) (nxt : V → V)
    (hop : o = (row.op : V)) (hreg : k = (row.reg.val : V))
    (hnext : ∀ b : V, nxt b = if b = 0 then (row.next0 : V) else (row.next1 : V))
    (hsame : row.op = 1 ∨ row.op = 3 → row.next0 = row.next1) (x : V) :
    (if o = 1 ∨ o = 2 ∨ o = 3 then
      liveValue (nxt (selectedValue x k)) (effectValue o k x)
    else 0) = ArithmeticControlBisim.sem regValue write liveValue row x := by
  subst hop hreg
  have hsel : selectedValue x (row.reg.val : V) = regValue x row.reg := selected_at x row.reg
  unfold ArithmeticControlBisim.sem effectValue
  simp only [hsel, hnext, cast_eq_one_iff, cast_eq_two_iff, cast_eq_three_iff, write]
  rcases row with ⟨op, r, n0, n1⟩
  simp only at hsame ⊢
  by_cases h1 : op = 1
  · subst h1
    have hs := hsame (.inl rfl)
    subst hs
    simp
  by_cases h2 : op = 2
  · subst h2
    by_cases hz : regValue x r = 0
    · have hw : writeValue (r.val : V) 0 x = x := by
        rw [← hz]; exact write_same r x
      simp [hz, hw]
    · simp [hz]
  by_cases h3 : op = 3
  · subst h3
    have hs := hsame (.inr rfl)
    subst hs
    simp
  · simp [h1, h2, h3]

theorem successor_same (t : Tree) (P : List Bool) (e : Edge)
    (h : edgeOpcode e = 1 ∨ edgeOpcode e = 3) :
    successorOf t P e false = successorOf t P e true := by
  cases e <;> simp_all [edgeOpcode, successorOf, outgoingPathOf]

/-- The step equation consumed by the internal bisimulation. -/
theorem spec (t : Tree) (n : Nat) (hlen : (leafEntries t).length = n)
    (c : Nat) (row : ArithmeticControlBisim.Row) (x : V) (h : rows t c = some row) :
    stepValue t n (liveValue (c : V) x) =
      ArithmeticControlBisim.sem regValue write liveValue row x := by
  obtain ⟨i, rfl, rfl⟩ := rows_some t n hlen c row h
  rw [step_live]
  exact transition_generic _ _ _ _ (opcodeValue_at t n i) (registerKey_at t n i) (next_at t n i)
    (successor_same t (source t i).1 (source t i).2) x

end Spec

end SetTheory.BusyBeaver.ZFC.ArithmeticControlTree
