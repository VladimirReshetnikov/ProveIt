import BusyBeaver.ZFC.ArithmeticControlFile
import BusyBeaver.ZFC.ControlCatalogue
import BusyBeaver.ZFC.ArithmeticControlBisim
import BusyBeaver.ZFC.Permutation252Frame

set_option autoImplicit false

/-!
# The represented control interpreter of a finite row table

For a finite list of catalogue rows (control number `c` is row `c - 1`), fixed
`Σ₀` opcode/register/successor tables built from compact binary constants, one
represented step on the nine-register file of `ArithmeticControlFile`, and the
represented run at every internal time of an `IΣ₁` model. `spec` states the
step in the catalogue-generic form used by `ArithmeticControlBisim` and
`ArithmeticDagRun`.

The interpreter is defined by its table alone. The rows of a decoder tree's
catalogue (`rowOf`, with successor paths resolved by the descent rank of
`ControlCatalogue`) are provided for the comparison with a binary machine,
which executes that tree; the kernel checks such tables as literal data.

The opcode convention, live encoding and physical register map `physOf` are
those of the Codex lane's Prog254 interpreter `ArithmeticControlStep254`, whose
construction this module generalizes from one fixed tree to every table.
-/

namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlTable

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

variable (t : Tree)

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

end Catalogue

/-! ## The represented tables and step -/

section Arithmetic

variable (rl : List ArithmeticControlBisim.Row)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

def opRows : List (Nat × Nat) := rl.map fun r => (r.op, r.op)
def regRows : List (Nat × Nat) := rl.map fun r => (r.reg.val, r.reg.val)
/-- Only a test (opcode 2) distinguishes its two successors. -/
def nextRows : List (Nat × Nat) :=
  rl.map fun r => if r.op = 2 then (r.next0, r.next1) else (r.next0, r.next0)

noncomputable def opcodeValue (q : V) : V := lookupValue (compactRows 0 (opRows rl)) q 0
def opcodeDef : 𝚺₀.Semisentence 2 := .mkSigma
  “output control. !(lookupDef (compactRows 0 (opRows rl))) output control 0”
instance opcode_defined : 𝚺₀-Function₁[V] (opcodeValue rl) via opcodeDef rl :=
  .mk fun e => by simp [opcodeDef, opcodeValue, (lookup_defined (compactRows 0 (opRows rl))).iff]

noncomputable def registerKeyValue (q : V) : V := lookupValue (compactRows 0 (regRows rl)) q 0
def registerKeyDef : 𝚺₀.Semisentence 2 := .mkSigma
  “out q. !(lookupDef (compactRows 0 (regRows rl))) out q 0”
instance registerKey_defined : 𝚺₀-Function₁[V] (registerKeyValue rl) via registerKeyDef rl :=
  .mk fun e => by
    simp [registerKeyDef, registerKeyValue, (lookup_defined (compactRows 0 (regRows rl))).iff]

noncomputable def nextValue (q branch : V) : V := lookupValue (compactRows 0 (nextRows rl)) q branch
def nextDef : 𝚺₀.Semisentence 3 := lookupDef (compactRows 0 (nextRows rl))
instance next_defined : 𝚺₀-Function₂[V] (nextValue rl) via nextDef rl := lookup_defined _

variable {rl}

theorem opcodeValue_at (i : Nat) (hi : i < rl.length) :
    opcodeValue rl ((i + 1 : Nat) : V) = ((rl[i]'hi).op : V) := by
  have h := compact_lookup_at (V := V) (opRows rl) 0 i (by simpa [opRows] using hi) 0
  simpa [opcodeValue, opRows] using h

theorem registerKey_at (i : Nat) (hi : i < rl.length) :
    registerKeyValue rl ((i + 1 : Nat) : V) = ((rl[i]'hi).reg.val : V) := by
  have h := compact_lookup_at (V := V) (regRows rl) 0 i (by simpa [regRows] using hi) 0
  simpa [registerKeyValue, regRows] using h

theorem next_at (i : Nat) (hi : i < rl.length) (branch : V) :
    nextValue rl ((i + 1 : Nat) : V) branch =
      if branch = 0 then ((rl[i]'hi).next0 : V) else
        (((if (rl[i]'hi).op = 2 then (rl[i]'hi).next1 else (rl[i]'hi).next0) : Nat) : V) := by
  have h := compact_lookup_at (V := V) (nextRows rl) 0 i (by simpa [nextRows] using hi) branch
  rw [nextValue]
  simp only [Nat.zero_add] at h
  rw [h]
  simp only [nextRows, List.getElem_map]
  split_ifs <;> rfl

variable (rl)

/-- One represented step; opcode conventions as in `ArithmeticControlStep254`. -/
noncomputable def transitionValue (control file : V) : V :=
  if opcodeValue rl control = 1 ∨ opcodeValue rl control = 2 ∨ opcodeValue rl control = 3 then
    liveValue (nextValue rl control (selectedValue file (registerKeyValue rl control)))
      (effectValue (opcodeValue rl control) (registerKeyValue rl control) file)
  else 0

def transitionDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out control file. ∃ opcode, !(opcodeDef rl) opcode control ∧
    ∃ index, !(registerKeyDef rl) index control ∧
    ∃ selected, !selectedDef selected file index ∧
    (((opcode = 1 ∨ opcode = 2 ∨ opcode = 3) ∧
       ∃ next, !(nextDef rl) next control selected ∧
       ∃ nextFile, !effectDef nextFile opcode index file ∧
       !liveDef out next nextFile) ∨
     (opcode ≠ 1 ∧ opcode ≠ 2 ∧ opcode ≠ 3 ∧ out = 0))”

instance transition_defined :
    𝚺₁-Function₂[V] (transitionValue rl) via transitionDef rl := .mk fun e => by
  classical
  by_cases h1 : opcodeValue rl (e 1) = 1
  · simp [transitionDef, transitionValue, h1, (opcode_defined rl).iff,
      (registerKey_defined rl).iff, (next_defined rl).iff, effect_defined.iff,
      live_defined.iff, selected_defined.iff]
  · by_cases h2 : opcodeValue rl (e 1) = 2
    · simp [transitionDef, transitionValue, h2, (opcode_defined rl).iff,
        (registerKey_defined rl).iff, (next_defined rl).iff, effect_defined.iff,
        live_defined.iff, selected_defined.iff]
    · by_cases h3 : opcodeValue rl (e 1) = 3
      · simp [transitionDef, transitionValue, h3, (opcode_defined rl).iff,
          (registerKey_defined rl).iff, (next_defined rl).iff, effect_defined.iff,
          live_defined.iff, selected_defined.iff]
      · simp [transitionDef, transitionValue, h1, h2, h3, (opcode_defined rl).iff,
          (registerKey_defined rl).iff, selected_defined.iff]

noncomputable def stepValue (state : V) : V :=
  if state = 0 then 0 else transitionValue rl (controlValue state) (fileCodeValue state)

def stepDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out state. (state = 0 ∧ out = 0) ∨
    (state ≠ 0 ∧ ∃ control, !controlDef control state ∧
      ∃ file, !fileCodeDef file state ∧ !(transitionDef rl) out control file)”

instance step_defined : 𝚺₁-Function₁[V] (stepValue rl) via stepDef rl := .mk fun e => by
  classical
  by_cases hs : e 1 = 0 <;>
    simp [stepDef, stepValue, hs, control_defined.iff, fileCode_defined.iff,
      (transition_defined rl).iff]

@[simp] theorem step_zero : stepValue rl (0 : V) = 0 := by simp [stepValue]

theorem step_live (q file : V) :
    stepValue rl (liveValue q file) = transitionValue rl q file := by
  simp [stepValue]

end Arithmetic

/-! ## The represented run -/

section Run

variable (rl : List ArithmeticControlBisim.Row)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def zeroDef : 𝚺₁.Semisentence 2 := .mkSigma “out initial. out = initial”
def succDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index initial. !(stepDef rl) out previous”
def blueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := succDef rl
noncomputable def construction : PR.Construction V (blueprint rl) where
  zero parameters := parameters 0
  succ _ _ previous := stepValue rl previous
  zero_defined := .mk fun e => by simp [blueprint, zeroDef]
  succ_defined := .mk fun e => by simp [blueprint, succDef, (step_defined rl).iff]

noncomputable def controlRun (time initial : V) : V :=
  (construction rl).result ![initial] time
def controlRunDef : 𝚺₁.Semisentence 3 := (blueprint rl).resultDef

instance controlRun_defined :
    𝚺₁-Function₂[V] (controlRun rl) via controlRunDef rl := .mk fun e => by
  have he : (fun i : Fin 1 => e i.succ.succ) = ![e 2] := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have h := (construction rl (V := V)).result_defined.df e
  change (blueprint rl).resultDef.val.Evalb e ↔
    e 0 = (construction rl).result (fun i : Fin 1 => e i.succ.succ) (e 1) at h
  rw [he] at h
  change (blueprint rl).resultDef.val.Evalb e ↔ e 0 = (construction rl).result ![e 2] (e 1)
  exact h

instance controlRun_definable : 𝚺₁-Function₂[V] (controlRun rl) :=
  (controlRun_defined rl).to_definable

@[simp] theorem controlRun_zero (initial : V) : controlRun rl 0 initial = initial := by
  simp [controlRun, construction]

@[simp] theorem controlRun_succ (time initial : V) :
    controlRun rl (time+1) initial = stepValue rl (controlRun rl time initial) := by
  simp [controlRun, PR.Construction.result_succ, construction]

theorem controlRun_add (firstTime secondTime initial : V) :
    controlRun rl (firstTime+secondTime) initial =
      controlRun rl secondTime (controlRun rl firstTime initial) := by
  induction secondTime using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ secondTime ih => rw [← add_assoc, controlRun_succ, controlRun_succ, ih]

@[simp] theorem controlRun_halted (time : V) : controlRun rl time 0 = 0 := by
  induction time using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact controlRun_zero rl 0
  case succ time ih => rw [controlRun_succ, ih, step_zero]

theorem controlRun_one (x : V) : controlRun rl 1 x = stepValue rl x := by
  simpa using controlRun_succ rl (0 : V) x

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
    (hnext : ∀ b : V, nxt b = if b = 0 then (row.next0 : V) else
      (((if row.op = 2 then row.next1 else row.next0) : Nat) : V)) (x : V) :
    (if o = 1 ∨ o = 2 ∨ o = 3 then
      liveValue (nxt (selectedValue x k)) (effectValue o k x)
    else 0) = ArithmeticControlBisim.sem regValue write liveValue row x := by
  subst hop hreg
  have hsel : selectedValue x (row.reg.val : V) = regValue x row.reg := selected_at x row.reg
  unfold ArithmeticControlBisim.sem effectValue
  simp only [hsel, hnext, cast_eq_one_iff, cast_eq_two_iff, cast_eq_three_iff, write]
  rcases row with ⟨op, r, n0, n1⟩
  simp only at hnext ⊢
  by_cases h1 : op = 1
  · subst h1
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
    simp
  · simp [h1, h2, h3]

theorem successor_same (t : Tree) (P : List Bool) (e : Edge)
    (h : edgeOpcode e = 1 ∨ edgeOpcode e = 3) :
    successorOf t P e false = successorOf t P e true := by
  cases e <;> simp_all [edgeOpcode, successorOf, outgoingPathOf]

/-- Row lookup by control number (control `c` is row `c - 1`). -/
def rows (rl : List ArithmeticControlBisim.Row) (c : Nat) : Option ArithmeticControlBisim.Row :=
  if c = 0 then none else (BT.ofList rl).get (c - 1)

/-- The step equation at a row given by list position (control `c` is row `c - 1`). -/
theorem spec_get (rl : List ArithmeticControlBisim.Row) (c : Nat) (row : ArithmeticControlBisim.Row)
    (x : V) (hc : c ≠ 0) (h : rl[c - 1]? = some row) :
    stepValue rl (liveValue (c : V) x) =
      ArithmeticControlBisim.sem regValue write liveValue row x := by
  have hlt : c - 1 < rl.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at h
    cases h
  rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at h
  subst h
  have hc' : ((c : Nat) : V) = ((c - 1 + 1 : Nat) : V) := by congr 1; omega
  rw [hc', step_live]
  exact transition_generic _ _ _ _ (opcodeValue_at (c - 1) hlt) (registerKey_at (c - 1) hlt)
    (next_at (c - 1) hlt) x

/-- The step equation consumed by the internal bisimulation and structured runs. -/
theorem spec (rl : List ArithmeticControlBisim.Row) (c : Nat) (row : ArithmeticControlBisim.Row)
    (x : V) (h : rows rl c = some row) :
    stepValue rl (liveValue (c : V) x) =
      ArithmeticControlBisim.sem regValue write liveValue row x := by
  unfold rows at h
  split_ifs at h with hc
  rw [BT.get_ofList] at h
  have hlt : c - 1 < rl.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at h
    cases h
  rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at h
  subst h
  have hc' : ((c : Nat) : V) = ((c - 1 + 1 : Nat) : V) := by congr 1; omega
  rw [hc', step_live]
  exact transition_generic _ _ _ _ (opcodeValue_at (c - 1) hlt) (registerKey_at (c - 1) hlt)
    (next_at (c - 1) hlt) x

end Spec

end SetTheory.BusyBeaver.ZFC.ArithmeticControlTable
