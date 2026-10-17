import BusyBeaver.ZFC.ArithmeticMachineGraphPerm252
import BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252

set_option autoImplicit false

/-!
Compact fixed arithmetic constants, an explicit finite lookup graph, and the
common forty-bit dispatch frame. The fixed lists below are syntax-construction
data. Arithmetic inputs, lookup index, register values, spare count and gap may
be arbitrary model elements. No actual 6,460-row table or runtime simulation
is certified in this module yet; the companion Python table is untrusted data.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticFiniteControl254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachinePerm252 (bitsCode)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Least-significant-first binary constant. Multiplication by the fixed term
`1+1` uses the recursive child once; doubling by `child+child` would duplicate
that child's syntax. No unary numeral of the denoted integer is constructed. -/
def binaryTerm : List Bool → Semiterm.Const ℒₒᵣ
  | [] => op(0)
  | b :: bs => op(+).comp ![
      op(*).comp ![op(+).comp ![op(1),op(1)],binaryTerm bs],
      if b then op(1) else op(0)]

section Lookup
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

noncomputable def binaryValue : List Bool → V
  | [] => 0
  | b :: bs => 2*binaryValue bs + if b then 1 else 0

/-- External structural induction only; no induction on an internal constant
or an internal register value is used. -/
theorem binaryTerm_val (bs : List Bool) :
    (binaryTerm bs).val (![] : Fin 0 → V) = binaryValue bs := by
  have ht : (1+1 : V) = 2 := by ring
  induction bs with
  | nil => exact Structure.Zero.zero (L := ℒₒᵣ) (M := V)
  | cons b bs ih =>
    cases b <;>
      simp [binaryTerm,binaryValue,Semiterm.Operator.val_comp,
        Matrix.fun_eq_vec_two,ih,ht]

/-- The bit list's denotation is exactly the existing native tape-code value. -/
theorem binaryValue_cast (bs : List Bool) : binaryValue (V := V) bs = (bitsCode bs : V) := by
  induction bs with
  | nil => simp [binaryValue,bitsCode]
  | cons b bs ih =>
    cases b <;>
      simp only [binaryValue,bitsCode,Bool.toNat_false,Bool.toNat_true,Bool.false_eq_true,
        if_false,if_true,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
        Nat.cast_zero,Nat.cast_one,ih] <;> ring

/-- Each key and output is encoded by a finite binary constant term. A branch
input of zero selects zeroValue; every nonzero input selects positiveValue. -/
structure Row where
  key : List Bool
  zeroValue : List Bool
  positiveValue : List Bool
  deriving DecidableEq, Repr

noncomputable def lookupValue : List Row → V → V → V
  | [], _, _ => 0
  | row :: rows, q, branch =>
    if q = binaryValue row.key then
      if branch = 0 then binaryValue row.zeroValue else binaryValue row.positiveValue
    else lookupValue rows q branch

/-- A fixed parameter-free bounded graph, constructed before choosing V.
The default absent row is zero; a genuine halt opcode must remain positive. -/
def lookupDef : List Row → 𝚺₀.Semisentence 3
  | [] => .mkSigma “out q branch. out = 0”
  | row :: rows => .mkSigma
    “out q branch.
      ((q = !!(binaryTerm row.key)) ∧
        ((branch = 0 ∧ out = !!(binaryTerm row.zeroValue)) ∨
         (branch ≠ 0 ∧ out = !!(binaryTerm row.positiveValue)))) ∨
      ((q ≠ !!(binaryTerm row.key)) ∧ !(lookupDef rows) out q branch)”

instance lookup_defined (rows : List Row) :
    𝚺₀-Function₂[V] (lookupValue rows) via lookupDef rows := by
  induction rows with
  | nil => exact .mk fun e => by simp [lookupDef,lookupValue]
  | cons row rows ih =>
    refine .mk fun e => ?_
    classical
    by_cases hq : e 1 = binaryValue row.key
    · by_cases hb : e 2 = 0 <;>
        simp [lookupDef,lookupValue,ih.iff,binaryTerm_val,hq,hb]
    · simp [lookupDef,lookupValue,ih.iff,binaryTerm_val,hq]

/-- Arbitrary internal lookup indices are classified by the fixed finite
external row list. A nonzero opcode supplies the classification witness.
For fields whose legitimate result is zero (including the first PC code),
classification comes from the positive opcode table, not from that field. -/
theorem lookup_supported (rows : List Row) (q branch : V)
    (hn : lookupValue rows q branch ≠ 0) :
    ∃ row ∈ rows, q = binaryValue row.key ∧
      lookupValue rows q branch =
        if branch = 0 then binaryValue row.zeroValue else binaryValue row.positiveValue := by
  induction rows with
  | nil => simp [lookupValue] at hn
  | cons row rows ih =>
    classical
    by_cases hq : q = binaryValue row.key
    · exact ⟨row,by simp,hq,by simp [lookupValue,hq]⟩
    · obtain ⟨other,hm,hkey,hvalue⟩ := ih (by simpa [lookupValue,hq] using hn)
      exact ⟨other,by simp [hm],hkey,by simpa [lookupValue,hq] using hvalue⟩

theorem lookup_absent (rows : List Row) (q branch : V)
    (h : ∀ row ∈ rows, q ≠ binaryValue row.key) : lookupValue rows q branch = 0 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have hq := h row (by simp)
    have ht : ∀ other ∈ rows, q ≠ binaryValue other.key := by
      intro other hm; exact h other (by simp [hm])
    simpa only [lookupValue,if_neg hq] using ih ht

end Lookup

section Frame
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
open ArithmeticMachineUniformScansPerm252 ArithmeticSymbolicTapePerm252
open ArithmeticSymbolicBoxesPerm252 ArithmeticSiteBootPerm252
open ArithmeticSitePerm252 ArithmeticDispatchRebasePerm252

lemma binaryValue_prefix (bs : List Bool) : binaryValue (V := V) bs = bitsPrefix bs 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [binaryValue,bitsPrefix,ih,digit]

/-- Splitting off a fixed finite prefix keeps the entire arbitrary suffix. -/
lemma bitsPrefix_split (bs : List Bool) (suffix : V) :
    bitsPrefix bs suffix = bitsPrefix bs 0 + bitPrefix false (bs.length : V) suffix := by
  induction bs with
  | nil => simp [bitsPrefix]
  | cons b bs ih =>
    rw [bitsPrefix,ih,List.length_cons,Nat.cast_succ,bitPrefix_succ]
    simp only [bitsPrefix,digit,Bool.false_eq_true,if_false]
    ring

/-- A single arithmetic representation for every leaf: the decoder path is
zero padded to forty bits; the remaining gap is an arbitrary model element. -/
noncomputable def frameValue (pc : V) (values : List V) (count gap : V) : V :=
  frame 95 1 (pc + bitPrefix false (40 : V)
    (bitPrefix false gap (2*boxPrefix values count (.plain .unchanged) 0+1)))

/-- No variable-length internal path decoder is needed in the relation.
The external path is used only to certify the corresponding fixed table row. -/
theorem start_fixed_frame (P : List Bool) (hP : P.length ≤ 40)
    (values : List V) (count gap : V) :
    startValue values count gap P = frameValue (binaryValue P) values count gap := by
  have hl : (padded P 40).length = 40 := by
    simp only [padded,List.length_append,List.length_replicate]
    omega
  have hz : bitsPrefix (padded P 40) (0 : V) = binaryValue P := by
    rw [padded,bitsPrefix_append,←bitPrefix_replicate,bitPrefix_false_zero]
    exact (binaryValue_prefix P).symm
  rw [start_format,padded_prefix,bitsPrefix_split,hl,hz]
  rfl

end Frame
end SetTheory.BusyBeaver.ZFC.ArithmeticFiniteControl254
