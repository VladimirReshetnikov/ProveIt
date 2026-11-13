module
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Machine.PAInternalPhysicalFrame
public import PA196.Arithmetic.Machine.EndpointInternalCarryNatBridge
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.FixedTrace
open M6 PA196.Arithmetic.Machine.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def fixedFileGraph : List Nat → 𝚺ᴬ₁.Semisentence 1
  | [] => .mkSigma “y. y=0”
  | x::xs => .mkSigma “y. ∃ tail, !(fixedFileGraph xs) tail ∧ !adjoinDef y ↑x tail”
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def fixedFile : List Nat → V
  | [] => 0
  | x::xs => (x : V) ∷ fixedFile xs

lemma fixedFile_correct (xs : List Nat) (v : Fin 1 → V) :
    (V ⊧/v (fixedFileGraph xs).val) ↔ v 0=fixedFile xs := by
  induction xs generalizing v with
  | nil => simp [fixedFileGraph,fixedFile]
  | cons x xs ih => simp [fixedFileGraph,fixedFile,ih,adjoin_defined.df,numeral_eq_natCast]

lemma fixedFile_length (xs : List Nat) : len (fixedFile (V := V) xs)=(xs.length : V) := by
  induction xs with
  | nil => simp [fixedFile]
  | cons x xs ih => simp [fixedFile,ih]

lemma fixedFile_nth (xs : List Nat) (i : Nat) :
    (fixedFile (V := V) xs).[(i : V)]=(xs.getD i 0 : V) := by
  induction xs generalizing i with
  | nil => simp [fixedFile]
  | cons x xs ih =>
    cases i with
    | zero => simp [fixedFile]
    | succ i => simpa [fixedFile,Nat.cast_add,Nat.cast_one] using ih i
end Models

lemma fixedFile_nat (xs : List Nat) : fixedFile (V := Nat) xs=CarryCode.fileCode xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [fixedFile,CarryCode.fileCode_cons,natCast_nat,ih]

lemma bitsWord_nat (path tail : List Bool) :
    PhysicalFrame.bitsWord (V := Nat) path (ZipNatTape.bits tail)=ZipNatTape.bits (path++tail) := by
  induction path with
  | nil => rfl
  | cons b path ih => simp [PhysicalFrame.bitsWord,ZipNatTape.bits_cons,NatTape.push,ih]

/-- Standard interpretation of the entire physical frame; all file cells and
relative bits are retained. This is only a Nat calibration lemma. -/
lemma frame_nat (path : Source.Path) (n : Nat) (xs : List Nat) :
    PhysicalFrame.frame path n (fixedFile (V := Nat) xs)=
      let c := ZipNatTape.encode (Zip.zc 84 [true] (path ++ List.replicate (n+(48-path.length)) false ++ true :: Runtime.sepsR xs))
      ({ q := StepFormula.controlCode c.control, left := c.left, right := c.right } : Symbolic.ModelConf Nat) := by
  unfold PhysicalFrame.frame
  rw [PhysicalFrame.root_concrete]
  simp only [FileEffects.effect,fixedFile_nat,add_zero,natCast_nat]
  have hr := CarryCode.right_standard xs []
  simp only [ZipNatTape.bits_nil,List.append_nil] at hr
  rw [hr]
  have hb := ScanBits.repeat_bits (n+(48-path.length)) false (true::Runtime.sepsR xs)
  simp only [Bool.toNat_false,ZipNatTape.bits_cons,NatTape.push,Bool.toNat_true] at hb
  simp only [natCast_nat,show (1+1 : Nat)=2 from rfl]
  rw [hb,bitsWord_nat]
  simp only [ZipNatTape.encode,Zip.zc,ZipNatTape.bits_trim,ZipNatTape.bits_cons,
    ZipNatTape.bits_nil,NatTape.push,Bool.toNat_true]
  simp only [List.append_assoc,show StepFormula.controlCode (NativeTable.inverse 84)=81 from rfl,
    Nat.mul_zero,Nat.zero_add]
  rfl
#print axioms fixedFile_correct
#print axioms fixedFile_nth
#print axioms frame_nat
end PA196.Arithmetic.Machine.PA.InternalTrace.FixedTrace

