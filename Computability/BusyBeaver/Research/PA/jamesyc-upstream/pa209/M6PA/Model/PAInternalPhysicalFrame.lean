module
public import M6PA.Model.PAInternalFileEffects
public import M6PA.Model.OriginalCheck
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace.PhysicalFrame
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open ScanBits FileLayout M6.Runtime Symbolic
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def bitsWord : List Bool → V → V
  | [],t => t
  | b::bs,t => (1+1)*bitsWord bs t+b.toNat

lemma word_append (n xs : V) (a b : List Seg) (t : V) :
    word n (FileBoxes.box xs) (a++b) t=
      word n (FileBoxes.box xs) a (word n (FileBoxes.box xs) b t) := by
  induction a with
  | nil => rfl
  | cons x a ih => cases x <;> simp only [List.cons_append,word,ih]

lemma word_bits (n xs : V) (bs : List Bool) (t : V) :
    word n (FileBoxes.box xs) (bs.map Seg.bit) t=bitsWord bs t := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map_cons,word,bitsWord,ih]

/-- Complete arithmetic physical root frame, retaining every HFS file cell. -/
noncomputable def frame (path : Source.Path) (n xs : V) : ModelConf V :=
  config n (FileBoxes.box xs) denseControl (OriginalCheck.frame path)

lemma root_concrete (path : Source.Path) (extra : Nat) (e : Eff) (n xs : V) :
    config n (FileBoxes.box xs) denseControl (OriginalCheck.frame path extra e)=
      ⟨81,1,bitsWord path (repeatBits (n+(38+extra-path.length : Nat)) 0
        ((1+1)*CarryCode.rightFile (FileEffects.effect e xs) 0+1))⟩ := by
  have hq : NativeRows.code 84=81 := by rfl
  simp only [OriginalCheck.frame,M6.RuntimeContracts.rootFrame,config,word_append,word_bits,word,denseControl,hq,
    FileEffects.box_effect,Bool.toNat_true,Bool.toNat_false,Nat.cast_one,Nat.cast_zero,
    Nat.cast_ofNat,one_mul,mul_zero,zero_add]
  simp

/-- Absorb the original primitive's padding shift and whole-file effect
without truncating spare cells or changing the head convention. -/
theorem root_effect (path : Source.Path) (hp : path.length≤38) (extra : Nat)
    (e : Eff) (n xs : V) :
    config n (FileBoxes.box xs) denseControl (OriginalCheck.frame path extra e)=
      frame path (n+extra) (FileEffects.effect e xs) := by
  unfold frame
  rw [root_concrete,root_concrete]
  have he : 38+extra-path.length=extra+(38-path.length) := by omega
  simp only [he,Nat.cast_add,add_zero,FileEffects.effect]
  rw [add_assoc]

/-- Initial exact normalized-frame comparison in any arithmetic model. -/
theorem matches_frame (n xs : V) {s t : SConf} (h : sMatches s t=true) :
    config n (FileBoxes.box xs) denseControl s=config n (FileBoxes.box xs) denseControl t :=
  matches_config n (FileBoxes.box xs) denseControl s t h
end Models
#print axioms root_concrete
#print axioms root_effect
#print axioms matches_frame
end M6.Arithmetic.PA.InternalTrace.PhysicalFrame

