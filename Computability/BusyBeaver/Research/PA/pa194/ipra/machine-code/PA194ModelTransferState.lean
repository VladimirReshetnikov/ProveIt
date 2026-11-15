import PA194ModelLoopIteration
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194ModelTransferState
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194ModelLoopIteration PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch

def gap : Code 1 := PackedClock.decodeLeft
def rest : Code 1 := unary PackedClock.decodeRight (.proj 0)
def count : Code 1 := unary PackedClock.decodeLeft rest
def rest2 : Code 1 := unary PackedClock.decodeRight rest
def spare : Code 1 := unary PackedClock.decodeLeft rest2
def control : Code 1 := unary PackedClock.decodeRight rest2
def one : Code 1 := constantCode 1
def plus1 (x : Code 1) : Code 1 := bin addCode x one
def next (advance : Code 1) : Code 1 :=
  bin pairCode (plus1 gap)
    (bin pairCode (plus1 count)
      (bin pairCode spare (unary advance control)))
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
def packed (g n s c : M) : M := F pairCode ![g,F pairCode ![n,F pairCode ![s,c]]]
theorem modelNext (advance : Code 1) (g n s c : M) :
    F (next advance) (fun _ => packed g n s c) = packed (g+1) (n+1) s (F advance (fun _ => c)) := by
  simp only [next,plus1,gap,count,rest,rest2,spare,control,one,modelBin,modelUnary,modelProjection,modelConstant,modelNumeralOne,modelDecodeLeft,modelDecodeRight,modelPairCode,packed]
  simp only [pi₁_pair,pi₂_pair]
  rfl
def body (advance : Code 1) : Semiformula language Nat 1 :=
  let ix : Semiterm language Nat 1 := .bvar 0
  let gap : Semiterm language Nat 1 := .fvar 0
  let count : Semiterm language Nat 1 := .fvar 1
  let spare : Semiterm language Nat 1 := .fvar 2
  let control : Semiterm language Nat 1 := .fvar 3
  let pack := fun a b c d => PA194ModelLoopIteration.app2 pairCode a (PA194ModelLoopIteration.app2 pairCode b (PA194ModelLoopIteration.app2 pairCode c d))
  let add := PA194ModelLoopIteration.app2 addCode
  .rel Language.ORing.Rel.eq ![
    PA194ModelLoopIteration.app2 (iterCode (next advance)) ix (pack gap count spare control),
    pack (add gap ix) (add count ix) spare (PA194ModelLoopIteration.app2 (iterCode advance) ix control)]
theorem body_open (advance : Code 1) : (body advance).Open := by simp [body,Semiformula.Open,Semiformula.qr]
theorem body_eval (advance : Code 1) (x : M) (e : Nat → M) :
    (body advance).Eval ![x] e ↔
      F (iterCode (next advance)) ![x,packed (e 0) (e 1) (e 2) (e 3)] =
        packed (e 0+x) (e 1+x) (e 2) (F (iterCode advance) ![x,e 3]) := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] (body advance) ↔ _
  simp only [body,Semiformula.EvalAux,eqRel]
  simp [PA194ModelLoopIteration.valApp2,Semiterm.val_bvar,Semiterm.val_fvar,Matrix.cons_val_zero,Matrix.cons_val_one,packed]
  rfl
theorem iterPacked (advance : Code 1) (i g n s c : M) :
    F (iterCode (next advance)) ![i,packed g n s c] =
      packed (g+i) (n+i) s (F (iterCode advance) ![i,c]) := by
  classical
  let e : Nat → M := fun j => if j=0 then g else if j=1 then n else if j=2 then s else c
  have h0 : e 0 = g := by simp [e]
  have h1 : e 1 = n := by simp [e]
  have h2 : e 2 = s := by simp [e]
  have h3 : e 3 = c := by simp [e]
  have main : (body advance).Eval ![i] e := by
    apply PRAOpenInduction.modelOpenInduction (M := M) (body advance) (body_open advance) e
    · apply (body_eval advance (0 : M) e).mpr
      rw [h0,h1,h2,h3,modelIterZero,modelIterZero]
      simp only [add_zero]
    · intro u hu
      apply (body_eval advance (F Code.succ (fun _ => u)) e).mpr
      rw [h0,h1,h2,h3,modelIterSucc,modelIterSucc]
      have prev := (body_eval advance u e).mp hu
      rw [h0,h1,h2,h3] at prev
      rw [prev,modelNext]
      have hs : F Code.succ (fun _ => u) = u+1 := (modelAddOne u).symm
      rw [hs]
      congr 1 <;> simp only [add_assoc,add_comm,add_left_comm]
  have h := (body_eval advance i e).mp main
  rw [h0,h1,h2,h3] at h
  exact h
#print axioms iterPacked
#print axioms modelNext
end models
end PA194ModelTransferState
