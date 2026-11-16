import PA194CompressedTape

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194CompressedExecutor
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion
open PA194BidirectionalRunScan PA194BidirectionalRow PA194CompressedTape
open M6.Runtime

/-- Active symbolic rows agree with the exact literal dense row at each image. -/
def RowAgreement (machine : M6.Zip.TMN) (label : Nat → Nat) : Prop :=
  ∀ q b w dir q', machine q b = some (w,dir,q') →
    label q < 194 ∧
    PA194Rows.rows.getD (label q + label q + bit b) (0,0,194) = (bit w,bit dir,label q')

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- These are the separate obligations for the physical register engine. Each
box begins with a separator, and every accepted register oracle call takes the
claimed physical machine segment to the updated file. -/
structure BoxAgreement (label : Nat → Nat) (br : Branch) (box : BoxSt → M) : Prop where
  boundary : ∀ x, ∃ tail, box x = PA194BidirectionalRow.push false tail
  execute : ∀ q q' x x' extra (l : M), oracle q br x = some (q',x',extra) →
    Reach (frame true (label q) l (box x)) (frame false (label q') (box x')
      (if extra then PA194BidirectionalRow.push true l else l))

def StepCorrect (label : Nat → Nat) (gap : M) (box : BoxSt → M) (s t : SConf) (m : Bool) : Prop :=
  Reach (encode label gap box s) (encode label gap box t) ∧
    (m = true → Reach1 (encode label gap box s) (encode label gap box t))

theorem ofAdmin {label : Nat → Nat} {gap : M} {box : BoxSt → M} {s t : SConf}
    (h : encode label gap box s = encode label gap box t) : StepCorrect label gap box s t false :=
  ⟨ofEq h, fun h => by cases h⟩

theorem ofMacro {label : Nat → Nat} {gap : M} {box : BoxSt → M} {s t : SConf}
    (h : Reach (encode label gap box s) (encode label gap box t)) : StepCorrect label gap box s t false :=
  ⟨h, fun h => by cases h⟩

theorem ofPositive {label : Nat → Nat} {gap : M} {box : BoxSt → M} {s t : SConf}
    (h : Reach1 (encode label gap box s) (encode label gap box t)) : StepCorrect label gap box s t true :=
  ⟨reachable h,fun _ => h⟩

theorem peelLeft_sound (label : Nat → Nat) (gap : M) (box : BoxSt → M) {q : Nat}
    {b : Bool} {a c : Nat} {l r : List Seg} {t : SConf} {m : Bool}
    (h : peelLeft q b a c l r = some (t,m)) :
    StepCorrect label gap box (q,true,.run b a c::l,r) t m := by
  cases c with
  | zero =>
    cases a with
    | zero =>
      simp only [peelLeft, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ofAdmin (by simp only [encode,removeEmptyRun])
    | succ a => simp [peelLeft] at h
  | succ c =>
    simp only [peelLeft, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    exact ofAdmin (by simp only [encode,peelRun])

theorem peelRight_sound (label : Nat → Nat) (gap : M) (box : BoxSt → M) {q : Nat}
    {b : Bool} {a c : Nat} {l r : List Seg} {t : SConf} {m : Bool}
    (h : peelRight q b a c l r = some (t,m)) :
    StepCorrect label gap box (q,false,l,.run b a c::r) t m := by
  cases c with
  | zero =>
    cases a with
    | zero =>
      simp only [peelRight, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ofAdmin (by simp only [encode,removeEmptyRun])
    | succ a => simp [peelRight] at h
  | succ c =>
    simp only [peelRight, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    exact ofAdmin (by simp only [encode,peelRun])

/-- Soundness of the upstream symbolic step over arbitrary PRA-model tape
lengths. The symbolic machine can retain its native labels. -/
theorem symbolicStep {machine : M6.Zip.TMN} {label : Nat → Nat}
    (hr : RowAgreement machine label) (gap : M) {br : Branch} {box : BoxSt → M}
    (hb : BoxAgreement label br box) {s t : SConf} {m : Bool}
    (h : sstep machine br s = some (t,m)) : StepCorrect label gap box s t m := by
  rcases s with ⟨q,onl,l,r⟩
  cases onl with
  | true =>
    cases l with
    | nil =>
      simp only [sstep,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      apply ofAdmin
      exact turnBlank (label q) (packSegments gap box r)
    | cons x l =>
      cases x with
      | bit b =>
        simp only [sstep,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        apply ofAdmin
        exact turnRight (label q) b (packSegments gap box l) (packSegments gap box r)
      | box x => simp [sstep] at h
      | run b a c =>
        simp only [sstep] at h
        split at h
        · rename_i w q' hrow
          split at h
          · rename_i he
            subst q'
            simp only [Option.some.injEq,Prod.mk.injEq] at h
            obtain ⟨rfl,rfl⟩ := h
            apply ofMacro
            obtain ⟨hlt,he⟩ := hr q b w false q hrow
            exact ⟨runLength gap a c, fullScan false b w (label q) _ _ _ hlt he⟩
          · exact peelLeft_sound label gap box h
        · exact peelLeft_sound label gap box h
  | false =>
    cases r with
    | nil => simp [sstep] at h
    | cons x r =>
      cases x with
      | bit b =>
        simp only [sstep] at h
        split at h
        · rename_i w q' hrow
          simp only [Option.some.injEq,Prod.mk.injEq] at h
          obtain ⟨rfl,rfl⟩ := h
          apply ofPositive
          obtain ⟨hlt,he⟩ := hr q b w true q' hrow
          exact rightRow (label q) (label q') b w _ _ hlt he
        · rename_i w q' hrow
          simp only [Option.some.injEq,Prod.mk.injEq] at h
          obtain ⟨rfl,rfl⟩ := h
          apply ofPositive
          obtain ⟨hlt,he⟩ := hr q b w false q' hrow
          exact leftRow (label q) (label q') b w _ _ hlt he
        · simp at h
      | run b a c =>
        simp only [sstep] at h
        split at h
        · rename_i w q' hrow
          split at h
          · rename_i he
            subst q'
            simp only [Option.some.injEq,Prod.mk.injEq] at h
            obtain ⟨rfl,rfl⟩ := h
            apply ofMacro
            obtain ⟨hlt,he⟩ := hr q b w true q hrow
            exact ⟨runLength gap a c, fullScan true b w (label q) _ _ _ hlt he⟩
          · exact peelRight_sound label gap box h
        · exact peelRight_sound label gap box h
      | box x =>
        cases r with
        | cons y r => simp [sstep] at h
        | nil =>
          simp only [sstep] at h
          split at h
          · rename_i q' x' extra ho
            simp only [Option.some.injEq,Prod.mk.injEq] at h
            obtain ⟨rfl,rfl⟩ := h
            apply ofMacro
            have hh := hb.execute q q' x x' extra (packSegments gap box l) ho
            cases extra <;> simpa only [encode, packSegments, ↓reduceIte, Bool.false_eq_true] using hh
          · split at h
            · rename_i q' hrow
              simp only [Option.some.injEq,Prod.mk.injEq] at h
              obtain ⟨rfl,rfl⟩ := h
              apply ofPositive
              obtain ⟨tail,ht⟩ := hb.boundary x
              obtain ⟨hlt,he⟩ := hr q false false false q' hrow
              simpa only [encode,packSegments,ht] using leftRow (label q) (label q') false false
                (packSegments gap box l) tail hlt he
            · simp at h

/-- A successful compressed certificate gives an exact literal run. Source
paths and the number of compressed transitions are standard, while every
literal scan and the total physical clock can have model-valued length. -/
theorem checkedRun {machine : M6.Zip.TMN} {label : Nat → Nat}
    (hr : RowAgreement machine label) (gap : M) {br : Branch} {box : BoxSt → M}
    (hb : BoxAgreement label br box) (tgt : SConf → Bool)
    (fuel : Nat) (s t : SConf) (m : Bool)
    (h : exec machine br tgt fuel s m = some t) :
    tgt t = true ∧ Reach (encode label gap box s) (encode label gap box t) ∧
      (m = false → Reach1 (encode label gap box s) (encode label gap box t)) := by
  induction fuel generalizing s m with
  | zero => simp [exec] at h
  | succ fuel ih =>
    simp only [exec] at h
    split at h
    · rename_i ht
      cases h
      obtain ⟨hm,hg⟩ := Bool.and_eq_true_iff.mp ht
      exact ⟨hg,ofEq rfl,fun hz => by simp [hm] at hz⟩
    · split at h
      · simp at h
      · rename_i mid took hs
        obtain ⟨hg,hrest,pr⟩ := ih mid (m || took) h
        obtain ⟨hstep,ps⟩ := symbolicStep hr gap hb hs
        refine ⟨hg,trans hstep hrest,?_⟩
        intro hm
        subst m
        cases took with
        | false => exact transPositive hstep (pr rfl)
        | true => exact positiveTrans (ps rfl) hrest

#print axioms symbolicStep
#print axioms checkedRun

end models
end PA194CompressedExecutor
