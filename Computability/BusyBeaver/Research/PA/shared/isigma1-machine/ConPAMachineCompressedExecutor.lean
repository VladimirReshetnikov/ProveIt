import ConPAMachineCompressedTape

/-! Soundness of the compressed M6 executor for arbitrary transition tables. -/

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace ConPA.Machine.Compressed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open M6.Runtime

/-- The first matching concrete row agrees with the corresponding symbolic
row at its pair of control images. -/
def RowAgreement (T : Table) (machine : M6.Zip.TMN) (label : Nat → Nat) : Prop :=
  ∀ q b w dir q', machine q b = some (w,dir,q') →
    findRow T (label q) b.toNat = some ⟨label q,b.toNat,w.toNat,dir,label q'⟩

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- These are the separate obligations for the physical register engine. Each
box begins with a separator, and every accepted register oracle call takes the
claimed physical machine segment to the updated file. -/
structure BoxAgreement (T : Table) (label : Nat → Nat) (br : Branch) (box : BoxSt → V) : Prop where
  boundary : ∀ x, ∃ tail, box x = push false tail
  execute : ∀ q q' x x' extra (l : V), oracle q br x = some (q',x',extra) →
    Reach T (scanFrame true (label q) l (box x)) (scanFrame false (label q') (box x')
      (if extra then push true l else l))

def StepCorrect (T : Table) (label : Nat → Nat) (gap : V) (box : BoxSt → V) (s t : SConf) (m : Bool) : Prop :=
  Reach T (encode label gap box s) (encode label gap box t) ∧
    (m = true → Reach1 T (encode label gap box s) (encode label gap box t))

theorem ofAdmin {T : Table} {label : Nat → Nat} {gap : V} {box : BoxSt → V} {s t : SConf}
    (h : encode label gap box s = encode label gap box t) : StepCorrect T label gap box s t false :=
  ⟨ofEq h, fun h => by cases h⟩

theorem ofMacro {T : Table} {label : Nat → Nat} {gap : V} {box : BoxSt → V} {s t : SConf}
    (h : Reach T (encode label gap box s) (encode label gap box t)) : StepCorrect T label gap box s t false :=
  ⟨h, fun h => by cases h⟩

theorem ofPositive {T : Table} {label : Nat → Nat} {gap : V} {box : BoxSt → V} {s t : SConf}
    (h : Reach1 T (encode label gap box s) (encode label gap box t)) : StepCorrect T label gap box s t true :=
  ⟨reachable h,fun _ => h⟩

theorem peelLeft_sound {T : Table} (label : Nat → Nat) (gap : V) (box : BoxSt → V) {q : Nat}
    {b : Bool} {a c : Nat} {l r : List Seg} {t : SConf} {m : Bool}
    (h : peelLeft q b a c l r = some (t,m)) :
    StepCorrect T label gap box (q,true,.run b a c::l,r) t m := by
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

theorem peelRight_sound {T : Table} (label : Nat → Nat) (gap : V) (box : BoxSt → V) {q : Nat}
    {b : Bool} {a c : Nat} {l r : List Seg} {t : SConf} {m : Bool}
    (h : peelRight q b a c l r = some (t,m)) :
    StepCorrect T label gap box (q,false,l,.run b a c::r) t m := by
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

/-- Soundness of the upstream symbolic step over arbitrary model-valued tape
lengths. The symbolic machine can retain its native labels. -/
theorem symbolicStep {T : Table} {machine : M6.Zip.TMN} {label : Nat → Nat}
    (hr : RowAgreement T machine label) (gap : V) {br : Branch} {box : BoxSt → V}
    (hb : BoxAgreement T label br box) {s t : SConf} {m : Bool}
    (h : sstep machine br s = some (t,m)) : StepCorrect T label gap box s t m := by
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
            have he := hr q b w false q hrow
            exact ⟨runLength gap a c, scan T false b w (label q) _ _ _ he⟩
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
          have he := hr q b w true q' hrow
          exact rightRow T (label q) (label q') b w _ _ he
        · rename_i w q' hrow
          simp only [Option.some.injEq,Prod.mk.injEq] at h
          obtain ⟨rfl,rfl⟩ := h
          apply ofPositive
          have he := hr q b w false q' hrow
          exact leftRow T (label q) (label q') b w _ _ he
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
            have he := hr q b w true q hrow
            exact ⟨runLength gap a c, scan T true b w (label q) _ _ _ he⟩
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
              have he := hr q false false false q' hrow
              simpa only [encode,packSegments,ht] using leftRow T (label q) (label q') false false
                (packSegments gap box l) tail he
            · simp at h

/-- A successful compressed certificate gives an exact arithmetic run. The
number of compressed transitions is standard. Literal scans and the total
clock may have arbitrary model-valued length. -/
theorem checkedRun {T : Table} {machine : M6.Zip.TMN} {label : Nat → Nat}
    (hr : RowAgreement T machine label) (gap : V) {br : Branch} {box : BoxSt → V}
    (hb : BoxAgreement T label br box) (tgt : SConf → Bool)
    (fuel : Nat) (s t : SConf) (m : Bool)
    (h : exec machine br tgt fuel s m = some t) :
    tgt t = true ∧ Reach T (encode label gap box s) (encode label gap box t) ∧
      (m = false → Reach1 T (encode label gap box s) (encode label gap box t)) := by
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
end ConPA.Machine.Compressed
