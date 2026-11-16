module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAInternalSymbolicStep
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace.Symbolic
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open M6.Runtime
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
variable (n : V) (box : BoxSt → V → V)

/-- Explicit obligations for precisely the visited box states in the original
finite execution, stopping at the same target test. No box theorem is postulated. -/
def ExecSafe (br : Branch) (tgt : SConf → Bool) : Nat → SConf → Bool → Prop
  | 0, _, _ => True
  | f+1, s, moved =>
    if moved && tgt s then True
    else match Runtime.sstep NativeTable.machine br s with
      | none => True
      | some (s',m) => OracleAt n box br s ∧ HeadAt box s ∧ ExecSafe br tgt f s' (moved || m)

theorem progress_weaken {s t : ModelConf V} {a b : Bool} (h : Progress a s t)
    (hab : b=true → a=true) : Progress b s t := by
  obtain ⟨k,q,l,r,hseg,hpos⟩ := h
  exact ⟨k,q,l,r,hseg,fun hb => hpos (hab hb)⟩

/-- Soundness of the existing finite checker execution in arbitrary PA models,
conditional only on explicit local box obligations for states it actually visits. -/
theorem exec_sound (br : Branch) (tgt : SConf → Bool) :
    ∀ (f : Nat) (s : SConf) (moved : Bool) (out : SConf),
      Runtime.exec NativeTable.machine br tgt f s moved=some out →
      ExecSafe n box br tgt f s moved →
      tgt out=true ∧ Progress (!moved) (config n box denseControl s) (config n box denseControl out) := by
  intro f
  induction f with
  | zero => intro s moved out h hs; simp [Runtime.exec] at h
  | succ f ih =>
    intro s moved out h hs
    simp only [Runtime.exec] at h
    split at h
    · rename_i ht
      have he : s=out := Option.some.inj h
      subst out
      have hb : moved=true ∧ tgt s=true := by simpa only [Bool.and_eq_true] using ht
      refine ⟨hb.2,?_⟩
      rw [hb.1]
      exact progress_eq rfl
    · rename_i ht
      cases hstep : Runtime.sstep NativeTable.machine br s with
      | none => simp [hstep] at h
      | some pair =>
        rcases pair with ⟨s',m⟩
        simp only [hstep] at h
        have hsafe : OracleAt n box br s ∧ HeadAt box s ∧
            ExecSafe n box br tgt f s' (moved || m) := by
          simpa [ExecSafe,ht,hstep] using hs
        obtain ⟨hmatch,hrest⟩ := ih s' (moved || m) out h hsafe.2.2
        have first := sstep_sound n box hstep hsafe.1 hsafe.2.1
        refine ⟨hmatch,progress_weaken (progress_trans first hrest) ?_⟩
        cases moved <;> cases m <;> simp
end Models
#print axioms exec_sound
end M6.Arithmetic.PA.InternalTrace.Symbolic

