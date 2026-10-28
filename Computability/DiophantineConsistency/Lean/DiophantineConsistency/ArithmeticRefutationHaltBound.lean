import DiophantineConsistency.ArithmeticProofWordBound
import DiophantineConsistency.ArithmeticRuntimeBoundDagHalt
import DiophantineConsistency.ArithmeticRuntimeBoundBisimReverse
import DiophantineConsistency.ArithmeticRuntimeBoundTapeRun

/-! # An accepted C222 refutation makes decimal215 halt within an explicit bound

In every model of `𝗜𝚺₁`, an accepted C222 refutation `code` makes the blank
decimal215 run halt at some time `t ≤ Bref code`, where `Bref` is an explicit
elementary term. The four layers compose:

* refutation ⇒ the enumerator halts within `Bword code ^ 2`
  (`ArithmeticProofWordBound.enum_halts_le_of_refutation_code`);
* enumerator time `n` ⇒ the DAG control halts within `Bdag n`
  (`ArithmeticRuntimeBoundDagHalt.dag_halts_le_of_enum_halts`);
* DAG time `ta` ⇒ the p215 control halts within `7 * ta`
  (`ArithmeticRuntimeBoundBisim.p215_halts_le_of_dag_seed`);
* p215 time `tp` ⇒ the blank machine halts within `Btape tp`
  (`ArithmeticRuntimeBoundTapeRun.blank_halts_le_of_p215_halts`).

So the refutation-to-halting-time map is a bounded search below an explicit
fixed-height tower: elementary recursive. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticRefutationHaltBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticProofWordBound ArithmeticRuntimeBoundDagHalt ArithmeticRuntimeBoundTapeRun

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The machine-time bound for an enumerator halting at time `n`. -/
def Bmach (n : V) : V := Btape (7 * Bdag n)

/-- The machine-time bound for an accepted refutation `code`. -/
def Bref (code : V) : V := Bmach (Bword code * Bword code)

theorem Btape_mono {a b : V} (h : a ≤ b) : Btape a ≤ Btape b := by
  unfold Btape
  gcongr

theorem Bdag_mono {a b : V} (h : a ≤ b) : Bdag a ≤ Bdag b := by
  unfold Bdag
  gcongr
  exact exp_monotone_le.mpr (exp_monotone_le.mpr (by gcongr))

theorem Bmach_mono {a b : V} (h : a ≤ b) : Bmach a ≤ Bmach b :=
  Btape_mono (by gcongr; exact Bdag_mono h)

/-- **An enumerator halt at `n` makes the blank machine halt within `Bmach n`.** -/
theorem blank_halts_le_of_enum_halts (n : V)
    (hn : ArithmeticEnumRunPerm222.run n (ArithmeticEnumStepPerm222.liveValue 0 4 0) = 0) :
    ∃ t ≤ Bmach n, first (ArithmeticMachineRun215.run t) = 0 := by
  obtain ⟨ta, hta, hdag⟩ := dag_halts_le_of_enum_halts n hn
  obtain ⟨tp, htp, hp⟩ := ArithmeticRuntimeBoundBisim.p215_halts_le_of_dag_seed ta hdag
  obtain ⟨t, ht, hb⟩ := blank_halts_le_of_p215_halts tp hp
  exact ⟨t, ht.trans (Btape_mono (htp.trans (by gcongr))), hb⟩

/-- **An accepted C222 refutation makes the blank decimal215 run halt within
the explicit elementary bound `Bref code`.** -/
theorem blank_halts_le_of_refutation (code : V)
    (h : ArithmeticHistory222.checkDef.val.Evalb ![code, 1]) :
    ∃ t ≤ Bref code, first (ArithmeticMachineRun215.run t) = 0 := by
  obtain ⟨n, hn, hrun⟩ := enum_halts_le_of_refutation_code code h
  obtain ⟨t, ht, hb⟩ := blank_halts_le_of_enum_halts n hrun
  exact ⟨t, ht.trans (Bmach_mono hn), hb⟩

end DiophantineConsistency.ArithmeticRefutationHaltBound
