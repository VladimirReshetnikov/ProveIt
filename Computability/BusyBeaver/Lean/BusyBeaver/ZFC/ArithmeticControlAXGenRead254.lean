import BusyBeaver.ZFC.ArithmeticControlGEN254
import BusyBeaver.ZFC.ArithmeticControlAXReadCache254

set_option autoImplicit false
noncomputable section

/-!
Compose the actual AX parameter pushes and GEN with the following cache read,
from control41 through control136. All clocks and complete register files are
internal to the ambient IΣ₁ model. Both scratch registers must initially be zero.
The old top is pushed, TW becomes wal(p1, old cache), and the next PL component
is then added to the cache. The remaining AX branch and Enum bridge are separate.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXGenRead254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254 ArithmeticControlRun254
open ArithmeticControlStep254 ArithmeticControlFrame254
open ArithmeticControlFetch254 (put s1Reg plReg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlPair254 (twReg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlDispatch254 (axEntry cacheReg)
open ArithmeticControlGEN254 (axGenFile)
open ArithmeticControlAXReadCache254 (cacheReadFile)
open FiniteControlTable254

/-- The two independently bound occurrences meet at actual control122. -/
theorem gen_read_join :
    ArithmeticControlGEN254.nextRead = ArithmeticControlAXReadCache254.entry := rfl

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem read_put_self (file x : V) (p : Fin 9) :
    regValue (put p x file) p = x := write_at file x p

private theorem read_put_other (file x : V) (p q : Fin 9) (h : p ≠ q) :
    regValue (put p x file) q = regValue file q := write_other file x p q h

private theorem axGenFile_other (file : V) (i : Fin 9)
    (ht : i ≠ twReg) (hs : i ≠ wsReg) :
    regValue (axGenFile file) i = regValue file i := by
  rw [axGenFile, read_put_other _ _ twReg i ht.symm,
    read_put_other _ _ wsReg i hs.symm]

/-- Complete register file after the first constructor and following read. -/
def axGenReadFile (file : V) : V := cacheReadFile (axGenFile file)

theorem axGenReadFile_eq (file : V) :
    axGenReadFile file =
      put cacheReg (regValue file cacheReg + first (regValue file plReg))
        (put plReg (second (regValue file plReg))
          (put twReg (wal (regValue file p1Reg) (regValue file cacheReg))
            (put wsReg (cantor (regValue file twReg) (regValue file wsReg)) file))) := by
  unfold axGenReadFile cacheReadFile
  simp only [axGenFile_other file cacheReg (by decide) (by decide),
    axGenFile_other file plReg (by decide) (by decide)]
  rfl

theorem axGenReadFile_tw (file : V) :
    regValue (axGenReadFile file) twReg =
      wal (regValue file p1Reg) (regValue file cacheReg) := by
  rw [axGenReadFile,
    ArithmeticControlAXReadCache254.cacheReadFile_other _ twReg (by decide) (by decide),
    axGenFile, read_put_self]

theorem axGenReadFile_ws (file : V) :
    regValue (axGenReadFile file) wsReg =
      cantor (regValue file twReg) (regValue file wsReg) := by
  rw [axGenReadFile,
    ArithmeticControlAXReadCache254.cacheReadFile_other _ wsReg (by decide) (by decide),
    axGenFile, read_put_other _ _ twReg wsReg (by decide), read_put_self]

theorem axGenReadFile_cache (file : V) :
    regValue (axGenReadFile file) cacheReg =
      regValue file cacheReg + first (regValue file plReg) := by
  rw [axGenReadFile, ArithmeticControlAXReadCache254.cacheReadFile_cache,
    axGenFile_other file cacheReg (by decide) (by decide),
    axGenFile_other file plReg (by decide) (by decide)]

theorem axGenReadFile_pl (file : V) :
    regValue (axGenReadFile file) plReg = second (regValue file plReg) := by
  rw [axGenReadFile, ArithmeticControlAXReadCache254.cacheReadFile_pl,
    axGenFile_other file plReg (by decide) (by decide)]

theorem axGenReadFile_other (file : V) (i : Fin 9)
    (ht : i ≠ twReg) (hs : i ≠ wsReg) (hc : i ≠ cacheReg) (hp : i ≠ plReg) :
    regValue (axGenReadFile file) i = regValue file i := by
  rw [axGenReadFile, ArithmeticControlAXReadCache254.cacheReadFile_other _ i hc hp,
    axGenFile_other file i ht hs]

/-- Actual41→136 execution, with a positive internal runtime and full-file output. -/
theorem ax_gen_read_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number axEntry : V) file) =
        liveValue (number ArithmeticControlAXReadCache254.exit : V) (axGenReadFile file) := by
  have hg1 : regValue (axGenFile file) s1Reg = 0 := by
    rw [axGenFile_other file s1Reg (by decide) (by decide)]
    exact h1
  have hg2 : regValue (axGenFile file) s2Reg = 0 := by
    rw [axGenFile_other file s2Reg (by decide) (by decide)]
    exact h2
  obtain ⟨tg, htg, hg⟩ := ArithmeticControlGEN254.ax_gen_run file h1 h2
  obtain ⟨tr, _, hr⟩ := ArithmeticControlAXReadCache254.read_cache_run (axGenFile file) hg1 hg2
  rw [gen_read_join] at hg
  refine ⟨tg + tr, le_trans htg (le_add_of_nonneg_right (Arithmetic.zero_le _)), ?_⟩
  rw [controlRun_add, hg]
  exact hr

/-- Stream client with arbitrary old cache, old top, old stack and remaining PL. -/
theorem ax_gen_read_pair_run (file x rest : V)
    (hp : regValue file plReg = cantor x rest)
    (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number axEntry : V) file) =
        liveValue (number ArithmeticControlAXReadCache254.exit : V)
          (put cacheReg (regValue file cacheReg + x)
            (put plReg rest
              (put twReg (wal (regValue file p1Reg) (regValue file cacheReg))
                (put wsReg (cantor (regValue file twReg) (regValue file wsReg)) file)))) := by
  simpa only [axGenReadFile_eq, hp, first_cantor, second_cantor] using
    ax_gen_read_run file h1 h2

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXGenRead254
