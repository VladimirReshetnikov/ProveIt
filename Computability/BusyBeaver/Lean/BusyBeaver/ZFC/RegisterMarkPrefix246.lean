import BusyBeaver.ZFC.TablePrefix246
import BusyBeaver.ZFC.RegisterMarkPerm252

/-!
Concrete marking on the exact 246-state contextual-fold table.

Adapted from the checked RegisterMarkPrefix250 proof and the attributed
Mira-Cult, Jeff Ketchersid and Wade framework. Source63, arrival 8cdc55ff92,
redirects the selected block's separator from old0 to old20. The next bit
is necessarily one in every ordinary block, and old20/read1 erases it with
the same action. No statement about old20/read0 or arbitrary startup is used.

Pure unary encodings and the state-count-generic return scanner are reused
from RegisterMarkPerm252. All finite table facts are checked on machinePrefix246.
Arbitrary values, suffixes and left contexts, and the exact original marking
time, are retained. The inherited prefix250/247 selector attribution remains
separate from the new246 pulse fold. No bootstrap or full program theorem.
-/

namespace SetTheory.BusyBeaver.ZFC.RegisterMarkPrefix246

open FiniteZipper ZipperRuns RegisterBoxesPerm252

/-- The nine selectors in increasing physical-register order. -/
def skip : Nat → Fin 246
  | 0 => oldStatePrefix246 60
  | 1 => oldStatePrefix246 44
  | 2 => oldStatePrefix246 31
  | 3 => oldStatePrefix246 56
  | 4 => oldStatePrefix246 38
  | 5 => oldStatePrefix246 40
  | 6 => oldStatePrefix246 28
  | 7 => oldStatePrefix246 64
  | _ => oldStatePrefix246 69

def restoreZero : Fin 246 := oldStatePrefix246 20
def markFirst : Fin 246 := oldStatePrefix246 2
def markReturnOnes : Fin 246 := oldStatePrefix246 4
def markReturnZero : Fin 246 := oldStatePrefix246 6

theorem skip_one_facts : ∀ j : Fin 9,
    machinePrefix246.transition (skip j.val) true = ⟨true, .right, some (skip j.val)⟩ := by decide +kernel

theorem skip_next_facts : ∀ j : Fin 8,
    machinePrefix246.transition (skip (j.val + 1)) false =
      ⟨false, .right, some (skip j.val)⟩ := by decide +kernel

theorem row_skip_target :
    machinePrefix246.transition (skip 0) false = ⟨false, .right, some restoreZero⟩ := by decide +kernel
theorem row_erase_one :
    machinePrefix246.transition restoreZero true = ⟨false, .left, some markFirst⟩ := by decide +kernel
theorem row_mark_back :
    machinePrefix246.transition markFirst false = ⟨false, .left, some markFirst⟩ := by decide +kernel
theorem row_mark_enter :
    machinePrefix246.transition markFirst true = ⟨true, .left, some markReturnOnes⟩ := by decide +kernel
theorem row_mark_return_one :
    machinePrefix246.transition markReturnOnes true =
      ⟨true, .left, some markReturnOnes⟩ := by decide +kernel
theorem row_mark_return_zero :
    machinePrefix246.transition markReturnOnes false =
      ⟨false, .left, some markReturnZero⟩ := by decide +kernel
theorem row_mark_return_probe :
    machinePrefix246.transition markReturnZero true =
      ⟨true, .left, some markReturnOnes⟩ := by decide +kernel

theorem skip_block (j : Nat) (hj : j < 8) (v : Nat) (h : Int) (l X : List Bool) :
    zipRun machinePrefix246 (zAt (skip (j + 1)) h l
      (false :: true :: (List.replicate v true ++ X))) (v + 2) =
      zAt (skip j) (h + ((v + 2 : Nat) : Int))
        (List.replicate (v + 1) true ++ false :: l) X := by
  rw [show v + 2 = (v + 1) + 1 by omega, zipRun_first,
    step_right _ _ _ _ _ _ _ _ (skip_next_facts ⟨j, hj⟩)]
  change zipRun machinePrefix246
    (zAt (skip j) (h + 1) (false :: l) (List.replicate (v + 1) true ++ X)) (v + 1) = _
  rw [scan_right _ _ _ (skip_one_facts ⟨j, by omega⟩)]
  congr 1
  omega

theorem skip_file (pre : List Nat) (m : Nat) (hm : pre.length + m < 9)
    (h : Int) (l X : List Bool) :
    zipRun machinePrefix246 (zAt (skip (pre.length + m)) h l (registerBits pre ++ X))
      (width pre) =
      zAt (skip m) (h + (width pre : Int)) ((registerBits pre).reverse ++ l) X := by
  induction pre generalizing h l with
  | nil => simp [registerBits, width, zipRun]
  | cons v pre ih =>
    simp only [width, registerBits, List.length_cons, List.cons_append, List.append_assoc]
    rw [show pre.length + 1 + m = (pre.length + m) + 1 by omega,
      zipRun_add, skip_block (pre.length + m) (by simp only [List.length_cons] at hm; omega), ih (by simp only [List.length_cons] at hm; omega)]
    simp only [List.reverse_cons, List.reverse_append, List.reverse_replicate,
      List.append_assoc, List.singleton_append, List.replicate_succ']
    congr 1
    omega

theorem mark_steps (v : Nat) (h : Int) (l X : List Bool) :
    zipRun machinePrefix246 (zAt (skip 0) h l (false :: true :: (List.replicate v true ++ X))) 3 =
      leftAt markFirst h l (false :: false :: (List.replicate v true ++ X)) := by
  rw [zipRun_first, step_right _ _ _ _ _ _ _ _ row_skip_target,
    zipRun_first, step_left _ _ _ _ _ _ _ _ row_erase_one, leftAt_cons,
    zipRun_first, step_left _ _ _ _ _ _ _ _ row_mark_back]
  simp only [zipRun]
  congr 1
  omega

def markExit (pre : List Nat) : Fin 246 :=
  if pre = [] then markFirst else markReturnZero

/-- Mark with an arbitrary terminal word, so both unpadded and explicitly
padded whole-file contracts are immediate clients. -/
theorem mark_word (pre : List Nat) (v : Nat) (hp : pre.length < 9)
    (h : Int) (l X : List Bool) :
    zipRun machinePrefix246
      (zAt (skip pre.length) h l
        (registerBits pre ++ false :: true :: (List.replicate v true ++ X)))
      (2 * width pre + 3) =
      leftAt (markExit pre) h l
        (registerBits pre ++ false :: false :: (List.replicate v true ++ X)) := by
  rw [show 2 * width pre + 3 = width pre + (3 + width pre) by omega,
    zipRun_add]
  have forward := skip_file pre 0 (by simpa using hp) h l
    (false :: true :: (List.replicate v true ++ X))
  simp only [Nat.add_zero] at forward
  rw [forward, zipRun_add, mark_steps]
  by_cases he : pre = []
  · subst pre
    simp [width, registerBits, zipRun, markExit]
  · rw [RegisterMarkPerm252.return_end machinePrefix246 markReturnOnes
      markReturnZero row_mark_return_one row_mark_return_zero
      row_mark_return_probe pre he markFirst row_mark_enter]
    simp only [markExit, if_neg he]
    congr 1
    omega

/-- Unpadded register-file contract, including every finite spare suffix. -/
theorem mark_zip (pre : List Nat) (v : Nat) (rest : List Nat)
    (hp : pre.length < 9) (h : Int) (l : List Bool) :
    zipRun machinePrefix246
      (zAt (skip pre.length) h l (registerBits (pre ++ v :: rest)))
      (2 * width pre + 3) =
      leftAt (markExit pre) h l
        (registerBits pre ++ false :: false ::
          (List.replicate v true ++ registerBits rest)) := by
  simpa only [registerBits_append, registerBits] using
    mark_word pre v hp h l (registerBits rest)

/-- Whole-tape Core semantics; no fixed false padding is required. -/
theorem mark {c : Config 246} (pre : List Nat) (v : Nat) (rest : List Nat)
    (hp : pre.length < 9) (h : Int) (l : List Bool)
    (hc : ZipRep c (zAt (skip pre.length) h l (registerBits (pre ++ v :: rest)))) :
    ZipRep (machinePrefix246.runFrom c (2 * width pre + 3))
      (leftAt (markExit pre) h l
        (registerBits pre ++ false :: false ::
          (List.replicate v true ++ registerBits rest))) := by
  have hs := zipRun_sound machinePrefix246 (2 * width pre + 3) hc
  rw [mark_zip pre v rest hp] at hs
  exact hs

/-- The same execution with an arbitrary explicitly represented terminal word. -/
theorem mark_with_suffix {c : Config 246} (pre : List Nat) (v : Nat)
    (hp : pre.length < 9) (h : Int) (l X : List Bool)
    (hc : ZipRep c (zAt (skip pre.length) h l
      (registerBits pre ++ false :: true :: (List.replicate v true ++ X)))) :
    ZipRep (machinePrefix246.runFrom c (2 * width pre + 3))
      (leftAt (markExit pre) h l
        (registerBits pre ++ false :: false :: (List.replicate v true ++ X))) := by
  have hs := zipRun_sound machinePrefix246 (2 * width pre + 3) hc
  rw [mark_word pre v hp] at hs
  exact hs

end SetTheory.BusyBeaver.ZFC.RegisterMarkPrefix246
