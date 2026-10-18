import BusyBeaver.ZFC.TableRouting245
import BusyBeaver.ZFC.RegisterMarkPerm252

/-!
Concrete marking on the exact routing245 table.

Direct port of the checked RegisterMarkPrefix246 proof. All selected old-label
rows are unchanged in source68 (arrival8286787dd0468d848db345debe304b002d7064a4).
The literal245 table is used for every finite row fact; no global machine
renaming or operational meaning for absent labels is assumed.

The original Mira-Cult, Jeff Ketchersid and Wade framework attribution and
source63's old20 selector restoration are retained. Pure unary encodings
and the state-count-generic return scanner come from RegisterMarkPerm252.
Arbitrary values, terminal words, spare suffixes and left contexts remain
quantified, with exact duration 2 * width pre + 3 and the complete tape.
No bootstrap, whole-program, or consistency theorem is asserted here.
-/

namespace SetTheory.BusyBeaver.ZFC.RegisterMarkRouting245

open FiniteZipper ZipperRuns RegisterBoxesPerm252

/-- The nine selectors in increasing physical-register order. -/
def skip : Nat → Fin 245
  | 0 => oldStateRouting245 60
  | 1 => oldStateRouting245 44
  | 2 => oldStateRouting245 31
  | 3 => oldStateRouting245 56
  | 4 => oldStateRouting245 38
  | 5 => oldStateRouting245 40
  | 6 => oldStateRouting245 28
  | 7 => oldStateRouting245 64
  | _ => oldStateRouting245 69

def restoreZero : Fin 245 := oldStateRouting245 20
def markFirst : Fin 245 := oldStateRouting245 2
def markReturnOnes : Fin 245 := oldStateRouting245 4
def markReturnZero : Fin 245 := oldStateRouting245 6

theorem skip_one_facts : ∀ j : Fin 9,
    machineRouting245.transition (skip j.val) true = ⟨true, .right, some (skip j.val)⟩ := by decide +kernel

theorem skip_next_facts : ∀ j : Fin 8,
    machineRouting245.transition (skip (j.val + 1)) false =
      ⟨false, .right, some (skip j.val)⟩ := by decide +kernel

theorem row_skip_target :
    machineRouting245.transition (skip 0) false = ⟨false, .right, some restoreZero⟩ := by decide +kernel
theorem row_erase_one :
    machineRouting245.transition restoreZero true = ⟨false, .left, some markFirst⟩ := by decide +kernel
theorem row_mark_back :
    machineRouting245.transition markFirst false = ⟨false, .left, some markFirst⟩ := by decide +kernel
theorem row_mark_enter :
    machineRouting245.transition markFirst true = ⟨true, .left, some markReturnOnes⟩ := by decide +kernel
theorem row_mark_return_one :
    machineRouting245.transition markReturnOnes true =
      ⟨true, .left, some markReturnOnes⟩ := by decide +kernel
theorem row_mark_return_zero :
    machineRouting245.transition markReturnOnes false =
      ⟨false, .left, some markReturnZero⟩ := by decide +kernel
theorem row_mark_return_probe :
    machineRouting245.transition markReturnZero true =
      ⟨true, .left, some markReturnOnes⟩ := by decide +kernel

theorem skip_block (j : Nat) (hj : j < 8) (v : Nat) (h : Int) (l X : List Bool) :
    zipRun machineRouting245 (zAt (skip (j + 1)) h l
      (false :: true :: (List.replicate v true ++ X))) (v + 2) =
      zAt (skip j) (h + ((v + 2 : Nat) : Int))
        (List.replicate (v + 1) true ++ false :: l) X := by
  rw [show v + 2 = (v + 1) + 1 by omega, zipRun_first,
    step_right _ _ _ _ _ _ _ _ (skip_next_facts ⟨j, hj⟩)]
  change zipRun machineRouting245
    (zAt (skip j) (h + 1) (false :: l) (List.replicate (v + 1) true ++ X)) (v + 1) = _
  rw [scan_right _ _ _ (skip_one_facts ⟨j, by omega⟩)]
  congr 1
  omega

theorem skip_file (pre : List Nat) (m : Nat) (hm : pre.length + m < 9)
    (h : Int) (l X : List Bool) :
    zipRun machineRouting245 (zAt (skip (pre.length + m)) h l (registerBits pre ++ X))
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
    zipRun machineRouting245 (zAt (skip 0) h l (false :: true :: (List.replicate v true ++ X))) 3 =
      leftAt markFirst h l (false :: false :: (List.replicate v true ++ X)) := by
  rw [zipRun_first, step_right _ _ _ _ _ _ _ _ row_skip_target,
    zipRun_first, step_left _ _ _ _ _ _ _ _ row_erase_one, leftAt_cons,
    zipRun_first, step_left _ _ _ _ _ _ _ _ row_mark_back]
  simp only [zipRun]
  congr 1
  omega

def markExit (pre : List Nat) : Fin 245 :=
  if pre = [] then markFirst else markReturnZero

/-- Mark with an arbitrary terminal word, so both unpadded and explicitly
padded whole-file contracts are immediate clients. -/
theorem mark_word (pre : List Nat) (v : Nat) (hp : pre.length < 9)
    (h : Int) (l X : List Bool) :
    zipRun machineRouting245
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
  · rw [RegisterMarkPerm252.return_end machineRouting245 markReturnOnes
      markReturnZero row_mark_return_one row_mark_return_zero
      row_mark_return_probe pre he markFirst row_mark_enter]
    simp only [markExit, if_neg he]
    congr 1
    omega

/-- Unpadded register-file contract, including every finite spare suffix. -/
theorem mark_zip (pre : List Nat) (v : Nat) (rest : List Nat)
    (hp : pre.length < 9) (h : Int) (l : List Bool) :
    zipRun machineRouting245
      (zAt (skip pre.length) h l (registerBits (pre ++ v :: rest)))
      (2 * width pre + 3) =
      leftAt (markExit pre) h l
        (registerBits pre ++ false :: false ::
          (List.replicate v true ++ registerBits rest)) := by
  simpa only [registerBits_append, registerBits] using
    mark_word pre v hp h l (registerBits rest)

/-- Whole-tape Core semantics; no fixed false padding is required. -/
theorem mark {c : Config 245} (pre : List Nat) (v : Nat) (rest : List Nat)
    (hp : pre.length < 9) (h : Int) (l : List Bool)
    (hc : ZipRep c (zAt (skip pre.length) h l (registerBits (pre ++ v :: rest)))) :
    ZipRep (machineRouting245.runFrom c (2 * width pre + 3))
      (leftAt (markExit pre) h l
        (registerBits pre ++ false :: false ::
          (List.replicate v true ++ registerBits rest))) := by
  have hs := zipRun_sound machineRouting245 (2 * width pre + 3) hc
  rw [mark_zip pre v rest hp] at hs
  exact hs

/-- The same execution with an arbitrary explicitly represented terminal word. -/
theorem mark_with_suffix {c : Config 245} (pre : List Nat) (v : Nat)
    (hp : pre.length < 9) (h : Int) (l X : List Bool)
    (hc : ZipRep c (zAt (skip pre.length) h l
      (registerBits pre ++ false :: true :: (List.replicate v true ++ X)))) :
    ZipRep (machineRouting245.runFrom c (2 * width pre + 3))
      (leftAt (markExit pre) h l
        (registerBits pre ++ false :: false :: (List.replicate v true ++ X))) := by
  have hs := zipRun_sound machineRouting245 (2 * width pre + 3) hc
  rw [mark_word pre v hp] at hs
  exact hs

end SetTheory.BusyBeaver.ZFC.RegisterMarkRouting245
