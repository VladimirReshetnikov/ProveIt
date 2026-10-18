import BusyBeaver.ZFC.TablePrefix250
import BusyBeaver.ZFC.RegisterMarkPerm252

/-!
Concrete marking on the exact prefix250 table. Pure unary encodings and the
state-count-generic return scanner are reused from the maintained permutation252
proof; every concrete row is checked again on the new table.

The contract is attributed to Mira-Cult, Jeff Ketchersid and Wade, via
mira-emmy PR20 head 0d544f2a2e3c18f12278441a74b7879f31cbe856 and the
maintained RegisterMarkPerm252 proof. Arbitrary values, suffixes, and left
contexts are preserved; no bootstrap or full instruction theorem is claimed.
-/

namespace SetTheory.BusyBeaver.ZFC.RegisterMarkPrefix250

open FiniteZipper ZipperRuns RegisterBoxesPerm252

/-- The nine selectors in increasing physical-register order. -/
def skip : Nat → Fin 250
  | 0 => oldStatePrefix250 60
  | 1 => oldStatePrefix250 44
  | 2 => oldStatePrefix250 31
  | 3 => oldStatePrefix250 56
  | 4 => oldStatePrefix250 38
  | 5 => oldStatePrefix250 40
  | 6 => oldStatePrefix250 28
  | 7 => oldStatePrefix250 64
  | _ => oldStatePrefix250 69

def restoreZero : Fin 250 := oldStatePrefix250 0
def markFirst : Fin 250 := oldStatePrefix250 2
def markReturnOnes : Fin 250 := oldStatePrefix250 4
def markReturnZero : Fin 250 := oldStatePrefix250 6

theorem skip_one_facts : ∀ j : Fin 9,
    machinePrefix250.transition (skip j.val) true = ⟨true, .right, some (skip j.val)⟩ := by decide +kernel

theorem skip_next_facts : ∀ j : Fin 8,
    machinePrefix250.transition (skip (j.val + 1)) false =
      ⟨false, .right, some (skip j.val)⟩ := by decide +kernel

theorem row_skip_target :
    machinePrefix250.transition (skip 0) false = ⟨false, .right, some restoreZero⟩ := by decide +kernel
theorem row_erase_one :
    machinePrefix250.transition restoreZero true = ⟨false, .left, some markFirst⟩ := by decide +kernel
theorem row_mark_back :
    machinePrefix250.transition markFirst false = ⟨false, .left, some markFirst⟩ := by decide +kernel
theorem row_mark_enter :
    machinePrefix250.transition markFirst true = ⟨true, .left, some markReturnOnes⟩ := by decide +kernel
theorem row_mark_return_one :
    machinePrefix250.transition markReturnOnes true =
      ⟨true, .left, some markReturnOnes⟩ := by decide +kernel
theorem row_mark_return_zero :
    machinePrefix250.transition markReturnOnes false =
      ⟨false, .left, some markReturnZero⟩ := by decide +kernel
theorem row_mark_return_probe :
    machinePrefix250.transition markReturnZero true =
      ⟨true, .left, some markReturnOnes⟩ := by decide +kernel

theorem skip_block (j : Nat) (hj : j < 8) (v : Nat) (h : Int) (l X : List Bool) :
    zipRun machinePrefix250 (zAt (skip (j + 1)) h l
      (false :: true :: (List.replicate v true ++ X))) (v + 2) =
      zAt (skip j) (h + ((v + 2 : Nat) : Int))
        (List.replicate (v + 1) true ++ false :: l) X := by
  rw [show v + 2 = (v + 1) + 1 by omega, zipRun_first,
    step_right _ _ _ _ _ _ _ _ (skip_next_facts ⟨j, hj⟩)]
  change zipRun machinePrefix250
    (zAt (skip j) (h + 1) (false :: l) (List.replicate (v + 1) true ++ X)) (v + 1) = _
  rw [scan_right _ _ _ (skip_one_facts ⟨j, by omega⟩)]
  congr 1
  omega

theorem skip_file (pre : List Nat) (m : Nat) (hm : pre.length + m < 9)
    (h : Int) (l X : List Bool) :
    zipRun machinePrefix250 (zAt (skip (pre.length + m)) h l (registerBits pre ++ X))
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
    zipRun machinePrefix250 (zAt (skip 0) h l (false :: true :: (List.replicate v true ++ X))) 3 =
      leftAt markFirst h l (false :: false :: (List.replicate v true ++ X)) := by
  rw [zipRun_first, step_right _ _ _ _ _ _ _ _ row_skip_target,
    zipRun_first, step_left _ _ _ _ _ _ _ _ row_erase_one, leftAt_cons,
    zipRun_first, step_left _ _ _ _ _ _ _ _ row_mark_back]
  simp only [zipRun]
  congr 1
  omega

def markExit (pre : List Nat) : Fin 250 :=
  if pre = [] then markFirst else markReturnZero

/-- Mark with an arbitrary terminal word, so both unpadded and explicitly
padded whole-file contracts are immediate clients. -/
theorem mark_word (pre : List Nat) (v : Nat) (hp : pre.length < 9)
    (h : Int) (l X : List Bool) :
    zipRun machinePrefix250
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
  · rw [RegisterMarkPerm252.return_end machinePrefix250 markReturnOnes
      markReturnZero row_mark_return_one row_mark_return_zero
      row_mark_return_probe pre he markFirst row_mark_enter]
    simp only [markExit, if_neg he]
    congr 1
    omega

/-- Unpadded register-file contract, including every finite spare suffix. -/
theorem mark_zip (pre : List Nat) (v : Nat) (rest : List Nat)
    (hp : pre.length < 9) (h : Int) (l : List Bool) :
    zipRun machinePrefix250
      (zAt (skip pre.length) h l (registerBits (pre ++ v :: rest)))
      (2 * width pre + 3) =
      leftAt (markExit pre) h l
        (registerBits pre ++ false :: false ::
          (List.replicate v true ++ registerBits rest)) := by
  simpa only [registerBits_append, registerBits] using
    mark_word pre v hp h l (registerBits rest)

/-- Whole-tape Core semantics; no fixed false padding is required. -/
theorem mark {c : Config 250} (pre : List Nat) (v : Nat) (rest : List Nat)
    (hp : pre.length < 9) (h : Int) (l : List Bool)
    (hc : ZipRep c (zAt (skip pre.length) h l (registerBits (pre ++ v :: rest)))) :
    ZipRep (machinePrefix250.runFrom c (2 * width pre + 3))
      (leftAt (markExit pre) h l
        (registerBits pre ++ false :: false ::
          (List.replicate v true ++ registerBits rest))) := by
  have hs := zipRun_sound machinePrefix250 (2 * width pre + 3) hc
  rw [mark_zip pre v rest hp] at hs
  exact hs

/-- The same execution with an arbitrary explicitly represented terminal word. -/
theorem mark_with_suffix {c : Config 250} (pre : List Nat) (v : Nat)
    (hp : pre.length < 9) (h : Int) (l X : List Bool)
    (hc : ZipRep c (zAt (skip pre.length) h l
      (registerBits pre ++ false :: true :: (List.replicate v true ++ X)))) :
    ZipRep (machinePrefix250.runFrom c (2 * width pre + 3))
      (leftAt (markExit pre) h l
        (registerBits pre ++ false :: false :: (List.replicate v true ++ X))) := by
  have hs := zipRun_sound machinePrefix250 (2 * width pre + 3) hc
  rw [mark_word pre v hp] at hs
  exact hs

end SetTheory.BusyBeaver.ZFC.RegisterMarkPrefix250
