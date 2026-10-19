import BusyBeaver.ZFC.TableRotation244
import BusyBeaver.ZFC.RegisterMarkPerm252

/-!
Fresh Rotation244 port of RegisterMarkRouting245.
Only machine/state/module identities and the explicit selector literals change.
All-register, complete-tape and positive-clock hypotheses are retained.
The original Mira-Cult/Jeff Ketchersid/Andrew James Wade and ProveIt lineage
remains attributed. This source is uncompiled at emission; coverage, exact
blank initialization and the final Combined243 calibration remain separate.
-/

namespace SetTheory.BusyBeaver.ZFC.RegisterMarkRotation244

open FiniteZipper ZipperRuns RegisterBoxesPerm252

/-- The nine selectors in increasing physical-register order. -/
def skip : Nat → Fin 244
  | 0 => oldStateRotation244 60
  | 1 => oldStateRotation244 44
  | 2 => oldStateRotation244 31
  | 3 => oldStateRotation244 56
  | 4 => oldStateRotation244 38
  | 5 => oldStateRotation244 40
  | 6 => oldStateRotation244 28
  | 7 => oldStateRotation244 64
  | _ => oldStateRotation244 69

def restoreZero : Fin 244 := oldStateRotation244 20
def markFirst : Fin 244 := oldStateRotation244 2
def markReturnOnes : Fin 244 := oldStateRotation244 4
def markReturnZero : Fin 244 := oldStateRotation244 6

theorem skip_one_facts : ∀ j : Fin 9,
    machineRotation244.transition (skip j.val) true = ⟨true, .right, some (skip j.val)⟩ := by decide +kernel

theorem skip_next_facts : ∀ j : Fin 8,
    machineRotation244.transition (skip (j.val + 1)) false =
      ⟨false, .right, some (skip j.val)⟩ := by decide +kernel

theorem row_skip_target :
    machineRotation244.transition (skip 0) false = ⟨false, .right, some restoreZero⟩ := by decide +kernel
theorem row_erase_one :
    machineRotation244.transition restoreZero true = ⟨false, .left, some markFirst⟩ := by decide +kernel
theorem row_mark_back :
    machineRotation244.transition markFirst false = ⟨false, .left, some markFirst⟩ := by decide +kernel
theorem row_mark_enter :
    machineRotation244.transition markFirst true = ⟨true, .left, some markReturnOnes⟩ := by decide +kernel
theorem row_mark_return_one :
    machineRotation244.transition markReturnOnes true =
      ⟨true, .left, some markReturnOnes⟩ := by decide +kernel
theorem row_mark_return_zero :
    machineRotation244.transition markReturnOnes false =
      ⟨false, .left, some markReturnZero⟩ := by decide +kernel
theorem row_mark_return_probe :
    machineRotation244.transition markReturnZero true =
      ⟨true, .left, some markReturnOnes⟩ := by decide +kernel

theorem skip_block (j : Nat) (hj : j < 8) (v : Nat) (h : Int) (l X : List Bool) :
    zipRun machineRotation244 (zAt (skip (j + 1)) h l
      (false :: true :: (List.replicate v true ++ X))) (v + 2) =
      zAt (skip j) (h + ((v + 2 : Nat) : Int))
        (List.replicate (v + 1) true ++ false :: l) X := by
  rw [show v + 2 = (v + 1) + 1 by omega, zipRun_first,
    step_right _ _ _ _ _ _ _ _ (skip_next_facts ⟨j, hj⟩)]
  change zipRun machineRotation244
    (zAt (skip j) (h + 1) (false :: l) (List.replicate (v + 1) true ++ X)) (v + 1) = _
  rw [scan_right _ _ _ (skip_one_facts ⟨j, by omega⟩)]
  congr 1
  omega

theorem skip_file (pre : List Nat) (m : Nat) (hm : pre.length + m < 9)
    (h : Int) (l X : List Bool) :
    zipRun machineRotation244 (zAt (skip (pre.length + m)) h l (registerBits pre ++ X))
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
    zipRun machineRotation244 (zAt (skip 0) h l (false :: true :: (List.replicate v true ++ X))) 3 =
      leftAt markFirst h l (false :: false :: (List.replicate v true ++ X)) := by
  rw [zipRun_first, step_right _ _ _ _ _ _ _ _ row_skip_target,
    zipRun_first, step_left _ _ _ _ _ _ _ _ row_erase_one, leftAt_cons,
    zipRun_first, step_left _ _ _ _ _ _ _ _ row_mark_back]
  simp only [zipRun]
  congr 1
  omega

def markExit (pre : List Nat) : Fin 244 :=
  if pre = [] then markFirst else markReturnZero

/-- Mark with an arbitrary terminal word, so both unpadded and explicitly
padded whole-file contracts are immediate clients. -/
theorem mark_word (pre : List Nat) (v : Nat) (hp : pre.length < 9)
    (h : Int) (l X : List Bool) :
    zipRun machineRotation244
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
  · rw [RegisterMarkPerm252.return_end machineRotation244 markReturnOnes
      markReturnZero row_mark_return_one row_mark_return_zero
      row_mark_return_probe pre he markFirst row_mark_enter]
    simp only [markExit, if_neg he]
    congr 1
    omega

/-- Unpadded register-file contract, including every finite spare suffix. -/
theorem mark_zip (pre : List Nat) (v : Nat) (rest : List Nat)
    (hp : pre.length < 9) (h : Int) (l : List Bool) :
    zipRun machineRotation244
      (zAt (skip pre.length) h l (registerBits (pre ++ v :: rest)))
      (2 * width pre + 3) =
      leftAt (markExit pre) h l
        (registerBits pre ++ false :: false ::
          (List.replicate v true ++ registerBits rest)) := by
  simpa only [registerBits_append, registerBits] using
    mark_word pre v hp h l (registerBits rest)

/-- Whole-tape Core semantics; no fixed false padding is required. -/
theorem mark {c : Config 244} (pre : List Nat) (v : Nat) (rest : List Nat)
    (hp : pre.length < 9) (h : Int) (l : List Bool)
    (hc : ZipRep c (zAt (skip pre.length) h l (registerBits (pre ++ v :: rest)))) :
    ZipRep (machineRotation244.runFrom c (2 * width pre + 3))
      (leftAt (markExit pre) h l
        (registerBits pre ++ false :: false ::
          (List.replicate v true ++ registerBits rest))) := by
  have hs := zipRun_sound machineRotation244 (2 * width pre + 3) hc
  rw [mark_zip pre v rest hp] at hs
  exact hs

/-- The same execution with an arbitrary explicitly represented terminal word. -/
theorem mark_with_suffix {c : Config 244} (pre : List Nat) (v : Nat)
    (hp : pre.length < 9) (h : Int) (l X : List Bool)
    (hc : ZipRep c (zAt (skip pre.length) h l
      (registerBits pre ++ false :: true :: (List.replicate v true ++ X)))) :
    ZipRep (machineRotation244.runFrom c (2 * width pre + 3))
      (leftAt (markExit pre) h l
        (registerBits pre ++ false :: false :: (List.replicate v true ++ X))) := by
  have hs := zipRun_sound machineRotation244 (2 * width pre + 3) hc
  rw [mark_word pre v hp] at hs
  exact hs

end SetTheory.BusyBeaver.ZFC.RegisterMarkRotation244
