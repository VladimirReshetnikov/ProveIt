import BusyBeaver.ZFC.RegisterBoxes253

/-!
Marking a primary register in the actual public253 table.

Source contract: mira-emmy PR20 head
0d544f2a2e3c18f12278441a74b7879f31cbe856,
`ZF/m253/coq/tm/Box.v`, `skip` and `box_mark`. The original machine is
Mira-Cult's, its verification is Jeff's, and the compiler framework is Wade's.
This proves the concrete binary excursion, with arbitrary register values,
spare suffix and external left context. Reachable-PC and general-dispatch
invariants remain separate obligations.
-/

namespace SetTheory.BusyBeaver.ZFC.RegisterMark253

open FiniteZipper ZipperRuns RegisterBoxes253

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/- The three-row return scanner is reusable by other actual253 boxes. -/
section Return

variable {n : Nat} (M : Machine n) (qa qb : Fin n)
    (one : M.transition qa true = ⟨true, .left, some qa⟩)
    (zero : M.transition qa false = ⟨false, .left, some qb⟩)
    (probe : M.transition qb true = ⟨true, .left, some qa⟩)

include one zero probe

theorem return_separator_left (rp : List Nat) (h : Int) (l Y : List Bool) :
    zipRun M (zAt qa h (leftBits rp ++ l) (false :: Y)) (width rp + 1) =
      leftAt qb (h - (width rp : Int)) l
        (registerBits rp.reverse ++ false :: Y) := by
  induction rp generalizing h Y with
  | nil =>
    simpa [width, leftBits, registerBits, zipRun] using
      step_left M qa qb false false h l Y zero
  | cons v rp ih =>
    simp only [width, leftBits, List.cons_append, List.append_assoc]
    rw [show v + 2 + width rp + 1 = (v + 2) + (width rp + 1) by omega, zipRun_add]
    have first :
        zipRun M
          (zAt qa h (true :: (List.replicate v true ++ false :: (leftBits rp ++ l)))
            (false :: Y)) (v + 2) =
        zAt qa (h - ((v + 2 : Nat) : Int)) (leftBits rp ++ l)
          (false :: (List.replicate v true ++ true :: false :: Y)) := by
      rw [show v + 2 = (v + 1) + 1 by omega, zipRun_first,
        step_left _ _ _ _ _ _ _ _ zero, leftAt_cons, zipRun_first,
        step_left _ _ _ _ _ _ _ _ probe,
        scan_left _ _ _ one, leftAt_cons]
      congr 1
      omega
    rw [first, ih]
    simp only [List.reverse_cons, registerBits_append, registerBits,
      List.append_nil, List.append_assoc, List.cons_append]
    have e : List.replicate v true ++ true :: false :: Y =
        true :: (List.replicate v true ++ false :: Y) := by
      calc
        _ = (List.replicate v true ++ [true]) ++ false :: Y :=
          (List.append_assoc _ _ _).symm
        _ = _ := by rw [← List.replicate_succ', List.replicate_succ]; rfl
    rw [e]
    congr 1
    omega

/-- Return from the last one of a nonempty file; every block is preserved. -/
theorem return_end_left (rp : List Nat) (hne : rp ≠ []) (q : Fin n)
    (enter : M.transition q true = ⟨true, .left, some qa⟩)
    (h : Int) (l Y : List Bool) :
    zipRun M (leftAt q h (leftBits rp ++ l) Y) (width rp) =
      leftAt qb (h - (width rp : Int)) l (registerBits rp.reverse ++ Y) := by
  cases rp with
  | nil => exact (hne rfl).elim
  | cons v rp =>
    simp only [width, leftBits, List.cons_append, List.append_assoc]
    rw [show v + 2 + width rp = (v + 1) + (width rp + 1) by omega, zipRun_add]
    have first :
        zipRun M
          (leftAt q h (true :: (List.replicate v true ++ false :: (leftBits rp ++ l))) Y)
          (v + 1) =
        zAt qa (h - ((v + 2 : Nat) : Int)) (leftBits rp ++ l)
          (false :: (List.replicate v true ++ true :: Y)) := by
      rw [leftAt_cons, zipRun_first, step_left _ _ _ _ _ _ _ _ enter,
        scan_left _ _ _ one, leftAt_cons]
      congr 1
      omega
    rw [first, return_separator_left M qa qb one zero probe]
    simp only [List.reverse_cons, registerBits_append, registerBits,
      List.append_nil, List.append_assoc, List.cons_append]
    have e : List.replicate v true ++ true :: Y =
        true :: (List.replicate v true ++ Y) := by
      calc
        _ = (List.replicate v true ++ [true]) ++ Y := (List.append_assoc _ _ _).symm
        _ = _ := by rw [← List.replicate_succ', List.replicate_succ]; rfl
    rw [e]
    congr 1
    omega

theorem return_end (pre : List Nat) (hne : pre ≠ []) (q : Fin n)
    (enter : M.transition q true = ⟨true, .left, some qa⟩)
    (h : Int) (l Y : List Bool) :
    zipRun M (leftAt q h ((registerBits pre).reverse ++ l) Y) (width pre) =
      leftAt qb (h - (width pre : Int)) l (registerBits pre ++ Y) := by
  have hr : pre.reverse ≠ [] := by
    intro he
    have hh := congrArg List.reverse he
    simp only [List.reverse_reverse, List.reverse_nil] at hh
    exact hne hh
  simpa only [reverse_registerBits, width_reverse, List.reverse_reverse] using
    return_end_left M qa qb one zero probe pre.reverse hr q enter h l Y

end Return

/-- The nine published skip states, in increasing physical-register order. -/
def skip : Nat → Fin 253
  | 0 => ⟨17, by decide⟩ -- old60
  | 1 => ⟨15, by decide⟩ -- old44
  | 2 => ⟨13, by decide⟩ -- old31
  | 3 => ⟨11, by decide⟩ -- old56
  | 4 => ⟨9, by decide⟩  -- old38
  | 5 => ⟨7, by decide⟩  -- old40
  | 6 => ⟨5, by decide⟩  -- old28
  | 7 => ⟨2, by decide⟩  -- old64
  | _ => ⟨122, by decide⟩ -- old69; only index8 is used below

def markFirst : Fin 253 := ⟨20, by decide⟩ -- old2
def markReturnOnes : Fin 253 := ⟨22, by decide⟩ -- old4
def markReturnZero : Fin 253 := ⟨24, by decide⟩ -- old6

theorem skip_one_facts : ∀ j : Fin 9,
    machine253.transition (skip j.val) true = ⟨true, .right, some (skip j.val)⟩ := by decide

theorem skip_next_facts : ∀ j : Fin 8,
    machine253.transition (skip (j.val + 1)) false =
      ⟨false, .right, some (skip j.val)⟩ := by decide

theorem row_skip_target :
    machine253.transition (skip 0) false = ⟨false, .right, some restoreZero⟩ := by decide
theorem row_erase_one :
    machine253.transition restoreZero true = ⟨false, .left, some markFirst⟩ := by decide
theorem row_mark_back :
    machine253.transition markFirst false = ⟨false, .left, some markFirst⟩ := by decide
theorem row_mark_enter :
    machine253.transition markFirst true = ⟨true, .left, some markReturnOnes⟩ := by decide
theorem row_mark_return_one :
    machine253.transition markReturnOnes true =
      ⟨true, .left, some markReturnOnes⟩ := by decide
theorem row_mark_return_zero :
    machine253.transition markReturnOnes false =
      ⟨false, .left, some markReturnZero⟩ := by decide
theorem row_mark_return_probe :
    machine253.transition markReturnZero true =
      ⟨true, .left, some markReturnOnes⟩ := by decide

theorem skip_block (j : Nat) (hj : j < 8) (v : Nat) (h : Int) (l X : List Bool) :
    zipRun machine253 (zAt (skip (j + 1)) h l
      (false :: true :: (List.replicate v true ++ X))) (v + 2) =
      zAt (skip j) (h + ((v + 2 : Nat) : Int))
        (List.replicate (v + 1) true ++ false :: l) X := by
  rw [show v + 2 = (v + 1) + 1 by omega, zipRun_first,
    step_right _ _ _ _ _ _ _ _ (skip_next_facts ⟨j, hj⟩)]
  change zipRun machine253
    (zAt (skip j) (h + 1) (false :: l) (List.replicate (v + 1) true ++ X)) (v + 1) = _
  rw [scan_right _ _ _ (skip_one_facts ⟨j, by omega⟩)]
  congr 1
  omega

theorem skip_file (pre : List Nat) (m : Nat) (hm : pre.length + m < 9)
    (h : Int) (l X : List Bool) :
    zipRun machine253 (zAt (skip (pre.length + m)) h l (registerBits pre ++ X))
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
    zipRun machine253 (zAt (skip 0) h l (false :: true :: (List.replicate v true ++ X))) 3 =
      leftAt markFirst h l (false :: false :: (List.replicate v true ++ X)) := by
  rw [zipRun_first, step_right _ _ _ _ _ _ _ _ row_skip_target,
    zipRun_first, step_left _ _ _ _ _ _ _ _ row_erase_one, leftAt_cons,
    zipRun_first, step_left _ _ _ _ _ _ _ _ row_mark_back]
  simp only [zipRun]
  congr 1
  omega

def markExit (pre : List Nat) : Fin 253 := if pre = [] then markFirst else markReturnZero

/-- Mark the selected register and return over every preceding register. -/
theorem mark_zip (pre : List Nat) (v : Nat) (rest : List Nat) (hp : pre.length < 9)
    (h : Int) (l : List Bool) :
    zipRun machine253
      (zAt (skip pre.length) h l (registerBits (pre ++ v :: rest) ++ [false]))
      (2 * width pre + 3) =
      leftAt (markExit pre) h l
        (registerBits pre ++ false :: false :: (List.replicate v true ++ registerBits rest ++ [false])) := by
  rw [show 2 * width pre + 3 = width pre + (3 + width pre) by omega,
    registerBits_append]
  simp only [registerBits, List.append_assoc, List.cons_append]
  have forward := skip_file pre 0 (by simpa using hp) h l
    (false :: true :: (List.replicate v true ++ registerBits rest ++ [false]))
  simp only [Nat.add_zero, List.append_assoc] at forward
  rw [zipRun_add, forward, zipRun_add, mark_steps]
  by_cases he : pre = []
  · subst pre
    simp [width, registerBits, zipRun, markExit]
  · rw [return_end machine253 markReturnOnes markReturnZero row_mark_return_one
      row_mark_return_zero row_mark_return_probe pre he markFirst row_mark_enter]
    simp only [markExit, if_neg he]
    congr 1
    omega

/-- Whole-tape Core semantics for the marking excursion, not an oracle box. -/
theorem mark {c : Config 253} (pre : List Nat) (v : Nat) (rest : List Nat)
    (hp : pre.length < 9) (h : Int) (l : List Bool)
    (hc : ZipRep c
      (zAt (skip pre.length) h l (registerBits (pre ++ v :: rest) ++ [false]))) :
    ZipRep (machine253.runFrom c (2 * width pre + 3))
      (leftAt (markExit pre) h l
        (registerBits pre ++ false :: false :: (List.replicate v true ++ registerBits rest ++ [false]))) := by
  have hs := zipRun_sound machine253 (2 * width pre + 3) hc
  rw [mark_zip pre v rest hp] at hs
  exact hs

end SetTheory.BusyBeaver.ZFC.RegisterMark253
