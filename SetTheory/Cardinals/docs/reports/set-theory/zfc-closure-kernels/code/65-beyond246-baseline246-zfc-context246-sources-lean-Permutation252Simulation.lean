import BusyBeaver.ZFC.RegisterPathClean
import BusyBeaver.ZFC.SitePerm252

/-!
Whole-tape framing adapters for the permutation252 symbolic site checker.

The machine, path operations, and site-checking strategy are attributed to
Mira-Cult, Jeff, and Wade's compiler framework as documented in the imported
modules (upstream commit 297ab8df7e5de329605c3875b4934643b371a5e3).

These adapters consume an explicit dispatch frame and clean consumed PC,
and rebase the symbolic checker's original physical register-file parameter
after a checked effect. Arbitrary physical spare data is retained. Positive
decrement appends a zero spare block. No decoder coverage or general
instruction-simulation theorem is assumed or asserted here.
-/

namespace SetTheory.BusyBeaver.ZFC.Permutation252Simulation

open RegisterPath FiniteZipper Permutation252Frame SymbolicPerm252

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

theorem registerBits_eq (vs : List Nat) :
    RegisterBoxesPerm252.registerBits vs = Permutation252Frame.registerBits vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change false :: true :: (List.replicate v true ++ RegisterBoxesPerm252.registerBits vs) =
      false :: true :: (List.replicate v true ++ Permutation252Frame.registerBits vs)
    rw [ih]

theorem flat_map_bit (n : Nat) (vs : List Nat) (P : List Bool) :
    flat n vs (P.map Segment.bit) = P := by
  induction P with
  | nil => rfl
  | cons b P ih => simpa only [List.map_cons, flat_cons, segmentBits,
      List.singleton_append] using congrArg (List.cons b) ih

theorem start_concrete (n : Nat) (vs : List Nat) (Q : List Bool) (h : Int) :
    concrete n vs (SitePerm252.start Q) h =
      zAtS (some SitePerm252.dispatch) h [true]
        ((Q ++ List.replicate (n + (40 - Q.length)) false ++ [true] ++
          Permutation252Frame.registerBits vs) ++ [false]) := by
  simp only [concrete, SitePerm252.start, Bool.false_eq_true, if_false]
  rw [flat_append, flat_map_bit]
  simp [SitePerm252.minDistance, flat, segmentBits, boxBits, registerBits_eq,
    zAtS, List.append_assoc]

private theorem strip_padding {binary : Config 252} (q : Option (Fin 252))
    (h : Int) (l r : List Bool) (leftPadding rightPadding : Nat)
    (hz : ZipRep binary (zAtS q h (l ++ List.replicate leftPadding false)
      (r ++ List.replicate rightPadding false))) :
    ZipRep binary (zAtS q h l (r ++ [false])) := by
  apply zipRep_at_congr q h _ _ _ _ _ _ hz
  · intro i
    exact getD_append_padding l leftPadding i
  · intro i
    exact (getD_append_padding r rightPadding i).trans
      (getD_append_padding r 1 i).symm

/-- The stored path may be shorter than the consumed prefix. The missing
bits are taken from its existing zero gap, preserving the complete tape. -/
theorem source_represents (logical : Configuration) (binary : Config 252)
    (gap : Nat) (spares : List Nat) (Q : List Bool)
    (hf : DispatchFrame SitePerm252.dispatch binary logical gap spares)
    (hq : Q = consume logical.path Q.length)
    (hz : ∀ b ∈ logical.path.drop Q.length, b = false)
    (hd : Q.length ≤ 40) :
    Represents (logical.path.length + gap - 40)
      (vregs logical.registers ++ spares) (SitePerm252.start Q) binary := by
  rcases hf with ⟨hbudget, htail, leftPadding, rightPadding, hf⟩
  have hpc : logical.path ++ List.replicate gap false =
      Q ++ List.replicate ((logical.path.length + gap - 40) +
        (40 - Q.length)) false := by
    have he := RegisterPathClean.gap_consume logical.path gap Q.length (by omega) hz
    rw [← hq] at he
    rw [he]
    congr 2
    omega
  refine ⟨binary.head, ?_⟩
  rw [start_concrete]
  apply strip_padding _ _ [true]
    (Q ++ List.replicate ((logical.path.length + gap - 40) +
      (40 - Q.length)) false ++ [true] ++
      Permutation252Frame.registerBits (vregs logical.registers ++ spares))
    leftPadding rightPadding
  simpa only [dispatchZip, hpc, zAtS, List.singleton_append,
    List.append_assoc] using hf

theorem target_concrete (n : Nat) (vs : List Nat) (P : List Bool)
    (overflow : Bool) (x : Box) (h : Int) :
    concrete n vs (SitePerm252.target P overflow x) h =
      zAtS (some SitePerm252.dispatch) h [true]
        (P ++ List.replicate (n + (40 + (if overflow then 1 else 0) - P.length)) false ++
          [true] ++ boxBits x vs) := by
  simp only [concrete, SitePerm252.target, Bool.false_eq_true, if_false]
  rw [flat_append, flat_map_bit]
  simp [SitePerm252.minDistance, flat, segmentBits, zAtS, List.append_assoc]

/-- Rebase a checked symbolic target at the updated logical register file.
The box equality states its entire physical file, including the spare tail. -/
theorem target_frame (n : Nat) (vs : List Nat) (P : List Bool)
    (overflow : Bool) (x : Box) (R' : Registers) (spares' : List Nat)
    (binary : Config 252)
    (hlen : P.length ≤ 40 + (if overflow then 1 else 0))
    (htail : LogicalTailZero R')
    (hbox : boxBits x vs =
      Permutation252Frame.registerBits (vregs R' ++ spares') ++ [false])
    (hr : Represents n vs (SitePerm252.target P overflow x) binary) :
    DispatchFrame SitePerm252.dispatch binary ⟨P, R'⟩
      (n + (40 + (if overflow then 1 else 0) - P.length)) spares' := by
  obtain ⟨h, hr⟩ := hr
  rw [target_concrete, hbox] at hr
  have hh : binary.head = h := hr.2.1
  refine ⟨by dsimp; omega, htail, 0, 1, ?_⟩
  simpa only [dispatchZip, zAtS, hh, List.replicate_zero,
    List.replicate_one, List.cons_append, List.nil_append, List.append_assoc] using hr

theorem incr_eq_write (vs : List Nat) (r : Nat) (hr : r < vs.length) :
    incr r vs = writeRegisters vs r (vs.getD r 0 + 1) := by
  induction r generalizing vs with
  | zero => cases vs <;> simp_all [incr, writeRegisters]
  | succ r ih =>
    cases vs with
    | nil => simp at hr
    | cons v vs =>
      change v :: incr r vs = v :: writeRegisters vs r (vs.getD r 0 + 1)
      rw [ih vs (by simpa using hr)]

theorem decr_eq_write (vs : List Nat) (r : Nat) (hr : r < vs.length) :
    decr r vs = writeRegisters vs r ((vs.getD r 0).pred) := by
  induction r generalizing vs with
  | zero => cases vs <;> simp_all [decr, writeRegisters]
  | succ r ih =>
    cases vs with
    | nil => simp at hr
    | cons v vs =>
      change v :: decr r vs = v :: writeRegisters vs r ((vs.getD r 0).pred)
      rw [ih vs (by simpa using hr)]

theorem unchanged_rebase (R : Registers) (spares : List Nat) :
    boxBits (.plain .unchanged) (vregs R ++ spares) =
      Permutation252Frame.registerBits (vregs R ++ spares) ++ [false] := by
  simp only [boxBits, registerBits_eq]

theorem nth_vregs_append_getD (R : Registers) (spares : List Nat) (r : Nat) (hr : r < 9) :
    (vregs R ++ spares).getD (physOf r) 0 = R r := by
  rw [List.getD_eq_getElem?_getD]
  exact nth_vregs_append R spares r hr

theorem increment_rebase (R : Registers) (spares : List Nat) (r : Nat) (hr : r < 9) :
    boxBits (.plain (.increment (SitePerm252.physical r hr))) (vregs R ++ spares) =
      Permutation252Frame.registerBits (vregs (update R r (R r + 1)) ++ spares) ++
        [false] := by
  have hp := physOf_lt (⟨r, hr⟩ : Fin 9)
  change physOf r < 9 at hp
  change RegisterBoxesPerm252.registerBits (incr (physOf r) (vregs R ++ spares)) ++
    [false] = _
  rw [incr_eq_write _ _ (by simp only [List.length_append, vregs_length]; omega),
    nth_vregs_append_getD R spares r hr, update_vregs_append R spares r (R r + 1) hr,
    registerBits_eq]

theorem decrement_rebase (R : Registers) (spares : List Nat) (r : Nat) (hr : r < 9) :
    boxBits (.plain (.decrement (SitePerm252.physical r hr))) (vregs R ++ spares) =
      Permutation252Frame.registerBits
        (vregs (update R r (R r - 1)) ++ (spares ++ [0])) ++ [false] := by
  have hp := physOf_lt (⟨r, hr⟩ : Fin 9)
  change physOf r < 9 at hp
  change RegisterBoxesPerm252.registerBits (decr (physOf r) (vregs R ++ spares) ++ [0]) ++
    [false] = _
  rw [decr_eq_write _ _ (by simp only [List.length_append, vregs_length]; omega),
    nth_vregs_append_getD R spares r hr, update_vregs_append R spares r (R r).pred hr]
  simp only [Nat.pred_eq_sub_one, List.append_assoc, registerBits_eq]

theorem valid_none (R : Registers) (spares : List Nat) :
    Valid none (vregs R ++ spares) :=
  ⟨by simp only [List.length_append, vregs_length]; omega, trivial⟩

theorem valid_branch (R : Registers) (spares : List Nat) (r : Nat) (hr : r < 9)
    (zero : Bool) (hz : if zero then R r = 0 else R r ≠ 0) :
    Valid (some (SitePerm252.physical r hr, zero)) (vregs R ++ spares) := by
  refine ⟨by simp only [List.length_append, vregs_length]; omega, ?_⟩
  simpa only [SitePerm252.physical, nth_vregs_append_getD R spares r hr] using hz

end SetTheory.BusyBeaver.ZFC.Permutation252Simulation
