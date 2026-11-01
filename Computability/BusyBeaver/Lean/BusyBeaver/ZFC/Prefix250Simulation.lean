import BusyBeaver.ZFC.Prefix246Simulation
import BusyBeaver.ZFC.RegisterPathClean
import BusyBeaver.ZFC.SitePrefix250

/-!
Whole-tape frame adapters for the exact shared-carry prefix250 machine.

Adapted from Permutation252Simulation and the attributed Mira-Cult, Jeff,
and Wade framework at upstream 297ab8df7e5de329605c3875b4934643b371a5e3.
The generic physical-register layout and dispatch frame are retained.

The symbolic file has no artificial final false cell. Increment appends a
value-one spare; positive decrement retains the suffix and contributes one
extra cell to the header distance. Branch validity explicitly requires a
nonempty spare suffix, which ensures at least ten physical blocks.

These are conditional framing and register-update adapters. No site is
asserted to pass, no decoder coverage is assumed, and no bootstrap or
consistency theorem is claimed here.
-/

namespace SetTheory.BusyBeaver.ZFC.Prefix250Simulation
export SetTheory.BusyBeaver.ZFC.Prefix246Simulation (registerBits_eq incr_eq_write decr_eq_write nth_vregs_append_getD valid_none valid_branch)

open RegisterPath FiniteZipper Permutation252Frame SymbolicPrefix250

theorem flat_map_bit (n : Nat) (vs : List Nat) (P : List Bool) :
    flat n vs (P.map Segment.bit) = P := by
  induction P with
  | nil => rfl
  | cons b P ih => simpa only [List.map_cons, flat_cons, segmentBits,
      List.singleton_append] using congrArg (List.cons b) ih

theorem start_concrete (n : Nat) (vs : List Nat) (Q : List Bool) (h : Int) :
    concrete n vs (SitePrefix250.start Q) h =
      zAtS (some SitePrefix250.dispatch) h [true]
        (Q ++ List.replicate (n + (40 - Q.length)) false ++ [true] ++
          Permutation252Frame.registerBits vs) := by
  simp only [concrete, SitePrefix250.start, Bool.false_eq_true, if_false]
  rw [flat_append, flat_map_bit]
  simp [SitePrefix250.minDistance, flat, segmentBits, boxBits, registerBits_eq,
    zAtS, List.append_assoc]

private theorem strip_padding {binary : Config 250} (q : Option (Fin 250))
    (h : Int) (l r : List Bool) (leftPadding rightPadding : Nat)
    (hz : ZipRep binary (zAtS q h (l ++ List.replicate leftPadding false)
      (r ++ List.replicate rightPadding false))) :
    ZipRep binary (zAtS q h l r) := by
  apply zipRep_at_congr q h _ _ _ _ _ _ hz
  · intro i
    exact getD_append_padding l leftPadding i
  · intro i
    exact getD_append_padding r rightPadding i

/-- The stored path may be shorter than the consumed prefix. The missing
bits are taken from its existing zero gap, preserving the complete tape. -/
theorem source_represents (logical : Configuration) (binary : Config 250)
    (gap : Nat) (spares : List Nat) (Q : List Bool)
    (hf : DispatchFrame SitePrefix250.dispatch binary logical gap spares)
    (hq : Q = consume logical.path Q.length)
    (hz : ∀ b ∈ logical.path.drop Q.length, b = false)
    (hd : Q.length ≤ 40) :
    Represents (logical.path.length + gap - 40)
      (vregs logical.registers ++ spares) (SitePrefix250.start Q) binary := by
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
    (overflow : Bool) (extra : Nat) (x : Box) (h : Int) :
    concrete n vs (SitePrefix250.target P overflow extra x) h =
      zAtS (some SitePrefix250.dispatch) h [true]
        (P ++ List.replicate (n + (40 + (if overflow then 1 else 0) + extra - P.length)) false ++
          [true] ++ boxBits x vs) := by
  simp only [concrete, SitePrefix250.target, Bool.false_eq_true, if_false]
  rw [flat_append, flat_map_bit]
  simp [SitePrefix250.minDistance, flat, segmentBits, zAtS, List.append_assoc]

/-- Rebase a checked symbolic target at the updated logical register file.
The box equality states its entire physical file, including the spare tail. -/
theorem target_frame (n : Nat) (vs : List Nat) (P : List Bool)
    (overflow : Bool) (extra : Nat) (x : Box) (R' : Registers) (spares' : List Nat)
    (binary : Config 250)
    (hlen : P.length ≤ 40 + (if overflow then 1 else 0) + extra)
    (htail : LogicalTailZero R')
    (hbox : boxBits x vs =
      Permutation252Frame.registerBits (vregs R' ++ spares'))
    (hr : Represents n vs (SitePrefix250.target P overflow extra x) binary) :
    DispatchFrame SitePrefix250.dispatch binary ⟨P, R'⟩
      (n + (40 + (if overflow then 1 else 0) + extra - P.length)) spares' := by
  obtain ⟨h, hr⟩ := hr
  rw [target_concrete, hbox] at hr
  have hh : binary.head = h := hr.2.1
  refine ⟨by dsimp; omega, htail, 0, 0, ?_⟩
  simpa only [dispatchZip, zAtS, hh, List.replicate_zero,
    List.append_nil, List.cons_append, List.nil_append, List.append_assoc] using hr

theorem unchanged_rebase (R : Registers) (spares : List Nat) :
    boxBits (.plain .unchanged) (vregs R ++ spares) =
      Permutation252Frame.registerBits (vregs R ++ spares) := by
  simp only [boxBits, registerBits_eq]

theorem increment_rebase (R : Registers) (spares : List Nat) (r : Nat) (hr : r < 9) :
    boxBits (.plain (.increment (SitePrefix250.physical r hr))) (vregs R ++ spares) =
      Permutation252Frame.registerBits (vregs (update R r (R r + 1)) ++ (spares ++ [1])) := by
  have hp := physOf_lt (⟨r, hr⟩ : Fin 9)
  change physOf r < 9 at hp
  change RegisterBoxesPerm252.registerBits (incr (physOf r) (vregs R ++ spares) ++ [1]) = _
  rw [incr_eq_write _ _ (by simp only [List.length_append, vregs_length]; omega),
    nth_vregs_append_getD R spares r hr, update_vregs_append R spares r (R r + 1) hr,
    List.append_assoc, registerBits_eq]

theorem decrement_rebase (R : Registers) (spares : List Nat) (r : Nat) (hr : r < 9) :
    boxBits (.plain (.decrement (SitePrefix250.physical r hr))) (vregs R ++ spares) =
      Permutation252Frame.registerBits
        (vregs (update R r (R r - 1)) ++ spares) := by
  have hp := physOf_lt (⟨r, hr⟩ : Fin 9)
  change physOf r < 9 at hp
  change RegisterBoxesPerm252.registerBits (decr (physOf r) (vregs R ++ spares)) = _
  rw [decr_eq_write _ _ (by simp only [List.length_append, vregs_length]; omega),
    nth_vregs_append_getD R spares r hr, update_vregs_append R spares r (R r).pred hr]
  simp only [Nat.pred_eq_sub_one, List.append_assoc, registerBits_eq]

end SetTheory.BusyBeaver.ZFC.Prefix250Simulation
