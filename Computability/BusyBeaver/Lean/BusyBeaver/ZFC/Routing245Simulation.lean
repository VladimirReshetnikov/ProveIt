import BusyBeaver.ZFC.RegisterPathClean
import BusyBeaver.ZFC.SiteRouting245

/-!
Whole-tape frame adapters for the literal routing245 machine.

Port of the checked Prefix246Simulation contracts, with a scoped header
budget of 64 cells for the new decoder. The physical-register permutation
and generic dispatch zipper remain unchanged. The historical distance-40
DispatchFrame predicate is retained in its original module; this module
introduces DispatchFrame64 and uses it throughout its new frame contracts.

The framework derives from Mira-Cult and Jeff's original machine verification
and Wade's path semantics at upstream 297ab8df7e5de329605c3875b4934643b371a5e3.
The symbolic file has no artificial final false cell. Increment appends a
value-one spare; positive decrement preserves the suffix and contributes
one extra cell to the header distance. Branch validity explicitly requires
a nonempty spare suffix, ensuring at least ten physical blocks.

The adapters quantify over arbitrary register values, gaps and spare values,
and retain the entire infinite tape. Their symbolic execution premises are
explicit. Actual site coverage, the blank bootstrap and the PA comparison
remain separate obligations.
-/

namespace SetTheory.BusyBeaver.ZFC.Routing245Simulation

open RegisterPath FiniteZipper Permutation252Frame SymbolicRouting245

/-- The routing decoder's whole-tape dispatch frame. Its margin is 64,
while padding, all register values and the complete spare suffix remain free. -/
def DispatchFrame64 {states : Nat} (dispatch : Fin states) (binary : Config states)
    (logical : Configuration) (gap : Nat) (spares : List Nat) : Prop :=
  64 ≤ logical.path.length + gap ∧ LogicalTailZero logical.registers ∧
    ∃ leftPadding rightPadding : Nat,
      ZipRep binary (dispatchZip dispatch binary.head leftPadding rightPadding logical gap spares)

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
    concrete n vs (SiteRouting245.start Q) h =
      zAtS (some SiteRouting245.dispatch) h [true]
        (Q ++ List.replicate (n + (64 - Q.length)) false ++ [true] ++
          Permutation252Frame.registerBits vs) := by
  simp only [concrete, SiteRouting245.start, Bool.false_eq_true, if_false]
  rw [flat_append, flat_map_bit]
  simp [SiteRouting245.minDistance, flat, segmentBits, boxBits, registerBits_eq,
    zAtS, List.append_assoc]

private theorem strip_padding {binary : Config 245} (q : Option (Fin 245))
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
theorem source_represents (logical : Configuration) (binary : Config 245)
    (gap : Nat) (spares : List Nat) (Q : List Bool)
    (hf : DispatchFrame64 SiteRouting245.dispatch binary logical gap spares)
    (hq : Q = consume logical.path Q.length)
    (hz : ∀ b ∈ logical.path.drop Q.length, b = false)
    (hd : Q.length ≤ 64) :
    Represents (logical.path.length + gap - 64)
      (vregs logical.registers ++ spares) (SiteRouting245.start Q) binary := by
  rcases hf with ⟨hbudget, htail, leftPadding, rightPadding, hf⟩
  have hpc : logical.path ++ List.replicate gap false =
      Q ++ List.replicate ((logical.path.length + gap - 64) +
        (64 - Q.length)) false := by
    have he := RegisterPathClean.gap_consume logical.path gap Q.length (by omega) hz
    rw [← hq] at he
    rw [he]
    congr 2
    omega
  refine ⟨binary.head, ?_⟩
  rw [start_concrete]
  apply strip_padding _ _ [true]
    (Q ++ List.replicate ((logical.path.length + gap - 64) +
      (64 - Q.length)) false ++ [true] ++
      Permutation252Frame.registerBits (vregs logical.registers ++ spares))
    leftPadding rightPadding
  simpa only [dispatchZip, hpc, zAtS, List.singleton_append,
    List.append_assoc] using hf

theorem target_concrete (n : Nat) (vs : List Nat) (P : List Bool)
    (overflow : Bool) (extra : Nat) (x : Box) (h : Int) :
    concrete n vs (SiteRouting245.target P overflow extra x) h =
      zAtS (some SiteRouting245.dispatch) h [true]
        (P ++ List.replicate (n + (64 + (if overflow then 1 else 0) + extra - P.length)) false ++
          [true] ++ boxBits x vs) := by
  simp only [concrete, SiteRouting245.target, Bool.false_eq_true, if_false]
  rw [flat_append, flat_map_bit]
  simp [SiteRouting245.minDistance, flat, segmentBits, zAtS, List.append_assoc]

/-- Rebase a checked symbolic target at the updated logical register file.
The box equality states its entire physical file, including the spare tail. -/
theorem target_frame (n : Nat) (vs : List Nat) (P : List Bool)
    (overflow : Bool) (extra : Nat) (x : Box) (R' : Registers) (spares' : List Nat)
    (binary : Config 245)
    (hlen : P.length ≤ 64 + (if overflow then 1 else 0) + extra)
    (htail : LogicalTailZero R')
    (hbox : boxBits x vs =
      Permutation252Frame.registerBits (vregs R' ++ spares'))
    (hr : Represents n vs (SiteRouting245.target P overflow extra x) binary) :
    DispatchFrame64 SiteRouting245.dispatch binary ⟨P, R'⟩
      (n + (64 + (if overflow then 1 else 0) + extra - P.length)) spares' := by
  obtain ⟨h, hr⟩ := hr
  rw [target_concrete, hbox] at hr
  have hh : binary.head = h := hr.2.1
  refine ⟨by dsimp; omega, htail, 0, 0, ?_⟩
  simpa only [dispatchZip, zAtS, hh, List.replicate_zero,
    List.append_nil, List.cons_append, List.nil_append, List.append_assoc] using hr

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
      Permutation252Frame.registerBits (vregs R ++ spares) := by
  simp only [boxBits, registerBits_eq]

theorem nth_vregs_append_getD (R : Registers) (spares : List Nat) (r : Nat) (hr : r < 9) :
    (vregs R ++ spares).getD (physOf r) 0 = R r := by
  rw [List.getD_eq_getElem?_getD]
  exact nth_vregs_append R spares r hr

theorem increment_rebase (R : Registers) (spares : List Nat) (r : Nat) (hr : r < 9) :
    boxBits (.plain (.increment (SiteRouting245.physical r hr))) (vregs R ++ spares) =
      Permutation252Frame.registerBits (vregs (update R r (R r + 1)) ++ (spares ++ [1])) := by
  have hp := physOf_lt (⟨r, hr⟩ : Fin 9)
  change physOf r < 9 at hp
  change RegisterBoxesPerm252.registerBits (incr (physOf r) (vregs R ++ spares) ++ [1]) = _
  rw [incr_eq_write _ _ (by simp only [List.length_append, vregs_length]; omega),
    nth_vregs_append_getD R spares r hr, update_vregs_append R spares r (R r + 1) hr,
    List.append_assoc, registerBits_eq]

theorem decrement_rebase (R : Registers) (spares : List Nat) (r : Nat) (hr : r < 9) :
    boxBits (.plain (.decrement (SiteRouting245.physical r hr))) (vregs R ++ spares) =
      Permutation252Frame.registerBits
        (vregs (update R r (R r - 1)) ++ spares) := by
  have hp := physOf_lt (⟨r, hr⟩ : Fin 9)
  change physOf r < 9 at hp
  change RegisterBoxesPerm252.registerBits (decr (physOf r) (vregs R ++ spares)) = _
  rw [decr_eq_write _ _ (by simp only [List.length_append, vregs_length]; omega),
    nth_vregs_append_getD R spares r hr, update_vregs_append R spares r (R r).pred hr]
  simp only [Nat.pred_eq_sub_one, registerBits_eq]

theorem valid_none (R : Registers) (spares : List Nat) (hspares : spares ≠ []) :
    Valid none (vregs R ++ spares) := by
  refine ⟨?_, trivial⟩
  cases spares with
  | nil => exact False.elim (hspares rfl)
  | cons v rest => simp only [List.length_append, vregs_length, List.length_cons]; omega

theorem valid_branch (R : Registers) (spares : List Nat) (hspares : spares ≠ [])
    (r : Nat) (hr : r < 9)
    (zero : Bool) (hz : if zero then R r = 0 else R r ≠ 0) :
    Valid (some (SiteRouting245.physical r hr, zero)) (vregs R ++ spares) := by
  refine ⟨(valid_none R spares hspares).1, ?_⟩
  simpa only [SiteRouting245.physical, nth_vregs_append_getD R spares r hr] using hz

end SetTheory.BusyBeaver.ZFC.Routing245Simulation
