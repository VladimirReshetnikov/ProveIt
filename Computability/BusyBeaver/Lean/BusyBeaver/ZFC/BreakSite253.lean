import BusyBeaver.ZFC.BootstrapFrame253
import BusyBeaver.ZFC.ZipperRuns

/-!
A complete concrete PC site of the actual public253 binary machine.

The literal Prog254 leaf at path001 is break1. This module proves its binary
execution for every gap, full register-file suffix and exterior context beyond
the ten-cell left margin. The source site contract is in mira-emmy PR20 head
0d544f2a2e3c18f12278441a74b7879f31cbe856, `ZF/m253/coq/tm/Site.v`;
the leaf/path semantics are Jeff's attributed `Prog254.v` / `RM.v` port.
Mira-Cult designed the original machine and Wade supplied its framework.

Only this concrete site is proved. There is no general decoder/site checker,
reachable-path invariant, first-arrival or enumeration/consistency claim.
-/

namespace SetTheory.BusyBeaver.ZFC.BreakSite253

open FiniteZipper ZipperRuns

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem row_forward :
    machine253.transition (14 : Fin 253) false = ⟨false, .right, some 14⟩ := by decide
theorem row_backward :
    machine253.transition (20 : Fin 253) false = ⟨false, .left, some 20⟩ := by decide
theorem row_margin_forward :
    machine253.transition (32 : Fin 253) false = ⟨false, .right, some 32⟩ := by decide
theorem row_dispatch_return :
    machine253.transition (32 : Fin 253) true = ⟨true, .right, some 33⟩ := by decide

/-- Decode001, erase its last bit, set the new first bit and seek the header. -/
theorem decoder_steps (gap : Nat) (h : Int) (l Y : List Bool) :
    zipRun machine253
      (zAt (33 : Fin 253) h l
        (false :: false :: true :: (List.replicate gap false ++ true :: false :: Y))) 5 =
      zAt (14 : Fin 253) (h + 1) (true :: l)
        (List.replicate (gap + 2) false ++ true :: false :: Y) := by
  rw [zipRun_first, step_right machine253 (33 : Fin 253) 34 false false _ _ _ (by decide),
    zipRun_first, step_right machine253 (34 : Fin 253) 36 false false _ _ _ (by decide),
    zipRun_first, step_left machine253 (36 : Fin 253) 10 true false _ _ _ (by decide), leftAt_cons,
    zipRun_first, step_left machine253 (10 : Fin 253) 12 false false _ _ _ (by decide), leftAt_cons,
    zipRun_first, step_right machine253 (12 : Fin 253) 14 false true _ _ _ (by decide)]
  simp only [zipRun, List.replicate_succ, List.cons_append]
  congr 1
  omega

/-- The first register separator is observed; all later file data is untouched. -/
theorem header_turn (h : Int) (l Y : List Bool) :
    zipRun machine253 (zAt (14 : Fin 253) h l (true :: false :: Y)) 3 =
      leftAt (20 : Fin 253) h l (true :: false :: Y) := by
  rw [zipRun_first, step_right machine253 (14 : Fin 253) 16 true false _ _ _ (by decide),
    zipRun_first, step_left machine253 (16 : Fin 253) 18 false false _ _ _ (by decide), leftAt_cons,
    zipRun_first, step_left machine253 (18 : Fin 253) 20 false true _ _ _ (by decide)]
  simp only [zipRun]
  congr 1
  omega

theorem margin_begin (h : Int) (L X : List Bool) :
    zipRun machine253
      (zAt (20 : Fin 253) h (true :: (List.replicate 10 false ++ L)) (true :: X)) 3 =
      zAt (24 : Fin 253) (h - 3) (List.replicate 8 false ++ L)
        (false :: false :: true :: true :: X) := by
  simp only [List.replicate_succ, List.replicate_zero, List.nil_append, List.cons_append]
  rw [zipRun_first, step_left machine253 (20 : Fin 253) 22 true true _ _ _ (by decide), leftAt_cons,
    zipRun_first, step_left machine253 (22 : Fin 253) 22 true true _ _ _ (by decide), leftAt_cons,
    zipRun_first, step_left machine253 (22 : Fin 253) 24 false false _ _ _ (by decide), leftAt_cons]
  simp only [zipRun]
  congr 1
  omega

/-- The eight distinct literal return states cross a fixed blank margin. -/
theorem margin_chain (h : Int) (L X : List Bool) :
    zipRun machine253
      (zAt (24 : Fin 253) h (List.replicate 8 false ++ L) (false :: X)) 8 =
      zAt (32 : Fin 253) (h - 8) L (List.replicate 9 false ++ X) := by
  simp only [List.replicate_succ, List.replicate_zero, List.nil_append, List.cons_append]
  rw [zipRun_first, step_left machine253 (24 : Fin 253) 25 false false _ _ _ (by decide), leftAt_cons,
    zipRun_first, step_left machine253 (25 : Fin 253) 26 false false _ _ _ (by decide), leftAt_cons,
    zipRun_first, step_left machine253 (26 : Fin 253) 27 false false _ _ _ (by decide), leftAt_cons,
    zipRun_first, step_left machine253 (27 : Fin 253) 28 false false _ _ _ (by decide), leftAt_cons,
    zipRun_first, step_left machine253 (28 : Fin 253) 29 false false _ _ _ (by decide), leftAt_cons,
    zipRun_first, step_left machine253 (29 : Fin 253) 30 false false _ _ _ (by decide), leftAt_cons,
    zipRun_first, step_left machine253 (30 : Fin 253) 31 false false _ _ _ (by decide), leftAt_cons,
    zipRun_first, step_left machine253 (31 : Fin 253) 32 false false _ _ _ (by decide), leftAt_cons]
  simp only [zipRun]
  congr 1
  omega

theorem margin_return (h : Int) (L X : List Bool) :
    zipRun machine253
      (zAt (20 : Fin 253) h (true :: (List.replicate 10 false ++ L)) (true :: X)) 22 =
      zAt (33 : Fin 253) h (true :: (List.replicate 10 false ++ L)) (true :: X) := by
  rw [show 22 = 3 + (8 + (10 + 1)) from rfl,
    zipRun_add, margin_begin, zipRun_add, margin_chain]
  change zipRun machine253
    (zAt (32 : Fin 253) (h - 3 - 8) L (List.replicate 10 false ++ true :: true :: X))
    (10 + 1) = _
  rw [zipRun_add, scan_right _ _ _ row_margin_forward, zipRun_first,
    step_right _ _ _ _ _ _ _ _ row_dispatch_return]
  simp only [zipRun]
  congr 1
  omega

/-- Complete site execution:001 becomes1, its padding grows by two and the
whole file, ten-cell margin and arbitrary farther-left data are retained. -/
theorem break001_zip (gap : Nat) (h : Int) (L Y : List Bool) :
    zipRun machine253
      (zAt (33 : Fin 253) h (true :: (List.replicate 10 false ++ L))
        (false :: false :: true :: (List.replicate gap false ++ true :: false :: Y)))
      (2 * gap + 34) =
      zAt (33 : Fin 253) h (true :: (List.replicate 10 false ++ L))
        (true :: (List.replicate (gap + 2) false ++ true :: false :: Y)) := by
  rw [show 2 * gap + 34 = 5 + ((gap + 2) + (3 + ((gap + 2) + 22))) by omega,
    zipRun_add, decoder_steps, zipRun_add, scan_right _ _ _ row_forward,
    zipRun_add, header_turn, zipRun_add, scan_left _ _ _ row_backward, leftAt_cons,
    margin_return]
  congr 1
  omega

theorem break001 {c : Config 253} (gap : Nat) (h : Int) (L Y : List Bool)
    (hc : ZipRep c
      (zAt (33 : Fin 253) h (true :: (List.replicate 10 false ++ L))
        (false :: false :: true :: (List.replicate gap false ++ true :: false :: Y)))) :
    ZipRep (machine253.runFrom c (2 * gap + 34))
      (zAt (33 : Fin 253) h (true :: (List.replicate 10 false ++ L))
        (true :: (List.replicate (gap + 2) false ++ true :: false :: Y))) := by
  have hs := zipRun_sound machine253 (2 * gap + 34) hc
  rw [break001_zip] at hs
  exact hs

/-- Source D0=40: path001 leaves n+37 gap cells, and returns with n+39. -/
theorem break001_D0 {c : Config 253} (n : Nat) (h : Int) (L Y : List Bool)
    (hc : ZipRep c
      (zAt (33 : Fin 253) h (true :: (List.replicate 10 false ++ L))
        (false :: false :: true :: (List.replicate (n + 37) false ++ true :: false :: Y)))) :
    ZipRep (machine253.runFrom c (2 * n + 108))
      (zAt (33 : Fin 253) h (true :: (List.replicate 10 false ++ L))
        (true :: (List.replicate (n + 39) false ++ true :: false :: Y))) := by
  have hs := break001 (n + 37) h L Y hc
  have ht : 2 * (n + 37) + 34 = 2 * n + 108 := by omega
  have hg : n + 37 + 2 = n + 39 := by omega
  simpa only [ht, hg] using hs

/-- The actual register-program instruction at this literal path. -/
theorem register_break001 (R : RegisterPath.Registers) :
    RegisterPath.step Prog254.program ⟨[false, false, true], R⟩ =
      some ⟨[true], R⟩ := rfl

private theorem zeros_getD (n i : Nat) : (List.replicate n false).getD i false = false := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => cases i with
    | zero => rfl
    | succ i => exact ih i

/-- The existing dispatch frame's entire left exterior is zero; its chosen
finite padding can therefore be represented with the ten-cell margin. -/
theorem normalize_left_margin {c : Config 253} (q : Fin 253) (h : Int)
    (padding : Nat) (r : List Bool)
    (hc : ZipRep c (zAt q h (true :: List.replicate padding false) r)) :
    ZipRep c (zAt q h (true :: List.replicate 10 false) r) := by
  refine ⟨hc.1, hc.2.1, ?_, hc.2.2.2⟩
  intro i
  cases i with
  | zero => exact hc.2.2.1 0
  | succ i =>
    have hx := hc.2.2.1 (i + 1)
    change Tape.read c.tape (h - ((i + 1 + 1 : Nat) : Int)) =
      (List.replicate padding false).getD i false at hx
    change Tape.read c.tape (h - ((i + 1 + 1 : Nat) : Int)) =
      (List.replicate 10 false).getD i false
    rw [zeros_getD] at hx ⊢
    exact hx

private theorem file_head (R : RegisterPath.Registers) (spares : List Nat) :
    ∃ Y, BootstrapFrame253.registerBits (BootstrapFrame253.primaryValues R ++ spares) =
      false :: Y := by
  unfold BootstrapFrame253.registerBits Boot253.registerBits253
    BootstrapFrame253.primaryValues Prefix330.physicalOrder
  exact ⟨_, rfl⟩

/-- This actual PC site preserves the existing whole dispatch representation,
including every primary and spare register and the logical zero tail. -/
theorem dispatch_frame_break001 {c : Config 253} (logical : RegisterPath.Configuration)
    (gap : Nat) (spares : List Nat) (hp : logical.path = [false, false, true])
    (hc : BootstrapFrame253.DispatchFrame BootstrapFrame253.dispatch253 c logical gap spares) :
    BootstrapFrame253.DispatchFrame BootstrapFrame253.dispatch253
      (machine253.runFrom c (2 * gap + 34)) { logical with path := [true] } (gap + 2) spares := by
  rcases hc with ⟨hgap, htail, leftPadding, rightPadding, hz⟩
  have hq : BootstrapFrame253.dispatch253 = (33 : Fin 253) := by decide
  change ZipRep c
    (zAt BootstrapFrame253.dispatch253 c.head (true :: List.replicate leftPadding false)
      (logical.path ++ List.replicate gap false ++ [true] ++
        BootstrapFrame253.registerBits (BootstrapFrame253.primaryValues logical.registers ++ spares) ++
        List.replicate rightPadding false)) at hz
  have hn := normalize_left_margin BootstrapFrame253.dispatch253 c.head leftPadding _ hz
  obtain ⟨Y, hY⟩ := file_head logical.registers spares
  have hi : ZipRep c
      (zAt (33 : Fin 253) c.head (true :: (List.replicate 10 false ++ []))
        (false :: false :: true :: (List.replicate gap false ++ true :: false ::
          (Y ++ List.replicate rightPadding false)))) := by
    simpa only [hq, hp, hY, List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
      using hn
  have hs := break001 gap c.head [] (Y ++ List.replicate rightPadding false) hi
  have hh : (machine253.runFrom c (2 * gap + 34)).head = c.head := hs.2.1
  refine ⟨?_, htail, 10, rightPadding, ?_⟩
  · simp only [hp, List.length_cons, List.length_nil] at hgap
    change 40 ≤ 1 + (gap + 2)
    omega
  · rw [show (machine253.runFrom c (2 * gap + 34)).head = c.head from hh]
    simpa only [BootstrapFrame253.dispatchZip, hq, zAt, hY, List.append_assoc,
      List.cons_append, List.nil_append, List.append_nil] using hs

/-- The literal register step and its complete binary dispatch frame agree
at this site. Reachability of an arbitrary path is not assumed or inferred. -/
theorem paired_break001 {c : Config 253} (logical : RegisterPath.Configuration)
    (gap : Nat) (spares : List Nat) (hp : logical.path = [false, false, true])
    (hc : BootstrapFrame253.DispatchFrame BootstrapFrame253.dispatch253 c logical gap spares) :
    RegisterPath.step Prog254.program logical = some { logical with path := [true] } ∧
    BootstrapFrame253.DispatchFrame BootstrapFrame253.dispatch253
      (machine253.runFrom c (2 * gap + 34)) { logical with path := [true] } (gap + 2) spares := by
  refine ⟨?_, dispatch_frame_break001 logical gap spares hp hc⟩
  rcases logical with ⟨P, R⟩
  change P = [false, false, true] at hp
  subst P
  exact register_break001 R

end SetTheory.BusyBeaver.ZFC.BreakSite253
