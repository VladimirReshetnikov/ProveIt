import BusyBeaver.ZFC.KHomeReady
import BusyBeaver.ZFC.RegisterPathClean
import BusyBeaver.ZFC.SiteCoverage

/-!
Decoder sites and the register-machine simulation of the K-family engine (port of K230's
`Interpreter230Sites.v`, `Interpreter230Check.v`, `Sim230.v` and `Sim230Main.v`, adapted there from
Jeff Ketchersid's m254 `Site.v` and `Sim.v`).

At the dispatch configuration the machine is in state 84 with `[true]` to its left; to its right lie
the program counter (the walk path), a gap of blanks, a `1`, and the register file. `checkEdge M Q e`
runs the certified symbolic executor from the site `Q` and confirms it reaches the dispatch
configuration of the successor path with the register file updated as the edge says (or, for a
halt leaf, the terminal state 230). `halts_iff`: for every table with K230's register lemmas whose
decoder sites all check, the register program halts iff the machine does, from every related
pair of configurations. Nothing here is specific to one table or one program.
-/

namespace SetTheory.BusyBeaver.ZFC.KSim

open KZip KRuntimeCore RegisterPath RegisterPathClean

/-! ## Sites -/

/-- Cells between the PC marker and the register header: at least `D0`. The boots leave 181
(the 221), 144 (the 219, 218, 217) and 65 (the 215). -/
def D0 : Nat := 64

def growth : BoxSt → Nat
  | .plain (.dec _) => 1
  | _ => 0

def start (Q : List Bool) : SConf :=
  (84, false, [.bit true],
    Q.map .bit ++ [.run false 1 (D0 - Q.length), .bit true, .box (.plain .none)])

/-- `ovf`: the PC overflowed and the marker moved one cell left. -/
def tgtConf (P : List Bool) (ovf : Bool) (x : BoxSt) : SConf :=
  (84, false, [.bit true],
    P.map .bit ++ [.run false 1 (D0 + (if ovf then 1 else 0) + growth x - P.length), .bit true, .box x])

def FUEL : Nat := 4000

def runTo (M : TMN) (br : Branch) (Q : List Bool) (e : SConf) : Bool :=
  (KHomeReady.exec M br (fun s => sMatches s e) FUEL (start Q) false).isSome

def isHalt (s : SConf) : Bool := s.1 == 230

def runHalt (M : TMN) (Q : List Bool) : Bool := (KHomeReady.exec M none isHalt FUEL (start Q) false).isSome

def allOnes (P : List Bool) : Bool := P.all id

/-- The tape order of the nine logical registers, and its inverse. -/
def physOrder : List Nat := [2, 8, 1, 4, 3, 7, 0, 5, 6]

def physOf (r : Nat) : Nat := [6, 2, 0, 4, 3, 7, 8, 5, 1].getD r 0

def vregs (R : Registers) : List Nat := physOrder.map R

/-- The per-leaf check: the symbolic run from the site reaches the successor's dispatch. Site
paths have at most 48 bits (the 217's source reaches 45), so they and their successors fit in
the `D0` cells before the register header. -/
def checkEdge (M : TMN) (Q : List Bool) : Edge → Bool
  | .inc r => decide (Q.length ≤ 48) && decide (r < 9) &&
      runTo M none Q (tgtConf (incPath Q) (allOnes Q) (.plain (.inc (physOf r))))
  | .decnz r => decide (Q.length ≤ 48) && decide (r < 9) &&
      runTo M (some (physOf r, true)) Q
        (tgtConf (breakPath 1 Q) (allOnes (stripPath false 1 Q)) (.plain .none)) &&
      runTo M (some (physOf r, false)) Q (tgtConf (incPath Q) (allOnes Q) (.plain (.dec (physOf r))))
  | .brk k => decide (Q.length ≤ 48) &&
      runTo M none Q (tgtConf (breakPath k Q) (allOnes (stripPath false k Q)) (.plain .none))
  | .cont k => decide (Q.length ≤ 48) &&
      runTo M none Q (tgtConf (continuePath k Q) false (.plain .none))
  | .halt => decide (Q.length ≤ 48) && runHalt M Q
  | .node _ => false

theorem checkEdge_length {M : TMN} {Q : List Bool} {e : Edge} (h : checkEdge M Q e = true) :
    Q.length ≤ 48 := by
  cases e <;> simp_all [checkEdge]

/-! ## The concrete meaning of `start` and `tgtConf` -/

theorem flat_bits (n : Nat) (vs : List Nat) (Q : List Bool) : flat n vs (Q.map .bit) = Q := by
  induction Q with
  | nil => rfl
  | cons b Q ih => simp only [List.map_cons, flat_cons, segList, ih]; rfl

theorem flat_append (n : Nat) (vs : List Nat) (a b : List Seg) :
    flat n vs (a ++ b) = flat n vs a ++ flat n vs b := by
  simp [flat, List.flatMap_append]

theorem conc_start (n : Nat) (vs : List Nat) (Q : List Bool) :
    conc n vs (start Q) =
      zc 84 [true] (Q ++ List.replicate (n + (D0 - Q.length)) false ++ true :: sepsR vs) := by
  simp only [start, conc, flat_append, flat_bits]
  simp [flat, segList, boxList, Nat.one_mul]

theorem conc_target (n : Nat) (vs : List Nat) (P : List Bool) (ovf : Bool) (x : BoxSt) :
    conc n vs (tgtConf P ovf x) =
      zc 84 [true] (P ++ List.replicate (n + (D0 + (if ovf then 1 else 0) + growth x - P.length)) false ++
        true :: boxList x vs) := by
  simp only [tgtConf, conc, flat_append, flat_bits]
  simp [flat, segList, Nat.one_mul]

section Sound

variable {M : TMN} (B : BoxLemmas M)
include B

theorem runTo_sound {br : Branch} {Q : List Bool} {e : SConf} (h : runTo M br Q e = true)
    (n : Nat) {vs : List Nat} (hv : Valid br vs) : Reach1 M (conc n vs (start Q)) (conc n vs e) := by
  unfold runTo at h
  cases hx : KHomeReady.exec M br (fun s => sMatches s e) FUEL (start Q) false with
  | none => simp [hx] at h
  | some s =>
      obtain ⟨hm, _, h1⟩ := KHomeReady.exec_sound B n hv FUEL (start Q) false s hx
      rw [← sMatches_conc n vs hm]
      exact h1 rfl

theorem runHalt_sound (hNH : ∀ b, M 230 b = none) {Q : List Bool} (h : runHalt M Q = true)
    (n : Nat) {vs : List Nat} (hv : 10 ≤ vs.length) : Halts M (conc n vs (start Q)) := by
  unfold runHalt at h
  cases hx : KHomeReady.exec M none isHalt FUEL (start Q) false with
  | none => simp [hx] at h
  | some s =>
      obtain ⟨hh, h0, _⟩ := KHomeReady.exec_sound B n (br := none) ⟨hv, trivial⟩ FUEL (start Q) false s hx
      refine ⟨_, h0, ?_⟩
      obtain ⟨q, onl, l, r⟩ := s
      simp only [isHalt, beq_iff_eq] at hh
      subst hh
      cases onl <;> simp [conc, zl, step_zc, hNH]

end Sound

/-! ## Registers on the tape -/

theorem vregs_length (R : Registers) {ext : List Nat} (h : ext ≠ []) : 10 ≤ (vregs R ++ ext).length := by
  cases ext with
  | nil => exact absurd rfl h
  | cons _ _ => simp [vregs, physOrder]

theorem getD_vregs (R : Registers) (ext : List Nat) {r : Nat} (hr : r < 9) :
    (vregs R ++ ext).getD (physOf r) 0 = R r := by
  match r, hr with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ => rfl

theorem incr_vregs (R : Registers) (ext : List Nat) {r : Nat} (hr : r < 9) :
    incr (physOf r) (vregs R ++ ext) = vregs (update R r (R r + 1)) ++ ext := by
  match r, hr with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ =>
      simp [vregs, physOrder, physOf, incr, update]

theorem decr_vregs (R : Registers) (ext : List Nat) {r : Nat} (hr : r < 9) :
    decr (physOf r) (vregs R ++ ext) = vregs (update R r (R r - 1)) ++ ext := by
  match r, hr with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ =>
      simp [vregs, physOrder, physOf, decr, update]

theorem valid_z {r : Nat} {vs : List Nat} (hl : 10 ≤ vs.length) (h : vs.getD r 0 = 0) :
    Valid (some (r, true)) vs := ⟨hl, h⟩

theorem valid_nz {r : Nat} {vs : List Nat} (hl : 10 ≤ vs.length) (h : vs.getD r 0 ≠ 0) :
    Valid (some (r, false)) vs := ⟨hl, h⟩

/-! ## Path lengths -/

theorem incPath_length (P : List Bool) : (incPath P).length = P.length := by
  rcases incPath_shape P with ⟨m, hp, hi⟩ | ⟨m, A, hp, hi⟩ <;> rw [hi, hp] <;> simp

theorem stripPath_length (b : Bool) (k : Nat) (P : List Bool) : (stripPath b k P).length ≤ P.length := by
  obtain ⟨T, hT⟩ := stripPath_prefix b k P
  have := congrArg List.length hT
  simp only [List.length_append] at this
  omega

theorem breakPath_length (k : Nat) (P : List Bool) : (breakPath k P).length ≤ P.length := by
  unfold breakPath; rw [incPath_length]; exact stripPath_length _ _ _

/-! ## The simulation -/

/-- Every decoder input reaches a leaf whose site checks. -/
def Covered (M : TMN) (p : Program) : Prop :=
  ∀ P, ∃ e d, walk p (p.nnodes + 1) p.root P 0 = some (e, d) ∧ checkEdge M (consume P d) e = true

theorem covered_of_allSites (M : TMN) (p : Program) (t : RMBisim.Tree) (ht : RMBisim.ptree p = t)
    (hs : SiteCoverage.allSites (checkEdge M) [] t = true) : Covered M p := by
  intro P
  obtain ⟨e, d, hw⟩ := SiteCoverage.allSites_walk_total (checkEdge M) p t ht hs P
  exact ⟨e, d, hw, SiteCoverage.allSites_walk (checkEdge M) p t ht hs P e d hw⟩

/-- A register configuration and the dispatch configuration that represents it. -/
def Rel (p : Program) (c : Configuration) (T : Conf) : Prop :=
  Clean p c.path ∧ ∃ k ext, D0 ≤ c.path.length + k ∧ ext ≠ [] ∧
    T = zc 84 [true] (c.path ++ List.replicate k false ++ true :: sepsR (vregs c.registers ++ ext))

/-- The tape seen from the leaf the walk reaches. -/
theorem rel_view {p : Program} {c : Configuration} {T : Conf} {e : Edge} {d : Nat}
    (hc : Rel p c T) (hw : walk p (p.nnodes + 1) p.root c.path 0 = some (e, d)) (hd : d ≤ 48) :
    ∃ k ext, D0 ≤ c.path.length + k ∧ ext ≠ [] ∧
      T = conc (c.path.length + k - D0) (vregs c.registers ++ ext) (start (consume c.path d)) := by
  obtain ⟨hcl, k, ext, hk, hext, rfl⟩ := hc
  refine ⟨k, ext, hk, hext, ?_⟩
  rw [conc_start, consume_length]
  have hz : ∀ b ∈ c.path.drop d, b = false := by
    intro b hb
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    have hv : bit (c.path.drop d) i = b := by simp [bit, hi]
    exact hv.symm.trans ((bit_drop c.path d i).trans (hcl e d hw (d + i) (by omega)))
  rw [gap_consume c.path k d (by unfold D0 at hk; omega) hz]
  have e : c.path.length + k - d = c.path.length + k - D0 + (D0 - d) := by unfold D0 at hk ⊢; omega
  rw [e]

section Sim

variable {M : TMN} (B : BoxLemmas M) {p : Program} (hcov : Covered M p)
include B hcov

theorem sim_step {c c' : Configuration} {T : Conf} (hc : Rel p c T) (hs : step p c = some c') :
    ∃ T', Rel p c' T' ∧ Reach1 M T T' := by
  have hcl' : Clean p c'.path := step_clean p c c' hs
  obtain ⟨e, d, hw, hck⟩ := hcov c.path
  have hd := checkEdge_length hck
  rw [consume_length] at hd
  obtain ⟨k, ext, hk, hext, hT⟩ := rel_view hc hw hd
  have hex : execute e (consume c.path d) c.registers = some c' := by
    simpa only [RegisterPath.step, hw] using hs
  have hl := vregs_length c.registers hext
  have hQ : (consume c.path d).length = d := consume_length _ _
  generalize consume c.path d = Q at hck hex hQ hT
  generalize c.path.length + k - D0 = n at hT
  subst hT
  cases e with
  | node _ => simp [checkEdge] at hck
  | halt => simp [execute] at hex
  | inc r =>
      simp only [checkEdge, Bool.and_eq_true, decide_eq_true_eq] at hck
      obtain ⟨⟨_, hr⟩, h1⟩ := hck
      simp only [execute, Option.some.injEq] at hex
      subst hex
      refine ⟨_, ⟨hcl', n + (D0 + (if allOnes Q then 1 else 0) + 0 - (incPath Q).length), ext ++ [1],
        ?_, by simp, rfl⟩, ?_⟩
      · simp only [incPath_length, hQ]; unfold D0; omega
      · have := runTo_sound B h1 n (vs := vregs c.registers ++ ext) ⟨hl, trivial⟩
        rw [conc_target] at this
        simpa [growth, boxList, incr_vregs _ _ hr, List.append_assoc] using this
  | decnz r =>
      simp only [checkEdge, Bool.and_eq_true, decide_eq_true_eq] at hck
      obtain ⟨⟨⟨_, hr⟩, h0⟩, h1⟩ := hck
      cases hv : c.registers r with
      | zero =>
          simp only [execute, hv, Option.some.injEq] at hex
          subst hex
          refine ⟨_, ⟨hcl', n + (D0 + (if allOnes (stripPath false 1 Q) then 1 else 0) + 0 -
            (breakPath 1 Q).length), ext, ?_, hext, rfl⟩, ?_⟩
          · have := breakPath_length 1 Q; simp only; unfold D0; omega
          · have := runTo_sound B h0 n (vs := vregs c.registers ++ ext)
              (valid_z hl (by rw [getD_vregs _ _ hr, hv]))
            rw [conc_target] at this
            simpa [growth, boxList] using this
      | succ v =>
          simp only [execute, hv, Option.some.injEq] at hex
          subst hex
          refine ⟨_, ⟨hcl', n + (D0 + (if allOnes Q then 1 else 0) + 1 - (incPath Q).length), ext,
            ?_, hext, rfl⟩, ?_⟩
          · simp only [incPath_length, hQ]; unfold D0; omega
          · have := runTo_sound B h1 n (vs := vregs c.registers ++ ext)
              (valid_nz hl (by rw [getD_vregs _ _ hr, hv]; omega))
            rw [conc_target] at this
            have hd' := decr_vregs c.registers ext hr
            rw [hv] at hd'
            simpa [growth, boxList, hd'] using this
  | brk k' =>
      simp only [checkEdge, Bool.and_eq_true, decide_eq_true_eq] at hck
      obtain ⟨_, h1⟩ := hck
      simp only [execute, Option.some.injEq] at hex
      subst hex
      refine ⟨_, ⟨hcl', n + (D0 + (if allOnes (stripPath false k' Q) then 1 else 0) + 0 -
        (breakPath k' Q).length), ext, ?_, hext, rfl⟩, ?_⟩
      · have := breakPath_length k' Q; simp only; unfold D0; omega
      · have := runTo_sound B h1 n (vs := vregs c.registers ++ ext) ⟨hl, trivial⟩
        rw [conc_target] at this
        simpa [growth, boxList] using this
  | cont k' =>
      simp only [checkEdge, Bool.and_eq_true, decide_eq_true_eq] at hck
      obtain ⟨_, h1⟩ := hck
      simp only [execute, Option.some.injEq] at hex
      subst hex
      refine ⟨_, ⟨hcl', n + (D0 + 0 + 0 - (continuePath k' Q).length), ext, ?_, hext, rfl⟩, ?_⟩
      · have := stripPath_length true k' Q; simp only [continuePath]; unfold D0; omega
      · have := runTo_sound B h1 n (vs := vregs c.registers ++ ext) ⟨hl, trivial⟩
        rw [conc_target] at this
        simpa [growth, boxList] using this

omit B in
theorem sim_stop {c : Configuration} (hs : step p c = none) : AtHalt p c := by
  obtain ⟨e, d, hw, hck⟩ := hcov c.path
  cases e with
  | node _ => simp [checkEdge] at hck
  | halt => exact ⟨d, hw⟩
  | inc r | brk r | cont r => simp [RegisterPath.step, hw, execute] at hs
  | decnz r => cases hv : c.registers r <;> simp [RegisterPath.step, hw, execute, hv] at hs

theorem sim_halt (hNH : ∀ b, M 230 b = none) {c : Configuration} {T : Conf} (hc : Rel p c T)
    (hh : AtHalt p c) : Halts M T := by
  obtain ⟨d, hw⟩ := hh
  obtain ⟨e, d', hw', hck⟩ := hcov c.path
  rw [hw] at hw'
  cases hw'
  have hd := checkEdge_length hck
  rw [consume_length] at hd
  obtain ⟨k, ext, _, hext, rfl⟩ := rel_view hc hw hd
  simp only [checkEdge, Bool.and_eq_true] at hck
  exact runHalt_sound B hNH hck.2 _ (vregs_length _ hext)

/-- **Simulation.** The register program halts iff the machine halts, from related configurations. -/
theorem halts_iff (hNH : ∀ b, M 230 b = none) {c : Configuration} {T : Conf} (hc : Rel p c T) :
    RegisterPath.Halts p c ↔ KZip.Halts M T := by
  constructor
  · rintro ⟨N, c', hr, hh⟩
    induction N generalizing c T with
    | zero =>
        simp only [RegisterPath.run, Option.some.injEq] at hr
        subst hr
        exact sim_halt B hcov hNH hc hh
    | succ N ih =>
        simp only [RegisterPath.run] at hr
        cases hs : step p c with
        | none => rw [hs] at hr; simp at hr
        | some c1 =>
            rw [hs] at hr
            obtain ⟨T1, h1, hR⟩ := sim_step B hcov hc hs
            exact Halts.of_reach hR.reach (ih h1 hr)
  · rintro ⟨cf, ⟨t, ht⟩, hstop⟩
    induction t using Nat.strongRecOn generalizing c T with
    | ind t ih =>
        cases hs : step p c with
        | none => exact ⟨0, c, rfl, sim_stop hcov hs⟩
        | some c1 =>
            obtain ⟨T1, h1, j, hj⟩ := sim_step B hcov hc hs
            have hle : j + 1 ≤ t := by
              refine Nat.not_lt.mp fun hlt => ?_
              have e1 : j + 1 = t + (j + 1 - t) := by omega
              rw [e1, KZip.run_add, ht] at hj
              obtain ⟨m, hm⟩ : ∃ m, j + 1 - t = m + 1 := ⟨j - t, by omega⟩
              rw [hm] at hj
              simp [KZip.run, hstop] at hj
            have e2 : t = (j + 1) + (t - (j + 1)) := by omega
            rw [e2, KZip.run_add, hj] at ht
            obtain ⟨N, c', hr, hh⟩ := ih (t - (j + 1)) (by omega) h1 ht
            exact ⟨N + 1, c', by simp only [RegisterPath.run, hs]; exact hr, hh⟩

end Sim

end SetTheory.BusyBeaver.ZFC.KSim
