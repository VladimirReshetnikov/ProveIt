import DiophantineConsistency.ArithmeticSymbolicCore215
import BusyBeaver.ZFC.KHomeReady

/-! Actual Home execution on arbitrary internal 215 tapes. The finite syntax
checker is reused; no ordinary-Nat Home execution theorem is a premise. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.ArithmeticHome215
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineTape215 ArithmeticRegisterBoxes215 ArithmeticSymbolicCore215
open KRuntimeCore (Seg SConf Branch)

private theorem reset_table : ∀ i : Fin 8,
    KTableCore.tm215 (KHome.state i.val) true=some (true,false,2) := by decide +kernel
private theorem next_table : ∀ i : Fin 7,
    KTableCore.tm215 (KHome.state i.val) false=some (false,false,KHome.state (i.val+1)) := by decide +kernel
lemma reset_row (i : Nat) (hi : i<8) :
    KTableCore.tm215 (KHome.state i) true=some (true,false,2) := reset_table ⟨i,hi⟩
lemma next_row (i : Nat) (hi : i+1<8) :
    KTableCore.tm215 (KHome.state i) false=some (false,false,KHome.state (i+1)) :=
  next_table ⟨i,by omega⟩
private theorem boundary_left_row : KTableCore.tm215 50 false=some (false,false,75) := by decide +kernel
private theorem boundary_scan_row : KTableCore.tm215 75 false=some (false,true,75) := by decide +kernel
private theorem boundary_marker_row : KTableCore.tm215 75 true=some (true,true,84) := by decide +kernel
/-- A literal table/window certificate, independently of the internal proof below. -/
theorem ready215 : KHomeReady.ready KTableCore.tm215=true := by decide +kernel

section Internal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "step" => ArithmeticMachineStep215.stepValue

lemma flatValue_append (gap : V) (v : Fin 9 → V) (k : V) (xs ys : List Seg) (z : V) :
    flatValue gap v k (xs++ys) z=flatValue gap v k xs (flatValue gap v k ys z) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,flatValue,ih]

/-- A finite zero streak never crosses the eighth zero boundary. -/
theorem scan_zeros_exact (i c : Nat) (hi : i+c<8) (L R : V) :
    runFrom (c:V) (leftFrame (KHome.state i) (bitPrefix false (c:V) L) R)=
      leftFrame (KHome.state (i+c)) L (bitPrefix false (c:V) R) := by
  induction c generalizing i R with
  | zero => simp
  | succ c ih =>
    rw [Nat.cast_add,Nat.cast_one,run_first,bitPrefix_succ,step_left_facing (next_row i (by omega)),ih (i+1) (by omega),bitPrefix_push]
    rw [show i+1+c=i+(c+1) by omega]

/-- A nonempty true run resets the counter; its length is internal. -/
theorem scan_ones (i : Nat) (hi : i<8) (n L R : V) (hn : 0<n) :
    Reach (leftFrame (KHome.state i) (bitPrefix true n L) R)
      (leftFrame 2 L (bitPrefix true n R)) := by
  have hn' : n-1+1=n := tsub_add_cancel_of_le (pos_iff_one_le.mp hn)
  have hfirst := Reach.of_step (step_left_facing (reset_row i hi) (bitPrefix true (n-1) L) R)
  have hrest : Reach (leftFrame 2 (bitPrefix true (n-1) L) (2*R+digit true))
      (leftFrame 2 L (bitPrefix true (n-1) (2*R+digit true))) :=
    ⟨n-1,scan_left 2 true true (reset_row 0 (by decide)) (n-1) L (2*R+digit true)⟩
  simpa only [←bitPrefix_succ,bitPrefix_push,hn'] using hfirst.trans hrest

private theorem boundary_eight (R : V) :
    runFrom 8 (leftFrame 2 0 (2*R+1))=
      frameSparse 75 0 (bitPrefix false 9 (2*R+1)) := by
  have hz := scan_zeros_exact (V:=V) 0 7 (by decide) 0 (2*R+1)
  change runFrom 7 (leftFrame 2 (bitPrefix false 7 0) (2*R+1))=
    leftFrame 50 0 (bitPrefix false 7 (2*R+1)) at hz
  rw [show bitPrefix false (7:V) 0=0 by simp [bitPrefix]] at hz
  rw [show (8:V)=7+1 by ring,runFrom_succ,hz]
  have he := step_left_facing (V:=V) boundary_left_row 0 (bitPrefix false 7 (2*R+1))
  have hp : bitPrefix false (9:V) (2*R+1)=2*(2*bitPrefix false 7 (2*R+1)) := by
    rw [show (9:V)=(7+1)+1 by ring,bitPrefix_succ,bitPrefix_succ]
    simp
  rw [hp]
  simpa [leftFrame] using he

/-- All eighteen actual steps, including the last marker write/move. -/
theorem boundary_actual (R : V) :
    runFrom 18 (leftFrame 2 0 (2*R+1))=frameSparse 84 1 R := by
  rw [show (18:V)=(8+9)+1 by ring,runFrom_succ,runFrom_add,boundary_eight,
    scan_right 75 false false boundary_scan_row]
  have he := step_right (V:=V) boundary_marker_row 0 R
  simpa [bitPrefix,digit] using he

/-- The actual zero counter can be smaller than the checker's bound. No box
is scanned, and a true affine run may be empty when the gap is zero. -/
theorem scanBound_actual (gap : V) (v : Fin 9 → V) (k : V)
    {xs : List Seg} {i bound j : Nat} (h : KHome.scanBound i xs=some bound)
    (hi : i<8) (hj : j≤i) (L R : V) :
    ∃ j', j'≤bound ∧ j'<8 ∧
      Reach (leftFrame (KHome.state j) (flatValue gap v k xs L) R)
        (leftFrame (KHome.state j') L (flatValue gap v k xs.reverse R)) := by
  induction xs generalizing i bound j L R with
  | nil =>
    simp only [KHome.scanBound,Option.some.injEq] at h
    subst bound
    exact ⟨j,hj,by omega,Reach.refl _⟩
  | cons x xs ih =>
    simp only [flatValue,List.reverse_cons,flatValue_append,flatValue]
    cases x with
    | box x => simp [KHome.scanBound] at h
    | bit b =>
      cases b with
      | true =>
        obtain ⟨j',hb,hlt,hr⟩ := ih (by simpa [KHome.scanBound] using h)
          (by decide : 0<8) (by rfl : 0≤0) L (2*R+digit true)
        refine ⟨j',hb,hlt,?_⟩
        exact (Reach.of_step (step_left_facing (reset_row j (by omega)) _ R)).trans hr
      | false =>
        by_cases hc : i+1<8
        · obtain ⟨j',hb,hlt,hr⟩ := ih (by simpa [KHome.scanBound,hc] using h)
            hc (show j+1≤i+1 by omega) L (2*R+digit false)
          exact ⟨j',hb,hlt,(Reach.of_step (step_left_facing (next_row j (by omega)) _ R)).trans hr⟩
        · simp [KHome.scanBound,hc] at h
    | run b a c =>
      cases b with
      | false =>
        by_cases hc : a=0 ∧ i+c<8
        · obtain ⟨rfl,hc⟩ := hc
          obtain ⟨j',hb,hlt,hr⟩ := ih (by simpa [KHome.scanBound,hc] using h)
            hc (show j+c≤i+c by omega) L (bitPrefix false (c:V) R)
          refine ⟨j',hb,hlt,?_⟩
          simpa only [segValue,Nat.cast_zero,zero_mul,zero_add] using
            (Reach.trans ⟨(c:V),scan_zeros_exact j c (by omega) (flatValue gap v k xs L) R⟩ hr)
        · simp [KHome.scanBound,hc] at h
      | true =>
        let n : V := (a:V)*gap+c
        by_cases hn : n=0
        · have hcV : (c:V)=0 := by
            have : (c:V)≤n := by dsimp [n]; simp
            exact le_zero_iff.mp (hn ▸ this)
          have hc : c=0 := Nat.cast_injective hcV
          subst c
          obtain ⟨j',hb,hlt,hr⟩ := ih (by simpa [KHome.scanBound] using h) hi hj L R
          refine ⟨j',hb,hlt,?_⟩
          simpa only [segValue,Nat.cast_zero,show (a:V)*gap+(0:V)=0 from hn,bitPrefix_zero] using hr
        · have hp : 0<n := pos_iff_ne_zero.mpr hn
          have hbnd : (if c=0 then i else 0)<8 := by split <;> omega
          obtain ⟨j',hb,hlt,hr⟩ := ih (by simpa [KHome.scanBound] using h)
            hbnd (show 0≤(if c=0 then i else 0) by omega) L (bitPrefix true n R)
          exact ⟨j',hb,hlt,(scan_ones j (by omega) n (flatValue gap v k xs L) R hp).trans hr⟩

/-- Discarded exterior zero segments vanish only at the zero tail. The
stopping marker is a literal true bit, not a true run or a hidden box. -/
theorem stripBlank_actual (gap : V) (v : Fin 9 → V) (k : V)
    {xs u : List Seg} (h : KHome.stripBlank xs=some u) :
    flatValue gap v k xs.reverse 0=flatValue gap v k u.reverse 1 := by
  induction xs with
  | nil => simp [KHome.stripBlank] at h
  | cons x xs ih =>
    cases x with
    | bit b =>
      cases b
      · simpa [List.reverse_cons,flatValue_append,flatValue,segValue,digit] using ih h
      · simp only [KHome.stripBlank,Option.some.injEq] at h
        subst u
        simp [List.reverse_cons,flatValue_append,flatValue,segValue,digit]
    | run b a c =>
      cases b
      · simpa [List.reverse_cons,flatValue_append,flatValue,segValue,bitPrefix] using ih h
      · simp [KHome.stripBlank] at h
    | box x => simp [KHome.stripBlank] at h

/-- A successful Home checker has a genuine positive execution on the actual
215 table for every internal affine gap and right tape tail. -/
theorem home_actual (gap : V) (v : Fin 9 → V) (k : V)
    {s t : SConf} (h : KHome.home s=some t) :
    ReachPos (interpret gap v k s) (interpret gap v k t) := by
  obtain ⟨q,onl,l,r⟩ := s
  simp only [KHome.home] at h
  split at h
  · rename_i hg
    obtain ⟨rfl,rfl⟩ := hg
    cases hs : KHome.stripBlank l.reverse with
    | none => simp [hs] at h
    | some u =>
      simp only [hs] at h
      cases hc : KHome.scanBound 0 u.reverse with
      | none => simp [hc] at h
      | some bound =>
        simp only [hc,Option.some.injEq] at h
        subst t
        have hl : flatValue gap v k l 0=flatValue gap v k u.reverse 1 := by
          simpa only [List.reverse_reverse] using stripBlank_actual gap v k hs
        obtain ⟨j',_,hj,hr⟩ := scanBound_actual gap v k hc (by decide) (by rfl : 0≤0) 1 (flatValue gap v k r 0)
        rw [List.reverse_reverse] at hr
        have hm := step_left_facing (V:=V) (reset_row j' hj) 0 (flatValue gap v k u (flatValue gap v k r 0))
        have hb : ReachPos (leftFrame 2 0 (2*(flatValue gap v k u (flatValue gap v k r 0))+1))
            (frameSparse 84 1 (flatValue gap v k u (flatValue gap v k r 0))) :=
          ⟨18,by simp,boundary_actual _⟩
        have ht := ArithmeticSymbolicCore215.Reach.trans_positive
          (hr.trans (Reach.of_step (by simpa using hm))) hb
        simpa only [interpret,flatValue,segValue,digit_true,mul_zero,zero_add,flatValue_append,hl,show KHome.state 0=2 from rfl] using ht
  · simp at h

theorem stepper_actual (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {br : Branch} (hv : BranchValid br v) {s t : SConf} {m : Bool}
    (h : KHomeReady.stepper KTableCore.tm215 br s=some (t,m)) : StepOk gap v k s t m := by
  simp only [KHomeReady.stepper,ready215,if_true] at h
  cases hs : KHome.home s with
  | none => exact sstep_actual gap v k hk hv (by simpa [KHomeReady.homeStep,hs] using h)
  | some u =>
    simp only [KHomeReady.homeStep,hs,Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    have hp := home_actual gap v k hs
    exact ⟨ArithmeticSymbolicCore215.ReachPos.reach hp,fun _ => hp⟩

/-- The moved flag is retained: initially true only yields ordinary Reach. -/
theorem exec_flag_actual (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {br : Branch} (hv : BranchValid br v) {target : SConf → Bool}
    {fuel : Nat} {s t : SConf} {m0 : Bool}
    (h : KHomeReady.exec KTableCore.tm215 br target fuel s m0=some t) :
    target t=true ∧ Reach (interpret gap v k s) (interpret gap v k t) ∧
      (m0=false → ReachPos (interpret gap v k s) (interpret gap v k t)) :=
  execWith_actual gap v k (fun _ _ _ hs => stepper_actual gap v k hk hv hs) fuel s m0 t h

theorem exec_actual (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {br : Branch} (hv : BranchValid br v) {target : SConf → Bool}
    {fuel : Nat} {s t : SConf}
    (h : KHomeReady.exec KTableCore.tm215 br target fuel s false=some t) :
    target t=true ∧ ReachPos (interpret gap v k s) (interpret gap v k t) := by
  obtain ⟨ht,_,hp⟩ := exec_flag_actual gap v k hk hv h
  exact ⟨ht,hp rfl⟩

theorem exec_matches_actual (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {br : Branch} (hv : BranchValid br v) {fuel : Nat} {s t target : SConf}
    (h : KHomeReady.exec KTableCore.tm215 br (fun u => KRuntimeCore.sMatches u target) fuel s false=some t) :
    ReachPos (interpret gap v k s) (interpret gap v k target) := by
  obtain ⟨ht,hp⟩ := exec_actual gap v k hk hv h
  rw [matches_actual gap v k ht] at hp
  exact hp
end Internal
end DiophantineConsistency.ArithmeticHome215
