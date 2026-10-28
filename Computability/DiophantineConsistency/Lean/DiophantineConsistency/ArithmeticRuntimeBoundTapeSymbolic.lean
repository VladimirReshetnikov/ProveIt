import DiophantineConsistency.ArithmeticRuntimeBoundTapeBoxes
import DiophantineConsistency.ArithmeticHome215

/-! # Clock-bounded symbolic execution of the literal decimal215 machine

Bounded twins of `ArithmeticSymbolicCore215` and `ArithmeticHome215`. A symbolic
configuration `s` has two finite weights: `confA s`, the total gap coefficient of
its runs, and `confC s`, its total constant length (bits plus run constants).
One abstract step (a transition, a whole run scan, a peel, a register box or a
Home return) costs at most

  `cost s = confA s * gap + confC s + boxW v k + 19`

machine steps, and never increases `confA` or increases `confC` by more than one.
Hence `fuel` executor steps cost at most `execB fuel s = fuel * (cost s + fuel)`.
Proof bodies follow the accepted originals; no existing statement is changed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.ArithmeticRuntimeBoundTapeSymbolic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineTape215 ArithmeticRegisterBoxes215 ArithmeticSymbolicCore215
open ArithmeticRuntimeBoundTape ArithmeticRuntimeBoundTapeBoxes
open KRuntimeCore (BoxSt Eff Seg SConf Branch Tok)

/-! ## Finite weights of symbolic configurations -/

def segA : Seg → Nat
  | .run _ a _ => a
  | _ => 0
def segC : Seg → Nat
  | .bit _ => 1
  | .run _ _ c => c
  | .box _ => 0
def wA (xs : List Seg) : Nat := (xs.map segA).sum
def wC (xs : List Seg) : Nat := (xs.map segC).sum
def confA (s : SConf) : Nat := wA s.2.2.1 + wA s.2.2.2
def confC (s : SConf) : Nat := wC s.2.2.1 + wC s.2.2.2

@[simp] theorem wA_nil : wA [] = 0 := rfl
@[simp] theorem wC_nil : wC [] = 0 := rfl
@[simp] theorem wA_cons (x : Seg) (xs : List Seg) : wA (x::xs) = segA x + wA xs := by simp [wA]
@[simp] theorem wC_cons (x : Seg) (xs : List Seg) : wC (x::xs) = segC x + wC xs := by simp [wC]
@[simp] theorem wA_append (xs ys : List Seg) : wA (xs++ys) = wA xs + wA ys := by simp [wA]
@[simp] theorem wC_append (xs ys : List Seg) : wC (xs++ys) = wC xs + wC ys := by simp [wC]
@[simp] theorem wA_reverse (xs : List Seg) : wA xs.reverse = wA xs := by simp [wA]
@[simp] theorem wC_reverse (xs : List Seg) : wC xs.reverse = wC xs := by simp [wC]
@[simp] theorem confA_mk (q : Nat) (o : Bool) (l r : List Seg) : confA (q,o,l,r) = wA l + wA r := rfl
@[simp] theorem confC_mk (q : Nat) (o : Bool) (l r : List Seg) : confC (q,o,l,r) = wC l + wC r := rfl

/-- Weight goals are linear Nat arithmetic after unfolding. -/
macro "wt" : tactic => `(tactic| (simp (config := {failIfUnchanged := false}) only
  [confA_mk, confC_mk, wA_cons, wC_cons, wA_nil, wC_nil, wA_append, wC_append,
   wA_reverse, wC_reverse, segA, segC, Bool.false_eq_true, if_true, if_false] at * <;> omega))

theorem stripBlank_weight : ∀ {xs u : List Seg}, KHome.stripBlank xs = some u →
    wA u ≤ wA xs ∧ wC u ≤ wC xs
  | [], u, h => by simp [KHome.stripBlank] at h
  | .bit false :: xs, u, h => by
    have := stripBlank_weight (xs:=xs) (u:=u) (by simpa [KHome.stripBlank] using h)
    wt
  | .bit true :: xs, u, h => by
    simp only [KHome.stripBlank, Option.some.injEq] at h
    subst h
    wt
  | .run false a c :: xs, u, h => by
    have := stripBlank_weight (xs:=xs) (u:=u) (by simpa [KHome.stripBlank] using h)
    wt
  | .run true a c :: xs, u, h => by simp [KHome.stripBlank] at h
  | .box x :: xs, u, h => by simp [KHome.stripBlank] at h

section Internal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem reachB_of_pos {x y B : V} (h : ReachPosB x y B) : ReachB x y B := by
  obtain ⟨t,_,ht,h⟩ := h; exact ⟨t,ht,h⟩

theorem lin_le {a a' c c' : Nat} (ha : a ≤ a') (hc : c ≤ c') (gap : V) :
    (a:V)*gap + c ≤ (a':V)*gap + c' :=
  _root_.add_le_add (mul_le_mul_of_nonneg_right (Nat.mono_cast ha) (Arithmetic.zero_le _))
    (Nat.mono_cast hc)

/-- The clock bound of one abstract step from `s`. -/
noncomputable def cost (gap : V) (v : Fin 9 → V) (k : V) (s : SConf) : V :=
  (confA s : V)*gap + (confC s : V) + boxW v k + 19

/-- One abstract step, with its clock bound and the weight invariant. -/
def StepOkB (gap : V) (v : Fin 9 → V) (k : V) (s t : SConf) (m : Bool) : Prop :=
  ReachB (interpret gap v k s) (interpret gap v k t) (cost gap v k s) ∧
    (m=true → ReachPosB (interpret gap v k s) (interpret gap v k t) (cost gap v k s)) ∧
    confA t ≤ confA s ∧ confC t ≤ confC s + 1

theorem one_le_cost (gap : V) (v : Fin 9 → V) (k : V) (s : SConf) : 1 ≤ cost gap v k s := by
  have h19 : (19:V) = 18 + 1 := by ring
  calc (1:V) ≤ 18 + 1 := le_add_self
    _ = 19 := h19.symm
    _ ≤ cost gap v k s := le_add_self
theorem box_le_cost (gap : V) (v : Fin 9 → V) (k : V) (s : SConf) : boxW v k ≤ cost gap v k s :=
  le_trans le_add_self le_self_add
theorem scan_le_cost (gap : V) (v : Fin 9 → V) (k : V) (s : SConf) {a c : Nat}
    (ha : a ≤ confA s) (hc : c ≤ confC s) : (a:V)*gap + c ≤ cost gap v k s :=
  le_trans (lin_le ha hc gap) (le_trans le_self_add le_self_add)

lemma stepOkB_eq {gap k : V} {v : Fin 9 → V} {s t : SConf}
    (h : interpret gap v k s=interpret gap v k t)
    (hA : confA t ≤ confA s) (hC : confC t ≤ confC s + 1) : StepOkB gap v k s t false :=
  ⟨(ReachB.of_eq h).mono (Arithmetic.zero_le _),⟨(fun h => by cases h),hA,hC⟩⟩
lemma stepOkB_one {gap k : V} {v : Fin 9 → V} {s t : SConf}
    (h : ArithmeticMachineStep215.stepValue (interpret gap v k s)=interpret gap v k t)
    (hA : confA t ≤ confA s) (hC : confC t ≤ confC s + 1) : StepOkB gap v k s t true :=
  ⟨(ReachB.of_step h).mono (one_le_cost _ _ _ _),
    ⟨fun _ => (ReachPosB.of_step h).mono (one_le_cost _ _ _ _),hA,hC⟩⟩

/-- `oracle_actual` within the box bound. -/
theorem oracle_actualB (v : Fin 9 → V) (k L : V) (hk : 0<k)
    {q q' : Nat} {br : Branch} {x x' : BoxSt} {extra : Bool}
    (h : KRuntimeCore.oracle q br x=some (q',x',extra)) (hv : BranchValid br v) :
    ReachPosB (frameSparse q L (boxValue v k x))
      (leftFrame q' (if extra then 2*L+1 else L) (boxValue v k x')) (boxW v k) := by
  cases x with
  | plain e =>
    cases e with
    | inc r => simp [KRuntimeCore.oracle] at h
    | dec r => simp [KRuntimeCore.oracle] at h
    | none =>
      cases hs : KRuntimeCore.skipTarget q with
      | none => simp [KRuntimeCore.oracle,hs] at h
      | some r =>
        obtain ⟨hq,hr⟩ := KRuntimeCore.skipTarget_sk hs
        simp only [KRuntimeCore.oracle,hs,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        subst q
        simpa only [box_plain,boxValue,boxTail,dif_pos hr,markedTail_zero,plainTail_zero,Bool.false_eq_true,if_false,
          KRuntimeCore.sk,KRuntimeCore.skList,KRuntimeCore.markExit,skipState,markExit] using
          box_markB v ⟨r,hr⟩ L k
  | mark r =>
    by_cases hr : r<9
    · by_cases hq : q=64
      · simp only [KRuntimeCore.oracle,if_pos hr,if_pos hq,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        subst q
        simpa only [boxValue,boxTail,dif_pos hr,markedTail_zero,plainTail_zero,Bool.false_eq_true,if_false] using
          box_incB v ⟨r,hr⟩ L k
      · by_cases hzero : q=0
        · cases br with
          | none => simp [KRuntimeCore.oracle,hr,hzero] at h
          | some rz =>
            obtain ⟨r',z⟩ := rz
            by_cases he : r=r'
            · subst r'
              subst q
              cases z
              · simp [KRuntimeCore.oracle,hr] at h
                obtain ⟨rfl,rfl,rfl⟩ := h
                have hp : 0<v ⟨r,hr⟩ := pos_iff_ne_zero.mpr (by simpa [BranchValid,getValue,hr] using hv)
                simpa only [boxValue,boxTail,dif_pos hr,markedTail_zero,plainTail_zero,if_true] using
                  box_decpB v ⟨r,hr⟩ L k hp
              · simp [KRuntimeCore.oracle,hr] at h
                obtain ⟨rfl,rfl,rfl⟩ := h
                have hz : v ⟨r,hr⟩=0 := by simpa [BranchValid,getValue,hr] using hv
                simpa only [boxValue,boxTail,dif_pos hr,markedTail_zero,plainTail_zero,Bool.false_eq_true,if_false] using
                  box_dec0B v ⟨r,hr⟩ L k hk hz
            · simp [KRuntimeCore.oracle,hr,hzero,he] at h
        · simp [KRuntimeCore.oracle,hr,hq,hzero] at h
    · simp [KRuntimeCore.oracle,hr] at h

lemma peelLeft_actualB (gap : V) (v : Fin 9 → V) (k : V)
    {q : Nat} {b : Bool} {a c : Nat} {l r : List Seg} {t : SConf} {m : Bool}
    (h : KRuntimeCore.peelLeft q b a c l r=some (t,m)) :
    StepOkB gap v k (q,true,.run b a c::l,r) t m := by
  cases c with
  | succ c =>
    simp only [KRuntimeCore.peelLeft,Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    refine stepOkB_eq ?_ (by wt) (by wt)
    simp only [interpret,flatValue,segValue,Nat.cast_add,Nat.cast_one,←add_assoc,bitPrefix_succ]
  | zero =>
    cases a with
    | zero =>
      simp only [KRuntimeCore.peelLeft,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      refine stepOkB_eq ?_ (by wt) (by wt)
      simp [interpret,flatValue,segValue]
    | succ a => simp [KRuntimeCore.peelLeft] at h
lemma peelRight_actualB (gap : V) (v : Fin 9 → V) (k : V)
    {q : Nat} {b : Bool} {a c : Nat} {l r : List Seg} {t : SConf} {m : Bool}
    (h : KRuntimeCore.peelRight q b a c l r=some (t,m)) :
    StepOkB gap v k (q,false,l,.run b a c::r) t m := by
  cases c with
  | succ c =>
    simp only [KRuntimeCore.peelRight,Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    refine stepOkB_eq ?_ (by wt) (by wt)
    simp only [interpret,flatValue,segValue,Nat.cast_add,Nat.cast_one,←add_assoc,bitPrefix_succ]
  | zero =>
    cases a with
    | zero =>
      simp only [KRuntimeCore.peelRight,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      refine stepOkB_eq ?_ (by wt) (by wt)
      simp [interpret,flatValue,segValue]
    | succ a => simp [KRuntimeCore.peelRight] at h

/-- `sstep_actual` with its clock bound and the weight invariant. -/
theorem sstep_actualB (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {br : Branch} (hv : BranchValid br v) {s t : SConf} {m : Bool}
    (h : KRuntimeCore.sstep KTableCore.tm215 br s=some (t,m)) : StepOkB gap v k s t m := by
  obtain ⟨q,onl,l,r⟩ := s
  cases onl with
  | true =>
    cases l with
    | nil =>
      simp only [KRuntimeCore.sstep,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      refine stepOkB_eq ?_ (by wt) (by wt)
      simp [interpret,flatValue,segValue,leftFrame]
    | cons x l =>
      cases x with
      | bit b =>
        simp only [KRuntimeCore.sstep,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        exact stepOkB_eq (leftFrame_bit q b _ _) (by wt) (by wt)
      | box x => simp [KRuntimeCore.sstep] at h
      | run b a c =>
        simp only [KRuntimeCore.sstep] at h
        split at h
        · rename_i w q' hm
          split at h
          · rename_i hq; subst q'; cases h
            exact ⟨(scan_leftB q b w hm ((a:V)*gap+c) _ _).mono
                (scan_le_cost gap v k _ (by wt) (by wt)),⟨(fun h => by cases h),by wt,by wt⟩⟩
          · exact peelLeft_actualB gap v k h
        · exact peelLeft_actualB gap v k h
  | false =>
    cases r with
    | nil => simp [KRuntimeCore.sstep] at h
    | cons x r =>
      cases x with
      | bit b =>
        simp only [KRuntimeCore.sstep] at h
        split at h
        · rename_i w q' hm; cases h
          exact stepOkB_one (step_right hm _ _) (by wt) (by wt)
        · rename_i w q' hm; cases h
          exact stepOkB_one (step_left hm _ _) (by wt) (by wt)
        · simp at h
      | run b a c =>
        simp only [KRuntimeCore.sstep] at h
        split at h
        · rename_i w q' hm
          split at h
          · rename_i hq; subst q'; cases h
            exact ⟨(scan_rightB q b w hm ((a:V)*gap+c) _ _).mono
                (scan_le_cost gap v k _ (by wt) (by wt)),⟨(fun h => by cases h),by wt,by wt⟩⟩
          · exact peelRight_actualB gap v k h
        · exact peelRight_actualB gap v k h
      | box x =>
        cases r with
        | cons y r => simp [KRuntimeCore.sstep] at h
        | nil =>
          simp only [KRuntimeCore.sstep] at h
          split at h
          · rename_i q' x' extra ho; cases h
            have he := (oracle_actualB v k (flatValue gap v k l 0) hk ho hv).mono
              (box_le_cost gap v k (q,false,l,[.box x]))
            cases extra
            · exact ⟨reachB_of_pos he,⟨(fun h => by cases h),by wt,by wt⟩⟩
            · exact ⟨reachB_of_pos he,⟨(fun h => by cases h),by wt,by wt⟩⟩
          · split at h
            · rename_i q' hm; cases h
              refine stepOkB_one ?_ (by wt) (by wt)
              obtain ⟨z,hz⟩ := boxTail_even v k 0 x
              change ArithmeticMachineStep215.stepValue (frameSparse q _ (boxTail v k x 0))=leftFrame q' _ (boxTail v k x 0)
              rw [hz]
              simpa using step_left hm (flatValue gap v k l 0) z
            · simp at h

/-! ## The Home return -/

/-- `scan_ones` takes exactly its run length. -/
theorem scan_onesB (i : Nat) (hi : i<8) (n L R : V) (hn : 0<n) :
    ReachB (leftFrame (KHome.state i) (bitPrefix true n L) R)
      (leftFrame 2 L (bitPrefix true n R)) n := by
  have hn' : n-1+1=n := tsub_add_cancel_of_le (pos_iff_one_le.mp hn)
  have hfirst := ReachB.of_step
    (step_left_facing (ArithmeticHome215.reset_row i hi) (bitPrefix true (n-1) L) R)
  have hrest : ReachB (leftFrame 2 (bitPrefix true (n-1) L) (2*R+digit true))
      (leftFrame 2 L (bitPrefix true (n-1) (2*R+digit true))) (n-1) :=
    scan_leftB 2 true true (ArithmeticHome215.reset_row 0 (by decide)) (n-1) L (2*R+digit true)
  have h := (hfirst.trans hrest).mono (le_of_eq (add_comm (1:V) (n-1)))
  simpa only [←bitPrefix_succ,bitPrefix_push,hn'] using h

theorem bound_cons (gap : V) (x : Seg) (xs : List Seg) :
    ((wA (x::xs) : Nat) : V)*gap + ((wC (x::xs) : Nat) : V) =
      (((segA x : Nat) : V)*gap + ((segC x : Nat) : V)) + (((wA xs : Nat) : V)*gap + ((wC xs : Nat) : V)) := by
  simp only [wA_cons, wC_cons, Nat.cast_add]; ring
theorem bound_bit (gap : V) (b : Bool) :
    ((segA (.bit b) : Nat) : V)*gap + ((segC (.bit b) : Nat) : V) = 1 := by
  simp [segA, segC]

/-- `scanBound_actual` within the weight of the scanned word. -/
theorem scanBound_actualB (gap : V) (v : Fin 9 → V) (k : V)
    {xs : List Seg} {i bound j : Nat} (h : KHome.scanBound i xs=some bound)
    (hi : i<8) (hj : j≤i) (L R : V) :
    ∃ j', j'≤bound ∧ j'<8 ∧
      ReachB (leftFrame (KHome.state j) (flatValue gap v k xs L) R)
        (leftFrame (KHome.state j') L (flatValue gap v k xs.reverse R))
        (((wA xs : Nat) : V)*gap + ((wC xs : Nat) : V)) := by
  induction xs generalizing i bound j L R with
  | nil =>
    simp only [KHome.scanBound,Option.some.injEq] at h
    subst bound
    exact ⟨j,hj,by omega,(ReachB.refl _).mono (Arithmetic.zero_le _)⟩
  | cons x xs ih =>
    rw [bound_cons]
    simp only [flatValue,List.reverse_cons,ArithmeticHome215.flatValue_append,flatValue]
    cases x with
    | box x => simp [KHome.scanBound] at h
    | bit b =>
      rw [bound_bit]
      cases b with
      | true =>
        obtain ⟨j',hb,hlt,hr⟩ := ih (by simpa [KHome.scanBound] using h)
          (by decide : 0<8) (by rfl : 0≤0) L (2*R+digit true)
        refine ⟨j',hb,hlt,?_⟩
        exact (ReachB.of_step (step_left_facing (ArithmeticHome215.reset_row j (by omega)) _ R)).trans hr
      | false =>
        by_cases hc : i+1<8
        · obtain ⟨j',hb,hlt,hr⟩ := ih (by simpa [KHome.scanBound,hc] using h)
            hc (show j+1≤i+1 by omega) L (2*R+digit false)
          exact ⟨j',hb,hlt,(ReachB.of_step
            (step_left_facing (ArithmeticHome215.next_row j (by omega)) _ R)).trans hr⟩
        · simp [KHome.scanBound,hc] at h
    | run b a c =>
      cases b with
      | false =>
        by_cases hc : a=0 ∧ i+c<8
        · obtain ⟨rfl,hc⟩ := hc
          obtain ⟨j',hb,hlt,hr⟩ := ih (by simpa [KHome.scanBound,hc] using h)
            hc (show j+c≤i+c by omega) L (bitPrefix false (c:V) R)
          refine ⟨j',hb,hlt,?_⟩
          simpa only [segA,segC,segValue,Nat.cast_zero,zero_mul,zero_add] using
            (ReachB.trans (⟨(c:V),le_rfl,
              ArithmeticHome215.scan_zeros_exact j c (by omega) (flatValue gap v k xs L) R⟩ :
                ReachB _ _ (c:V)) hr)
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
          have hn0 : ((segA (.run true a 0) : Nat) : V)*gap + ((segC (.run true a 0) : Nat) : V) = 0 := hn
          rw [hn0, zero_add]
          simpa only [segValue,Nat.cast_zero,show (a:V)*gap+(0:V)=0 from hn,bitPrefix_zero] using hr
        · have hp : 0<n := pos_iff_ne_zero.mpr hn
          have hbnd : (if c=0 then i else 0)<8 := by split <;> omega
          obtain ⟨j',hb,hlt,hr⟩ := ih (by simpa [KHome.scanBound] using h)
            hbnd (show 0≤(if c=0 then i else 0) by omega) L (bitPrefix true n R)
          exact ⟨j',hb,hlt,(scan_onesB j (by omega) n (flatValue gap v k xs L) R hp).trans hr⟩

/-- A successful Home shortcut, within one step bound, with the weight invariant. -/
theorem home_actualB (gap : V) (v : Fin 9 → V) (k : V)
    {s t : SConf} (h : KHome.home s=some t) :
    ReachPosB (interpret gap v k s) (interpret gap v k t) (cost gap v k s) ∧
      confA t ≤ confA s ∧ confC t ≤ confC s + 1 := by
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
        have hw := stripBlank_weight hs
        simp only [wA_reverse, wC_reverse] at hw
        have hl : flatValue gap v k l 0=flatValue gap v k u.reverse 1 := by
          simpa only [List.reverse_reverse] using ArithmeticHome215.stripBlank_actual gap v k hs
        obtain ⟨j',_,hj,hr⟩ := scanBound_actualB gap v k hc (by decide) (by rfl : 0≤0) 1
          (flatValue gap v k r 0)
        rw [List.reverse_reverse] at hr
        have hm := step_left_facing (V:=V) (ArithmeticHome215.reset_row j' hj) 0
          (flatValue gap v k u (flatValue gap v k r 0))
        have hb : ReachPosB (leftFrame 2 0 (2*(flatValue gap v k u (flatValue gap v k r 0))+1))
            (frameSparse 84 1 (flatValue gap v k u (flatValue gap v k r 0))) 18 :=
          ⟨18,by simp,le_rfl,ArithmeticHome215.boundary_actual _⟩
        have ht := ReachB.trans_positive (hr.trans (ReachB.of_step (by simpa using hm))) hb
        have hle : ((wA u.reverse : Nat) : V)*gap + ((wC u.reverse : Nat) : V) + 1 + 18 ≤
            cost gap v k (2,true,l,r) := by
          have ha : wA u ≤ confA (2,true,l,r) := by wt
          have hc' : wC u ≤ confC (2,true,l,r) := by wt
          unfold cost
          calc ((wA u.reverse : Nat) : V)*gap + ((wC u.reverse : Nat) : V) + 1 + 18
              = (((wA u : Nat) : V)*gap + ((wC u : Nat) : V)) + 19 := by
                rw [wA_reverse, wC_reverse]; ring
            _ ≤ ((confA (2,true,l,r) : V)*gap + (confC (2,true,l,r) : V)) + 19 :=
                _root_.add_le_add (lin_le ha hc' gap) le_rfl
            _ ≤ _ := _root_.add_le_add le_self_add le_rfl
        refine ⟨?_,by wt,by wt⟩
        simpa only [interpret,flatValue,segValue,digit_true,mul_zero,zero_add,
          ArithmeticHome215.flatValue_append,hl,show KHome.state 0=2 from rfl] using ht.mono hle
  · simp at h

theorem stepper_actualB (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {br : Branch} (hv : BranchValid br v) {s t : SConf} {m : Bool}
    (h : KHomeReady.stepper KTableCore.tm215 br s=some (t,m)) : StepOkB gap v k s t m := by
  simp only [KHomeReady.stepper,ArithmeticHome215.ready215,if_true] at h
  cases hs : KHome.home s with
  | none => exact sstep_actualB gap v k hk hv (by simpa [KHomeReady.homeStep,hs] using h)
  | some u =>
    simp only [KHomeReady.homeStep,hs,Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    obtain ⟨hp,hA,hC⟩ := home_actualB gap v k hs
    exact ⟨reachB_of_pos hp,⟨fun _ => hp,hA,hC⟩⟩

/-! ## The executor -/

/-- The clock bound of `fuel` executor steps from `s`. -/
noncomputable def execB (gap : V) (v : Fin 9 → V) (k : V) (fuel : Nat) (s : SConf) : V :=
  (fuel:V)*(cost gap v k s + fuel)

theorem cost_le_succ {gap k : V} {v : Fin 9 → V} {s t : SConf}
    (hA : confA t ≤ confA s) (hC : confC t ≤ confC s + 1) :
    cost gap v k t ≤ cost gap v k s + 1 := by
  unfold cost
  calc (confA t : V)*gap + (confC t : V) + boxW v k + 19
      ≤ (confA s : V)*gap + ((confC s + 1 : Nat) : V) + boxW v k + 19 :=
        _root_.add_le_add (_root_.add_le_add (lin_le hA hC gap) le_rfl) le_rfl
    _ = _ := by push_cast; ring

theorem execB_step {gap k : V} {v : Fin 9 → V} {s t : SConf}
    (hA : confA t ≤ confA s) (hC : confC t ≤ confC s + 1) (fuel : Nat) :
    cost gap v k s + execB gap v k fuel t ≤ execB gap v k (fuel+1) s := by
  unfold execB
  have h1 := cost_le_succ (gap:=gap) (v:=v) (k:=k) hA hC
  calc cost gap v k s + (fuel:V)*(cost gap v k t + fuel)
      ≤ cost gap v k s + (fuel:V)*(cost gap v k s + 1 + fuel) :=
        _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left (_root_.add_le_add h1 le_rfl)
          (Arithmetic.zero_le _))
    _ ≤ ((fuel+1 : Nat) : V)*(cost gap v k s + ((fuel+1 : Nat) : V)) :=
        le_of_add_eq (c := (fuel:V)+1) (by push_cast; ring)

/-- `execWith_actual` with the executor clock bound. -/
theorem execWith_actualB (gap : V) (v : Fin 9 → V) (k : V)
    {next : SConf → Option (SConf×Bool)} {target : SConf → Bool}
    (hnext : ∀ s t m, next s=some (t,m) → StepOkB gap v k s t m) :
    ∀ fuel s m0 t, KRuntimeCore.execWith next target fuel s m0=some t →
      target t=true ∧ ReachB (interpret gap v k s) (interpret gap v k t) (execB gap v k fuel s) ∧
      (m0=false → ReachPosB (interpret gap v k s) (interpret gap v k t) (execB gap v k fuel s))
  | 0,_,_,_,h => by simp [KRuntimeCore.execWith] at h
  | fuel+1,s,m0,t,h => by
    simp only [KRuntimeCore.execWith] at h
    split at h
    · rename_i ht; cases h
      simp only [Bool.and_eq_true] at ht
      exact ⟨ht.2,(ReachB.refl _).mono (Arithmetic.zero_le _),by intro hz; simp [hz] at ht⟩
    · split at h
      · simp at h
      · rename_i s' m hs
        obtain ⟨hg,he,hp⟩ := execWith_actualB gap v k hnext fuel s' (m0||m) t h
        obtain ⟨he0,hp0,hA,hC⟩ := hnext s s' m hs
        have hle := execB_step (gap:=gap) (v:=v) (k:=k) hA hC fuel
        refine ⟨hg,(he0.trans he).mono hle,?_⟩
        intro hm0; subst m0
        cases m with
        | true => exact ((hp0 rfl).trans_reach he).mono hle
        | false => exact (ReachB.trans_positive he0 (hp rfl)).mono hle

theorem exec_actualB (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {br : Branch} (hv : BranchValid br v) {target : SConf → Bool}
    {fuel : Nat} {s t : SConf}
    (h : KHomeReady.exec KTableCore.tm215 br target fuel s false=some t) :
    target t=true ∧ ReachPosB (interpret gap v k s) (interpret gap v k t) (execB gap v k fuel s) := by
  obtain ⟨ht,_,hp⟩ := execWith_actualB gap v k
    (fun _ _ _ hs => stepper_actualB gap v k hk hv hs) fuel s false t h
  exact ⟨ht,hp rfl⟩

theorem exec_matches_actualB (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {br : Branch} (hv : BranchValid br v) {fuel : Nat} {s t target : SConf}
    (h : KHomeReady.exec KTableCore.tm215 br (fun u => KRuntimeCore.sMatches u target) fuel s false=some t) :
    ReachPosB (interpret gap v k s) (interpret gap v k target) (execB gap v k fuel s) := by
  obtain ⟨ht,hp⟩ := exec_actualB gap v k hk hv h
  rw [matches_actual gap v k ht] at hp
  exact hp

end Internal
end DiophantineConsistency.ArithmeticRuntimeBoundTapeSymbolic
