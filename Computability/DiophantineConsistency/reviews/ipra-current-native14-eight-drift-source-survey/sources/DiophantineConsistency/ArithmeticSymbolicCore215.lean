import DiophantineConsistency.ArithmeticRegisterBoxes215

/-! The existing finite K symbolic checker, interpreted at arbitrary internal
215 tape values. Only syntax is reused from KRuntimeCore; all execution
premises are discharged by the actual arithmetic215 rows and register boxes. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.ArithmeticSymbolicCore215
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineTape215 ArithmeticRegisterBoxes215
open KRuntimeCore (BoxSt Eff Seg SConf Branch Tok)

section Internal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def plainTail (v : Fin 9 → V) (k z : V) : V :=
  file (List.ofFn v) (repeat3 6 k z)
noncomputable def markedTail (v : Fin 9 → V) (r : Fin 9) (k z : V) : V :=
  file (before v r) (markedBlock (v r) (file (after v r) (repeat3 6 k z)))

/-- Invalid finite indices have the explicit plain-file fallback. Actual
oracle success always proves the physical index is less than nine. -/
noncomputable def boxTail (v : Fin 9 → V) (k : V) : BoxSt → V → V
  | .plain .none, z => plainTail v k z
  | .plain (.inc r), z => if h : r<9 then
      plainTail (Function.update v ⟨r,h⟩ (v ⟨r,h⟩+1)) (k+1) z else plainTail v k z
  | .plain (.dec r), z => if h : r<9 then
      plainTail (Function.update v ⟨r,h⟩ (v ⟨r,h⟩-1)) k z else plainTail v k z
  | .mark r, z => if h : r<9 then markedTail v ⟨r,h⟩ k z else plainTail v k z
noncomputable def boxValue (v : Fin 9 → V) (k : V) (x : BoxSt) : V := boxTail v k x 0
noncomputable def getValue (v : Fin 9 → V) (r : Nat) : V :=
  if h : r<9 then v ⟨r,h⟩ else 0
def BranchValid (br : Branch) (v : Fin 9 → V) : Prop :=
  match br with
  | none => True
  | some (r,z) => if z then getValue v r=0 else getValue v r≠0

@[simp] lemma plainTail_zero (v : Fin 9 → V) (k : V) : plainTail v k 0=plain v k := rfl
@[simp] lemma markedTail_zero (v : Fin 9 → V) (r : Fin 9) (k : V) :
    markedTail v r k 0=marked v r k := rfl
@[simp] lemma box_plain (v : Fin 9 → V) (k : V) : boxValue v k (.plain .none)=plain v k := rfl
@[simp] lemma box_marked (v : Fin 9 → V) (r : Fin 9) (k : V) :
    boxValue v k (.mark r)=marked v r k := by simp [boxValue,boxTail,r.isLt]
@[simp] lemma box_incremented (v : Fin 9 → V) (r : Fin 9) (k : V) :
    boxValue v k (.plain (.inc r))=plain (Function.update v r (v r+1)) (k+1) := by
  simp [boxValue,boxTail,r.isLt]
@[simp] lemma box_decremented (v : Fin 9 → V) (r : Fin 9) (k : V) :
    boxValue v k (.plain (.dec r))=plain (Function.update v r (v r-1)) k := by
  simp [boxValue,boxTail,r.isLt]

private lemma file_even (xs : List V) (hx : xs≠[]) (z : V) : ∃ u, file xs z=2*u := by
  cases xs with
  | nil => contradiction
  | cons x xs => exact ⟨bitPrefix true (x+1) (file xs z),rfl⟩
lemma plainTail_even (v : Fin 9 → V) (k z : V) : ∃ u, plainTail v k z=2*u := by
  exact file_even _ (by intro h; have := congrArg List.length h; simp at this) _
lemma markedTail_even (v : Fin 9 → V) (r : Fin 9) (k z : V) : ∃ u, markedTail v r k z=2*u := by
  by_cases hr : r.val=0
  · have he : before v r=[] := by simp [before,hr]
    simp only [markedTail,he,file,markedBlock]
    exact ⟨_,rfl⟩
  · exact file_even _ (by intro h; have := congrArg List.length h; rw [before_length] at this; exact hr this) _
lemma boxTail_even (v : Fin 9 → V) (k z : V) (x : BoxSt) : ∃ u, boxTail v k x z=2*u := by
  cases x with
  | mark r => by_cases h : r<9 <;> simp only [boxTail,h,dif_pos]
              · exact markedTail_even v ⟨r,h⟩ k z
              · exact plainTail_even v k z
  | plain e =>
    cases e with
    | none => exact plainTail_even v k z
    | inc r => by_cases h : r<9 <;> simp only [boxTail,h,dif_pos] <;> exact plainTail_even _ _ _
    | dec r => by_cases h : r<9 <;> simp only [boxTail,h,dif_pos] <;> exact plainTail_even _ _ _

lemma ReachPos.reach {x y : V} (h : ReachPos x y) : Reach x y := by
  obtain ⟨t,_,ht⟩ := h; exact ⟨t,ht⟩
lemma ReachPos.of_step {x y : V} (h : ArithmeticMachineStep215.stepValue x=y) : ReachPos x y :=
  ⟨1,by simp,(run_one x).trans h⟩
lemma ReachPos.trans_reach {x y z : V} (h : ReachPos x y) (g : Reach y z) : ReachPos x z := by
  obtain ⟨t,ht,he⟩ := h; obtain ⟨u,hu⟩ := g
  exact ⟨t+u,lt_of_lt_of_le ht (by simp),by rw [runFrom_add,he,hu]⟩
lemma Reach.trans_positive {x y z : V} (h : Reach x y) (g : ReachPos y z) : ReachPos x z := by
  obtain ⟨t,he⟩ := h; obtain ⟨u,hu,hue⟩ := g
  exact ⟨t+u,lt_of_lt_of_le hu (by simp),by rw [runFrom_add,he,hue]⟩

/-- Oracle dispatch is independent of the relation used to certify each box. -/
theorem oracle_of_boxes (v : Fin 9 → V) (k L : V) (R : V → V → Prop)
    (hmark : ∀ r : Fin 9, R (frameSparse (skipState r) L (plain v k))
      (leftFrame (markExit r) L (marked v r k)))
    (hinc : ∀ r : Fin 9, R (frameSparse 64 L (marked v r k))
      (leftFrame 40 L (plain (Function.update v r (v r+1)) (k+1))))
    (hdecp : ∀ r : Fin 9, 0 < v r → R (frameSparse 0 L (marked v r k))
      (leftFrame 40 (2*L+1) (plain (Function.update v r (v r-1)) k)))
    (hdec0 : ∀ r : Fin 9, v r = 0 → R (frameSparse 0 L (marked v r k))
      (leftFrame 97 L (plain v k)))
    {q q' : Nat} {br : Branch} {x x' : BoxSt} {extra : Bool}
    (h : KRuntimeCore.oracle q br x=some (q',x',extra)) (hv : BranchValid br v) :
    R (frameSparse q L (boxValue v k x))
      (leftFrame q' (if extra then 2*L+1 else L) (boxValue v k x')) := by
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
          hmark ⟨r,hr⟩
  | mark r =>
    by_cases hr : r<9
    · by_cases hq : q=64
      · simp only [KRuntimeCore.oracle,if_pos hr,if_pos hq,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        subst q
        simpa only [boxValue,boxTail,dif_pos hr,markedTail_zero,plainTail_zero,Bool.false_eq_true,if_false] using hinc ⟨r,hr⟩
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
                simpa only [boxValue,boxTail,dif_pos hr,markedTail_zero,plainTail_zero,if_true] using hdecp ⟨r,hr⟩ hp
              · simp [KRuntimeCore.oracle,hr] at h
                obtain ⟨rfl,rfl,rfl⟩ := h
                have hz : v ⟨r,hr⟩=0 := by simpa [BranchValid,getValue,hr] using hv
                simpa only [boxValue,boxTail,dif_pos hr,markedTail_zero,plainTail_zero,Bool.false_eq_true,if_false] using hdec0 ⟨r,hr⟩ hz
            · simp [KRuntimeCore.oracle,hr,hzero,he] at h
        · simp [KRuntimeCore.oracle,hr,hq,hzero] at h
    · simp [KRuntimeCore.oracle,hr] at h


/-- The actual checker oracle, without a caller-supplied box axiom. -/
theorem oracle_actual (v : Fin 9 → V) (k L : V) (hk : 0<k)
    {q q' : Nat} {br : Branch} {x x' : BoxSt} {extra : Bool}
    (h : KRuntimeCore.oracle q br x=some (q',x',extra)) (hv : BranchValid br v) :
    ReachPos (frameSparse q L (boxValue v k x))
      (leftFrame q' (if extra then 2*L+1 else L) (boxValue v k x')) := by
  exact oracle_of_boxes v k L ReachPos
    (fun r => box_mark v r L k) (fun r => box_inc v r L k)
    (fun r hr => box_decp v r L k hr) (fun r hr => box_dec0 v r L k hk hr) h hv

noncomputable def segValue (gap : V) (v : Fin 9 → V) (k : V) : Seg → V → V
  | .bit b,z => 2*z+digit b
  | .run b a c,z => bitPrefix b ((a:V)*gap+c) z
  | .box x,z => boxTail v k x z
noncomputable def flatValue (gap : V) (v : Fin 9 → V) (k : V) : List Seg → V → V
  | [],z => z
  | x::xs,z => segValue gap v k x (flatValue gap v k xs z)
noncomputable def interpret (gap : V) (v : Fin 9 → V) (k : V) : SConf → V
  | (q,true,l,r) => leftFrame q (flatValue gap v k l 0) (flatValue gap v k r 0)
  | (q,false,l,r) => frameSparse q (flatValue gap v k l 0) (flatValue gap v k r 0)
def StepOk (gap : V) (v : Fin 9 → V) (k : V) (s t : SConf) (m : Bool) : Prop :=
  Reach (interpret gap v k s) (interpret gap v k t) ∧
    (m=true → ReachPos (interpret gap v k s) (interpret gap v k t))
lemma stepOk_eq {gap k : V} {v : Fin 9 → V} {s t : SConf}
    (h : interpret gap v k s=interpret gap v k t) : StepOk gap v k s t false :=
  ⟨Reach.of_eq h,by intro h; cases h⟩
lemma stepOk_one {gap k : V} {v : Fin 9 → V} {s t : SConf}
    (h : ArithmeticMachineStep215.stepValue (interpret gap v k s)=interpret gap v k t) :
    StepOk gap v k s t true := ⟨Reach.of_step h,fun _ => ReachPos.of_step h⟩

lemma peelLeft_actual (gap : V) (v : Fin 9 → V) (k : V)
    {q : Nat} {b : Bool} {a c : Nat} {l r : List Seg} {t : SConf} {m : Bool}
    (h : KRuntimeCore.peelLeft q b a c l r=some (t,m)) :
    StepOk gap v k (q,true,.run b a c::l,r) t m := by
  cases c with
  | succ c =>
    simp only [KRuntimeCore.peelLeft,Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    apply stepOk_eq
    simp only [interpret,flatValue,segValue,Nat.cast_add,Nat.cast_one,←add_assoc,bitPrefix_succ]
  | zero =>
    cases a with
    | zero =>
      simp only [KRuntimeCore.peelLeft,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      apply stepOk_eq
      simp [interpret,flatValue,segValue]
    | succ a => simp [KRuntimeCore.peelLeft] at h
lemma peelRight_actual (gap : V) (v : Fin 9 → V) (k : V)
    {q : Nat} {b : Bool} {a c : Nat} {l r : List Seg} {t : SConf} {m : Bool}
    (h : KRuntimeCore.peelRight q b a c l r=some (t,m)) :
    StepOk gap v k (q,false,l,.run b a c::r) t m := by
  cases c with
  | succ c =>
    simp only [KRuntimeCore.peelRight,Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    apply stepOk_eq
    simp only [interpret,flatValue,segValue,Nat.cast_add,Nat.cast_one,←add_assoc,bitPrefix_succ]
  | zero =>
    cases a with
    | zero =>
      simp only [KRuntimeCore.peelRight,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      apply stepOk_eq
      simp [interpret,flatValue,segValue]
    | succ a => simp [KRuntimeCore.peelRight] at h

/-- Full actual215 symbolic step, including zero scans and the literal moved flag. -/
theorem sstep_actual (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {br : Branch} (hv : BranchValid br v) {s t : SConf} {m : Bool}
    (h : KRuntimeCore.sstep KTableCore.tm215 br s=some (t,m)) : StepOk gap v k s t m := by
  obtain ⟨q,onl,l,r⟩ := s
  cases onl with
  | true =>
    cases l with
    | nil =>
      simp only [KRuntimeCore.sstep,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      apply stepOk_eq
      simp [interpret,flatValue,segValue,leftFrame]
    | cons x l =>
      cases x with
      | bit b =>
        simp only [KRuntimeCore.sstep,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        exact stepOk_eq (leftFrame_bit q b _ _)
      | box x => simp [KRuntimeCore.sstep] at h
      | run b a c =>
        simp only [KRuntimeCore.sstep] at h
        split at h
        · rename_i w q' hm
          split at h
          · rename_i hq; subst q'; cases h
            exact ⟨⟨_,scan_left q b w hm _ _ _⟩,by intro h; cases h⟩
          · exact peelLeft_actual gap v k h
        · exact peelLeft_actual gap v k h
  | false =>
    cases r with
    | nil => simp [KRuntimeCore.sstep] at h
    | cons x r =>
      cases x with
      | bit b =>
        simp only [KRuntimeCore.sstep] at h
        split at h
        · rename_i w q' hm; cases h
          exact stepOk_one (step_right hm _ _)
        · rename_i w q' hm; cases h
          exact stepOk_one (step_left hm _ _)
        · simp at h
      | run b a c =>
        simp only [KRuntimeCore.sstep] at h
        split at h
        · rename_i w q' hm
          split at h
          · rename_i hq; subst q'; cases h
            exact ⟨⟨_,scan_right q b w hm _ _ _⟩,by intro h; cases h⟩
          · exact peelRight_actual gap v k h
        · exact peelRight_actual gap v k h
      | box x =>
        cases r with
        | cons y r => simp [KRuntimeCore.sstep] at h
        | nil =>
          simp only [KRuntimeCore.sstep] at h
          split at h
          · rename_i q' x' extra ho; cases h
            have he := ReachPos.reach (oracle_actual v k (flatValue gap v k l 0) hk ho hv)
            cases extra <;> exact ⟨he,by intro h; cases h⟩
          · split at h
            · rename_i q' hm; cases h
              apply stepOk_one
              obtain ⟨z,hz⟩ := boxTail_even v k 0 x
              change ArithmeticMachineStep215.stepValue (frameSparse q _ (boxTail v k x 0))=leftFrame q' _ (boxTail v k x 0)
              rw [hz]
              simpa using step_left hm (flatValue gap v k l 0) z
            · simp at h

theorem execWith_actual (gap : V) (v : Fin 9 → V) (k : V)
    {next : SConf → Option (SConf×Bool)} {target : SConf → Bool}
    (hnext : ∀ s t m, next s=some (t,m) → StepOk gap v k s t m) :
    ∀ fuel s m0 t, KRuntimeCore.execWith next target fuel s m0=some t →
      target t=true ∧ Reach (interpret gap v k s) (interpret gap v k t) ∧
      (m0=false → ReachPos (interpret gap v k s) (interpret gap v k t))
  | 0,_,_,_,h => by simp [KRuntimeCore.execWith] at h
  | fuel+1,s,m0,t,h => by
    simp only [KRuntimeCore.execWith] at h
    split at h
    · rename_i ht; cases h
      simp only [Bool.and_eq_true] at ht
      exact ⟨ht.2,Reach.refl _,by intro hz; simp [hz] at ht⟩
    · split at h
      · simp at h
      · rename_i s' m hs
        obtain ⟨hg,he,hp⟩ := execWith_actual gap v k hnext fuel s' (m0||m) t h
        obtain ⟨he0,hp0⟩ := hnext s s' m hs
        refine ⟨hg,he0.trans he,?_⟩
        intro hm0; subst m0
        cases m with
        | true => exact ReachPos.trans_reach (hp0 rfl) he
        | false => exact Reach.trans_positive he0 (hp rfl)
theorem exec_actual (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {br : Branch} (hv : BranchValid br v) {target : SConf → Bool}
    {fuel : Nat} {s t : SConf}
    (h : KRuntimeCore.exec KTableCore.tm215 br target fuel s false=some t) :
    target t=true ∧ ReachPos (interpret gap v k s) (interpret gap v k t) := by
  obtain ⟨hg,_,hp⟩ := execWith_actual gap v k
    (fun _ _ _ hs => sstep_actual gap v k hk hv hs) fuel s false t h
  exact ⟨hg,hp rfl⟩

noncomputable def tokValue (gap : V) (v : Fin 9 → V) (k : V) : Tok → V → V
  | .run b a c,z => bitPrefix b ((a:V)*gap+c) z
  | .box x,z => boxTail v k x z
noncomputable def flatTok (gap : V) (v : Fin 9 → V) (k : V) : List Tok → V → V
  | [],z => z
  | t::ts,z => tokValue gap v k t (flatTok gap v k ts z)
lemma flatTok_append (gap : V) (v : Fin 9 → V) (k : V) (xs ys : List Tok) (z : V) :
    flatTok gap v k (xs++ys) z=flatTok gap v k xs (flatTok gap v k ys z) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,flatTok,ih]
lemma flatTok_push (gap : V) (v : Fin 9 → V) (k : V) (t : Tok) (ts : List Tok) (z : V) :
    flatTok gap v k (KRuntimeCore.push t ts) z=tokValue gap v k t (flatTok gap v k ts z) := by
  cases t with
  | box x => rfl
  | run b a c =>
    have h : flatTok gap v k (match ts with
        | .run b' a' c'::rest => if b=b' then .run b (a+a') (c+c')::rest else .run b a c::ts
        | _ => .run b a c::ts) z=tokValue gap v k (.run b a c) (flatTok gap v k ts z) := by
      cases ts with
      | nil => rfl
      | cons t ts =>
        cases t with
        | box x => rfl
        | run b' a' c' =>
          by_cases hb : b=b'
          · subst b'
            simp only [if_true,flatTok,tokValue,Nat.cast_add]
            rw [show ((a:V)+a')*gap+(c+c')=((a:V)*gap+c)+((a':V)*gap+c') by ring,bitPrefix_add]
          · simp only [if_neg hb,flatTok,tokValue]
    cases a with
    | zero => cases c with
              | zero => simp [KRuntimeCore.push,tokValue]
              | succ c => exact h
    | succ a => exact h
lemma flatTok_norm (gap : V) (v : Fin 9 → V) (k : V) (xs : List Seg) (z : V) :
    flatTok gap v k (KRuntimeCore.norm xs) z=flatValue gap v k xs z := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [KRuntimeCore.norm,List.foldr_cons] at ih ⊢
    rw [flatTok_push,ih]
    cases x <;> simp [KRuntimeCore.tokOf,tokValue,flatValue,segValue]
lemma flatTok_normL (gap : V) (v : Fin 9 → V) (k : V) (xs : List Seg) :
    flatTok gap v k (KRuntimeCore.normL xs) 0=flatValue gap v k xs 0 := by
  rw [←flatTok_norm]
  unfold KRuntimeCore.normL
  generalize he : (KRuntimeCore.norm xs).reverse=ys
  rw [show KRuntimeCore.norm xs=ys.reverse by rw [←he,List.reverse_reverse]]
  cases ys with
  | nil => rfl
  | cons t ys =>
    cases t with
    | box x => rfl
    | run b a c =>
      cases b <;> simp [List.reverse_cons,flatTok_append,flatTok,tokValue,bitPrefix]
theorem matches_actual (gap : V) (v : Fin 9 → V) (k : V) {s t : SConf}
    (h : KRuntimeCore.sMatches s t=true) : interpret gap v k s=interpret gap v k t := by
  obtain ⟨q,onl,l,r⟩ := s
  obtain ⟨q',onl',l',r'⟩ := t
  simp only [KRuntimeCore.sMatches,Bool.and_eq_true,beq_iff_eq] at h
  obtain ⟨⟨⟨rfl,rfl⟩,hr⟩,hl⟩ := h
  have er : flatValue gap v k r 0=flatValue gap v k r' 0 := by rw [←flatTok_norm,hr,flatTok_norm]
  have el : flatValue gap v k l 0=flatValue gap v k l' 0 := by rw [←flatTok_normL,hl,flatTok_normL]
  cases onl <;> simp only [interpret,er,el]
private lemma numeral_six_eq_six : (ORingStructure.numeral 6 : V)=6 := by
  simp [numeral_eq_natCast]
end Internal

/-! The ordinary-Nat binding is algebraic and is not used to transfer any
execution theorem into a nonstandard arithmetic model. -/
open ArithmeticMachinePerm252 (bitsCode)
lemma bitsCode_prefix (b : Bool) (n : Nat) (xs : List Bool) :
    bitsCode (List.replicate n b++xs)=bitPrefix b n (bitsCode xs) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ,List.cons_append,bitsCode,ih,bitPrefix_succ,←digit_cast,natCast_nat]
    omega
lemma file_nat (vs : List Nat) (xs : List Bool) :
    file vs (bitsCode xs)=bitsCode (KRuntimeCore.sepsR vs++xs) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [KRuntimeCore.sepsR,List.flatMap_cons,List.cons_append,List.append_assoc,
      bitsCode,Bool.toNat_false,zero_add,file,block]
    rw [bitsCode_prefix, ih]
    rfl
lemma repeat3_nat (k : Nat) (xs : List Bool) :
    repeat3 6 k (bitsCode xs)=bitsCode (KRuntimeCore.sepsR (List.replicate k 1)++xs) := by
  induction k with
  | zero => simp [KRuntimeCore.sepsR]
  | succ k ih =>
    rw [repeat3_succ,ih,List.replicate_succ]
    simp only [KRuntimeCore.sepsR,List.flatMap_cons,List.replicate_succ,List.replicate_zero,
      List.cons_append,List.nil_append,bitsCode,Bool.toNat_false,Bool.toNat_true]
    omega
theorem plain_nat (v : Fin 9 → Nat) (k : Nat) :
    plain v k=bitsCode (KRuntimeCore.sepsR (List.ofFn v++List.replicate k 1)) := by
  have hk : repeat3 6 k (0:Nat)=bitsCode (KRuntimeCore.sepsR (List.replicate k 1)) := by
    simpa only [bitsCode,List.append_nil] using repeat3_nat k []
  unfold plain
  rw [←numeral_six_eq_six,Nat.numeral_eq,hk]
  simpa [KRuntimeCore.sepsR,List.flatMap_append] using
    file_nat (List.ofFn v) (KRuntimeCore.sepsR (List.replicate k 1))
private lemma sepsM_split (pre rest : List Nat) (w : Nat) :
    KRuntimeCore.sepsM pre.length (pre++w::rest)=
      KRuntimeCore.sepsR pre++false::false::List.replicate w true++KRuntimeCore.sepsR rest := by
  induction pre with
  | nil => rfl
  | cons u pre ih =>
    simp only [List.length_cons,List.cons_append,KRuntimeCore.sepsM,ih,KRuntimeCore.sepsR,List.flatMap_cons]
    simp [List.append_assoc]
theorem marked_nat (v : Fin 9 → Nat) (r : Fin 9) (k : Nat) :
    marked v r k=bitsCode (KRuntimeCore.sepsM r (List.ofFn v++List.replicate k 1)) := by
  rw [values_split v r,List.append_assoc, List.cons_append,←before_length v r,sepsM_split]
  unfold marked
  simp only [List.append_assoc]
  rw [←file_nat]
  congr 1
  simp only [List.cons_append,bitsCode,Bool.toNat_false,zero_add]
  rw [bitsCode_prefix]
  unfold markedBlock
  congr 2
  rw [show KRuntimeCore.sepsR (after v r++List.replicate k 1)=
    KRuntimeCore.sepsR (after v r)++KRuntimeCore.sepsR (List.replicate k 1) by simp [KRuntimeCore.sepsR]]
  rw [←file_nat,←numeral_six_eq_six,Nat.numeral_eq,show repeat3 6 k (0:Nat)=bitsCode (KRuntimeCore.sepsR (List.replicate k 1)) by
    simpa only [bitsCode,List.append_nil] using repeat3_nat k []]

private lemma primary_update (v : Fin 9 → Nat) (r : Fin 9) (w : Nat) :
    List.ofFn (Function.update v r w)=before v r++w::after v r := by
  rw [values_update,List.set_eq_take_append_cons_drop,if_pos (by simp)]
  rfl
private lemma incr_split (pre rest : List Nat) (w : Nat) :
    KRuntimeCore.incr pre.length (pre++w::rest)=pre++(w+1)::rest := by
  induction pre with
  | nil => rfl
  | cons x pre ih => simp only [List.length_cons,List.cons_append,KRuntimeCore.incr,ih]
private lemma decr_split (pre rest : List Nat) (w : Nat) :
    KRuntimeCore.decr pre.length (pre++w::rest)=pre++(w-1)::rest := by
  induction pre with
  | nil => rfl
  | cons x pre ih => simp only [List.length_cons,List.cons_append,KRuntimeCore.decr,ih]
theorem increment_nat (v : Fin 9 → Nat) (r : Fin 9) (k : Nat) :
    boxValue v k (.plain (.inc r))=
      bitsCode (KRuntimeCore.boxList (.plain (.inc r)) (List.ofFn v++List.replicate k 1)) := by
  rw [box_incremented,plain_nat,KRuntimeCore.boxList]
  congr 2
  rw [primary_update,values_split v r,←before_length v r]
  simp only [List.append_assoc,List.cons_append]
  rw [incr_split]
  simp only [List.append_assoc,List.cons_append]
  congr 2
  exact congrArg (fun xs => after v r++xs) (List.replicate_add k 1 1)
theorem decrement_nat (v : Fin 9 → Nat) (r : Fin 9) (k : Nat) :
    boxValue v k (.plain (.dec r))=
      bitsCode (KRuntimeCore.boxList (.plain (.dec r)) (List.ofFn v++List.replicate k 1)) := by
  rw [box_decremented,plain_nat,KRuntimeCore.boxList]
  congr 2
  rw [primary_update,values_split v r,←before_length v r]
  simp only [List.append_assoc,List.cons_append]
  rw [decr_split]
  change before v r++Arithmetic.sub (v r) 1::(after v r++List.replicate k 1)=
    before v r++(v r-1)::(after v r++List.replicate k 1)
  rw [ArithmeticRow254.foundation_sub_nat]

end DiophantineConsistency.ArithmeticSymbolicCore215
