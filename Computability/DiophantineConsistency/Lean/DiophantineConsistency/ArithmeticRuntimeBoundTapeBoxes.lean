import DiophantineConsistency.ArithmeticRuntimeBoundTape

/-! # Clock-bounded register boxes of the literal decimal215 machine

Bounded twins of the file traversals and the four register boxes of
`ArithmeticRegisterBoxes215`. One traversal of a register file costs `v+2`
steps per block (`fileCost`), and every box excursion (mark, increment, zero
and positive decrement) finishes within `boxW values k = 2*fileCost + 6*k + 7`
steps, linear in the tape length. Proof bodies follow the accepted originals;
no existing statement is changed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.ArithmeticRuntimeBoundTapeBoxes
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticTapePrefix254 ArithmeticMachineTape215
open ArithmeticRegisterBoxes215 ArithmeticRuntimeBoundTape
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem le_of_add_eq {a b c : V} (h : a + c = b) : a ≤ b := h ▸ le_self_add

/-- Steps of one traversal of a register file: `v+2` per block. -/
noncomputable def fileCost : List V → V
  | [] => 0
  | v::vs => (v+2) + fileCost vs


@[simp] theorem fileCost_nil : fileCost ([] : List V) = 0 := rfl

@[simp] theorem fileCost_cons (v : V) (vs : List V) : fileCost (v::vs) = (v+2) + fileCost vs := rfl
theorem fileCost_append (vs ws : List V) : fileCost (vs++ws) = fileCost vs + fileCost ws := by
  induction vs with
  | nil => simp
  | cons v vs ih => simp only [List.cons_append, fileCost_cons, ih]; ring

/-- The common clock bound of every register box. -/
noncomputable def boxW (values : Fin 9 → V) (k : V) : V :=
  2*fileCost (List.ofFn values) + 6*k + 7

theorem fileCost_split (values : Fin 9 → V) (r : Fin 9) :
    fileCost (List.ofFn values) =
      fileCost (before values r) + ((values r + 2) + fileCost (after values r)) := by
  rw [values_split values r, fileCost_append, fileCost_cons]

lemma forward_fileB {qa qb : Nat}
    (h0 : KTableCore.tm215 qa false=some (false,true,qb))
    (h1 : KTableCore.tm215 qb true=some (true,true,qa))
    (hs : KTableCore.tm215 qa true=some (true,true,qa)) (vs : List V) (L R : V) :
    ReachB (frameSparse qa L (file vs R)) (frameSparse qa (reverseFile vs L) R) (fileCost vs) := by
  induction vs generalizing L with
  | nil => exact ReachB.refl _
  | cons v vs ih =>
    exact (show ReachB _ _ (v+2) from ⟨v+2,le_rfl,forward_block h0 h1 hs v L (file vs R)⟩).trans (ih _)
lemma carry_fileB (vs : List V) (L R : V) :
    ReachB (frameSparse 0 L (file vs R)) (frameSparse 0 (reverseCarry vs L) R) (fileCost vs) := by
  induction vs generalizing L with
  | nil => exact ReachB.refl _
  | cons v vs ih =>
    exact (show ReachB _ _ (v+2) from ⟨v+2,le_rfl,carry_block v L (file vs R)⟩).trans (ih _)
lemma return_nonemptyB {entry ones exit : Nat}
    (he : KTableCore.tm215 entry true=some (true,false,ones))
    (h1 : KTableCore.tm215 exit true=some (true,false,ones))
    (hs : KTableCore.tm215 ones true=some (true,false,ones))
    (h0 : KTableCore.tm215 ones false=some (false,false,exit))
    (vs : List V) (hn : vs≠[]) (L R : V) :
    ReachB (leftFrame entry (reverseFile vs L) R) (leftFrame exit L (file vs R)) (fileCost vs) := by
  induction vs generalizing L R with
  | nil => exact (hn rfl).elim
  | cons v vs ih =>
    cases vs with
    | nil => exact ⟨v+2,by simp,return_block he hs h0 v L R⟩
    | cons w ws =>
      rw [fileCost_cons, add_comm]
      exact (ih (by simp) _ _).trans ⟨v+2,le_rfl,return_block h1 hs h0 v L (file (w::ws) R)⟩
lemma return_fileB {ones exit : Nat}
    (h1 : KTableCore.tm215 exit true=some (true,false,ones))
    (hs : KTableCore.tm215 ones true=some (true,false,ones))
    (h0 : KTableCore.tm215 ones false=some (false,false,exit)) (vs : List V) (L R : V) :
    ReachB (leftFrame exit (reverseFile vs L) R) (leftFrame exit L (file vs R)) (fileCost vs) := by
  cases vs with
  | nil => exact ReachB.refl _
  | cons v vs =>
    exact return_nonemptyB h1 h1 hs h0 (v::vs) (by simp) L R
lemma rollback_fileB (vs : List V) (L R : V) :
    ReachB (leftFrame 97 (reverseCarry vs L) R) (leftFrame 97 L (file vs R)) (fileCost vs) := by
  induction vs generalizing L R with
  | nil => exact ReachB.refl _
  | cons v vs ih =>
    rw [fileCost_cons, add_comm]
    exact (ih _ _).trans ⟨v+2,le_rfl,rollback_block v L (file vs R)⟩

lemma skip_fileB (pre : List V) (m : Nat) (h : pre.length+m<9) (L R : V) :
    ReachB (frameSparse (skipState (pre.length+m)) L (file pre R))
      (frameSparse (skipState m) (reverseFile pre L) R) (fileCost pre) := by
  induction pre generalizing L with
  | nil =>
    simpa only [List.length_nil,Nat.zero_add,file,reverseFile,fileCost_nil] using
      ReachB.refl (frameSparse (skipState m) L R)
  | cons v pre ih =>
    have hn : pre.length+m<8 := by simp only [List.length_cons] at h; omega
    change ReachB (frameSparse (skipState (pre.length+1+m)) L (block v (file pre R))) _ _
    rw [show pre.length+1+m=(pre.length+m)+1 by omega,block,
      show fileCost (v::pre) = 1 + ((v+1) + fileCost pre) by simp only [fileCost_cons]; ring]
    refine (ReachB.of_step (by simpa using right_zero (skip_next _ hn) L (bitPrefix true (v+1) (file pre R)))).trans ?_
    refine (show ReachB _ _ (v+1) from ⟨v+1,le_rfl,scan_right _ true true (skip_self _ (by omega)) _ _ _⟩).trans ?_
    exact ih (by omega) _

lemma mark_splitB (pre rest : List V) (v L tail : V) (hr : pre.length<9) :
    ReachB (frameSparse (skipState pre.length) L (file pre (block v (file rest tail))))
      (leftFrame (markExit pre.length) L (file pre (markedBlock v (file rest tail))))
      (fileCost pre + (3 + fileCost pre)) := by
  refine (show ReachB _ _ (fileCost pre) from by
    simpa using skip_fileB pre 0 (by simpa using hr) L (block v (file rest tail))).trans ?_
  refine (show ReachB _ _ (3:V) from ⟨3,le_rfl,mark_local v (reverseFile pre L) (file rest tail)⟩).trans ?_
  cases pre with
  | nil => exact ReachB.refl _
  | cons w ws =>
    exact return_nonemptyB (ones:=2) (exit:=3) (by rfl) (by rfl) (by rfl) (by rfl) _ (by simp) _ _
lemma decrement_positive_splitB (pre rest : List V) (v L tail : V) :
    ReachB (frameSparse 0 L (file pre (markedBlock (v+1) (file rest tail))))
      (leftFrame 40 (2*L+1) (file pre (block v (file rest tail))))
      (fileCost pre + (4 + fileCost pre)) := by
  refine (carry_fileB pre L _).trans ?_
  refine (show ReachB _ _ (4:V) from
    ⟨4,le_rfl,decrement_positive_local v (reverseCarry pre L) (file rest tail)⟩).trans ?_
  rw [carry_reverse_file]
  exact return_fileB (ones:=54) (by rfl) (by rfl) (by rfl) _ _ _
lemma decrement_zero_splitB (pre : List V) (w L R : V) :
    ReachB (frameSparse 0 L (file pre (markedBlock 0 (block w R))))
      (leftFrame 97 L (file pre (block 0 (block w R)))) (fileCost pre + (7 + fileCost pre)) := by
  refine (carry_fileB pre L _).trans ?_
  exact (show ReachB _ _ (7:V) from ⟨7,le_rfl,decrement_zero_local w (reverseCarry pre L) R⟩).trans
    (rollback_fileB pre L _)
lemma increment_splitB (pre rest : List V) (v L k : V) :
    ReachB (frameSparse 64 L (file pre (markedBlock v (file rest (repeat3 6 k 0)))))
      (leftFrame 40 L (file pre (block (v+1) (file rest (repeat3 6 (k+1) 0)))))
      (fileCost pre + ((v+2) + (fileCost rest + (3*k + (6 + (3*k +
        (fileCost rest + (((v+1)+2) + fileCost pre)))))))) := by
  refine (forward_fileB (qa:=64) (qb:=74) (by rfl) (by rfl) (by rfl) pre L _).trans ?_
  refine (show ReachB _ _ (v+2) from ⟨v+2,le_rfl,increment_middle v (reverseFile pre L) _⟩).trans ?_
  refine (carry_fileB rest _ _).trans ?_
  refine (show ReachB _ _ (3*k) from ⟨3*k,le_rfl,carry_spares k _ 0⟩).trans ?_
  refine (show ReachB _ _ (6:V) from ⟨6,le_rfl,increment_tail _⟩).trans ?_
  rw [carry_reverse_spares,carry_reverse_file,increment_middle_reverse]
  refine (show ReachB _ _ (3*k) from ⟨3*k,le_rfl,return_spares k _ 6⟩).trans ?_
  have hr : repeat3 6 k (6:V)=repeat3 6 (k+1) 0 := by
    simpa using repeat3_push (6:V) k 0
  rw [hr]
  refine (return_fileB (ones:=54) (by rfl) (by rfl) (by rfl) rest _ _).trans ?_
  refine (show ReachB _ _ ((v+1)+2) from
    ⟨(v+1)+2,le_rfl,return_block (ones:=54) (by rfl) (by rfl) (by rfl) (v+1) _ _⟩).trans ?_
  exact return_fileB (ones:=54) (by rfl) (by rfl) (by rfl) pre L _

/-- `Reach.positive` with its clock bound. -/
lemma ReachB.positive {q q' : Nat} {L R L' R' B : V}
    (h : ReachB (frameSparse q L R) (leftFrame q' L' R') B)
    (hne : sparseCode q≠sparseCode q') :
    ReachPosB (frameSparse q L R) (leftFrame q' L' R') B := by
  obtain ⟨t,htB,ht⟩ := h
  refine ⟨t,pos_iff_ne_zero.mpr ?_,htB,ht⟩
  intro hz
  subst t
  have he := congrArg first ht
  have hc : (sparseCode q:V)=(sparseCode q':V) := by
    simpa only [runFrom_zero,leftFrame,frameSparse,first_cantor] using he
  exact hne (nat_cast_inj.mp hc)

/-- Every physical marker entry, within the box bound. -/
theorem box_markB (values : Fin 9 → V) (r : Fin 9) (L k : V) :
    ReachPosB (frameSparse (skipState r) L (plain values k))
      (leftFrame (markExit r) L (marked values r k)) (boxW values k) := by
  apply ReachB.positive
  · refine ReachB.mono (B := fileCost (before values r) + (3 + fileCost (before values r))) ?_ ?_
    · rw [plain_split values r,marked]
      have h := mark_splitB (before values r) (after values r) (values r) L (repeat3 6 k 0)
        (by rw [before_length]; exact r.isLt)
      simpa only [before_length] using h
    · rw [boxW, fileCost_split values r]
      exact le_of_add_eq (c := 2*(values r+2) + 2*fileCost (after values r) + 6*k + 4) (by ring)
  · have h : ∀ r : Fin 9, sparseCode (skipState r)≠sparseCode (markExit r) := by decide
    exact h r
/-- The increment box, within the box bound. -/
theorem box_incB (values : Fin 9 → V) (r : Fin 9) (L k : V) :
    ReachPosB (frameSparse 64 L (marked values r k))
      (leftFrame 40 L (plain (Function.update values r (values r+1)) (k+1))) (boxW values k) := by
  apply ReachB.positive
  · refine ReachB.mono (B := fileCost (before values r) + ((values r+2) +
      (fileCost (after values r) + (3*k + (6 + (3*k + (fileCost (after values r) +
        (((values r+1)+2) + fileCost (before values r))))))))) ?_ (le_of_eq ?_)
    · rw [plain_update,marked]
      exact increment_splitB _ _ _ _ _
    · rw [boxW, fileCost_split values r]
      ring
  · decide
/-- The zero decrement box, within the box bound. -/
theorem box_dec0B (values : Fin 9 → V) (r : Fin 9) (L k : V)
    (hk : 0<k) (hv : values r=0) :
    ReachPosB (frameSparse 0 L (marked values r k)) (leftFrame 97 L (plain values k))
      (boxW values k) := by
  apply ReachB.positive
  · refine ReachB.mono (B := fileCost (before values r) + (7 + fileCost (before values r))) ?_ ?_
    · rw [plain_split values r,marked,hv]
      obtain ⟨w,R,hR⟩ := following_block (after values r) k hk
      rw [hR]
      exact decrement_zero_splitB _ _ _ _
    · rw [boxW, fileCost_split values r]
      exact le_of_add_eq (c := 2*(values r+2) + 2*fileCost (after values r) + 6*k) (by ring)
  · decide
/-- The positive decrement box, within the box bound. -/
theorem box_decpB (values : Fin 9 → V) (r : Fin 9) (L k : V)
    (hv : 0<values r) :
    ReachPosB (frameSparse 0 L (marked values r k))
      (leftFrame 40 (2*L+1) (plain (Function.update values r (values r-1)) k)) (boxW values k) := by
  apply ReachB.positive
  · refine ReachB.mono (B := fileCost (before values r) + (4 + fileCost (before values r))) ?_ ?_
    · rw [plain_update,marked]
      have he : values r-1+1=values r := tsub_add_cancel_of_le (pos_iff_one_le.mp hv)
      have h := decrement_positive_splitB (before values r) (after values r) (values r-1) L
        (repeat3 6 k 0)
      simpa only [he] using h
    · rw [boxW, fileCost_split values r]
      exact le_of_add_eq (c := 2*(values r+2) + 2*fileCost (after values r) + 6*k + 3) (by ring)
  · decide

/-- A file of values all at most `M` is traversed within `length*(M+2)` steps. -/
theorem fileCost_le (vs : List V) (M : V) (h : ∀ x ∈ vs, x ≤ M) :
    fileCost vs ≤ (vs.length : V)*(M+2) := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    rw [fileCost_cons, List.length_cons, Nat.cast_succ, add_mul, one_mul, add_comm _ (M+2)]
    exact _root_.add_le_add (_root_.add_le_add (h v (by simp)) le_rfl)
      (ih fun x hx => h x (by simp [hx]))

theorem fileCost_ofFn_le (values : Fin 9 → V) (M : V) (h : ∀ p, values p ≤ M) :
    fileCost (List.ofFn values) ≤ 9*(M+2) := by
  have := fileCost_le (List.ofFn values) M (by
    intro x hx
    obtain ⟨p,rfl⟩ := List.mem_ofFn.mp hx
    exact h p)
  simpa only [List.length_ofFn, Nat.cast_ofNat] using this

end DiophantineConsistency.ArithmeticRuntimeBoundTapeBoxes
