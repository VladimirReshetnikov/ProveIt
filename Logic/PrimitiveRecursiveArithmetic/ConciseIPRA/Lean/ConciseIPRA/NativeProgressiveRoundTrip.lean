import ConciseIPRA.NativeTargetClosure

/-!
# The second formula round trip for the uniform calculus

`NativeProgressive` reads a formula of the uniform calculus `RPrf` as a
formula of the kernel (`NFm.rd`), and `NativeProgressiveEmbedding` translates
a formula of the kernel into `RPrf` (`NFm.emb`).  The kernel proves
`rd (emb A)` equivalent to `A` (`NEquiv.rd_emb`).  This module proves the
other composite:

  `REquivIn.emb_rd`: in `RPrf`, over every context, a formula `B` is
  interderivable with `emb (rd B)`.

Hence the progressive reading is faithful:

  `rprf_iff_rd : RPrf Γ A ↔ NPrf (Γ.map NFm.rd) A.rd`,

and with `tqprf_iff_rprf` the same holds for the target-directed calculus.
Together with `rprf_emb_iff` the two translations and the two round trips
make the uniform calculus and the kernel bi-interpretable, on all formulas
and over arbitrary contexts.

The proof is by induction on `B`.  At a compound matrix both calculi read the
binder alike, and the congruence rules of `NativeProgressiveLeibniz` apply.
At a literal equation `E` the binder `Q_y E` is progressivity, and
`rd (Q_y E)` is the kernel formula `∀ y, (E(y) → E(S y))`, built from the
connectives of `NativeLogic`.  No rule for those connectives is re-proved in
`RPrf`.  Instead:

* from `emb (∀ y, (E(y) → E(S y)))` and `E(z)` the step `E(S z)` is the
  translation of a three-line kernel derivation (`RPrf.progBack`);
* conversely, one step of progress at a term `a`, "`s(a) = t(a)` gives
  `s(S a) = t(S a)`", is itself a closure over an equation,
  `Q_w (sel(w, s(a), s(S a)) = sel(w, t(a), t(S a)))`; `RPrf` derives the
  translation of that formula at `0` and of its closure in `a`
  (`RPrf.stepQ`), and the kernel derives progressivity from the two
  (`RPrf.progForth`).

The binder `D` at an equation reduces to these by one opening and one
introduction on each side.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m k : ℕ}

namespace NFm

theorem emb_of_isEq {A : NFm n} (h : A.isEq = true) : emb A = A := by
  cases A with
  | eq s t => rfl
  | Q B => cases h
  | D B => cases h

theorem rd_of_isEq {A : NFm n} (h : A.isEq = true) : rd A = A := by
  cases A with
  | eq s t => rfl
  | Q B => cases h
  | D B => cases h

theorem rd_Q_ne {B : NFm (n + 1)} (h : B.isEq = false) : rd (.Q B) = .Q (rd B) := by
  show (if B.isEq then prog (rd B) else NFm.Q (rd B)) = _
  simp [h]

theorem rd_Q_eq {B : NFm (n + 1)} (h : B.isEq = true) : rd (.Q B) = prog B := by
  show (if B.isEq then prog (rd B) else NFm.Q (rd B)) = _
  simp [h, rd_of_isEq h]

theorem rd_D_ne {B : NFm (n + 2)} (h : B.isEq = false) : rd (.D B) = .D (rd B) := by
  show (if B.isEq then ex (prog (rd B)) else NFm.D (rd B)) = _
  simp [h]

theorem rd_D_eq {B : NFm (n + 2)} (h : B.isEq = true) : rd (.D B) = ex (prog B) := by
  show (if B.isEq then ex (prog (rd B)) else NFm.D (rd B)) = _
  simp [h, rd_of_isEq h]

/-- The matrix of the conditional `a = b → a' = b'`: at `0` it is `a = b`, and
at a successor it is `a' = b'`. -/
def stepM (a a' b b' : Tm n) : NFm (n + 1) :=
  .eq (Tm.sel (Syn.var 0) (Syn.shift a) (Syn.shift a'))
    (Tm.sel (Syn.var 0) (Syn.shift b) (Syn.shift b'))

theorem stepM_inst (a a' b b' c : Tm n) :
    (stepM a a' b b').subst (inst c) = .eq (Tm.sel c a a') (Tm.sel c b b') := by
  simp [stepM]

theorem stepM_repl (a a' b b' : Tm n) (c : Tm (n + 1)) :
    (stepM a a' b b').subst (repl c)
      = .eq (Tm.sel c (Syn.shift a) (Syn.shift a')) (Tm.sel c (Syn.shift b) (Syn.shift b')) := by
  simp [stepM, Syn.subst_repl_shift]

theorem map_shift_subst_inst (Γ : List (NFm n)) (t : Tm n) :
    (Γ.map NFm.shift).map (fun A => A.subst (inst t)) = Γ := by
  rw [List.map_map]
  exact (List.map_congr_left fun A _ => NFm.subst_inst_shift A t).trans (List.map_id _)

end NFm

namespace RPrf

variable {Γ : List (NFm n)}

/-- One step of progress at an equation. -/
theorem oneStep {B : NFm (n + 1)} (hB : B.isEq = true) (t : Tm n) (h₁ : RPrf Γ (.Q B))
    (h₂ : RPrf Γ (B.subst (inst t))) : RPrf Γ (B.subst (inst (succ t))) := by
  have q := RPrf.qE t (succ zero) h₁ (by rw [NFm.eta_of_eq hB]; exact h₂)
  rw [NFm.eta_of_eq hB] at q
  exact RPrf.trF B hB (RPrf.addOne t) q

/-- Redex removal for an arbitrary matrix. -/
theorem red0 {p : ℕ} (C : NFm (p + 1)) {Δ : List (NFm (p + 1))} (c : Tm (p + 1))
    (h : RPrf Δ (C.subst (repl (Tm.add c zero)))) : RPrf Δ (C.subst (repl c)) := by
  have k := REquivIn.red (C := C) (fun σ σ' he => RPrf.leibnizIn C σ σ' he) Syn.var c
    (by rw [Syn.up_var, NFm.subst_id]; exact h)
  rwa [Syn.up_var, NFm.subst_id] at k

/-- A derivation of `a' = b'` from `a = b` gives the translation of the
closure that expresses that step. -/
theorem stepQ {a a' b b' : Tm n} (h : RPrf (.eq a b :: Γ) (.eq a' b')) :
    RPrf Γ (.Q (NFm.pad (NFm.stepM a a' b b'))) := by
  refine RPrf.qIC _ (NFm.pad_isEq _) ?_
  rw [NFm.shift_subst_inst_zero, NFm.pad_subst, NFm.pad_subst]
  refine RPrf.padI ?_
  rw [NFm.stepM_repl, NFm.stepM_repl]
  have hab : RPrf (NFm.pad (.eq (Tm.sel zero (Syn.shift a) (Syn.shift a'))
        (Tm.sel zero (Syn.shift b) (Syn.shift b'))) :: Γ.map NFm.shift)
      (.eq (Syn.shift a) (Syn.shift b)) :=
    eqTrans (eqSymm (selZero _ _)) (eqTrans (RPrf.padE hyp0) (selZero _ _))
  exact eqTrans (selSucc (Syn.var 0) (Syn.shift a) (Syn.shift a'))
    (eqTrans (RPrf.cut1 hab
        (h.shift.weaken (List.cons_subset_cons _ (List.subset_cons_self _ _))))
      (eqSymm (selSucc (Syn.var 0) (Syn.shift b) (Syn.shift b'))))

/-- From the translation of `∀ y, (E(y) → E(S y))` the uniform calculus derives
the progressive `Q_y E`. -/
theorem progBack (E : NFm (n + 1)) (hE : E.isEq = true) :
    RPrf (NFm.emb (NFm.prog E) :: Γ) (.Q E) := by
  refine RPrf.qIE E hE ?_
  have nd : NPrf [E, (NFm.prog E).shift] (E.subst (repl (succ (Syn.var 0)))) := by
    have hp : NPrf [E, (NFm.prog E).shift] (NFm.prog (E.subst (up fun i => Syn.var i.succ))) := by
      rw [← NFm.prog_subst]
      exact .hyp (List.mem_cons_of_mem _ List.mem_cons_self)
    have ha := NPrf.allE (Syn.var 0) hp
    rw [NFm.imp_subst, NFm.subst_repl_inst, NFm.subst_up_inst_var] at ha
    simp only [Tm.subst_succ, Syn.subst_var, Syn.inst_zero] at ha
    rw [NFm.subst_dummy_up_inst] at ha
    exact NPrf.impE ha NPrf.hyp0
  have k := NPrf.toR nd
  simp only [List.map_cons, List.map_nil, NFm.emb_shift, NFm.emb_subst,
    NFm.emb_of_isEq hE] at k
  refine k.weaken fun C hC => ?_
  rcases List.mem_cons.1 hC with rfl | hC
  · exact List.mem_cons_self
  · rw [List.mem_singleton] at hC
    subst hC
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem List.mem_cons_self)

/-- From the progressive `Q_y E` the uniform calculus derives the translation
of `∀ y, (E(y) → E(S y))`. -/
theorem progForth (s t : Tm (n + 1)) :
    RPrf (.Q (.eq s t) :: Γ) (NFm.emb (NFm.prog (.eq s t))) := by
  obtain ⟨sp, hsp⟩ : ∃ sp, sp = Syn.subst (repl (succ (Syn.var 0))) s := ⟨_, rfl⟩
  obtain ⟨tp, htp⟩ : ∃ tp, tp = Syn.subst (repl (succ (Syn.var 0))) t := ⟨_, rfl⟩
  -- the step at the variable `y`, as a closure over an equation
  have gen : ∀ {Δ : List (NFm n)},
      RPrf ((NFm.Q (.eq s t)).shift :: Δ.map NFm.shift)
        (.Q (NFm.pad (NFm.stepM s sp t tp))) := by
    intro Δ
    refine RPrf.stepQ ?_
    have q := RPrf.oneStep (B := (NFm.eq s t).subst (up fun i => Syn.var i.succ)) rfl
      (Syn.var 0)
      (Γ := NFm.eq s t :: (NFm.Q (.eq s t)).shift :: Δ.map NFm.shift)
      (.hyp (List.mem_cons_of_mem _ List.mem_cons_self))
      (by rw [NFm.subst_up_inst_var]; exact hyp0)
    rw [NFm.subst_dummy_up_inst] at q
    rw [hsp, htp]
    exact q
  have r0 : RPrf (.Q (.eq s t) :: Γ)
      (NFm.emb ((NFm.Q (NFm.stepM s sp t tp)).subst (inst zero))) := by
    have g := (gen (Δ := Γ)).subst (inst zero)
    rw [List.map_cons, NFm.subst_inst_shift, NFm.map_shift_subst_inst] at g
    rw [NFm.emb_subst]
    exact g
  have rQ : RPrf (.Q (.eq s t) :: Γ) (NFm.emb (.Q (.Q (NFm.stepM s sp t tp)))) := by
    show RPrf _ (.Q (.Q (NFm.pad (NFm.stepM s sp t tp))))
    refine RPrf.qIC (.Q (NFm.pad (NFm.stepM s sp t tp))) rfl ?_
    have g := (gen (Δ := Γ)).subst (repl (succ (Syn.var 0)))
    rw [List.map_cons, NFm.subst_repl_shift, NFm.map_shift_subst_repl] at g
    exact g.wk
  have nd : NPrf [(NFm.Q (NFm.stepM s sp t tp)).subst (inst zero),
        NFm.Q (.Q (NFm.stepM s sp t tp))] (NFm.prog (.eq s t)) := by
    refine NPrf.allI (NPrf.impI ?_)
    have hK : NPrf (NFm.eq s t :: [(NFm.Q (NFm.stepM s sp t tp)).subst (inst zero),
          NFm.Q (.Q (NFm.stepM s sp t tp))].map NFm.shift) (.Q (NFm.stepM s sp t tp)) := by
      have q := NPrf.qE
        (B := (NFm.Q (NFm.stepM s sp t tp)).subst (up fun i => Syn.var i.succ)) (Syn.var 0)
        (Γ := NFm.eq s t :: [(NFm.Q (NFm.stepM s sp t tp)).subst (inst zero),
          NFm.Q (.Q (NFm.stepM s sp t tp))].map NFm.shift)
        (.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
        (by
          rw [NFm.subst_dummy_up_inst, ← NFm.shift_subst_inst_zero]
          exact .hyp (List.mem_cons_of_mem _ List.mem_cons_self))
      rwa [NFm.subst_up_inst_var] at q
    have q := NPrf.qE (succ zero) hK (by
      rw [NFm.stepM_inst]
      exact NPrf.eqTrans (NPrf.selZero s sp)
        (NPrf.eqTrans NPrf.hyp0 (NPrf.eqSymm (NPrf.selZero t tp))))
    rw [NFm.stepM_inst] at q
    have q' := NPrf.eqTrans (NPrf.eqSymm (NPrf.selSucc zero s sp))
      (NPrf.eqTrans q (NPrf.selSucc zero t tp))
    show NPrf _ (.eq (Syn.subst (repl (succ (Syn.var 0))) s)
      (Syn.subst (repl (succ (Syn.var 0))) t))
    rw [← hsp, ← htp]
    exact q'
  refine (NPrf.toR nd).cut fun C hC => ?_
  have hC' : C ∈ [NFm.emb ((NFm.Q (NFm.stepM s sp t tp)).subst (inst zero)),
      NFm.emb (.Q (.Q (NFm.stepM s sp t tp)))] := hC
  rcases List.mem_cons.1 hC' with rfl | h2
  · exact r0
  · rw [List.mem_singleton] at h2
    subst h2
    exact rQ

/-- From `D_{x,y} E` at an equation the uniform calculus derives the
translation of `∃ x ∀ y, (E(x, y) → E(x, S y))`. -/
theorem exProgForth (s t : Tm (n + 2)) :
    RPrf (.D (.eq s t) :: Γ) (NFm.emb (NFm.ex (NFm.prog (.eq s t)))) := by
  refine .dE hyp0 ?_
  have h1 : RPrf (.Q (.eq s t) :: (NFm.D (.eq s t) :: Γ).map NFm.shift)
      (NFm.emb (NFm.prog (.eq s t))) := progForth s t
  have nd : NPrf [NFm.prog (.eq s t)] (NFm.ex (NFm.prog (.eq s t))).shift := by
    show NPrf _ ((NFm.ex (NFm.prog (.eq s t))).subst fun i => Syn.var i.succ)
    rw [NFm.ex_subst]
    exact NPrf.exI (Syn.var 0) (by rw [NFm.subst_up_inst_var]; exact NPrf.hyp0)
  have k := NPrf.toR nd
  rw [NFm.emb_shift] at k
  exact RPrf.cut1 h1 (k.weaken (List.cons_subset_cons _ (List.nil_subset _)))

/-- From the translation of `∃ x ∀ y, (E(x, y) → E(x, S y))` the uniform
calculus derives `D_{x,y} E`. -/
theorem exProgBack (E : NFm (n + 2)) (hE : E.isEq = true) :
    RPrf (NFm.emb (NFm.ex (NFm.prog E)) :: Γ) (.D E) := by
  refine .dE (B := NFm.pad (NFm.emb (NFm.gate (Syn.var 0) (NFm.prog E).shift))) hyp0 ?_
  have nd : NPrf [NFm.Q (NFm.gate (Syn.var 0) (NFm.prog E).shift)] (NFm.prog E) :=
    (NEquiv.qGate (NFm.prog E)).mp NPrf.hyp0
  have hP : RPrf (.Q (NFm.pad (NFm.emb (NFm.gate (Syn.var 0) (NFm.prog E).shift)))
        :: (NFm.emb (NFm.ex (NFm.prog E)) :: Γ).map NFm.shift) (NFm.emb (NFm.prog E)) :=
    (NPrf.toR nd).weaken (List.cons_subset_cons _ (List.nil_subset _))
  have hQ := RPrf.cut1 hP (progBack E hE)
  refine RPrf.cut1 hQ ?_
  show RPrf _ (.D (E.subst (up (up fun i => Syn.var i.succ))))
  refine .dI _ (Syn.var 0) ?_
  rw [NFm.subst_upup_inst_var,
    NFm.eta_of_eq (B := E.subst (up (up fun i => Syn.var i.succ)))
      (by rw [NFm.isEq_subst]; exact hE), NFm.subst_repl_var]
  exact REquivIn.qStepE hE ⟨hyp0, hyp0⟩ (List.Subset.refl _)

end RPrf

namespace REquivIn

variable {Γ : List (NFm n)} {A B C : NFm n}

theorem refl (A : NFm n) : REquivIn Γ A A := ⟨RPrf.hyp0, RPrf.hyp0⟩

theorem trans (e₁ : REquivIn Γ A B) (e₂ : REquivIn Γ B C) : REquivIn Γ A C :=
  ⟨e₂.mp (List.subset_cons_self _ _) e₁.1, e₁.mpr (List.subset_cons_self _ _) e₂.2⟩

/-- A formula and its padding are interderivable. -/
theorem pad (A : NFm n) : REquivIn Γ A A.pad := ⟨RPrf.padI RPrf.hyp0, RPrf.padE RPrf.hyp0⟩

/-- **The second round trip.**  In the uniform calculus, over every context, a
formula is interderivable with the translation of its progressive reading. -/
theorem emb_rd (B : NFm k) : ∀ {Γ : List (NFm k)}, REquivIn Γ B (NFm.emb (NFm.rd B)) := by
  induction B with intro Γ
  | eq s t => exact refl _
  | Q B ih =>
    cases hB : B.isEq
    · rw [NFm.rd_Q_ne hB]
      exact QC hB (NFm.pad_isEq _) (ih.trans (pad _)) (fun c h => RPrf.red0 _ c h)
        (fun c h => RPrf.red0 _ c h)
    · rw [NFm.rd_Q_eq hB]
      cases B with
      | eq s t => exact ⟨RPrf.progForth s t, RPrf.progBack _ rfl⟩
      | Q B' => cases hB
      | D B' => cases hB
  | D B ih =>
    cases hB : B.isEq
    · rw [NFm.rd_D_ne hB]
      exact ⟨dStepC hB (NFm.pad_isEq _) (ih.trans (pad _)) (fun c h => RPrf.red0 _ c h),
        dStepC (NFm.pad_isEq _) hB (ih.trans (pad _)).symm (fun c h => RPrf.red0 _ c h)⟩
    · rw [NFm.rd_D_eq hB]
      cases B with
      | eq s t => exact ⟨RPrf.exProgForth s t, RPrf.exProgBack _ rfl⟩
      | Q B' => cases hB
      | D B' => cases hB

end REquivIn

variable {Γ : List (NFm n)} {A : NFm n}

/-- **The progressive reading is faithful.**  The uniform calculus derives a
sequent exactly when the kernel derives its progressive reading. -/
theorem rprf_iff_rd : RPrf Γ A ↔ NPrf (Γ.map NFm.rd) A.rd := by
  constructor
  · exact RPrf.toNPrf
  · intro h
    refine (REquivIn.emb_rd A).mpr (List.Subset.refl _) ((NPrf.toR h).cut fun C hC => ?_)
    rw [List.map_map, List.mem_map] at hC
    obtain ⟨X, hX, rfl⟩ := hC
    exact (REquivIn.emb_rd X).mp (List.Subset.refl _) (.hyp hX)

/-- The uniform calculus derives a sequent exactly when iPRA proves its
progressive reading. -/
theorem rprf_iff_pra :
    RPrf Γ A ↔ ((Γ.map fun X => X.rd.toPRA) ⊢[PRAAx] A.rd.toPRA) := by
  have h := native_iff_pra (Γ := Γ.map NFm.rd) (A := A.rd)
  rw [List.map_map] at h
  exact rprf_iff_rd.trans h

/-- The calculus with the target-directed elimination derives a sequent
exactly when the kernel derives its progressive reading. -/
theorem tqprf_iff_rd : TQPrf Γ A ↔ NPrf (Γ.map NFm.rd) A.rd :=
  tqprf_iff_rprf.trans rprf_iff_rd

end LeanProofs.ConciseIPRA
