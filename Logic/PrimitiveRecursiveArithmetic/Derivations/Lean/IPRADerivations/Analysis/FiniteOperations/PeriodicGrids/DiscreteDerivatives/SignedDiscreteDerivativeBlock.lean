import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.CubicTaylor.PeriodicThirdDifferenceConstancy

/-!
# Telescoping a coded derivative rate across an actual signed block

The values and the proposed derivative are actual signed PR bodies.
The fine step has physical width 1/D. An error at most E for
D times each adjacent difference minus the derivative observation
gives error at most M*E for the original length-M block.
-/

set_option autoImplicit false
set_option maxHeartbeats 1350000

namespace LeanProofs.IPRA.Analysis.SignedDiscreteDerivativeBlock

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open SignedGridStepBounds (difference difference_value read_index)
open PeriodicThirdDifferenceConstancy (band band_add band_congr subst_band)
open PolynomialBisection (zle_congr zle_refl)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sliceBody (b : PTm 2) : PTm 2 := inst2 b (fstT (var 1)+var 0) (sndT (var 1))

def slice (b : ZB) : ZB := ⟨sliceBody b.pos,sliceBody b.neg⟩

def block (b : ZB) (x i M : PTm n) : ZT n := (slice b).sum M (pairT i x)

@[simp] theorem subst_block {m : ℕ} (σ : Fin n → PTm m) (b : ZB) (x i M : PTm n) :
    (block b x i M).subst σ = block b (Syn.subst σ x) (Syn.subst σ i) (Syn.subst σ M) := by
  simp [block,ZB.sum,ZT.subst]

private theorem component_at (b : PTm 2) (x i k : PTm n) :
    Γ ⊢[PRAAx] inst2 (sliceBody b) k (pairT i x) ≐ inst2 b (i+k) x := by
  have e : inst2 (sliceBody b) k (pairT i x) =
      inst2 b (fstT (pairT i x)+k) (sndT (pairT i x)) := by
    change Syn.subst ![k,pairT i x] (sliceBody b) = _
    rw [sliceBody,subst_inst2]
    simp
  rw [e]
  exact congrInst2 b (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)

theorem slice_at (b : ZB) (x i k : PTm n) :
    ZT.toZ Γ ((slice b).val k (pairT i x)) = ZT.toZ Γ (b.val (i+k) x) := by
  simp only [ZB.toZ_val,slice]
  rw [natEq (component_at b.pos x i k),natEq (component_at b.neg x i k)]

theorem block_zero (b : ZB) (x i : PTm n) : ZT.toZ Γ (block b x i zero) = 0 :=
  ZB.toZ_sum_zero _ _

theorem block_succ (b : ZB) (x i M : PTm n) :
    ZT.toZ Γ (block b x i (succ M)) = ZT.toZ Γ (block b x i M)+ZT.toZ Γ (b.val (i+M) x) := by
  rw [block, ZB.toZ_sum_succ, slice_at]
  rfl

def stepError (b g : ZB) (x D i : PTm n) : ZT n :=
  ZT.ofNat D*(difference b).val i x-g.val i x

def source (b g : ZB) (x L D E : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift L) ⟶ band (stepError b g (Syn.shift x) (Syn.shift D) (var 0)) (Syn.shift E))

@[simp] theorem subst_stepError {m : ℕ} (σ : Fin n → PTm m) (b g : ZB) (x D i : PTm n) :
    (stepError b g x D i).subst σ = stepError b g (Syn.subst σ x) (Syn.subst σ D) (Syn.subst σ i) := by
  simp [stepError]

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (b g : ZB) (x L D E : PTm n) :
    (source b g x L D E).subst σ =
      source b g (Syn.subst σ x) (Syn.subst σ L) (Syn.subst σ D) (Syn.subst σ E) := by
  simp [source,Syn.subst_shift,Syn.shift_subst]

theorem step_at (b g : ZB) (x L D E i : PTm n)
    (h : Γ ⊢[PRAAx] source b g x L D E) (hi : Γ ⊢[PRAAx] lt i L) :
    Γ ⊢[PRAAx] band (stepError b g x D i) E := by
  have read := h.allE i
  have edge : Γ ⊢[PRAAx] lt i L ⟶ band (stepError b g x D i) E := by
    simpa only [source,Fm.subst_imp,subst_lt,subst_band,subst_stepError,Syn.subst_var,Syn.inst_zero,
      Syn.subst_inst_shift] using read
  exact .impE edge hi

def residual (b g : ZB) (x i D M : PTm n) : ZT n :=
  ZT.ofNat D*(b.val (i+M) x-b.val i x)-block g x i M

@[simp] theorem subst_residual {m : ℕ} (σ : Fin n → PTm m) (b g : ZB) (x i D M : PTm n) :
    (residual b g x i D M).subst σ =
      residual b g (Syn.subst σ x) (Syn.subst σ i) (Syn.subst σ D) (Syn.subst σ M) := by
  simp [residual]

theorem residual_succ (b g : ZB) (x i D M : PTm n) :
    ZT.toZ Γ (residual b g x i D (succ M)) =
      ZT.toZ Γ (residual b g x i D M)+ZT.toZ Γ (stepError b g x D (i+M)) := by
  simp only [residual,stepError,ZT.toZ_sub,ZT.toZ_mul,block_succ,difference_value,
    read_index b x (add_succ i M)]
  ring

private def law (b g : ZB) (x L i D E M : PTm n) : Fm PTm n :=
  le (i+M) L ⟶ band (residual b g x i D M) (M*E)

@[simp] private theorem subst_law {m : ℕ} (σ : Fin n → PTm m) (b g : ZB) (x L i D E M : PTm n) :
    (law b g x L i D E M).subst σ = law b g (Syn.subst σ x) (Syn.subst σ L)
      (Syn.subst σ i) (Syn.subst σ D) (Syn.subst σ E) (Syn.subst σ M) := by simp [law]

private theorem law_zero (b g : ZB) (x L i D E : PTm n) :
    Γ ⊢[PRAAx] law b g x L i D E zero := by
  refine .impI ?_
  let Δ := le (i+zero) L :: Γ
  have eq : ZT.toZ Δ (ZT.ofNat zero) = ZT.toZ Δ (residual b g x i D zero) := by
    simp only [residual,ZT.toZ_sub,ZT.toZ_mul,read_index b x (add_zero i),block_zero]
    simp only [ZT.toZ_ofNat,Q.mk_zero,map_zero]
    ring
  exact .andI (zle_congr (by simp) eq (zle_refl (ZT.ofNat zero)))
    (zle_congr eq (by simp) (zle_refl (ZT.ofNat zero)))

private theorem law_succ (b g : ZB) (x L i D E M : PTm n)
    (h : Γ ⊢[PRAAx] source b g x L D E) (ih : Γ ⊢[PRAAx] law b g x L i D E M) :
    Γ ⊢[PRAAx] law b g x L i D E (succ M) := by
  refine .impI ?_
  have step : (le (i+succ M) L :: Γ) ⊢[PRAAx] lt (i+M) L :=
    le_congr (add_succ i M) (.eqRefl _) Prf.hyp0
  have old := Prf.impE ih.wk (le_of_lt step)
  have edge := step_at b g x L D E (i+M) h.wk step
  exact band_congr (by rw [ZT.toZ_add,residual_succ]) (by ipra_ring) (band_add old edge)

theorem residual_bound (b g : ZB) (x L i D E M : PTm n)
    (h : Γ ⊢[PRAAx] source b g x L D E) (hm : Γ ⊢[PRAAx] le (i+M) L) :
    Γ ⊢[PRAAx] band (residual b g x i D M) (M*E) := by
  let sh (z : PTm n) := Syn.shift z
  have h' : Γ.map Fm.shift ⊢[PRAAx] source b g (sh x) (sh L) (sh D) (sh E) := by
    simpa only [sh,Fm.shift,Syn.shift,subst_source] using h.shift
  have universal : Γ ⊢[PRAAx] .all (law b g (sh x) (sh L) (sh i) (sh D) (sh E) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, ⟨le_QF _ _,le_QF _ _⟩⟩ ?_ ?_
    · simpa only [subst_law,sh,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        law_zero (Γ := Γ) b g x L i D E
    · simp only [subst_law,sh,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact law_succ b g _ _ _ _ _ _ h'.wk Prf.hyp0
  have atM : Γ ⊢[PRAAx] law b g x L i D E M := by
    simpa only [subst_law,sh,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using universal.allE M
  exact .impE atM hm

theorem actual_signed_discrete_derivative_block_closed (b g : ZB) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let x := var 0
       let L := var 1
       let i := var 2
       let D := var 3
       let E := var 4
       let M := var 5
       source b g x L D E ⟶ le (i+M) L ⟶ band (residual b g x i D M) (M*E)) :=
  closeUniv 6 (.impI (.impI (residual_bound b g _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.SignedDiscreteDerivativeBlock
