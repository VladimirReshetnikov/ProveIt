import DiophantineConsistency.ModelEnumeratorCantor
import DiophantineConsistency.ArithmeticCommandStepPerm222

/-! # Internal meaning of the enumerator's formula rows, gate, stack and state

The step program `DirectEnumerator.rawStepProgram` builds the C222 seed
formulas with the constructor programs of `ModelEnumeratorCantor`. This file
identifies, at every input of an arbitrary model `V` of `𝗜𝚺₁`:

* the axiom rows `row1 … row6`, `row8`, `growth`, `request`, `closure` with the
  model-level templates `rho1 … rho8`, `growG`, `req`, `clos` of the BusyBeaver
  arithmetic packages (by unfolding the constructors and the fixed circuits);
* `gated` with `ArithmeticCommandStepPerm222.gateValue` (label collisions give
  `0`, otherwise the helper-free bundle `bundle222`);
* `stack` with `ArithmeticCommandStepPerm222.axStackValue`;
* `state` with the Foundation-paired six-register code `encV`.

Each combinator's code is exposed one level deep by `rfl`; the concrete
program is never evaluated. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelEnumeratorRows
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelScalarPR ScalarPRCode DirectScalar ModelDirectScalar ModelEnumeratorCantor
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor SetTheory.BusyBeaver.ZFC.ArithmeticCode254
  SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254 SetTheory.BusyBeaver.ZFC.ArithmeticTemplates222
  SetTheory.BusyBeaver.ZFC.ArithmeticSeedTemplates222
open ArithmeticCommandStepPerm222

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The program's six-register state code: nested Foundation pairs. -/
def encV (pl np tw ws d h : V) : V := mpair pl (mpair np (mpair tw (mpair ws (mpair d h))))

/-! ### Axiom rows and seed templates -/

section Rows
variable {a b c u : ℕ → ℕ} (ha : R a) (hb : R b) (hc : R c) (hu : R u) (x : V)

theorem evalV_row1 :
    evalV (DirectEnumerator.row1 ha hb).val x = rho1 (evalV ha.val x) (evalV hb.val x) := by
  simp only [DirectEnumerator.row1, evalV_existential, evalV_equality]
  rfl

theorem evalV_row2 : evalV (DirectEnumerator.row2 ha hb hc).val x =
    rho2 (evalV ha.val x) (evalV hb.val x) (evalV hc.val x) := by
  simp only [DirectEnumerator.row2, evalV_implication, evalV_universal]
  rfl

theorem evalV_row3 : evalV (DirectEnumerator.row3 ha hb hc).val x =
    rho3 (evalV ha.val x) (evalV hb.val x) (evalV hc.val x) := by
  simp only [DirectEnumerator.row3, evalV_implication, evalV_equality, evalV_membership]
  rfl

theorem evalV_row4 : evalV (DirectEnumerator.row4 ha hb hc).val x =
    rho4 (evalV ha.val x) (evalV hb.val x) (evalV hc.val x) := by
  simp only [DirectEnumerator.row4, evalV_implication, evalV_universal]
  rfl

theorem evalV_row5 : evalV (DirectEnumerator.row5 ha hb hc).val x =
    rho5 (evalV ha.val x) (evalV hb.val x) (evalV hc.val x) := by
  simp only [DirectEnumerator.row5, evalV_implication, evalV_equality, evalV_membership]
  rfl

theorem evalV_row6 :
    evalV (DirectEnumerator.row6 ha hb).val x = rho6 (evalV ha.val x) (evalV hb.val x) := by
  simp only [DirectEnumerator.row6, evalV_implication, evalV_existential, evalV_universal]
  rfl

theorem evalV_growth : evalV (DirectEnumerator.growth ha hb hc).val x =
    growG (evalV ha.val x) (evalV hb.val x) (evalV hc.val x) := by
  simp only [DirectEnumerator.growth, evalV_implication, evalV_equality, evalV_universal,
    evalV_membership]
  rfl

theorem evalV_row8 : evalV (DirectEnumerator.row8 ha hb hc hu).val x =
    rho8 (evalV ha.val x) (evalV hb.val x) (evalV hc.val x) (evalV hu.val x) := by
  simp only [DirectEnumerator.row8, evalV_implication]
  rfl

theorem evalV_request : evalV (DirectEnumerator.request ha hb hc).val x =
    req (evalV ha.val x) (evalV hb.val x) (evalV hc.val x) := by
  simp only [DirectEnumerator.request, evalV_universal, evalV_implication, evalV_negation,
    evalV_membership]
  rfl

theorem evalV_closure : evalV (DirectEnumerator.closure ha hb hc hu).val x =
    clos (evalV ha.val x) (evalV hb.val x) (evalV hc.val x) (evalV hu.val x) := by
  simp only [DirectEnumerator.closure, evalV_universal, evalV_implication, evalV_negation,
    evalV_membership, evalV_request]
  rfl

end Rows

/-! ### The gate -/

section Gate
variable {a b c : ℕ → ℕ}

theorem gatedBody_val (ha : R a) (hb : R b) (hc : R c) :
    (DirectEnumerator.gatedBody ha hb hc).val =
      (ifEq hc ha Realizes.zero (ifEq hc hb Realizes.zero
        (DirectEnumerator.negation (DirectEnumerator.implication
          (DirectEnumerator.implication (DirectEnumerator.membership ha hb)
            (DirectEnumerator.universal hc (DirectEnumerator.membership ha hb)))
          (DirectEnumerator.universal hc (DirectEnumerator.implication
            (DirectEnumerator.closure ha hb hc hc)
            (DirectEnumerator.negation (DirectEnumerator.request hb hc hc)))))))).val := rfl

theorem gated_val (ha : R a) (hb : R b) (hc : R c) :
    (DirectEnumerator.gated ha hb hc).val =
      .comp (DirectEnumerator.gatedBody Realizes.left (Realizes.left.comp Realizes.right)
        (Realizes.right.comp Realizes.right)).val (ha.pair (hb.pair hc)).val := rfl

theorem evalV_gatedBody (ha : R a) (hb : R b) (hc : R c) (x : V) :
    evalV (DirectEnumerator.gatedBody ha hb hc).val x =
      gateValue (evalV ha.val x) (evalV hb.val x) (evalV hc.val x) := by
  rw [gatedBody_val, evalV_ifEq, gateValue]
  by_cases hca : evalV hc.val x = evalV ha.val x
  · rw [if_pos hca, if_pos (Or.inl hca), evalV_zeroR]
  · rw [if_neg hca, evalV_ifEq]
    by_cases hcb : evalV hc.val x = evalV hb.val x
    · rw [if_pos hcb, if_pos (Or.inr hcb), evalV_zeroR]
    · rw [if_neg hcb, if_neg (not_or.mpr ⟨hca, hcb⟩)]
      simp only [evalV_negation, evalV_implication, evalV_membership, evalV_universal,
        evalV_closure, evalV_request]
      rw [bundle222_eq, vrel_eq, nks_eq]

theorem evalV_gated (ha : R a) (hb : R b) (hc : R c) (x : V) :
    evalV (DirectEnumerator.gated ha hb hc).val x =
      gateValue (evalV ha.val x) (evalV hb.val x) (evalV hc.val x) := by
  rw [gated_val, evalV_comp, evalV_gatedBody]
  simp only [evalV_pairR, evalV_leftR, evalV_rightR, evalV_compR, munpair₁_mpair, munpair₂_mpair]

end Gate

/-! ### The axiom stack -/

section Stack
variable {a h b c u t w : ℕ → ℕ}

theorem evalV_stackBody (ha : R a) (hh : R h) (hb : R b) (hc : R c) (hu : R u) (ht : R t)
    (hw : R w) (x : V) :
    evalV (DirectEnumerator.stackBody ha hh hb hc hu ht hw).val x =
      axStackValue (evalV ha.val x) (evalV hh.val x) (evalV hb.val x) (evalV hc.val x)
        (evalV hu.val x) (evalV ht.val x) (evalV hw.val x) := by
  simp only [DirectEnumerator.stackBody, evalV_cantorPair, evalV_row1, evalV_row2, evalV_row3,
    evalV_row4, evalV_row5, evalV_row6, evalV_growth, evalV_row8, evalV_universal]
  rfl

theorem stack_val (ha : R a) (hh : R h) (hb : R b) (hc : R c) (hu : R u) (ht : R t)
    (hw : R w) :
    (DirectEnumerator.stack ha hh hb hc hu ht hw).val =
      .comp (DirectEnumerator.stackBody Realizes.left (Realizes.left.comp Realizes.right)
        (Realizes.left.comp (Realizes.right.comp Realizes.right))
        (Realizes.left.comp (Realizes.right.comp (Realizes.right.comp Realizes.right)))
        (Realizes.left.comp (Realizes.right.comp (Realizes.right.comp
          (Realizes.right.comp Realizes.right))))
        (Realizes.left.comp (Realizes.right.comp (Realizes.right.comp (Realizes.right.comp
          (Realizes.right.comp Realizes.right)))))
        (Realizes.right.comp (Realizes.right.comp (Realizes.right.comp (Realizes.right.comp
          (Realizes.right.comp Realizes.right)))))).val
        (ha.pair (hh.pair (hb.pair (hc.pair (hu.pair (ht.pair hw)))))).val := rfl

theorem evalV_stack (ha : R a) (hh : R h) (hb : R b) (hc : R c) (hu : R u) (ht : R t)
    (hw : R w) (x : V) :
    evalV (DirectEnumerator.stack ha hh hb hc hu ht hw).val x =
      axStackValue (evalV ha.val x) (evalV hh.val x) (evalV hb.val x) (evalV hc.val x)
        (evalV hu.val x) (evalV ht.val x) (evalV hw.val x) := by
  rw [stack_val, evalV_comp, evalV_stackBody]
  simp only [evalV_pairR, evalV_leftR, evalV_rightR, evalV_compR, munpair₁_mpair, munpair₂_mpair]

end Stack

/-! ### States -/

theorem evalV_state {a b c d e f : ℕ → ℕ} (ha : R a) (hb : R b) (hc : R c) (hd : R d)
    (he : R e) (hf : R f) (x : V) :
    evalV (DirectEnumerator.state ha hb hc hd he hf).val x =
      encV (evalV ha.val x) (evalV hb.val x) (evalV hc.val x) (evalV hd.val x)
        (evalV he.val x) (evalV hf.val x) := by
  simp only [DirectEnumerator.state, evalV_pairR, encV]

theorem pl_val : DirectEnumerator.pl.val = .left := rfl
theorem np_val : DirectEnumerator.np.val = .comp .left .right := rfl
theorem tw_val : DirectEnumerator.tw.val = .comp .left (.comp .right .right) := rfl
theorem ws_val : DirectEnumerator.ws.val = .comp .left (.comp .right (.comp .right .right)) := rfl
theorem depth_val :
    DirectEnumerator.depth.val = .comp .left (.comp .right (.comp .right (.comp .right .right))) :=
  rfl
theorem cache_val :
    DirectEnumerator.cache.val = .comp .right (.comp .right (.comp .right (.comp .right .right))) :=
  rfl

section Registers
variable {n pl np tw ws d h : V} (hn : n = encV pl np tw ws d h)
include hn

theorem reg_pl : evalV DirectEnumerator.pl.val n = pl := by
  rw [hn, pl_val]
  simp only [encV, evalV_comp, evalV_left, evalV_right, munpair₁_mpair, munpair₂_mpair]

theorem reg_np : evalV DirectEnumerator.np.val n = np := by
  rw [hn, np_val]
  simp only [encV, evalV_comp, evalV_left, evalV_right, munpair₁_mpair, munpair₂_mpair]

theorem reg_tw : evalV DirectEnumerator.tw.val n = tw := by
  rw [hn, tw_val]
  simp only [encV, evalV_comp, evalV_left, evalV_right, munpair₁_mpair, munpair₂_mpair]

theorem reg_ws : evalV DirectEnumerator.ws.val n = ws := by
  rw [hn, ws_val]
  simp only [encV, evalV_comp, evalV_left, evalV_right, munpair₁_mpair, munpair₂_mpair]

theorem reg_depth : evalV DirectEnumerator.depth.val n = d := by
  rw [hn, depth_val]
  simp only [encV, evalV_comp, evalV_left, evalV_right, munpair₁_mpair, munpair₂_mpair]

theorem reg_cache : evalV DirectEnumerator.cache.val n = h := by
  rw [hn, cache_val]
  simp only [encV, evalV_comp, evalV_left, evalV_right, munpair₁_mpair, munpair₂_mpair]

end Registers

end DiophantineConsistency.ModelEnumeratorRows
