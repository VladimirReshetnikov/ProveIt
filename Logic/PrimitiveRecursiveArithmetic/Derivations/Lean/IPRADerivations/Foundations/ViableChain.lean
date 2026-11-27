import IPRADerivations.Foundations.BackwardViability

/-!
# The certified finite chain (`ipra_evidence_framework`, "certified finite chain")

Packet: `foundations/ipra_evidence_framework`, theorem "PR backward viability and certified
finite chain", second part: if the start candidate is viable for the whole horizon, a
verified chain of length `h + 1` is produced.

For a finite compatibility instance `I` (`Foundations/BackwardViability`) and a start
candidate `s(p)`, the chain is the primitive recursion

`c(0) = s(p)`, `c(t + 1) = nxt(h ∸ (t + 1), c(t))`

(`chain_zero`, `chain_succ`), where `nxt` is the selected successor (bounded search). The
chain is a term in `t`, so no coded sequence is needed. If `s(p) < B(0, p)` and
`V(h, s(p)) = 1` (the start is viable with `h` levels remaining), then:

* `chain_inv`: for every `t ≤ h`, `c(t) < B(t)` and `V(h ∸ t, c(t)) = 1`;
* `chain_local`: for every `t ≤ h`, `G(t, c(t)) ≠ 0`;
* `chain_edge`: for every `t < h`, `T(t, c(t), c(t + 1)) ≠ 0`.

So `c(0), …, c(h)` is an admissible chain. The induction is on the quantifier-free formula
`t ≤ h → c(t) < B(t) ∧ V(h ∸ t, c(t)) = 1`; each step is `V_unfold`.

Theorem "Constraint refinement under stronger evidence": if every test passed for `I'` is
passed for `I` (`Refines`), the chain certified by `I'` passes the tests of `I`
(`refinement_local`, `refinement_edge`). This does not give viability for `I` in the sense
of its own rows; it transfers the certified chain, as the packet states.

`monus_succ_sub`, `monus_sub`, `succ_monus`: for `t < h`, `h ∸ ((h ∸ (t + 1)) + 1) = t`,
`h ∸ (h ∸ (t + 1)) = t + 1` and `(h ∸ (t + 1)) + 1 = h ∸ t`.
-/

namespace LeanProofs.IPRA.Foundations.ViableChain

open_ipra exports
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Foundations.BackwardViability
open LeanProofs.IPRA.Foundations.BackwardViability.Instance
open LeanProofs.IPRA.Foundations.BoundedReflection (sg_cases one_ne_zero)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## Truncated subtraction below the horizon -/

/-- `(h ∸ (t + 1)) + 1 = h ∸ t` for `t < h`. -/
theorem succ_monus {t h : PTm k} (ht : Γ ⊢[PRAAx] lt t h) :
    Γ ⊢[PRAAx] succ (monus h (succ t)) ≐ monus h t := by
  ipra_lc natEq (eq_add_of_le (le_trans (le_succ_self t) ht)) - natEq (eq_add_of_le ht)

/-- `h ∸ (h ∸ (t + 1)) = t + 1` for `t < h`. -/
theorem monus_sub {t h : PTm k} (ht : Γ ⊢[PRAAx] lt t h) :
    Γ ⊢[PRAAx] monus h (monus h (succ t)) ≐ succ t := by
  have e₁ := natEq (eq_add_of_le ht)
  have hd : Γ ⊢[PRAAx] le (monus h (succ t)) h :=
    le_of_eq_add (d := succ t) (by ipra_lc e₁)
  ipra_lc e₁ - natEq (eq_add_of_le hd)

/-- `h ∸ ((h ∸ (t + 1)) + 1) = t` for `t < h`. -/
theorem monus_succ_sub {t h : PTm k} (ht : Γ ⊢[PRAAx] lt t h) :
    Γ ⊢[PRAAx] monus h (succ (monus h (succ t))) ≐ t := by
  have e₁ := natEq (eq_add_of_le ht)
  have hd : Γ ⊢[PRAAx] le (succ (monus h (succ t))) h :=
    le_of_eq_add (d := t) (by ipra_lc e₁)
  ipra_lc e₁ - natEq (eq_add_of_le hd)

/-! ## Congruence of the instance terms -/

section Congr

variable (I : Instance)

theorem g_congr {i i' a p : PTm k} (h : Γ ⊢[PRAAx] i ≐ i') :
    Γ ⊢[PRAAx] I.g i a p ≐ I.g i' a p :=
  Prf.eqCongr I.G fun l => by
    fin_cases l
    · exact h
    · exact .eqRefl _
    · exact .eqRefl _

theorem t_congr {i i' a b p : PTm k} (h : Γ ⊢[PRAAx] i ≐ i') :
    Γ ⊢[PRAAx] I.t i a b p ≐ I.t i' a b p :=
  Prf.eqCongr I.T fun l => by
    fin_cases l
    · exact h
    · exact .eqRefl _
    · exact .eqRefl _
    · exact .eqRefl _

theorem bd_congr {i i' p : PTm k} (h : Γ ⊢[PRAAx] i ≐ i') :
    Γ ⊢[PRAAx] I.bd i p ≐ I.bd i' p :=
  Prf.eqCongr I.B fun l => by
    fin_cases l
    · exact h
    · exact .eqRefl _

theorem V_congr {j j' a a' p : PTm k} (hj : Γ ⊢[PRAAx] j ≐ j') (ha : Γ ⊢[PRAAx] a ≐ a') :
    Γ ⊢[PRAAx] I.V j a p ≐ I.V j' a' p :=
  congrAp2 remF (congrAp2 quoF (congrAp2 (rec2 I.base I.step) hj (.eqRefl p))
    (congrPw (.eqRefl _) ha)) (.eqRefl _)

end Congr

/-! ## The chain -/

section Chain

variable (I : Instance) (s : PTm 1)

/-- The start candidate `s(p)`. -/
def start (p : PTm k) : PTm k := Syn.subst ![p] s

@[simp] theorem subst_start {m : ℕ} (σ : Fin k → PTm m) (p : PTm k) :
    Syn.subst σ (start s p) = start s (Syn.subst σ p) := by
  simp only [start, Syn.subst_subst]
  congr 1; funext j; fin_cases j; rfl

@[simp] theorem subst_nxt {m : ℕ} (σ : Fin k → PTm m) (j a p : PTm k) :
    Syn.subst σ (I.nxt j a p) = I.nxt (Syn.subst σ j) (Syn.subst σ a) (Syn.subst σ p) := by
  simp [Instance.nxt, Instance.row]

@[simp] theorem subst_V {m : ℕ} (σ : Fin k → PTm m) (j a p : PTm k) :
    Syn.subst σ (I.V j a p) = I.V (Syn.subst σ j) (Syn.subst σ a) (Syn.subst σ p) := by
  simp [Instance.V, Instance.row]

/-- The step of the chain; variables `0 = t`, `1 = c(t)`, `2 = p`. -/
def chainStep : PTm 3 := I.nxt (monus (I.h (var 2)) (succ (var 0))) (var 1) (var 2)

/-- The chain `c(t)`. -/
def chain (t p : PTm k) : PTm k := ap2 (rec2 s (chainStep I)) t p

@[simp] theorem subst_chain {m : ℕ} (σ : Fin k → PTm m) (t p : PTm k) :
    Syn.subst σ (chain I s t p) = chain I s (Syn.subst σ t) (Syn.subst σ p) := by
  simp [chain]

theorem chain_zero (p : PTm k) : Γ ⊢[PRAAx] chain I s zero p ≐ start s p :=
  rec2_zero (Γ := Γ) s (chainStep I) p

theorem chain_succ (t p : PTm k) :
    Γ ⊢[PRAAx] chain I s (succ t) p ≐ I.nxt (monus (I.h p) (succ t)) (chain I s t p) p := by
  have h := rec2_succ (Γ := Γ) s (chainStep I) t p
  have e : Syn.subst ![t, ap2 (rec2 s (chainStep I)) t p, p] (chainStep I) =
      I.nxt (monus (I.h p) (succ t)) (chain I s t p) p := by
    simp only [chainStep, subst_nxt, PTm.subst_monus, Instance.subst_h, Syn.subst_var,
      ConciseIPRA.PTm.subst_succ]
    rfl
  rw [e] at h
  exact h

/-- One step of the chain at time `t < h`: from `c(t) < B(t)` and `V(h ∸ t, c(t)) = 1`, the
local test at `t`, the edge test, and the invariant at `t + 1`. -/
theorem chain_step {t p : PTm k} (ht : Γ ⊢[PRAAx] lt t (I.h p))
    (hb : Γ ⊢[PRAAx] lt (chain I s t p) (I.bd t p))
    (hv : Γ ⊢[PRAAx] I.V (monus (I.h p) t) (chain I s t p) p ≐ one) :
    Γ ⊢[PRAAx] neg (I.g t (chain I s t p) p ≐ zero) ⋏
      (neg (I.t t (chain I s t p) (chain I s (succ t) p) p ≐ zero) ⋏
        (lt (chain I s (succ t) p) (I.bd (succ t) p) ⋏
          (I.V (monus (I.h p) (succ t)) (chain I s (succ t) p) p ≐ one))) := by
  have a₁ := monus_succ_sub ht
  have a₂ := monus_sub ht
  have a₃ := succ_monus ht
  have cs := chain_succ (Γ := Γ) I s t p
  -- the hypotheses of `V_unfold` at `j = h ∸ (t + 1)`
  have hb' : Γ ⊢[PRAAx] lt (chain I s t p)
      (I.bd (monus (I.h p) (succ (monus (I.h p) (succ t)))) p) :=
    lt_congr (.eqRefl _) (bd_congr I a₁.eqSymm) hb
  have hv' : Γ ⊢[PRAAx] I.V (succ (monus (I.h p) (succ t))) (chain I s t p) p ≐ one :=
    (V_congr I a₃ (.eqRefl _)).eqTrans hv
  have u := V_unfold I hb' hv'
  refine .andI ?_ (.andI ?_ (.andI ?_ ?_))
  · exact .impI (.impE (Prf.andE₁ u).wk ((g_congr I a₁.wk).eqTrans Prf.hyp0))
  · refine .impI (.impE (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ u))).wk ?_)
    refine (t_congr I a₁.wk).eqTrans (.eqTrans ?_ Prf.hyp0)
    exact Prf.eqCongr I.T fun l => by
      fin_cases l
      · exact .eqRefl _
      · exact .eqRefl _
      · exact cs.wk.eqSymm
      · exact .eqRefl _
  · exact lt_congr cs.eqSymm (bd_congr I a₂) (Prf.andE₁ (Prf.andE₂ u))
  · exact (V_congr I (.eqRefl _) cs).eqTrans (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ u)))

/-- Variables: `0 = t`, `1 = p`. -/
private def invF (I : Instance) (s : PTm 1) : Fm PTm 2 :=
  (lt (start s (var 1)) (I.bd zero (var 1)) ⋏ (I.V (I.h (var 1)) (start s (var 1)) (var 1) ≐ one)) ⟶
    le (var 0) (I.h (var 1)) ⟶
      (lt (chain I s (var 0) (var 1)) (I.bd (var 0) (var 1)) ⋏
        (I.V (monus (I.h (var 1)) (var 0)) (chain I s (var 0) (var 1)) (var 1) ≐ one))

private theorem inv₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] invF I s := by
  ipra_ind (⟨⟨trivial, trivial⟩, trivial, trivial, trivial⟩) [invF, subst_lt, subst_le, subst_start, subst_V,
      subst_chain, Instance.subst_bd, Instance.subst_h]
  · refine .impI (.impI ?_)
    exact .andI (lt_congr (chain_zero I s _).eqSymm (.eqRefl _) (.andE₁ Prf.hyp1))
      ((V_congr I (monus_zero _) (chain_zero I s _)).eqTrans (.andE₂ Prf.hyp1))
  · have ih : [invF I s] ⊢[PRAAx]
        (lt (start s (var 1)) (I.bd zero (var 1)) ⋏
          (I.V (I.h (var 1)) (start s (var 1)) (var 1) ≐ one)) ⟶
        le (var 0) (I.h (var 1)) ⟶
          (lt (chain I s (var 0) (var 1)) (I.bd (var 0) (var 1)) ⋏
            (I.V (monus (I.h (var 1)) (var 0)) (chain I s (var 0) (var 1)) (var 1) ≐ one)) :=
      Prf.hyp0
    refine .impI (.impI ?_)
    -- `t + 1 ≤ h`, hence `t ≤ h` and `t < h`
    have r := Prf.impE (Prf.impE ih.wk.wk Prf.hyp1) (le_trans (le_succ_self _) Prf.hyp0)
    exact Prf.andE₂ (Prf.andE₂ (chain_step I s Prf.hyp0 (Prf.andE₁ r) (Prf.andE₂ r)))

variable {I s}

/-- The invariant of the chain: for `t ≤ h`, `c(t) < B(t)` and `V(h ∸ t, c(t)) = 1`. -/
theorem chain_inv {t p : PTm k} (hs : Γ ⊢[PRAAx] lt (start s p) (I.bd zero p))
    (hv : Γ ⊢[PRAAx] I.V (I.h p) (start s p) p ≐ one) (ht : Γ ⊢[PRAAx] le t (I.h p)) :
    Γ ⊢[PRAAx] lt (chain I s t p) (I.bd t p) ⋏
      (I.V (monus (I.h p) t) (chain I s t p) p ≐ one) := by
  have i := inst (Γ := Γ) (inv₀ I s) (![t, p] : Fin 2 → PTm k)
  simp [invF] at i
  exact .impE (.impE i (.andI hs hv)) ht

/-- The edge tests along the chain: `T(t, c(t), c(t + 1)) ≠ 0` for `t < h`. -/
theorem chain_edge {t p : PTm k} (hs : Γ ⊢[PRAAx] lt (start s p) (I.bd zero p))
    (hv : Γ ⊢[PRAAx] I.V (I.h p) (start s p) p ≐ one) (ht : Γ ⊢[PRAAx] lt t (I.h p)) :
    Γ ⊢[PRAAx] neg (I.t t (chain I s t p) (chain I s (succ t) p) p ≐ zero) := by
  have r := chain_inv hs hv (le_trans (le_succ_self t) ht)
  exact Prf.andE₁ (Prf.andE₂ (chain_step I s ht (Prf.andE₁ r) (Prf.andE₂ r)))

/-- The local tests along the chain: `G(t, c(t)) ≠ 0` for `t ≤ h`. -/
theorem chain_local {t p : PTm k} (hs : Γ ⊢[PRAAx] lt (start s p) (I.bd zero p))
    (hv : Γ ⊢[PRAAx] I.V (I.h p) (start s p) p ≐ one) (ht : Γ ⊢[PRAAx] le t (I.h p)) :
    Γ ⊢[PRAAx] neg (I.g t (chain I s t p) p ≐ zero) := by
  have r := chain_inv hs hv ht
  refine .orE (lt_or_eq_of_le ht) ?_ ?_
  · exact Prf.andE₁ (chain_step I s Prf.hyp0 (Prf.andE₁ r).wk (Prf.andE₂ r).wk)
  · -- the last level: `h ∸ t = 0` and `V(0, a) = sg G(h, a)`
    have hth : ((t ≐ I.h p) :: Γ) ⊢[PRAAx] t ≐ I.h p := Prf.hyp0
    have z : ((t ≐ I.h p) :: Γ) ⊢[PRAAx] monus (I.h p) t ≐ zero :=
      (congrMonus (.eqRefl _) hth).eqTrans (le_refl (I.h p))
    have hb : ((t ≐ I.h p) :: Γ) ⊢[PRAAx] lt (chain I s t p) (I.bd (I.h p) p) :=
      lt_congr (.eqRefl _) (bd_congr I hth) (Prf.andE₁ r).wk
    have v0 := (V_zero I hb).eqSymm.eqTrans ((V_congr I z.eqSymm (.eqRefl _)).eqTrans (Prf.andE₂ r).wk)
    refine .impI (one_ne_zero _ (v0.wk.eqSymm.eqTrans (sg_of_zero ?_)))
    exact (g_congr I hth.wk.eqSymm).eqTrans Prf.hyp0

end Chain

/-! ## Refinement under stronger evidence -/

/-- `I'` is stronger evidence than `I`: every local test and every edge test passed for `I'`
is passed for `I` (the Boolean inequalities `G' ≤ G`, `T' ≤ T`). -/
structure Refines (I' I : Instance) : Prop where
  g_mono : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {i a p : PTm k},
    (Γ ⊢[PRAAx] neg (I'.g i a p ≐ zero)) → (Γ ⊢[PRAAx] neg (I.g i a p ≐ zero))
  t_mono : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {i a b p : PTm k},
    (Γ ⊢[PRAAx] neg (I'.t i a b p ≐ zero)) → (Γ ⊢[PRAAx] neg (I.t i a b p ≐ zero))

section Refinement

variable {I' I : Instance} {s : PTm 1}

/-- The chain certified by the stronger evidence passes the local tests of the weaker. -/
theorem refinement_local (R : Refines I' I) {t p : PTm k}
    (hs : Γ ⊢[PRAAx] lt (start s p) (I'.bd zero p))
    (hv : Γ ⊢[PRAAx] I'.V (I'.h p) (start s p) p ≐ one) (ht : Γ ⊢[PRAAx] le t (I'.h p)) :
    Γ ⊢[PRAAx] neg (I.g t (chain I' s t p) p ≐ zero) :=
  R.g_mono (chain_local hs hv ht)

/-- The chain certified by the stronger evidence passes the edge tests of the weaker. -/
theorem refinement_edge (R : Refines I' I) {t p : PTm k}
    (hs : Γ ⊢[PRAAx] lt (start s p) (I'.bd zero p))
    (hv : Γ ⊢[PRAAx] I'.V (I'.h p) (start s p) p ≐ one) (ht : Γ ⊢[PRAAx] lt t (I'.h p)) :
    Γ ⊢[PRAAx] neg (I.t t (chain I' s t p) (chain I' s (succ t) p) p ≐ zero) :=
  R.t_mono (chain_edge hs hv ht)

end Refinement

end LeanProofs.IPRA.Foundations.ViableChain
