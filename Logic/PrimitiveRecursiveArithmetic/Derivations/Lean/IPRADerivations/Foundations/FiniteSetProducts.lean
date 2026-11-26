import IPRADerivations.Foundations.FiniteSetCategory
import IPRADerivations.Core.Header

/-!
# Binary products in the table category of finite sets (`ipra_categorical_methods`, Section 4)

Packet: `foundations/ipra_categorical_methods`, Subsection "The category of finite sets has
exponentials in iPRA": "the product is `[n] × [m] ≅ [nm]`. Use `(i, j) ↦ i m + j` for the
product ... The pairing of two tables `f : [z] → [n]` and `g : [z] → [m]` has entries
`f(k) m + g(k)`. Its projection equations and uniqueness are entrywise equations."

In the presentation `finSet` of `Foundations/FiniteSetCategory` (objects `≥ 1`, arrows are
codes):

* `p1c n m`, `p2c n m`: the codes of the projections `[n m] → [n]`, `[n m] → [m]`
  (`x ↦ ⌊x / m⌋`, `x ↦ x mod m`); `pairc z n m f g`: the code of the pairing
  `t ↦ ev(f, t) m + ev(g, t)`;
* `p1_hom`, `p2_hom`, `pair_hom`: they are arrows;
* `prod_fst`: `π₁ ∘ ⟨f, g⟩ = f`; `prod_snd`: `π₂ ∘ ⟨f, g⟩ = g`;
* `prod_unique`: `⟨π₁ ∘ h, π₂ ∘ h⟩ = h` for every arrow `h : [z] → [n m]`.

Equalities are equalities of codes. Each is proved by evaluating the two tables at an
arbitrary `t < z` (`pair_ev`, `p1_ev`, `p2_ev`) and then `code_congr` and `curry_ev`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.FiniteSetProducts

open_ipra
open LeanProofs.IPRA.Probability.ProductPower (dg)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (pos_mul')
open LeanProofs.IPRA.Foundations.FiniteSetExponential
open LeanProofs.IPRA.Foundations.FiniteSetCategory
open LeanProofs.IPRA.Foundations.PresentedCategory

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## The tables -/

/-- The first projection table `x ↦ ⌊x / m⌋`; variables `0 = x`, `1 = m`. -/
def p1T : PTm 2 := quo (var 0) (var 1)
/-- The second projection table `x ↦ x mod m`; variables `0 = x`, `1 = m`. -/
def p2T : PTm 2 := rem (var 0) (var 1)

/-- The code of `π₁ : [n m] → [n]`. -/
abbrev p1c (n m : PTm k) : PTm k := code p1T (n * m) n m
/-- The code of `π₂ : [n m] → [m]`. -/
abbrev p2c (n m : PTm k) : PTm k := code p2T (n * m) m m

/-- The pairing entry `ev(f, t) m + ev(g, t)`; variables `0 = t`, `1 = ⟨n, ⟨m, ⟨f, g⟩⟩⟩`. -/
def prT : PTm 2 :=
  dg (fstT (var 1)) (var 0) (fstT (sndT (sndT (var 1)))) * fstT (sndT (var 1)) +
    dg (fstT (sndT (var 1))) (var 0) (sndT (sndT (sndT (var 1))))

/-- The code of `⟨f, g⟩ : [z] → [n m]`. -/
abbrev pairc (z n m f g : PTm k) : PTm k := code prT z (n * m) (pairT n (pairT m (pairT f g)))

theorem prT_at (t n m f g : PTm k) :
    Γ ⊢[PRAAx] inst2 prT t (pairT n (pairT m (pairT f g))) ≐ dg n t f * m + dg m t g := by
  have e₁ : inst2 prT t (pairT n (pairT m (pairT f g))) =
      Syn.subst ![t, fstT (pairT n (pairT m (pairT f g))),
          fstT (sndT (pairT n (pairT m (pairT f g)))),
          fstT (sndT (sndT (pairT n (pairT m (pairT f g))))),
          sndT (sndT (sndT (pairT n (pairT m (pairT f g)))))]
        (dg (var 1 : PTm 5) (var 0) (var 3) * var 2 + dg (var 2) (var 0) (var 4)) := by
    show Syn.subst ![t, pairT n (pairT m (pairT f g))] prT = _
    simp [prT]
  have e₂ : dg n t f * m + dg m t g =
      Syn.subst ![t, n, m, f, g]
        (dg (var 1 : PTm 5) (var 0) (var 3) * var 2 + dg (var 2) (var 0) (var 4)) := by simp
  rw [e₁, e₂]
  have s₁ : Γ ⊢[PRAAx] sndT (pairT n (pairT m (pairT f g))) ≐ pairT m (pairT f g) :=
    snd_pair _ _
  have s₂ : Γ ⊢[PRAAx] sndT (sndT (pairT n (pairT m (pairT f g)))) ≐ pairT f g :=
    (congrSnd s₁).eqTrans (snd_pair _ _)
  exact Prf.eqCongr _ fun l => by
    fin_cases l
    · exact .eqRefl _
    · exact fst_pair _ _
    · exact (congrFst s₁).eqTrans (fst_pair _ _)
    · exact (congrFst s₂).eqTrans (fst_pair _ _)
    · exact (congrSnd s₂).eqTrans (snd_pair _ _)

theorem shift_mul' (a b : PTm k) : Syn.shift (a * b) = Syn.shift a * Syn.shift b := by
  simp [Syn.shift]

theorem shift_p1c (n m : PTm k) : Syn.shift (p1c n m) = p1c (Syn.shift n) (Syn.shift m) := by
  simp [Syn.shift]

theorem shift_p2c (n m : PTm k) : Syn.shift (p2c n m) = p2c (Syn.shift n) (Syn.shift m) := by
  simp [Syn.shift]

theorem shift_pairc (z n m f g : PTm k) :
    Syn.shift (pairc z n m f g) =
      pairc (Syn.shift z) (Syn.shift n) (Syn.shift m) (Syn.shift f) (Syn.shift g) := by
  simp [Syn.shift]

/-! ## Entrywise evaluation -/

/-- `ev(⟨f, g⟩, t) = ev(f, t) m + ev(g, t)` for `t < z`. -/
theorem pair_ev {z n m f g t : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (ht : Γ ⊢[PRAAx] lt t z) :
    Γ ⊢[PRAAx] dg (n * m) t (pairc z n m f g) ≐ dg n t f * m + dg m t g :=
  (ev_curry prT (pos_mul' hn hm) ht (pairT n (pairT m (pairT f g)))).eqTrans
    ((congrAp2 remF (prT_at t n m f g) (.eqRefl _)).eqTrans
      (rem_of_lt (pos_mul' hn hm) (pair_lt (dg_lt hn t f) (dg_lt hm t g))))

/-- `ev(π₁, y) = ⌊y / m⌋` for `y < n m`. -/
theorem p1_ev {n m y : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hy : Γ ⊢[PRAAx] lt y (n * m)) :
    Γ ⊢[PRAAx] dg n y (p1c n m) ≐ quo y m := by
  have e : inst2 p1T y m = quo y m := by simp [inst2, p1T]
  have r := ev_curry p1T hn hy m
  rw [e] at r
  exact r.eqTrans (rem_of_lt hn (fst_lt hm hy))

/-- `ev(π₂, y) = y mod m` for `y < n m`. -/
theorem p2_ev {n m y : PTm k} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hy : Γ ⊢[PRAAx] lt y (n * m)) : Γ ⊢[PRAAx] dg m y (p2c n m) ≐ rem y m := by
  have e : inst2 p2T y m = rem y m := by simp [inst2, p2T]
  have r := ev_curry p2T hm hy m
  rw [e] at r
  exact r.eqTrans (rem_of_lt hm (snd_lt hm y))

theorem fst_pt {t z n m f g : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (ht : Γ ⊢[PRAAx] lt t z) :
    Γ ⊢[PRAAx] inst2 cmT t (pairT (n * m) (pairT n (pairT (p1c n m) (pairc z n m f g)))) ≐
      inst2 evT t (pairT n f) := by
  have hy := pair_lt (dg_lt hn t f) (dg_lt hm t g)
  exact (cmT_at t (n * m) n (p1c n m) (pairc z n m f g)).eqTrans
    ((dg_idx (pair_ev hn hm ht)).eqTrans ((p1_ev hn hm hy).eqTrans
      ((pair_fst hm (dg_lt hm t g)).eqTrans (evT_at t n f).eqSymm)))

theorem snd_pt {t z n m f g : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (ht : Γ ⊢[PRAAx] lt t z) :
    Γ ⊢[PRAAx] inst2 cmT t (pairT (n * m) (pairT m (pairT (p2c n m) (pairc z n m f g)))) ≐
      inst2 evT t (pairT m g) := by
  have hy := pair_lt (dg_lt hn t f) (dg_lt hm t g)
  exact (cmT_at t (n * m) m (p2c n m) (pairc z n m f g)).eqTrans
    ((dg_idx (pair_ev hn hm ht)).eqTrans ((p2_ev hm hy).eqTrans
      ((pair_snd hm (dg_lt hm t g)).eqTrans (evT_at t m g).eqSymm)))

theorem uniq_pt {t z n m h : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (ht : Γ ⊢[PRAAx] lt t z) :
    Γ ⊢[PRAAx] inst2 prT t (pairT n (pairT m (pairT (cmpc z (n * m) n (p1c n m) h)
        (cmpc z (n * m) m (p2c n m) h)))) ≐
      inst2 evT t (pairT (n * m) h) := by
  have hy := dg_lt (pos_mul' hn hm) t h
  have c₁ := (ev_comp (b := n * m) (g := p1c n m) (f := h) hn ht).eqTrans (p1_ev hn hm hy)
  have c₂ := (ev_comp (b := n * m) (g := p2c n m) (f := h) hm ht).eqTrans (p2_ev hm hy)
  exact (prT_at t n m _ _).eqTrans ((congrAdd (congrMul c₁ (.eqRefl _)) c₂).eqTrans
    ((pair_eta hm (dg (n * m) t h)).eqSymm.eqTrans (evT_at t (n * m) h).eqSymm))

/-! ## The arrows and the universal property -/

/-- `π₁ : [n m] → [n]`. -/
theorem p1_hom {n m : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) : Γ ⊢[PRAAx] finSet.hom (n * m) n (p1c n m) := by
  rw [fs_hom]
  exact .andI (pos_mul' hn hm) (.andI hn (code_lt p1T hn (n * m) m))

/-- `π₂ : [n m] → [m]`. -/
theorem p2_hom {n m : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) : Γ ⊢[PRAAx] finSet.hom (n * m) m (p2c n m) := by
  rw [fs_hom]
  exact .andI (pos_mul' hn hm) (.andI hm (code_lt p2T hm (n * m) m))

/-- `⟨f, g⟩ : [z] → [n m]`. -/
theorem pair_hom {z n m f g : PTm k} (hf : Γ ⊢[PRAAx] finSet.hom z n f)
    (hg : Γ ⊢[PRAAx] finSet.hom z m g) : Γ ⊢[PRAAx] finSet.hom z (n * m) (pairc z n m f g) := by
  rw [fs_hom] at hf hg ⊢
  have hnm := pos_mul' (Prf.andE₁ (Prf.andE₂ hf)) (Prf.andE₁ (Prf.andE₂ hg))
  exact .andI (Prf.andE₁ hf) (.andI hnm (code_lt prT hnm z _))

/-- `π₁ ∘ ⟨f, g⟩ = f`. -/
theorem prod_fst {z n m f g : PTm k} (hf : Γ ⊢[PRAAx] finSet.hom z n f)
    (hg : Γ ⊢[PRAAx] finSet.hom z m g) :
    Γ ⊢[PRAAx] cmpc z (n * m) n (p1c n m) (pairc z n m f g) ≐ f := by
  rw [fs_hom] at hf hg
  have hn := Prf.andE₁ (Prf.andE₂ hf)
  have hm := Prf.andE₁ (Prf.andE₂ hg)
  refine .eqTrans (code_congr cmT evT (q' := pairT n f) (.allI (.impI ?_)))
    (curry_ev hn (Prf.andE₂ (Prf.andE₂ hf)))
  simp only [shift_pairT, shift_mul', shift_p1c, shift_pairc]
  have hn' := hn.shift
  rw [shift_pos] at hn'
  have hm' := hm.shift
  rw [shift_pos] at hm'
  exact congrAp2 remF (fst_pt hn'.wk hm'.wk Prf.hyp0) (.eqRefl _)

/-- `π₂ ∘ ⟨f, g⟩ = g`. -/
theorem prod_snd {z n m f g : PTm k} (hf : Γ ⊢[PRAAx] finSet.hom z n f)
    (hg : Γ ⊢[PRAAx] finSet.hom z m g) :
    Γ ⊢[PRAAx] cmpc z (n * m) m (p2c n m) (pairc z n m f g) ≐ g := by
  rw [fs_hom] at hf hg
  have hn := Prf.andE₁ (Prf.andE₂ hf)
  have hm := Prf.andE₁ (Prf.andE₂ hg)
  refine .eqTrans (code_congr cmT evT (q' := pairT m g) (.allI (.impI ?_)))
    (curry_ev hm (Prf.andE₂ (Prf.andE₂ hg)))
  simp only [shift_pairT, shift_mul', shift_p2c, shift_pairc]
  have hn' := hn.shift
  rw [shift_pos] at hn'
  have hm' := hm.shift
  rw [shift_pos] at hm'
  exact congrAp2 remF (snd_pt hn'.wk hm'.wk Prf.hyp0) (.eqRefl _)

/-- Uniqueness of the pairing: `⟨π₁ ∘ h, π₂ ∘ h⟩ = h` for `h : [z] → [n m]`. -/
theorem prod_unique {z n m h : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hh : Γ ⊢[PRAAx] finSet.hom z (n * m) h) :
    Γ ⊢[PRAAx] pairc z n m (cmpc z (n * m) n (p1c n m) h) (cmpc z (n * m) m (p2c n m) h) ≐ h := by
  rw [fs_hom] at hh
  refine .eqTrans (code_congr prT evT (q' := pairT (n * m) h) (.allI (.impI ?_)))
    (curry_ev (pos_mul' hn hm) (Prf.andE₂ (Prf.andE₂ hh)))
  simp only [shift_pairT, shift_mul', shift_p1c, shift_p2c, shift_cmpc]
  have hn' := hn.shift
  rw [shift_pos] at hn'
  have hm' := hm.shift
  rw [shift_pos] at hm'
  exact congrAp2 remF (uniq_pt hn'.wk hm'.wk Prf.hyp0) (.eqRefl _)

end LeanProofs.IPRA.Foundations.FiniteSetProducts
