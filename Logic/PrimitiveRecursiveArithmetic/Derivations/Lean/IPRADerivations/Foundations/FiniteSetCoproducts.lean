import IPRADerivations.Foundations.FiniteSetCategory
import IPRADerivations.Foundations.FiniteGluing
import IPRADerivations.Core.LinearCombination

/-!
# Binary coproducts in the table category of finite sets (`ipra_categorical_methods`, Section 4)

Packet: `foundations/ipra_categorical_methods`, Subsection "The category of finite sets has
exponentials in iPRA": "the coproduct is `[n + m]`. ... The coproduct mediator is the table
obtained by concatenating its two input tables; its two equations and uniqueness are equally
direct."

In the presentation `finSet` of `Foundations/FiniteSetCategory`:

* `inlc n m`, `inrc n m`: the codes of the injections `[n] → [n + m]` (`x ↦ x`) and
  `[m] → [n + m]` (`x ↦ n + x`); `copairc n m c f g`: the code of the concatenated table
  `x ↦ f(x)` for `x < n`, `x ↦ g(x ∸ n)` for `x ≥ n`;
* `inl_hom`, `inr_hom`, `copair_hom`: they are arrows;
* `copair_inl`: `[f, g] ∘ inl = f`; `copair_inr`: `[f, g] ∘ inr = g`;
* `copair_unique`: `[h ∘ inl, h ∘ inr] = h` for every arrow `h : [n + m] → [c]`.

Equalities are equalities of codes, obtained entrywise (`inl_ev`, `inr_ev`, `cp_ev_lt`,
`cp_ev_ge`) with `code_congr` and `curry_ev`. The case distinction `x < n` or `n ≤ x` is the
decidable comparison of natural numbers; in the table it is the bit `sg (n ∸ x)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.FiniteSetCoproducts

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Probability.ProductPower (dg)
open LeanProofs.IPRA.Foundations.BoundedFormulas (sg_of_zero)
open LeanProofs.IPRA.Foundations.FiniteGluing (sg_of_ne)
open LeanProofs.IPRA.Foundations.FiniteSetExponential
open LeanProofs.IPRA.Foundations.FiniteSetCategory
open LeanProofs.IPRA.Foundations.PresentedCategory
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Arithmetic of the two halves -/

/-- `n + m ≥ 1` for `n ≥ 1`. -/
theorem add_pos {n m : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n)) :
    Γ ⊢[PRAAx] n + m ≐ succ (pred (n + m)) := by
  have e := natEq hn
  exact pos_of_eq_succ (c := pred n + m) (by apply deriveNat; ipra_simps; linear_combination e)

/-- `x < n` gives `x < n + m`. -/
theorem lt_add_right {x n m : PTm k} (h : Γ ⊢[PRAAx] lt x n) : Γ ⊢[PRAAx] lt x (n + m) :=
  le_trans h (le_add_right n m)

/-- `x < m` gives `n + x < n + m`. -/
theorem add_lt_add {x n m : PTm k} (h : Γ ⊢[PRAAx] lt x m) : Γ ⊢[PRAAx] lt (n + x) (n + m) := by
  have e := natEq (eq_add_of_le h)
  exact le_of_eq_add (d := monus m (succ x)) (by apply deriveNat; ipra_simps; linear_combination e)

/-- `(n + t) ∸ n = t`. -/
theorem add_monus_left (n t : PTm k) : Γ ⊢[PRAAx] monus (n + t) n ≐ t := by
  ipra_lc -natEq (eq_add_of_le (le_add_right (Γ := Γ) n t))

/-- `n + (x ∸ n) = x` for `n ≤ x`. -/
theorem add_monus_of_le {n x : PTm k} (h : Γ ⊢[PRAAx] le n x) : Γ ⊢[PRAAx] n + monus x n ≐ x :=
  (eq_add_of_le h).eqSymm

/-- `x ∸ n < m` for `n ≤ x < n + m`. -/
theorem monus_lt {n m x : PTm k} (h : Γ ⊢[PRAAx] le n x) (hx : Γ ⊢[PRAAx] lt x (n + m)) :
    Γ ⊢[PRAAx] lt (monus x n) m := by
  have e₁ := natEq (eq_add_of_le h)
  have e₂ := natEq (eq_add_of_le hx)
  exact le_of_eq_add (d := monus (n + m) (succ x))
    (by apply deriveNat; ipra_simps; linear_combination e₂ + e₁)

/-! ## The tables -/

/-- The right injection table `x ↦ n + x`; variables `0 = x`, `1 = n`. -/
def inrT : PTm 2 := var 1 + var 0

/-- The code of `inl : [n] → [n + m]`. -/
abbrev inlc (n m : PTm k) : PTm k := code idT n (n + m) zero
/-- The code of `inr : [m] → [n + m]`. -/
abbrev inrc (n m : PTm k) : PTm k := code inrT m (n + m) n

/-- The concatenated entry; variables `0 = x`, `1 = ⟨n, ⟨c, ⟨f, g⟩⟩⟩`. -/
def cpT : PTm 2 :=
  sg (monus (fstT (var 1)) (var 0)) *
      dg (fstT (sndT (var 1))) (var 0) (fstT (sndT (sndT (var 1)))) +
    monus one (sg (monus (fstT (var 1)) (var 0))) *
      dg (fstT (sndT (var 1))) (monus (var 0) (fstT (var 1))) (sndT (sndT (sndT (var 1))))

/-- The code of the copairing `[f, g] : [n + m] → [c]`. -/
abbrev copairc (n m c f g : PTm k) : PTm k :=
  code cpT (n + m) c (pairT n (pairT c (pairT f g)))

theorem cpT_at (x n c f g : PTm k) :
    Γ ⊢[PRAAx] inst2 cpT x (pairT n (pairT c (pairT f g))) ≐
      sg (monus n x) * dg c x f + monus one (sg (monus n x)) * dg c (monus x n) g := by
  have e₁ : inst2 cpT x (pairT n (pairT c (pairT f g))) =
      Syn.subst ![x, fstT (pairT n (pairT c (pairT f g))),
          fstT (sndT (pairT n (pairT c (pairT f g)))),
          fstT (sndT (sndT (pairT n (pairT c (pairT f g))))),
          sndT (sndT (sndT (pairT n (pairT c (pairT f g)))))]
        (sg (monus (var 1 : PTm 5) (var 0)) * dg (var 2) (var 0) (var 3) +
          monus one (sg (monus (var 1) (var 0))) * dg (var 2) (monus (var 0) (var 1)) (var 4)) := by
    show Syn.subst ![x, pairT n (pairT c (pairT f g))] cpT = _
    simp [cpT]
  have e₂ : sg (monus n x) * dg c x f + monus one (sg (monus n x)) * dg c (monus x n) g =
      Syn.subst ![x, n, c, f, g]
        (sg (monus (var 1 : PTm 5) (var 0)) * dg (var 2) (var 0) (var 3) +
          monus one (sg (monus (var 1) (var 0))) * dg (var 2) (monus (var 0) (var 1)) (var 4)) := by
    simp
  rw [e₁, e₂]
  have s₁ : Γ ⊢[PRAAx] sndT (pairT n (pairT c (pairT f g))) ≐ pairT c (pairT f g) :=
    snd_pair _ _
  have s₂ : Γ ⊢[PRAAx] sndT (sndT (pairT n (pairT c (pairT f g)))) ≐ pairT f g :=
    (congrSnd s₁).eqTrans (snd_pair _ _)
  exact Prf.eqCongr _ fun l => by
    fin_cases l
    · exact .eqRefl _
    · exact fst_pair _ _
    · exact (congrFst s₁).eqTrans (fst_pair _ _)
    · exact (congrFst s₂).eqTrans (fst_pair _ _)
    · exact (congrSnd s₂).eqTrans (snd_pair _ _)

/-- The concatenated entry on the left half. -/
theorem cp_entry_lt {x n c f g : PTm k} (hx : Γ ⊢[PRAAx] lt x n) :
    Γ ⊢[PRAAx] inst2 cpT x (pairT n (pairT c (pairT f g))) ≐ dg c x f := by
  have hne : Γ ⊢[PRAAx] neg (monus n x ≐ zero) :=
    .impI (le_lt_absurd _ (Prf.hyp0 (Γ := Γ) (φ := monus n x ≐ zero)) hx.wk)
  refine (cpT_at x n c f g).eqTrans ?_
  ipra_lc 𝔞 (dg c x f) * natEq (sg_of_ne hne) +
    𝔞 (dg c (monus x n) g) * natEq ((congrMonus (.eqRefl (one : PTm k)) (sg_of_ne hne)).eqTrans (le_refl one))

/-- The concatenated entry on the right half. -/
theorem cp_entry_ge {x n c f g : PTm k} (hx : Γ ⊢[PRAAx] le n x) :
    Γ ⊢[PRAAx] inst2 cpT x (pairT n (pairT c (pairT f g))) ≐ dg c (monus x n) g := by
  refine (cpT_at x n c f g).eqTrans ?_
  ipra_lc 𝔞 (dg c x f) * natEq (sg_of_zero hx) +
    𝔞 (dg c (monus x n) g) * natEq ((congrMonus (.eqRefl (one : PTm k)) (sg_of_zero hx)).eqTrans (monus_zero _))

theorem shift_add' (a b : PTm k) : Syn.shift (a + b) = Syn.shift a + Syn.shift b := by
  simp [Syn.shift]

theorem shift_inlc (n m : PTm k) : Syn.shift (inlc n m) = inlc (Syn.shift n) (Syn.shift m) := by
  simp [Syn.shift]

theorem shift_inrc (n m : PTm k) : Syn.shift (inrc n m) = inrc (Syn.shift n) (Syn.shift m) := by
  simp [Syn.shift]

theorem shift_copairc (n m c f g : PTm k) :
    Syn.shift (copairc n m c f g) =
      copairc (Syn.shift n) (Syn.shift m) (Syn.shift c) (Syn.shift f) (Syn.shift g) := by
  simp [Syn.shift]

/-! ## Entrywise evaluation -/

/-- `ev(inl, x) = x` for `x < n`. -/
theorem inl_ev {n m x : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n)) (hx : Γ ⊢[PRAAx] lt x n) :
    Γ ⊢[PRAAx] dg (n + m) x (inlc n m) ≐ x := by
  have e : inst2 idT x (zero : PTm k) = x := by simp [inst2, idT]
  have r := ev_curry_of_lt idT (p := (zero : PTm k)) (add_pos (m := m) hn) hx
    (by rw [e]; exact lt_add_right hx)
  rw [e] at r
  exact r

/-- `ev(inr, x) = n + x` for `x < m`. -/
theorem inr_ev {n m x : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n)) (hx : Γ ⊢[PRAAx] lt x m) :
    Γ ⊢[PRAAx] dg (n + m) x (inrc n m) ≐ n + x := by
  have e : inst2 inrT x n = n + x := by simp [inst2, inrT]
  have r := ev_curry_of_lt inrT (p := n) (add_pos (m := m) hn) hx
    (by rw [e]; exact add_lt_add hx)
  rw [e] at r
  exact r

/-- `ev([f, g], x) = ev(f, x)` for `x < n`. -/
theorem cp_ev_lt {n m c f g x : PTm k} (hc : Γ ⊢[PRAAx] c ≐ succ (pred c))
    (hx : Γ ⊢[PRAAx] lt x n) : Γ ⊢[PRAAx] dg c x (copairc n m c f g) ≐ dg c x f :=
  (ev_curry cpT hc (lt_add_right hx) (pairT n (pairT c (pairT f g)))).eqTrans
    ((congrAp2 remF (cp_entry_lt hx) (.eqRefl _)).eqTrans (rem_of_lt hc (dg_lt hc _ _)))

/-- `ev([f, g], x) = ev(g, x ∸ n)` for `n ≤ x < n + m`. -/
theorem cp_ev_ge {n m c f g x : PTm k} (hc : Γ ⊢[PRAAx] c ≐ succ (pred c))
    (hx : Γ ⊢[PRAAx] le n x) (hx' : Γ ⊢[PRAAx] lt x (n + m)) :
    Γ ⊢[PRAAx] dg c x (copairc n m c f g) ≐ dg c (monus x n) g :=
  (ev_curry cpT hc hx' (pairT n (pairT c (pairT f g)))).eqTrans
    ((congrAp2 remF (cp_entry_ge hx) (.eqRefl _)).eqTrans (rem_of_lt hc (dg_lt hc _ _)))

theorem inl_pt {t n m c f g : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hc : Γ ⊢[PRAAx] c ≐ succ (pred c)) (ht : Γ ⊢[PRAAx] lt t n) :
    Γ ⊢[PRAAx] inst2 cmT t (pairT (n + m) (pairT c (pairT (copairc n m c f g) (inlc n m)))) ≐
      inst2 evT t (pairT c f) :=
  (cmT_at t (n + m) c (copairc n m c f g) (inlc n m)).eqTrans
    ((dg_idx (inl_ev hn ht)).eqTrans ((cp_ev_lt hc ht).eqTrans (evT_at t c f).eqSymm))

theorem inr_pt {t n m c f g : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hc : Γ ⊢[PRAAx] c ≐ succ (pred c)) (ht : Γ ⊢[PRAAx] lt t m) :
    Γ ⊢[PRAAx] inst2 cmT t (pairT (n + m) (pairT c (pairT (copairc n m c f g) (inrc n m)))) ≐
      inst2 evT t (pairT c g) :=
  (cmT_at t (n + m) c (copairc n m c f g) (inrc n m)).eqTrans
    ((dg_idx (inr_ev hn ht)).eqTrans
      ((cp_ev_ge hc (le_add_right n t) (add_lt_add ht)).eqTrans
        ((dg_idx (add_monus_left n t)).eqTrans (evT_at t c g).eqSymm)))

theorem uniq_pt {x n m c h : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hc : Γ ⊢[PRAAx] c ≐ succ (pred c)) (hx : Γ ⊢[PRAAx] lt x (n + m)) :
    Γ ⊢[PRAAx] inst2 cpT x (pairT n (pairT c (pairT (cmpc n (n + m) c h (inlc n m))
        (cmpc m (n + m) c h (inrc n m))))) ≐
      inst2 evT x (pairT c h) := by
  refine .orE (lt_or_le x n) ?_ ?_
  · have hl : (lt x n :: Γ) ⊢[PRAAx] lt x n := Prf.hyp0
    exact (cp_entry_lt hl).eqTrans ((ev_comp hc.wk hl).eqTrans
      ((dg_idx (inl_ev hn.wk hl)).eqTrans (evT_at x c h).eqSymm))
  · have hg : (le n x :: Γ) ⊢[PRAAx] le n x := Prf.hyp0
    have hm := monus_lt hg hx.wk
    exact (cp_entry_ge hg).eqTrans ((ev_comp hc.wk hm).eqTrans
      ((dg_idx ((inr_ev hn.wk hm).eqTrans (add_monus_of_le hg))).eqTrans (evT_at x c h).eqSymm))

/-! ## The arrows and the universal property -/

/-- `inl : [n] → [n + m]`. -/
theorem inl_hom {n m : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n)) :
    Γ ⊢[PRAAx] finSet.hom n (n + m) (inlc n m) := by
  rw [fs_hom]
  exact .andI hn (.andI (add_pos hn) (code_lt idT (add_pos hn) n zero))

/-- `inr : [m] → [n + m]`. -/
theorem inr_hom {n m : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) : Γ ⊢[PRAAx] finSet.hom m (n + m) (inrc n m) := by
  rw [fs_hom]
  exact .andI hm (.andI (add_pos hn) (code_lt inrT (add_pos hn) m n))

/-- `[f, g] : [n + m] → [c]`. -/
theorem copair_hom {n m c f g : PTm k} (hf : Γ ⊢[PRAAx] finSet.hom n c f) :
    Γ ⊢[PRAAx] finSet.hom (n + m) c (copairc n m c f g) := by
  rw [fs_hom] at hf ⊢
  have hc := Prf.andE₁ (Prf.andE₂ hf)
  exact .andI (add_pos (Prf.andE₁ hf)) (.andI hc (code_lt cpT hc (n + m) _))

/-- `[f, g] ∘ inl = f`. -/
theorem copair_inl {n m c f g : PTm k} (hf : Γ ⊢[PRAAx] finSet.hom n c f) :
    Γ ⊢[PRAAx] cmpc n (n + m) c (copairc n m c f g) (inlc n m) ≐ f := by
  rw [fs_hom] at hf
  have hn := Prf.andE₁ hf
  have hc := Prf.andE₁ (Prf.andE₂ hf)
  refine .eqTrans (code_congr cmT evT (q' := pairT c f) (.allI (.impI ?_)))
    (curry_ev hc (Prf.andE₂ (Prf.andE₂ hf)))
  simp only [shift_pairT, shift_add', shift_inlc, shift_copairc]
  have hn' := hn.shift
  rw [shift_pos] at hn'
  have hc' := hc.shift
  rw [shift_pos] at hc'
  exact congrAp2 remF (inl_pt hn'.wk hc'.wk Prf.hyp0) (.eqRefl _)

/-- `[f, g] ∘ inr = g`. -/
theorem copair_inr {n m c f g : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hg : Γ ⊢[PRAAx] finSet.hom m c g) :
    Γ ⊢[PRAAx] cmpc m (n + m) c (copairc n m c f g) (inrc n m) ≐ g := by
  rw [fs_hom] at hg
  have hc := Prf.andE₁ (Prf.andE₂ hg)
  refine .eqTrans (code_congr cmT evT (q' := pairT c g) (.allI (.impI ?_)))
    (curry_ev hc (Prf.andE₂ (Prf.andE₂ hg)))
  simp only [shift_pairT, shift_add', shift_inrc, shift_copairc]
  have hn' := hn.shift
  rw [shift_pos] at hn'
  have hc' := hc.shift
  rw [shift_pos] at hc'
  exact congrAp2 remF (inr_pt hn'.wk hc'.wk Prf.hyp0) (.eqRefl _)

/-- Uniqueness of the copairing: `[h ∘ inl, h ∘ inr] = h` for `h : [n + m] → [c]`. -/
theorem copair_unique {n m c h : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hh : Γ ⊢[PRAAx] finSet.hom (n + m) c h) :
    Γ ⊢[PRAAx] copairc n m c (cmpc n (n + m) c h (inlc n m)) (cmpc m (n + m) c h (inrc n m)) ≐
      h := by
  rw [fs_hom] at hh
  have hc := Prf.andE₁ (Prf.andE₂ hh)
  refine .eqTrans (code_congr cpT evT (q' := pairT c h) (.allI (.impI ?_)))
    (curry_ev hc (Prf.andE₂ (Prf.andE₂ hh)))
  simp only [shift_pairT, shift_add', shift_inlc, shift_inrc, shift_cmpc]
  have hn' := hn.shift
  rw [shift_pos] at hn'
  have hc' := hc.shift
  rw [shift_pos] at hc'
  exact congrAp2 remF (uniq_pt hn'.wk hc'.wk Prf.hyp0) (.eqRefl _)

end LeanProofs.IPRA.Foundations.FiniteSetCoproducts
