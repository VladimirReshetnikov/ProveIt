import IPRADerivations.Foundations.FilteredEnumeration
import IPRADerivations.Foundations.FiniteSetExponential
import IPRADerivations.Core.Header

/-!
# Pullbacks of finite sets (`ipra_categorical_methods`, finite limits)

Packet: `foundations/ipra_categorical_methods`, Section 4, Subsection "Finite limits,
including equalizers and pullbacks": "A cospan gives pairs with equal images, so pullbacks are
obtained by the same bounded filter."

For tables `f : [n] → C` and `g : [m] → C` given by terms `f(i, p)`, `g(j, p)` (`m ≥ 1`), a
pair `(i, j)` is the number `i m + j < n m` (`Foundations/FiniteSetExponential`), and it is
retained when `f(i) = g(j)`. With `rank` and `sel` of `Foundations/FilteredEnumeration` for
this retained set (`pbK f g`), the pullback is `[ℓ]`, `ℓ = rank (n m)`, with projections

`π₁(r) = ⌊sel r / m⌋`, `π₂(r) = sel r mod m`.

* `pb_square`: for `r < ℓ`, `π₁(r) < n`, `π₂(r) < m` and `f(π₁(r)) = g(π₂(r))`: a cone;
* `pb_factor`: for `i < n`, `j < m` with `f(i) = g(j)`, the mediator `u = rank (i m + j)` is
  below `ℓ` and `π₁(u) = i`, `π₂(u) = j`;
* `pb_unique`: if `v < ℓ`, `π₁(v) = i` and `π₂(v) = j`, then `v = rank (i m + j)`.

These are the universal property of the pullback, entrywise, with a primitive-recursive
mediator. The Chinese remainder square of the packet (`Foundations/ChineseRemainder`) is a
pullback of this kind with an explicit closed-form mediator.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.FinitePullback

open_ipra
open LeanProofs.IPRA.Foundations.FilteredEnumeration
open LeanProofs.IPRA.Foundations.FiniteSetExponential
  (pair_lt pair_fst pair_snd pair_eta fst_lt snd_lt)
open LeanProofs.IPRA.Foundations.BoundedReflection (sgB)

variable {k : ℕ} {Γ : List (Fm PTm k)}

section Pullback

variable (f g : PTm 2)

/-- `f(⌊x / m⌋, p)`; variables `0 = x`, `1 = ⟨m, p⟩`. -/
def fB : PTm 2 := inst2 f (quo (var 0) (fstT (var 1))) (sndT (var 1))
/-- `g(x mod m, p)`; variables `0 = x`, `1 = ⟨m, p⟩`. -/
def gB : PTm 2 := inst2 g (rem (var 0) (fstT (var 1))) (sndT (var 1))

theorem fB_at (x m p : PTm k) :
    Γ ⊢[PRAAx] inst2 (fB f) x (pairT m p) ≐ inst2 f (quo x m) p := by
  have e : inst2 (fB f) x (pairT m p) =
      inst2 f (quo x (fstT (pairT m p))) (sndT (pairT m p)) := by
    show Syn.subst ![x, pairT m p] (fB f) = _
    simp [fB]
  rw [e]
  exact congrInst2 f (congrAp2 quoF (.eqRefl _) (fst_pair _ _)) (snd_pair _ _)

theorem gB_at (x m p : PTm k) :
    Γ ⊢[PRAAx] inst2 (gB g) x (pairT m p) ≐ inst2 g (rem x m) p := by
  have e : inst2 (gB g) x (pairT m p) =
      inst2 g (rem x (fstT (pairT m p))) (sndT (pairT m p)) := by
    show Syn.subst ![x, pairT m p] (gB g) = _
    simp [gB]
  rw [e]
  exact congrInst2 g (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (snd_pair _ _)

/-- The retained set of the pullback: pairs with equal images. -/
abbrev pbK : PTm 2 := eqK (fB f) (gB g)

/-- The size `ℓ` of the pullback. -/
abbrev size (n m p : PTm k) : PTm k := rank (pbK f g) (n * m) (pairT m p)

/-- The `r`-th retained pair. -/
abbrev pt (r n m p : PTm k) : PTm k := sel (pbK f g) r (n * m) (pairT m p)

/-- The pullback is a cone: its projections are in range and the square commutes. -/
theorem pb_square {r n m p : PTm k} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (h : Γ ⊢[PRAAx] lt r (size f g n m p)) :
    Γ ⊢[PRAAx] lt (quo (pt f g r n m p) m) n ⋏
      (lt (rem (pt f g r n m p) m) m ⋏
        (inst2 f (quo (pt f g r n m p) m) p ≐ inst2 g (rem (pt f g r n m p) m) p)) := by
  have e := equalizer_incl (fB f) (gB g) h
  refine .andI (fst_lt hm (Prf.andE₁ e)) (.andI (snd_lt hm _) ?_)
  exact (fB_at f _ m p).eqSymm.eqTrans ((Prf.andE₂ e).eqTrans (gB_at g _ m p))

/-- A compatible pair is retained. -/
theorem pair_agree {i j m p : PTm k} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hj : Γ ⊢[PRAAx] lt j m) (h : Γ ⊢[PRAAx] inst2 f i p ≐ inst2 g j p) :
    Γ ⊢[PRAAx] inst2 (fB f) (i * m + j) (pairT m p) ≐ inst2 (gB g) (i * m + j) (pairT m p) :=
  (fB_at f _ m p).eqTrans ((congrInst2 f (pair_fst hm hj) (.eqRefl _)).eqTrans
    (h.eqTrans ((congrInst2 g (pair_snd hm hj) (.eqRefl _)).eqSymm.eqTrans
      (gB_at g _ m p).eqSymm)))

/-- Every compatible pair factors through the pullback, with mediator `rank (i m + j)`. -/
theorem pb_factor {i j n m p : PTm k} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hi : Γ ⊢[PRAAx] lt i n) (hj : Γ ⊢[PRAAx] lt j m)
    (h : Γ ⊢[PRAAx] inst2 f i p ≐ inst2 g j p) :
    Γ ⊢[PRAAx] lt (rank (pbK f g) (i * m + j) (pairT m p)) (size f g n m p) ⋏
      ((quo (pt f g (rank (pbK f g) (i * m + j) (pairT m p)) n m p) m ≐ i) ⋏
        (rem (pt f g (rank (pbK f g) (i * m + j) (pairT m p)) n m p) m ≐ j)) := by
  have e := equalizer_factor (fB f) (gB g) (pair_lt hi hj) (pair_agree f g hm hj h)
  exact .andI (Prf.andE₁ e)
    (.andI ((congrAp2 quoF (Prf.andE₂ e) (.eqRefl _)).eqTrans (pair_fst hm hj))
      ((congrAp2 remF (Prf.andE₂ e) (.eqRefl _)).eqTrans (pair_snd hm hj)))

/-- The mediator is unique. -/
theorem pb_unique {v i j n m p : PTm k} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hv : Γ ⊢[PRAAx] lt v (size f g n m p))
    (h₁ : Γ ⊢[PRAAx] quo (pt f g v n m p) m ≐ i) (h₂ : Γ ⊢[PRAAx] rem (pt f g v n m p) m ≐ j) :
    Γ ⊢[PRAAx] v ≐ rank (pbK f g) (i * m + j) (pairT m p) :=
  equalizer_unique (fB f) (gB g) hv
    ((pair_eta hm (pt f g v n m p)).eqTrans (congrAdd (congrMul h₁ (.eqRefl _)) h₂))

end Pullback

end LeanProofs.IPRA.Foundations.FinitePullback
