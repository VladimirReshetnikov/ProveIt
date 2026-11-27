import IPRADerivations.Foundations.FiniteGluing

/-!
# Rank and select for a decidable finite subset (`ipra_categorical_methods`, finite limits)

Packet: `foundations/ipra_categorical_methods`, Section 4, Subsection "Finite limits,
including equalizers and pullbacks": "Let `L` be the increasing list of retained tuple codes.
Its size is a PR number `ℓ ≤ P`. Ranking within `L` and selecting its `r`th element are
bounded PR operations; rank is only used on an element known to have been retained."

A subset of `[P]` is given by a term `K(x, p)` (variables `0 = x`, `1 = p`): `x` is retained
when `K(x, p) ≠ 0`. No list is coded:

* `rank K x p = #{y < x : K(y, p) ≠ 0}` (a bounded sum); the size is `ℓ = rank K P p`;
* `sel K r P p` = the least `x < P` that is retained and has rank `r` (bounded search).

Derived:

* `rank_zero`, `rank_succ`, `rank_mono`, `rank_lt_of_kept`: the rank is nondecreasing and
  increases strictly past a retained element;
* `sel_spec`: for `r < ℓ`, `sel r < P`, `sel r` is retained and `rank (sel r) = r`;
* `sel_rank`: for a retained `x < P`, `sel (rank x) = x`;
* `rank_lt_size`: for a retained `x < P`, `rank x < ℓ`.

So `r ↦ sel r` and `x ↦ rank x` are mutually inverse between `[ℓ]` and the retained elements
of `[P]`, in increasing order. The existence of the `r`-th element is proved by induction on
`P` for the quantifier-free bit of `∃ x < P (x retained ∧ rank x = r)`.

**Equalizers.** For two tables `f`, `g` the retained set is `{x : f(x) = g(x)}`
(`eqK f g`). A cone value `c < P` with `f(c) = g(c)` factors through the mediator
`rank c < ℓ`: `sel (rank c) = c` (`equalizer_factor`), and the mediator is unique: if
`v < ℓ` and `sel v = c` then `v = rank c` (`equalizer_unique`). "A parallel pair produces the
list of points where its two tables agree, so equalizers require no undecidable set
formation."

Not derived: limits of general finite diagrams (mixed-radix tuples), pullbacks as a separate
statement, finite colimits by bounded equivalence closure.
-/

namespace LeanProofs.IPRA.Foundations.FilteredEnumeration

open_ipra exports
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Foundations.BoundedReflection
  (sgB inst2_sgB exB wit ex_intro ex_elim ex_least sg_cases one_ne_zero)

variable {k : ℕ} {Γ : List (Fm PTm k)}

section Rank

variable (K : PTm 2)

/-- `rank K x p`: the number of retained elements below `x`. -/
abbrev rank (x p : PTm k) : PTm k := ap2 (sumF (sgB K)) x p

theorem rank_zero (p : PTm k) : Γ ⊢[PRAAx] rank K zero p ≐ zero := sum_zero _ _

theorem rank_succ (x p : PTm k) :
    Γ ⊢[PRAAx] rank K (succ x) p ≐ rank K x p + sg (inst2 K x p) := by
  have h := sum_succ' (Γ := Γ) (sgB K) x p
  rw [inst2_sgB] at h
  exact h

/-- Variables: `0 = d`, `1 = x`, `2 = p`. -/
private def monoF (K : PTm 2) : Fm PTm 3 :=
  le (rank K (var 1) (var 2)) (rank K (var 1 + var 0) (var 2))

private theorem mono₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] monoF K := by
  ipra_ind [monoF, subst_le, subst_ap2]
  · exact le_congr (.eqRefl _) (congrAp2 (sumF (sgB K)) (add_zero _).eqSymm (.eqRefl _))
      (le_refl _)
  · have ih : [monoF K] ⊢[PRAAx] le (rank K (var 1) (var 2)) (rank K (var 1 + var 0) (var 2)) :=
      Prf.hyp0
    have e : [monoF K] ⊢[PRAAx] rank K (var 1 + succ (var 0)) (var 2) ≐
        rank K (var 1 + var 0) (var 2) + sg (inst2 K (var 1 + var 0) (var 2)) :=
      (congrAp2 (sumF (sgB K)) (add_succ _ _) (.eqRefl _)).eqTrans (rank_succ K _ _)
    exact le_trans ih (le_of_eq_add e)

/-- The rank is nondecreasing. -/
theorem rank_mono {x x' : PTm k} (h : Γ ⊢[PRAAx] le x x') (p : PTm k) :
    Γ ⊢[PRAAx] le (rank K x p) (rank K x' p) := by
  have i := inst (Γ := Γ) (mono₀ K) (![monus x' x, x, p] : Fin 3 → PTm k)
  simp [monoF] at i
  exact le_congr (.eqRefl _) (congrAp2 (sumF (sgB K)) (eq_add_of_le h).eqSymm (.eqRefl _)) i

/-- Past a retained element the rank increases strictly. -/
theorem rank_lt_of_kept {x x' p : PTm k} (hk : Γ ⊢[PRAAx] neg (inst2 K x p ≐ zero))
    (h : Γ ⊢[PRAAx] lt x x') : Γ ⊢[PRAAx] lt (rank K x p) (rank K x' p) := by
  have s : Γ ⊢[PRAAx] rank K (succ x) p ≐ succ (rank K x p) :=
    (rank_succ K x p).eqTrans ((congrAdd (.eqRefl _) (sg_of_ne hk)).eqTrans
      (succ_eq_add_one _).eqSymm)
  exact le_congr s (.eqRefl _) (rank_mono K h p)

end Rank

/-! ## Selection -/

section Select

variable (K : PTm 2)

/-- `[x retained] · [rank x = r]`; variables `0 = x`, `1 = ⟨r, p⟩`. -/
def tB : PTm 2 :=
  sg (inst2 K (var 0) (sndT (var 1))) *
    eqb (ap2 (sumF (sgB K)) (var 0) (sndT (var 1))) (fstT (var 1))

theorem tB_at (x r p : PTm k) :
    Γ ⊢[PRAAx] inst2 (tB K) x (pairT r p) ≐ sg (inst2 K x p) * eqb (rank K x p) r := by
  have e₁ : inst2 (tB K) x (pairT r p) =
      Syn.subst ![x, fstT (pairT r p), sndT (pairT r p)]
        (sg (inst2 K (var 0 : PTm 3) (var 2)) *
          eqb (ap2 (sumF (sgB K)) (var 0) (var 2)) (var 1)) := by
    show Syn.subst ![x, pairT r p] (tB K) = _
    simp [tB]
  have e₂ : sg (inst2 K x p) * eqb (rank K x p) r =
      Syn.subst ![x, r, p]
        (sg (inst2 K (var 0 : PTm 3) (var 2)) *
          eqb (ap2 (sumF (sgB K)) (var 0) (var 2)) (var 1)) := by simp
  rw [e₁, e₂]
  exact Prf.eqCongr _ fun l => by
    fin_cases l
    · exact .eqRefl _
    · exact fst_pair _ _
    · exact snd_pair _ _

/-- `sel K r P p`: the least retained `x < P` of rank `r`. -/
def sel (r P p : PTm k) : PTm k := wit (tB K) P (pairT r p)

/-- A retained element of rank `r` passes the test. -/
theorem tB_ne_of {x r p : PTm k} (hk : Γ ⊢[PRAAx] neg (inst2 K x p ≐ zero))
    (hr : Γ ⊢[PRAAx] rank K x p ≐ r) : Γ ⊢[PRAAx] neg (inst2 (tB K) x (pairT r p) ≐ zero) := by
  refine .impI (one_ne_zero _ ?_)
  have t := (tB_at (Γ := (inst2 (tB K) x (pairT r p) ≐ zero) :: Γ) K x r p).eqSymm.eqTrans
    Prf.hyp0
  exact ((one_mul _).eqSymm.eqTrans (congrMul (sg_of_ne hk.wk).eqSymm
    (eqb_of_eq hr.wk).eqSymm)).eqTrans t

/-- An element passing the test is retained. -/
theorem kept_of_tB {x r p : PTm k} (h : Γ ⊢[PRAAx] neg (inst2 (tB K) x (pairT r p) ≐ zero)) :
    Γ ⊢[PRAAx] neg (inst2 K x p ≐ zero) := by
  refine .impI (.impE h.wk ?_)
  exact (tB_at K x r p).eqTrans ((congrMul (sg_of_zero Prf.hyp0) (.eqRefl _)).eqTrans
    (zero_mul _))

/-- An element passing the test has rank `r`. -/
theorem rank_of_tB {x r p : PTm k} (h : Γ ⊢[PRAAx] neg (inst2 (tB K) x (pairT r p) ≐ zero)) :
    Γ ⊢[PRAAx] rank K x p ≐ r := by
  refine eq_of_eqb_ne (.impI (.impE h.wk ?_))
  exact (tB_at K x r p).eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))

/-- One step of the existence of the `r`-th retained element. -/
theorem ex_step {P r p : PTm k}
    (ih : Γ ⊢[PRAAx] lt r (rank K P p) ⟶ (exB (tB K) P (pairT r p) ≐ one))
    (h : Γ ⊢[PRAAx] lt r (rank K (succ P) p)) :
    Γ ⊢[PRAAx] exB (tB K) (succ P) (pairT r p) ≐ one := by
  refine .orE (lt_or_le r (rank K P p)) ?_ ?_
  · -- the witness is already below `P`
    have w := ex_elim (tB K) (.impE ih.wk (Prf.hyp0 (Γ := Γ) (φ := lt r (rank K P p))))
    exact ex_intro (tB K) (Prf.andE₂ w) (le_trans (Prf.andE₁ w) (le_succ_self P))
  · -- `rank P ≤ r < rank (P + 1)`: `P` is retained and has rank `r`
    have hs := rank_succ (Γ := le (rank K P p) r :: Γ) K P p
    refine .orE (sg_cases (inst2 K P p)) ?_ ?_
    · have e : ((sg (inst2 K P p) ≐ zero) :: le (rank K P p) r :: Γ) ⊢[PRAAx]
          rank K (succ P) p ≐ rank K P p :=
        hs.wk.eqTrans ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _))
      exact le_lt_absurd _ Prf.hyp1 (lt_congr (.eqRefl _) e h.wk.wk)
    · have e : ((sg (inst2 K P p) ≐ one) :: le (rank K P p) r :: Γ) ⊢[PRAAx]
          rank K (succ P) p ≐ succ (rank K P p) :=
        hs.wk.eqTrans ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (succ_eq_add_one _).eqSymm)
      have hle : ((sg (inst2 K P p) ≐ one) :: le (rank K P p) r :: Γ) ⊢[PRAAx]
          le r (rank K P p) :=
        (succ_monus_succ r (rank K P p)).eqSymm.eqTrans (lt_congr (.eqRefl _) e h.wk.wk)
      have hr := le_antisymm Prf.hyp1 hle
      have hk : ((sg (inst2 K P p) ≐ one) :: le (rank K P p) r :: Γ) ⊢[PRAAx]
          neg (inst2 K P p ≐ zero) :=
        .impI (one_ne_zero _ (Prf.hyp1.eqSymm.eqTrans (sg_of_zero Prf.hyp0)))
      exact ex_intro (tB K) (tB_ne_of K hk hr) (le_refl (succ P))

/-- Variables: `0 = P`, `1 = r`, `2 = p`. -/
private def exF (K : PTm 2) : Fm PTm 3 :=
  lt (var 1) (rank K (var 0) (var 2)) ⟶
    (exB (tB K) (var 0) (pairT (var 1) (var 2)) ≐ one)

private theorem ex₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] exF K := by
  ipra_ind (⟨trivial, trivial⟩) [exF, subst_lt, subst_ap2, subst_pairT]
  · exact .impI (lt_zero_absurd _ (lt_congr (.eqRefl _) (rank_zero K _) Prf.hyp0))
  · have ih : [exF K] ⊢[PRAAx] lt (var 1) (rank K (var 0) (var 2)) ⟶
        (exB (tB K) (var 0) (pairT (var 1) (var 2)) ≐ one) := Prf.hyp0
    exact .impI (ex_step K ih.wk Prf.hyp0)

/-- For `r` below the size, the `r`-th retained element exists (as a bit). -/
theorem ex_of_lt {P r p : PTm k} (h : Γ ⊢[PRAAx] lt r (rank K P p)) :
    Γ ⊢[PRAAx] exB (tB K) P (pairT r p) ≐ one := by
  have i := inst (Γ := Γ) (ex₀ K) (![P, r, p] : Fin 3 → PTm k)
  simp [exF] at i
  exact .impE i h

/-- For `r < ℓ`: `sel r < P`, `sel r` is retained, and `rank (sel r) = r`. -/
theorem sel_spec {P r p : PTm k} (h : Γ ⊢[PRAAx] lt r (rank K P p)) :
    Γ ⊢[PRAAx] lt (sel K r P p) P ⋏
      (neg (inst2 K (sel K r P p) p ≐ zero) ⋏ (rank K (sel K r P p) p ≐ r)) := by
  have w := ex_elim (tB K) (ex_of_lt K h)
  exact .andI (Prf.andE₁ w) (.andI (kept_of_tB K (Prf.andE₂ w)) (rank_of_tB K (Prf.andE₂ w)))

/-- For a retained `x < P`: `sel (rank x) = x`. -/
theorem sel_rank {P x p : PTm k} (hx : Γ ⊢[PRAAx] lt x P)
    (hk : Γ ⊢[PRAAx] neg (inst2 K x p ≐ zero)) :
    Γ ⊢[PRAAx] sel K (rank K x p) P p ≐ x := by
  have hx' := tB_ne_of K hk (.eqRefl (rank K x p))
  have w := ex_elim (tB K) (ex_intro (tB K) hx' hx)
  -- the selected element is at most `x`
  have hle : Γ ⊢[PRAAx] le (sel K (rank K x p) P p) x := by
    refine .orE (lt_or_le x (sel K (rank K x p) P p)) ?_ Prf.hyp0
    exact .botE _ (.impE hx'.wk (ex_least (tB K) Prf.hyp0))
  refine .orE (lt_or_eq_of_le hle) ?_ Prf.hyp0
  -- it cannot be smaller: it is retained and has the same rank
  have hlt := rank_lt_of_kept K (kept_of_tB K (Prf.andE₂ w)).wk
    (Prf.hyp0 (Γ := Γ) (φ := lt (sel K (rank K x p) P p) x)) (p := p)
  exact lt_irrefl (rank K x p) _ (lt_congr (rank_of_tB K (Prf.andE₂ w)).wk (.eqRefl _) hlt)

/-- The rank of a retained `x < P` is below the size. -/
theorem rank_lt_size {P x p : PTm k} (hx : Γ ⊢[PRAAx] lt x P)
    (hk : Γ ⊢[PRAAx] neg (inst2 K x p ≐ zero)) : Γ ⊢[PRAAx] lt (rank K x p) (rank K P p) :=
  rank_lt_of_kept K hk hx

end Select

/-! ## Equalizers of tables -/

section Equalizer

variable (f g : PTm 2)

/-- The agreement bit `[f(x, p) = g(x, p)]`. -/
def eqK : PTm 2 := eqb f g

theorem inst2_eqK (x p : PTm k) : inst2 (eqK f g) x p = eqb (inst2 f x p) (inst2 g x p) := by
  simp [inst2, eqK]

/-- A point of agreement is retained. -/
theorem eqK_ne {c p : PTm k} (h : Γ ⊢[PRAAx] inst2 f c p ≐ inst2 g c p) :
    Γ ⊢[PRAAx] neg (inst2 (eqK f g) c p ≐ zero) := by
  rw [inst2_eqK]
  exact .impI (one_ne_zero _ ((eqb_of_eq h.wk).eqSymm.eqTrans Prf.hyp0))

/-- A retained point is a point of agreement. -/
theorem eq_of_eqK {c p : PTm k} (h : Γ ⊢[PRAAx] neg (inst2 (eqK f g) c p ≐ zero)) :
    Γ ⊢[PRAAx] inst2 f c p ≐ inst2 g c p := by
  rw [inst2_eqK] at h
  exact eq_of_eqb_ne h

/-- The equalizer inclusion lands in the points of agreement: for `r < ℓ`,
`f(sel r) = g(sel r)` and `sel r < P`. -/
theorem equalizer_incl {P r p : PTm k} (h : Γ ⊢[PRAAx] lt r (rank (eqK f g) P p)) :
    Γ ⊢[PRAAx] lt (sel (eqK f g) r P p) P ⋏
      (inst2 f (sel (eqK f g) r P p) p ≐ inst2 g (sel (eqK f g) r P p) p) := by
  have s := sel_spec (eqK f g) h
  exact .andI (Prf.andE₁ s) (eq_of_eqK f g (Prf.andE₁ (Prf.andE₂ s)))

/-- Every cone value factors through the equalizer: for `c < P` with `f(c) = g(c)`, the
mediator `rank c` is below the size and `sel (rank c) = c`. -/
theorem equalizer_factor {P c p : PTm k} (hc : Γ ⊢[PRAAx] lt c P)
    (h : Γ ⊢[PRAAx] inst2 f c p ≐ inst2 g c p) :
    Γ ⊢[PRAAx] lt (rank (eqK f g) c p) (rank (eqK f g) P p) ⋏
      (sel (eqK f g) (rank (eqK f g) c p) P p ≐ c) :=
  .andI (rank_lt_size (eqK f g) hc (eqK_ne f g h)) (sel_rank (eqK f g) hc (eqK_ne f g h))

/-- The mediator is unique: if `v < ℓ` and `sel v = c`, then `v = rank c`. -/
theorem equalizer_unique {P v c p : PTm k} (hv : Γ ⊢[PRAAx] lt v (rank (eqK f g) P p))
    (h : Γ ⊢[PRAAx] sel (eqK f g) v P p ≐ c) : Γ ⊢[PRAAx] v ≐ rank (eqK f g) c p :=
  (Prf.andE₂ (Prf.andE₂ (sel_spec (eqK f g) hv))).eqSymm.eqTrans
    (congrAp2 (sumF (sgB (eqK f g))) h (.eqRefl _))

end Equalizer

end LeanProofs.IPRA.Foundations.FilteredEnumeration

export_ipra Foundations.FilteredEnumeration (rank_lt_size rank_mono sel_rank sel_spec)
