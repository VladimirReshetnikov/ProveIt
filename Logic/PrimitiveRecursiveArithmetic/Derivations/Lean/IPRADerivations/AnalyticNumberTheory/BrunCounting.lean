import IPRADerivations.Foundations.ChineseRemainder
import IPRADerivations.Probability.MedianCounts
import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.LinearCombination

/-!
# Counting along residue classes: Brun's finite counting error

Packet: `brun_ipra_2026-11-15`, `sections/02_finite_arithmetic.tex`, Lemma `lem:count-error`. For a
modulus `D = d' + 1` and a weight `f(t, p) ≥ 0` on residues `t < D` (for Brun, the indicator of the
`ρ(D)` roots of `n(n + 2) ≡ 0`), put

  `A(X) = ∑_{n<X} f(n mod D)`,   `ρ = A(D) = ∑_{t<D} f(t)`.

* `block`: `A(M + D) = A(M) + ρ`, since `n ↦ n mod D` has period `D`;
* `blocks`: `A(D q + r) = q ρ + A(r)`;
* `partial_le`: `A(r) ≤ ρ` for `r ≤ D`;
* `count_upper`, `count_lower` (`lem:count-error`): `|D A(X) − X ρ| ≤ D ρ`, i.e.
  `|A(X) − X ρ/D| ≤ ρ`, as the two cleared inequalities `D A(X) ≤ X ρ + D ρ` and
  `X ρ ≤ D A(X) + D ρ`.

The counting window here is `0 ≤ n < X`; the packet's window `1 ≤ n ≤ X` is the same statement for
the shifted weight.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.BrunCounting

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.ChineseRemainder (rem_eq_of_eq')
open LeanProofs.IPRA.Probability.MedianCounts (subst_data)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

section Weight

variable (f : PTm 2)

/-- `f(n mod fst y, snd y)`. -/
def gB : PTm 2 := Syn.subst ![rem (var 0) (fstT (var 1)), sndT (var 1)] f

theorem inst2_g (i y : PTm n) : inst2 (gB f) i y = inst2 f (rem i (fstT y)) (sndT y) := by
  simp only [inst2, gB, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

theorem g_at (i D p : PTm n) : Γ ⊢[PRAAx] inst2 (gB f) i (pairT D p) ≐ inst2 f (rem i D) p := by
  rw [inst2_g]
  exact congrInst2 f (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (snd_pair _ _)

/-- `A(X) = ∑_{n<X} f(n mod D)`. -/
abbrev A (X D p : PTm n) : PTm n := ap2 (sumF (gB f)) X (pairT D p)

theorem g_period (M d' p : PTm n) :
    Γ ⊢[PRAAx] inst2 (gB f) (M + succ d') (pairT (succ d') p) ≐ inst2 (gB f) M (pairT (succ d') p) := by
  refine (g_at f _ _ _).eqTrans (.eqTrans ?_ (g_at f _ _ _).eqSymm)
  exact congrInst2 f (rem_eq_of_eq' (k₁ := zero) (k₂ := one) (by ipra_ring)) (.eqRefl _)

theorem block_base (d' p : PTm n) :
    Γ ⊢[PRAAx] A f (zero + succ d') (succ d') p ≐ A f zero (succ d') p + A f (succ d') (succ d') p := by
  ipra_lc natEq (congrAp2 (sumF (gB f)) (zero_add (Γ := Γ) (succ d')) (.eqRefl (pairT (succ d') p))) -
    natEq (sum_zero (Γ := Γ) (gB f) (pairT (succ d') p))

theorem block_step {M d' p : PTm n}
    (ih : Γ ⊢[PRAAx] A f (M + succ d') (succ d') p ≐ A f M (succ d') p + A f (succ d') (succ d') p) :
    Γ ⊢[PRAAx] A f (succ M + succ d') (succ d') p ≐ A f (succ M) (succ d') p + A f (succ d') (succ d') p := by
  ipra_lc natEq (congrAp2 (sumF (gB f)) (succ_add (Γ := Γ) M (succ d')) (.eqRefl (pairT (succ d') p))) +
    natEq (sum_succ' (Γ := Γ) (gB f) (M + succ d') (pairT (succ d') p)) + natEq ih +
    natEq (g_period (Γ := Γ) f M d' p) - natEq (sum_succ' (Γ := Γ) (gB f) M (pairT (succ d') p))

/-- Variables: `0 = M`, `1 = d'`, `2 = p`. -/
private abbrev blockF : Fm PTm 3 :=
  ap2 (sumF (gB f)) (var 0 + succ (var 1)) (pairT (succ (var 1)) (var 2)) ≐
    ap2 (sumF (gB f)) (var 0) (pairT (succ (var 1)) (var 2)) +
      ap2 (sumF (gB f)) (succ (var 1)) (pairT (succ (var 1)) (var 2))

private theorem block₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] blockF f := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_add, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      inst_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact block_base f _ _
  · simp only [Fm.subst_eq, PTm.subst_add, subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero, repl_one,
      repl_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact block_step f Prf.hyp0

/-- `A(M + D) = A(M) + ρ`. -/
theorem block (M d' p : PTm n) :
    Γ ⊢[PRAAx] A f (M + succ d') (succ d') p ≐ A f M (succ d') p + A f (succ d') (succ d') p := by
  have h := inst (Γ := Γ) (block₀ f) (![M, d', p] : Fin 3 → PTm n)
  simpa using h

theorem blocks_base (r d' p : PTm n) :
    Γ ⊢[PRAAx] A f (succ d' * zero + r) (succ d') p ≐ zero * A f (succ d') (succ d') p + A f r (succ d') p := by
  have ei : Γ ⊢[PRAAx] succ d' * zero + r ≐ r := by ipra_ring
  ipra_lc natEq (congrAp2 (sumF (gB f)) ei (.eqRefl (pairT (succ d') p)))

theorem blocks_step {q r d' p : PTm n}
    (ih : Γ ⊢[PRAAx] A f (succ d' * q + r) (succ d') p ≐ q * A f (succ d') (succ d') p + A f r (succ d') p) :
    Γ ⊢[PRAAx] A f (succ d' * succ q + r) (succ d') p ≐ succ q * A f (succ d') (succ d') p + A f r (succ d') p := by
  have ei : Γ ⊢[PRAAx] succ d' * succ q + r ≐ (succ d' * q + r) + succ d' := by ipra_ring
  ipra_lc natEq (congrAp2 (sumF (gB f)) ei (.eqRefl (pairT (succ d') p))) +
    natEq (block (Γ := Γ) f (succ d' * q + r) d' p) + natEq ih

/-- Variables: `0 = q`, `1 = r`, `2 = d'`, `3 = p`. -/
private abbrev blocksF : Fm PTm 4 :=
  ap2 (sumF (gB f)) (succ (var 2) * var 0 + var 1) (pairT (succ (var 2)) (var 3)) ≐
    var 0 * ap2 (sumF (gB f)) (succ (var 2)) (pairT (succ (var 2)) (var 3)) +
      ap2 (sumF (gB f)) (var 1) (pairT (succ (var 2)) (var 3))

private theorem blocks₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] blocksF f := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, inst_two, inst_three, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact blocks_base f _ _ _
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero,
      repl_one, repl_two, repl_three, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact blocks_step f Prf.hyp0

/-- `A(D q + r) = q ρ + A(r)`. -/
theorem blocks (q r d' p : PTm n) :
    Γ ⊢[PRAAx] A f (succ d' * q + r) (succ d') p ≐ q * A f (succ d') (succ d') p + A f r (succ d') p := by
  have h := inst (Γ := Γ) (blocks₀ f) (![q, r, d', p] : Fin 4 → PTm n)
  simpa using h

/-- `A(r) ≤ ρ` for `r ≤ D`. -/
theorem partial_le {r D : PTm n} (p : PTm n) (h : Γ ⊢[PRAAx] le r D) : Γ ⊢[PRAAx] le (A f r D p) (A f D D p) := by
  have sp := sum_split (Γ := Γ) (gB f) r (monus D r) (pairT D p)
  refine le_of_eq_add (d := ap2 (sumF (offB (gB f))) (monus D r) (pairT r (pairT D p))) ?_
  exact (congrAp2 (sumF (gB f)) (eq_add_of_le h) (.eqRefl _)).eqTrans sp

/-- `lem:count-error`, upper half: `D A(X) ≤ X ρ + D ρ`. -/
theorem count_upper (X d' p : PTm n) :
    Γ ⊢[PRAAx] le (succ d' * A f X (succ d') p) (X * A f (succ d') (succ d') p + succ d' * A f (succ d') (succ d') p) := by
  have dm := div_mod (Γ := Γ) X d'
  have ex := Prf.andE₁ dm
  have hr := le_of_lt (Prf.andE₂ dm)
  have rl := natEq (eq_add_of_le hr)
  refine le_of_eq_add (d := succ d' * monus (A f (succ d') (succ d') p) (A f (rem X (succ d')) (succ d') p) +
    rem X (succ d') * A f (succ d') (succ d') p) ?_
  ipra_lc 𝔞 (A f (succ d') (succ d') p) * natEq ex -
    (𝔞 d' + 1) * natEq ((congrAp2 (sumF (gB f)) ex (.eqRefl _)).eqTrans (blocks (Γ := Γ) f (quo X (succ d')) (rem X (succ d')) d' p)) +
    (𝔞 d' + 1) * natEq (eq_add_of_le (partial_le f p hr))

/-- `lem:count-error`, lower half: `X ρ ≤ D A(X) + D ρ`. -/
theorem count_lower (X d' p : PTm n) :
    Γ ⊢[PRAAx] le (X * A f (succ d') (succ d') p) (succ d' * A f X (succ d') p + succ d' * A f (succ d') (succ d') p) := by
  have dm := div_mod (Γ := Γ) X d'
  have ex := Prf.andE₁ dm
  have hr := le_of_lt (Prf.andE₂ dm)
  refine le_of_eq_add (d := succ d' * A f (rem X (succ d')) (succ d') p +
    monus (succ d') (rem X (succ d')) * A f (succ d') (succ d') p) ?_
  ipra_lc -𝔞 (A f (succ d') (succ d') p) * natEq ex +
    (𝔞 d' + 1) * natEq ((congrAp2 (sumF (gB f)) ex (.eqRefl _)).eqTrans (blocks (Γ := Γ) f (quo X (succ d')) (rem X (succ d')) d' p)) +
    𝔞 (A f (succ d') (succ d') p) * natEq (eq_add_of_le hr)

end Weight

end LeanProofs.IPRA.AnalyticNumberTheory.BrunCounting
