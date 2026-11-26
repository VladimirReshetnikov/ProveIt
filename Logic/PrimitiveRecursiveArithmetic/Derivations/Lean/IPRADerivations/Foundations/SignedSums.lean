import IPRADerivations.Core.IntCertificates
import IPRADerivations.Core.Fubini
import IPRADerivations.Core.SumReflect
import IPRADerivations.Analysis.RationalArithmetic.Powers.PowerSums

/-!
# Bounded sums of signed bodies

A reusable layer for finite sums of integer-valued terms whose length is an object-level number.

`Core/Integers` reads a pair of natural terms `⟨pos, neg⟩` (`ZT`) as the integer `pos − neg` in the ring of
differences `Groth (Q Γ)`. A *signed body* `ZB` is a pair of natural bodies; its value at `(i, x)` and its bounded
sum `Σ_{i<N} b(i, x)` are integer terms, the sum being the pair of the two natural sums. The lemmas below state the
usual rules as equations between evaluations `ZT.toZ`, so that an argument about signed finite sums (for instance
sieve weights `λ_d = λ_d⁺ − λ_d⁻`, as in `analytic-number-theory/prime_distribution_ipra`, `05_sieve.tex`) is a
commutative-ring computation followed by `ZT.derive` or an order certificate of `Core/IntCertificates`.

* `mixB`, `mix_at`, `sum_mix`: `Σ_{i<N} (f(i, x) + g(i, y)) = Σ_{i<N} f(i, x) + Σ_{i<N} g(i, y)` for two natural
  bodies with separate parameters;
* `ZB.val`, `ZB.sum`, `ZB.toZ_sum_zero`, `ZB.toZ_sum_succ`: the recursion of the signed sum;
* `ZB.toZ_sum_add`, `ZB.toZ_sum_neg`, `ZB.toZ_sum_zeroB`: additivity, negation and the zero body;
* `ZB.toZ_sum_congr`: sums agree when the values agree as integers below the bound (the two bodies need not agree
  in their positive and negative parts separately, and may have different parameters);
* `ZB.sum_zle`: monotonicity for the integer order `zle`;
* `ZB3.toZ_fubini`: exchange of a signed double sum.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA.Analysis.PowerSums (sum_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Two natural bodies with separate parameters -/

/-- `f(i, fst z)`. -/
def fstB (f : PTm 2) : PTm 2 := Syn.subst ![var 0, fstT (var 1)] f
/-- `f(i, snd z)`. -/
def sndB (f : PTm 2) : PTm 2 := Syn.subst ![var 0, sndT (var 1)] f

theorem inst2_fstB (f : PTm 2) (i z : PTm n) : inst2 (fstB f) i z = inst2 f i (fstT z) := by
  simp only [inst2, fstB, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

theorem inst2_sndB (f : PTm 2) (i z : PTm n) : inst2 (sndB f) i z = inst2 f i (sndT z) := by
  simp only [inst2, sndB, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

/-- `f(i, fst z) + g(i, snd z)`. -/
def mixB (f g : PTm 2) : PTm 2 := addBody (fstB f) (sndB g)

theorem mix_at (f g : PTm 2) (i x y : PTm n) :
    Γ ⊢[PRAAx] inst2 (mixB f g) i (pairT x y) ≐ inst2 f i x + inst2 g i y := by
  rw [mixB, inst2_addBody, inst2_fstB, inst2_sndB]
  exact congrAdd (congrInst2 f (.eqRefl _) (fst_pair x y)) (congrInst2 g (.eqRefl _) (snd_pair x y))

/-- `Σ_{i<N} (f(i, x) + g(i, y)) = Σ_{i<N} f(i, x) + Σ_{i<N} g(i, y)`. -/
theorem sum_mix (f g : PTm 2) (N x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (mixB f g)) N (pairT x y) ≐ ap2 (sumF f) N x + ap2 (sumF g) N y := by
  have cf : Γ ⊢[PRAAx] ap2 (sumF (fstB f)) N (pairT x y) ≐ ap2 (sumF f) N x := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, inst2_fstB]
    exact congrInst2 f (.eqRefl _) (fst_pair _ _)
  have cg : Γ ⊢[PRAAx] ap2 (sumF (sndB g)) N (pairT x y) ≐ ap2 (sumF g) N y := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, inst2_sndB]
    exact congrInst2 g (.eqRefl _) (snd_pair _ _)
  exact (sum_add (fstB f) (sndB g) N (pairT x y)).eqTrans (congrAdd cf cg)

/-! ## Signed bodies -/

/-- A signed body `pos − neg` over `0 = i`, `1 = x`. -/
structure ZB where
  /-- The positive part. -/
  pos : PTm 2
  /-- The negative part. -/
  neg : PTm 2

namespace ZB

/-- The value `b(i, x)`. -/
def val (b : ZB) (i x : PTm n) : ZT n := ⟨inst2 b.pos i x, inst2 b.neg i x⟩

/-- The bounded sum `Σ_{i<N} b(i, x)`. -/
def sum (b : ZB) (N x : PTm n) : ZT n := ⟨ap2 (sumF b.pos) N x, ap2 (sumF b.neg) N x⟩

instance : Add ZB := ⟨fun b c => ⟨addBody b.pos c.pos, addBody b.neg c.neg⟩⟩
instance : Neg ZB := ⟨fun b => ⟨b.neg, b.pos⟩⟩
instance : Zero ZB := ⟨⟨zero, zero⟩⟩

/-- A natural body as a signed body. -/
def ofNat (f : PTm 2) : ZB := ⟨f, zero⟩

theorem toZ_val (b : ZB) (i x : PTm n) :
    ZT.toZ Γ (b.val i x) = Groth.ι (Q.mk Γ (inst2 b.pos i x)) - Groth.ι (Q.mk Γ (inst2 b.neg i x)) := rfl

theorem toZ_sum (b : ZB) (N x : PTm n) :
    ZT.toZ Γ (b.sum N x) =
      Groth.ι (Q.mk Γ (ap2 (sumF b.pos) N x)) - Groth.ι (Q.mk Γ (ap2 (sumF b.neg) N x)) := rfl

/-- The empty sum. -/
theorem toZ_sum_zero (b : ZB) (x : PTm n) : ZT.toZ Γ (b.sum zero x) = 0 := by
  have hp := natEq (sum_zero (Γ := Γ) b.pos x)
  have hn := natEq (sum_zero (Γ := Γ) b.neg x)
  simp only [Q.mk_zero, map_zero] at hp hn
  rw [toZ_sum]
  linear_combination hp - hn

/-- One more term. -/
theorem toZ_sum_succ (b : ZB) (N x : PTm n) :
    ZT.toZ Γ (b.sum (succ N) x) = ZT.toZ Γ (b.sum N x) + ZT.toZ Γ (b.val N x) := by
  have hp := natEq (sum_succ' (Γ := Γ) b.pos N x)
  have hn := natEq (sum_succ' (Γ := Γ) b.neg N x)
  simp only [Q.mk_add, map_add] at hp hn
  rw [toZ_sum, toZ_sum, toZ_val]
  linear_combination hp - hn

/-- Additivity. -/
theorem toZ_sum_add (b c : ZB) (N x : PTm n) :
    ZT.toZ Γ ((b + c).sum N x) = ZT.toZ Γ (b.sum N x) + ZT.toZ Γ (c.sum N x) := by
  have hp := natEq (sum_add (Γ := Γ) b.pos c.pos N x)
  have hn := natEq (sum_add (Γ := Γ) b.neg c.neg N x)
  simp only [Q.mk_add, map_add] at hp hn
  show Groth.ι (Q.mk Γ (ap2 (sumF (addBody b.pos c.pos)) N x)) -
      Groth.ι (Q.mk Γ (ap2 (sumF (addBody b.neg c.neg)) N x)) =
    (Groth.ι (Q.mk Γ (ap2 (sumF b.pos) N x)) - Groth.ι (Q.mk Γ (ap2 (sumF b.neg) N x))) +
      (Groth.ι (Q.mk Γ (ap2 (sumF c.pos) N x)) - Groth.ι (Q.mk Γ (ap2 (sumF c.neg) N x)))
  linear_combination hp - hn

/-- Negation. -/
theorem toZ_sum_neg (b : ZB) (N x : PTm n) : ZT.toZ Γ ((-b).sum N x) = -ZT.toZ Γ (b.sum N x) := by
  show Groth.ι (Q.mk Γ (ap2 (sumF b.neg) N x)) - Groth.ι (Q.mk Γ (ap2 (sumF b.pos) N x)) =
    -(Groth.ι (Q.mk Γ (ap2 (sumF b.pos) N x)) - Groth.ι (Q.mk Γ (ap2 (sumF b.neg) N x)))
  ring

/-- The zero body. -/
theorem toZ_sum_zeroB (N x : PTm n) : ZT.toZ Γ ((0 : ZB).sum N x) = 0 := by
  show Groth.ι (Q.mk Γ (ap2 (sumF (zero : PTm 2)) N x)) - Groth.ι (Q.mk Γ (ap2 (sumF (zero : PTm 2)) N x)) = 0
  ring

/-- A natural body. -/
theorem toZ_sum_ofNat (f : PTm 2) (N x : PTm n) :
    ZT.toZ Γ ((ofNat f).sum N x) = Groth.ι (Q.mk Γ (ap2 (sumF f) N x)) := by
  have hz : Γ ⊢[PRAAx] ap2 (sumF (zero : PTm 2)) N x ≐ zero := by
    refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
    have e : inst2 (zero : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift x) = zero := by simp [inst2]
    rw [e]
    exact .eqRefl _
  have h := natEq hz
  simp only [Q.mk_zero, map_zero] at h
  show Groth.ι (Q.mk Γ (ap2 (sumF f) N x)) - Groth.ι (Q.mk Γ (ap2 (sumF (zero : PTm 2)) N x)) =
    Groth.ι (Q.mk Γ (ap2 (sumF f) N x))
  linear_combination -h

/-- Signed sums agree when the values agree as integers below the bound. -/
theorem toZ_sum_congr (b c : ZB) (x y N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      ZT.eq (b.val (var 0) (Syn.shift x)) (c.val (var 0) (Syn.shift y)))) :
    ZT.toZ Γ (b.sum N x) = ZT.toZ Γ (c.sum N y) := by
  have e : Γ ⊢[PRAAx] ap2 (sumF (mixB b.pos c.neg)) N (pairT x y) ≐
      ap2 (sumF (mixB c.pos b.neg)) N (pairT y x) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, shift_pairT]
    have hv : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
        inst2 b.pos (var 0) (Syn.shift x) + inst2 c.neg (var 0) (Syn.shift y) ≐
          inst2 c.pos (var 0) (Syn.shift y) + inst2 b.neg (var 0) (Syn.shift x) :=
      Prf.impE h.allOpen.wk Prf.hyp0
    exact (mix_at _ _ _ _ _).eqTrans (hv.eqTrans (mix_at _ _ _ _ _).eqSymm)
  have a := natEq ((sum_mix (Γ := Γ) b.pos c.neg N x y).eqSymm.eqTrans (e.eqTrans (sum_mix c.pos b.neg N y x)))
  simp only [Q.mk_add, map_add] at a
  rw [toZ_sum, toZ_sum]
  linear_combination a

/-- Signed sums are monotone: `b(i, x) ≤ c(i, x)` for `i < N` gives `Σ b ≤ Σ c`. -/
theorem sum_zle (b c : ZB) (x N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      zle (b.val (var 0) (Syn.shift x)) (c.val (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] zle (b.sum N x) (c.sum N x) := by
  have l : Γ ⊢[PRAAx] le (ap2 (sumF (addBody b.pos c.neg)) N x) (ap2 (sumF (addBody c.pos b.neg)) N x) := by
    refine sum_le _ _ _ _ (.allI (.impI ?_))
    rw [inst2_addBody, inst2_addBody]
    exact Prf.impE h.allOpen.wk Prf.hyp0
  exact le_congr (sum_add b.pos c.neg N x) (sum_add c.pos b.neg N x) l

end ZB

/-! ## Signed double sums -/

/-- A signed body over `0 = i`, `1 = j`, `2 = x`. -/
structure ZB3 where
  /-- The positive part. -/
  pos : PTm 3
  /-- The negative part. -/
  neg : PTm 3

namespace ZB3

/-- The row sums `Σ_{j < fst y} a(i, j, snd y)` as a signed body. -/
def rows (a : ZB3) : ZB := ⟨oB a.pos, oB a.neg⟩
/-- The column sums `Σ_{i < fst y} a(i, j, snd y)` as a signed body. -/
def cols (a : ZB3) : ZB := ⟨pB a.pos, pB a.neg⟩

/-- `Σ_{i<M} Σ_{j<N} a(i, j, x) = Σ_{j<N} Σ_{i<M} a(i, j, x)` for a signed body. -/
theorem toZ_fubini (a : ZB3) (M N x : PTm n) :
    ZT.toZ Γ (a.rows.sum M (pairT N x)) = ZT.toZ Γ (a.cols.sum N (pairT M x)) := by
  have hp := natEq (fubini (Γ := Γ) a.pos M N x)
  have hn := natEq (fubini (Γ := Γ) a.neg M N x)
  show Groth.ι (Q.mk Γ (ap2 (sumF (oB a.pos)) M (pairT N x))) -
      Groth.ι (Q.mk Γ (ap2 (sumF (oB a.neg)) M (pairT N x))) =
    Groth.ι (Q.mk Γ (ap2 (sumF (pB a.pos)) N (pairT M x))) -
      Groth.ι (Q.mk Γ (ap2 (sumF (pB a.neg)) N (pairT M x)))
  linear_combination hp - hn

end ZB3

end LeanProofs.IPRA
