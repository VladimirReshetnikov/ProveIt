import IPRADerivations.Foundations.RationalRootDegree
import IPRADerivations.Core.SumReflect
import IPRADerivations.Core.SumLemmas
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# Rational roots: the constant coefficient (`ipra_presentations_to_witnesses`, `lem:norm-rational-roots`)

Packet: `foundations/ipra_presentations_to_witnesses`, lemma `lem:norm-rational-roots`: from
(RR2) "reduction modulo `p` shows `p ∣ c_0 q^d` ... Euclid's lemma ... gives `p ∣ c_0`".

`Foundations/RationalRootDegree` has the denominator statement `q ∣ c_d` (`leading_dvd`). The
numerator statement follows by reading the homogeneous polynomial from the other end:

* `revC a`: the reversed coefficient list, `(revC a)(i, ⟨d, x⟩) = a(d ∸ i, x)` (`revC_at`);
* `reversal`: `∑_{i≤d} a_i p^i q^{d∸i} = ∑_{i≤d} a_{d∸i} q^i p^{d∸i}`, by reflecting the sum
  (`sum_reflect` of `Core/SumReflect`) and comparing the summands below `d + 1` (`rev_pt`);
* `constant_dvd`: from `∑_{i≤d} a_i p^i q^{d∸i} = ∑_{i≤d} b_i p^i q^{d∸i}` and a Bezout
  relation between `p` and `q`, `p` divides `(a_0 ∸ b_0) + (b_0 ∸ a_0)`.

With `leading_dvd` this is the whole divisibility step of the lemma in every degree.

"The coefficients are nonzero, so `|p| ≤ |c_0|` and `q ≤ |c_d|`. Thus every root occurs in the
scan":

* `dvd_le`: a divisor of a positive number is at most that number;
* `num_bound`, `den_bound`: `p ≤ |c_0|` and `q ≤ |c_d|` when those coefficients are nonzero.

The scan itself (the enumeration of candidate pairs, the exact substitution test and the list
without repetition) is not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.RationalRootConstant

open_ipra
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Foundations.RationalRootDegree

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem shift_succ₁ (t : PTm k) : Syn.shift (succ t) = succ (Syn.shift t) := by
  simp [Syn.shift]

/-- `n ∸ (n ∸ j) = j` for `j ≤ n`. -/
theorem monus_monus' {j n : PTm k} (h : Γ ⊢[PRAAx] le j n) :
    Γ ⊢[PRAAx] monus n (monus n j) ≐ j := by
  have e₁ := natEq (eq_add_of_le h)
  have hd : Γ ⊢[PRAAx] le (monus n j) n :=
    le_of_eq_add (d := j) (by apply deriveNat; ipra_simps; linear_combination e₁)
  ipra_lc e₁ - natEq (eq_add_of_le hd)

variable (a : PTm 2)

/-- The reversed coefficient list; variables `0 = i`, `1 = ⟨d, x⟩`. -/
def revC : PTm 2 := Syn.subst ![monus (fstT (var 1)) (var 0), sndT (var 1)] a

theorem revC_at (i d x : PTm k) :
    Γ ⊢[PRAAx] inst2 (revC a) i (pairT d x) ≐ inst2 a (monus d i) x := by
  have e : inst2 (revC a) i (pairT d x) =
      inst2 a (monus (fstT (pairT d x)) i) (sndT (pairT d x)) := by
    simp only [inst2, revC, Syn.subst_subst]
    congr 1; funext j; fin_cases j <;> simp
  rw [e]
  exact congrInst2 a (congrMonus (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)

/-- The reflected summand of the polynomial is the summand of the reversed polynomial. -/
theorem rev_pt {i p q d x : PTm k} (hi : Γ ⊢[PRAAx] lt i (succ d)) :
    Γ ⊢[PRAAx]
      inst2 (rflBody (tB a)) i (pairT (succ d) (pairT p (pairT q (pairT d x)))) ≐
        inst2 (tB (revC a)) i (pairT q (pairT p (pairT d (pairT d x)))) := by
  have hle : Γ ⊢[PRAAx] le i d := (succ_monus_succ i d).eqSymm.eqTrans hi
  rw [inst2_rflBody]
  have l₀ : Γ ⊢[PRAAx]
      inst2 (tB a) (monus (fstT (pairT (succ d) (pairT p (pairT q (pairT d x))))) (succ i))
          (sndT (pairT (succ d) (pairT p (pairT q (pairT d x))))) ≐
        inst2 (tB a) (monus d i) (pairT p (pairT q (pairT d x))) :=
    congrInst2 (tB a)
      ((congrMonus (fst_pair _ _) (.eqRefl _)).eqTrans (succ_monus_succ d i)) (snd_pair _ _)
  ipra_lc natEq (l₀.eqTrans (tB_at a (monus d i) p q d x)) - natEq (tB_at (Γ := Γ) (revC a) i q p d (pairT d x)) +
    𝔞 (pw p (monus d i)) * 𝔞 (inst2 a (monus d i) x) * natEq (congrPw (.eqRefl q) (monus_monus' hle)) -
    𝔞 (pw p (monus d i)) * 𝔞 (pw q i) * natEq (revC_at (Γ := Γ) a i d x)

/-- Reading the homogeneous polynomial from the other end. -/
theorem reversal (p q d x : PTm k) :
    Γ ⊢[PRAAx] P a (succ d) p q d x ≐ P (revC a) (succ d) q p d (pairT d x) := by
  refine (sum_reflect (tB a) (succ d) _).eqTrans
    (sum_congr_bounded (rflBody (tB a)) (tB (revC a)) _ _ (succ d) (.allI (.impI ?_)))
  simp only [shift_pairT, shift_succ₁]
  exact rev_pt a Prf.hyp0

variable (b : PTm 2)

/-- `lem:norm-rational-roots`, the numerator: if
`∑_{i≤d} a_i p^i q^{d∸i} = ∑_{i≤d} b_i p^i q^{d∸i}` and `p`, `q` are coprime, then `p` divides
`(a_0 ∸ b_0) + (b_0 ∸ a_0)`. -/
theorem constant_dvd {p' q u v d x : PTm k} (hB : Γ ⊢[PRAAx] Bez p' q u v)
    (hE : Γ ⊢[PRAAx] P a (succ d) (succ p') q d x ≐ P b (succ d) (succ p') q d x) :
    Γ ⊢[PRAAx] dvd (succ p')
      (monus (inst2 a zero x) (inst2 b zero x) + monus (inst2 b zero x) (inst2 a zero x)) := by
  have hE' : Γ ⊢[PRAAx] P (revC a) (succ d) q (succ p') d (pairT d x) ≐
      P (revC b) (succ d) q (succ p') d (pairT d x) :=
    (reversal a (succ p') q d x).eqSymm.eqTrans (hE.eqTrans (reversal b (succ p') q d x))
  have l := leading_dvd (revC a) (revC b) hB hE'
  have ea : Γ ⊢[PRAAx] inst2 (revC a) d (pairT d x) ≐ inst2 a zero x :=
    (revC_at a d d x).eqTrans (congrInst2 a (le_refl d) (.eqRefl _))
  have eb : Γ ⊢[PRAAx] inst2 (revC b) d (pairT d x) ≐ inst2 b zero x :=
    (revC_at b d d x).eqTrans (congrInst2 b (le_refl d) (.eqRefl _))
  exact dvd_congr (congrAdd (congrMonus ea eb) (congrMonus eb ea)) l

/-! ## The bounds of the scan -/

/-- A divisor of a positive number is at most that number. -/
theorem dvd_le {m' C : PTm k} (h : Γ ⊢[PRAAx] dvd (succ m') C)
    (hC : Γ ⊢[PRAAx] C ≐ succ (pred C)) : Γ ⊢[PRAAx] le (succ m') C := by
  have e := eq_of_dvd h
  refine .orE (zero_or_succ (quo C (succ m'))) ?_ ?_
  · -- a zero cofactor would make `C` zero
    have e' := natEq (e.wk (ψ := quo C (succ m') ≐ zero))
    have c0 : ((quo C (succ m') ≐ zero) :: Γ) ⊢[PRAAx] C ≐ zero := by
      ipra_lc e' + (𝔞 m' + 1) * natEq (Prf.hyp0 (Γ := Γ) (φ := quo C (succ m') ≐ zero))
    exact succ_ne_zero' _ (hC.wk.eqSymm.eqTrans c0)
  · have s := natEq (Prf.hyp0 (Γ := Γ)
      (φ := quo C (succ m') ≐ succ (pred (quo C (succ m')))))
    have e' := natEq (e.wk (ψ := quo C (succ m') ≐ succ (pred (quo C (succ m')))))
    refine le_of_eq_add (d := succ m' * pred (quo C (succ m'))) ?_
    ipra_lc e' + (𝔞 m' + 1) * s

/-- The numerator of a root is bounded by the absolute value of a nonzero constant
coefficient: `p ≤ |c_0|`. -/
theorem num_bound {p' q u v d x : PTm k} (hB : Γ ⊢[PRAAx] Bez p' q u v)
    (hE : Γ ⊢[PRAAx] P a (succ d) (succ p') q d x ≐ P b (succ d) (succ p') q d x)
    (hne : Γ ⊢[PRAAx]
      monus (inst2 a zero x) (inst2 b zero x) + monus (inst2 b zero x) (inst2 a zero x) ≐
        succ (pred (monus (inst2 a zero x) (inst2 b zero x) +
          monus (inst2 b zero x) (inst2 a zero x)))) :
    Γ ⊢[PRAAx] le (succ p')
      (monus (inst2 a zero x) (inst2 b zero x) + monus (inst2 b zero x) (inst2 a zero x)) :=
  dvd_le (constant_dvd a b hB hE) hne

/-- The denominator of a root is bounded by the absolute value of a nonzero leading
coefficient: `q ≤ |c_d|`. -/
theorem den_bound {p q' u v d x : PTm k} (hB : Γ ⊢[PRAAx] Bez q' p u v)
    (hE : Γ ⊢[PRAAx] P a (succ d) p (succ q') d x ≐ P b (succ d) p (succ q') d x)
    (hne : Γ ⊢[PRAAx]
      monus (inst2 a d x) (inst2 b d x) + monus (inst2 b d x) (inst2 a d x) ≐
        succ (pred (monus (inst2 a d x) (inst2 b d x) + monus (inst2 b d x) (inst2 a d x)))) :
    Γ ⊢[PRAAx] le (succ q')
      (monus (inst2 a d x) (inst2 b d x) + monus (inst2 b d x) (inst2 a d x)) :=
  dvd_le (leading_dvd a b hB hE) hne

end LeanProofs.IPRA.Foundations.RationalRootConstant
