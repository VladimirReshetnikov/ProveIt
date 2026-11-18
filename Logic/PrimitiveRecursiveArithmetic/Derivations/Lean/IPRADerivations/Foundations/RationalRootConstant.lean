import IPRADerivations.Foundations.RationalRootDegree
import IPRADerivations.Core.SumReflect
import IPRADerivations.Core.SumLemmas

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

With `leading_dvd` this is the whole divisibility step of the lemma in every degree. The bound
`B(H)`, the scan and the completeness of the root list are not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.RationalRootConstant

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Foundations.RationalRootDegree
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

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
  have e₂ := natEq (eq_add_of_le hd)
  apply deriveNat; ipra_simps
  linear_combination e₁ - e₂

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
  have e₁ := natEq (l₀.eqTrans (tB_at a (monus d i) p q d x))
  have e₂ := natEq (tB_at (Γ := Γ) (revC a) i q p d (pairT d x))
  have e₃ := natEq (revC_at (Γ := Γ) a i d x)
  have e₄ := natEq (congrPw (.eqRefl q) (monus_monus' hle))
  apply deriveNat; ipra_simps
  linear_combination e₁ - e₂ + 𝔞 (pw p (monus d i)) * 𝔞 (inst2 a (monus d i) x) * e₄ -
    𝔞 (pw p (monus d i)) * 𝔞 (pw q i) * e₃

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

end LeanProofs.IPRA.Foundations.RationalRootConstant
