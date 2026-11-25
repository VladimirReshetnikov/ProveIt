import IPRADerivations.Foundations.EigenvalueBound
import IPRADerivations.Foundations.RationalRootConstant
import IPRADerivations.Core.ProdLemmas
import IPRADerivations.Core.CertificateTactics

/-!
# Integrality of a rational eigenvalue in every dimension (`ipra_presentations_to_witnesses`, `lem:integer-eigenvalue`)

Packet: `foundations/ipra_presentations_to_witnesses`, lemma `lem:integer-eigenvalue`, first
part: "Write `λ = a/b` in reduced form ... `a w_j = b ∑_i w_i A_ij`. Thus `b` divides `a w_j`,
and coprimality gives `b ∣ w_j`. ... Since `w` is primitive, there are integers `e_j` with
`∑_j e_j w_j = 1`. Therefore `b ∣ 1`. Positivity of `b` forces `b = 1`."

`Foundations/WitnessAlgebra` has dimensions `2` and `3` as polynomial certificates. Here the
dimension `D` is a variable. In natural-number form, with `ω_j = |w_j|`, `La = |a|`,
`b = b' + 1`, and the primitivity certificate split by sign (`ep_j`, `en_j` the coefficients of
`|w_j|` with positive and negative sign):

* `gB`, `gB_at`, `pt`, `sum_div`: if `b ∣ ω_j` for `j < D`, then
  `∑_{j<D} e_j ω_j = b ∑_{j<D} e_j ⌊ω_j / b⌋`;
* `eigen_integral`: from a Bezout relation between `b` and `La`, `b ∣ ω_j La` for `j < D`, and
  `∑_{j<D} ep_j ω_j = ∑_{j<D} en_j ω_j + 1`, the conclusion `b' = 0`, that is `b = 1`.

The hypothesis `b ∣ |a| |w_j|` is the absolute value of the `j`-th coordinate equation. With
`Foundations/EigenvalueBound` this is the whole lemma for one maximizing column. The
construction of the primitive vector and of its Bezout coefficients (the preceding lemma of the
packet) and `cor:eigenvalue-grid` are not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.EigenvalueIntegral

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.RationalRootDegree (Bez euclid)
open LeanProofs.IPRA.Foundations.RationalRootConstant (dvd_le shift_succ₁)
open LeanProofs.IPRA.Foundations.EigenvalueBound (wB inst2_wB mB mB_at sum_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

variable (e ω : PTm 2)

/-- The body `e(j, x) ⌊ω(j, x) / W⌋`; variables `0 = j`, `1 = ⟨W, x⟩`. -/
def gB : PTm 2 :=
  Syn.subst ![var 0, sndT (var 1)] e * quo (Syn.subst ![var 0, sndT (var 1)] ω) (fstT (var 1))

theorem gB_at (j W x : PTm k) :
    Γ ⊢[PRAAx] inst2 (gB e ω) j (pairT W x) ≐ inst2 e j x * quo (inst2 ω j x) W := by
  have e₁ : ∀ t : PTm 2,
      Syn.subst ![j, pairT W x] (Syn.subst ![(var 0 : PTm 2), sndT (var 1)] t) =
        inst2 t j (sndT (pairT W x)) := by
    intro t
    simp only [inst2, Syn.subst_subst]
    congr 1; funext l; fin_cases l <;> simp
  have h : inst2 (gB e ω) j (pairT W x) =
      inst2 e j (sndT (pairT W x)) * quo (inst2 ω j (sndT (pairT W x))) (fstT (pairT W x)) := by
    rw [← e₁ e, ← e₁ ω]
    show Syn.subst ![j, pairT W x] (gB e ω) = _
    simp [gB]
  rw [h]
  exact congrMul (congrInst2 e (.eqRefl _) (snd_pair _ _))
    (congrAp2 quoF (congrInst2 ω (.eqRefl _) (snd_pair _ _)) (fst_pair _ _))

/-- A summand with `ω_j` divisible by `b` is `b` times the summand with the quotient. -/
theorem pt {j b' x : PTm k} (hd : Γ ⊢[PRAAx] dvd (succ b') (inst2 ω j x)) :
    Γ ⊢[PRAAx] inst2 (wB e ω) j x ≐
      inst2 (mB (gB e ω)) j (pairT (succ b') (pairT (succ b') x)) := by
  rw [inst2_wB]
  ipra_lc 𝔞 (inst2 e j x) * natEq (eq_of_dvd hd) - natEq (mB_at (Γ := Γ) (gB e ω) j (succ b') (pairT (succ b') x)) -
    (𝔞 b' + 1) * natEq (gB_at (Γ := Γ) e ω j (succ b') x)

/-- `∑_{j<D} e_j ω_j = b ∑_{j<D} e_j ⌊ω_j / b⌋` when `b ∣ ω_j` for `j < D`. -/
theorem sum_div {D b' x : PTm k}
    (hall : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift D) ⟶
      dvd (succ (Syn.shift b')) (inst2 ω (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] ap2 (sumF (wB e ω)) D x ≐
      succ b' * ap2 (sumF (gB e ω)) D (pairT (succ b') x) := by
  refine (sum_congr_bounded (wB e ω) (mB (gB e ω)) x
    (pairT (succ b') (pairT (succ b') x)) D (.allI (.impI ?_))).eqTrans
    (sum_scale (gB e ω) D (succ b') (pairT (succ b') x))
  simp only [shift_pairT, shift_succ₁]
  exact pt e ω (.impE hall.allOpen.wk Prf.hyp0)

variable (ep en : PTm 2)

/-- `lem:integer-eigenvalue`, integrality, for any dimension `D`: a reduced denominator
`b = b' + 1` of an eigenvalue of an integer matrix with a primitive eigenvector is `1`. -/
theorem eigen_integral {D b' La u v x : PTm k} (hB : Γ ⊢[PRAAx] Bez b' La u v)
    (h1 : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift D) ⟶
      dvd (succ (Syn.shift b')) (inst2 ω (var 0) (Syn.shift x) * Syn.shift La)))
    (h2 : Γ ⊢[PRAAx] ap2 (sumF (wB ep ω)) D x ≐ ap2 (sumF (wB en ω)) D x + one) :
    Γ ⊢[PRAAx] b' ≐ zero := by
  -- `b ∣ ω_j` for every `j < D`, by Euclid's lemma
  have hall : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift D) ⟶
      dvd (succ (Syn.shift b')) (inst2 ω (var 0) (Syn.shift x))) := by
    refine .allI (.impI ?_)
    have hB' := hB.shift
    have eB : Fm.shift (Bez b' La u v) =
        Bez (Syn.shift b') (Syn.shift La) (Syn.shift u) (Syn.shift v) := by
      simp [Fm.shift, Syn.shift]
    rw [eB] at hB'
    exact euclid hB'.wk (.impE h1.allOpen.wk Prf.hyp0)
  -- `b X = 1 + b Y`, so `b ∣ 1`
  have eq : Γ ⊢[PRAAx] succ b' * ap2 (sumF (gB ep ω)) D (pairT (succ b') x) ≐
      one + succ b' * ap2 (sumF (gB en ω)) D (pairT (succ b') x) := by
    ipra_lc natEq h2 - natEq (sum_div ep ω hall) + natEq (sum_div en ω hall)
  have d := dvd_sub (dvd_congr eq (dvd_of_eq (w := ap2 (sumF (gB ep ω)) D (pairT (succ b') x))
    (.eqRefl _))) (dvd_of_eq (w := ap2 (sumF (gB en ω)) D (pairT (succ b') x)) (.eqRefl _))
  have l := dvd_le d (pos_of_eq_succ (c := zero) (.eqRefl _))
  exact (monus_zero b').eqSymm.eqTrans ((succ_monus_succ b' zero).eqSymm.eqTrans l)

end LeanProofs.IPRA.Foundations.EigenvalueIntegral
