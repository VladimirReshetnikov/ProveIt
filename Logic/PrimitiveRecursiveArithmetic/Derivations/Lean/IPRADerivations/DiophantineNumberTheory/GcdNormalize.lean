import IPRADerivations.DiophantineNumberTheory.GcdList
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# Normalizing a vector by its gcd

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Lemma `lem:normalize`: "Every nonzero integral
vector `v` has a primitive representative `norm(v)`, obtained by dividing by `g = gcd(|v_0|, …, |v_n|)` ...
Normalization is primitive recursive and never increases the maximum absolute coordinate." Here for vectors of
any length with natural entries (`GcdList.gv` is `g`).

* `gcd_zero_zero`, `gv_all_zero`: the gcd of a zero vector is `0`;
* `q_at`: the quotient vector `q_i = f_i / g`, as a body over `⟨N, x⟩`;
* `f_eq`: `f_i = g q_i` for `i < N`;
* `q_le`: `q_i ≤ f_i` (the height does not increase);
* `gv_quotients`: if `g ≥ 1` then `gcd(q_0, …, q_{N−1}) = 1`, i.e. the quotient vector is primitive.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.GcdNormalize

open_ipra
open LeanProofs.IPRA.DiophantineNumberTheory.GcdList (gv gv_zero gv_succ gv_dvd gv_greatest gv_eq_zero)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' dvd_of_eq' dvd_le')
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem congrGcd {a a' b b' : PTm k} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] gcd a b ≐ gcd a' b' := by
  have h := Prf.eqCongr (Γ := Γ) (gcd (var 0) (var 1) : PTm 2) (σ := ![a, b]) (σ' := ![a', b'])
    (fun j => by fin_cases j <;> assumption)
  simp only [subst_ex2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    ConciseIPRA.PTm.subst_succ] at h
  exact h

theorem quo_le_of {x g q : PTm k} (hg : Γ ⊢[PRAAx] g ≐ succ (pred g)) (h : Γ ⊢[PRAAx] x ≐ g * q) :
    Γ ⊢[PRAAx] le q x := by
  have e := natEq h; have eg := natEq hg
  ipra_le 𝔞 (pred g) * 𝔞 q using linear_combination e + 𝔞 q * eg

theorem gcd_zero_zero : Γ ⊢[PRAAx] gcd (zero : PTm k) zero ≐ zero := by
  ipra_lc natEq (ex_succ (Γ := Γ) zero ![(zero : PTm k), zero]) +
    𝔞 (sg (ey zero ![(zero : PTm k), zero])) * natEq (ey_zero (Γ := Γ) (zero : PTm k) zero) +
    𝔞 (monus one (sg (ey zero ![(zero : PTm k), zero]))) * natEq (ex_zero (Γ := Γ) (zero : PTm k) zero)

/-- The gcd of a zero vector is `0`. -/
theorem gv_all_zero (f : PTm 2) {N x : PTm k}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ inst2 f (var 0) (Syn.shift x) ≐ zero)) :
    Γ ⊢[PRAAx] gv f N x ≐ zero := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶ gv f (var 0) (Syn.shift x) ≐ zero) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact .impI (gv_zero f x)
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      let Δ := le (succ (var 0)) (Syn.shift N) ::
        (le (var 0) (Syn.shift N) ⟶ gv f (var 0) (Syn.shift x) ≐ zero) :: Γ.map Fm.shift
      have hle : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) := le_trans (le_succ_self _) Prf.hyp0
      have ih : Δ ⊢[PRAAx] gv f (var 0) (Syn.shift x) ≐ zero := Prf.impE Prf.hyp1 hle
      have hf : Δ ⊢[PRAAx] inst2 f (var 0) (Syn.shift x) ≐ zero := Prf.impE h.allOpen.wk.wk Prf.hyp0
      exact (gv_succ f (var 0) (Syn.shift x)).eqTrans ((congrGcd ih hf).eqTrans gcd_zero_zero)
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h2
  exact Prf.impE h2 (le_refl N)

/-- The quotient vector `q_i = f_i / g`, over `0 = i`, `1 = ⟨N, x⟩`. -/
abbrev qBody (f : PTm 2) : PTm 2 :=
  quo (inst2 f (var 0) (sndT (var 1))) (gv f (fstT (var 1)) (sndT (var 1)))

theorem q_at (f : PTm 2) (i N x : PTm k) :
    Γ ⊢[PRAAx] inst2 (qBody f) i (pairT N x) ≐ quo (inst2 f i x) (gv f N x) := by
  have h : inst2 (qBody f) i (pairT N x) =
      quo (inst2 f i (sndT (pairT N x))) (gv f (fstT (pairT N x)) (sndT (pairT N x))) := by
    rw [show inst2 (qBody f) i (pairT N x) = Syn.subst ![i, pairT N x] (qBody f) from rfl]
    simp
  rw [h]
  exact congrAp2 quoF (congrInst2 f (.eqRefl _) (snd_pair _ _)) (congrAp2 _ (fst_pair _ _) (snd_pair _ _))

/-- `f_i = g q_i` for `i < N`, when `g ≥ 1`. -/
theorem f_eq (f : PTm 2) {i N x : PTm k} (hG : Γ ⊢[PRAAx] gv f N x ≐ succ (pred (gv f N x)))
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] inst2 f i x ≐ gv f N x * inst2 (qBody f) i (pairT N x) :=
  (eq_of_dvd' hG (gv_dvd f hi)).eqTrans (congrMul (.eqRefl _) (q_at f i N x).eqSymm)

/-- `q_i ≤ f_i`: normalization does not increase the entries. -/
theorem q_le (f : PTm 2) {i N x : PTm k} (hG : Γ ⊢[PRAAx] gv f N x ≐ succ (pred (gv f N x)))
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] le (inst2 (qBody f) i (pairT N x)) (inst2 f i x) :=
  quo_le_of hG (f_eq f hG hi)

/-- The pointwise divisibility `g h ∣ f_i` for `h = gcd(q)`. -/
theorem point_dvd (f : PTm 2) {i N x : PTm k} (hG : Γ ⊢[PRAAx] gv f N x ≐ succ (pred (gv f N x)))
    (hH : Γ ⊢[PRAAx] gv (qBody f) N (pairT N x) ≐ succ (pred (gv (qBody f) N (pairT N x))))
    (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] dvd (succ (pred (gv f N x * gv (qBody f) N (pairT N x)))) (inst2 f i x) := by
  have hGH := pos_mul hG hH
  refine dvd_congr_left hGH (dvd_of_eq' hGH (w := quo (inst2 (qBody f) i (pairT N x)) (gv (qBody f) N (pairT N x))) ?_)
  ipra_lc natEq (f_eq f hG hi) + 𝔞 (gv f N x) * natEq (eq_of_dvd' hH (gv_dvd (qBody f) (x := pairT N x) hi))

/-- `lem:normalize`: dividing by the gcd gives a primitive vector, `gcd(q_0, …, q_{N−1}) = 1`. -/
theorem gv_quotients (f : PTm 2) {N x : PTm k} (hG : Γ ⊢[PRAAx] gv f N x ≐ succ (pred (gv f N x))) :
    Γ ⊢[PRAAx] gv (qBody f) N (pairT N x) ≐ one := by
  have hGs : Γ.map Fm.shift ⊢[PRAAx] gv f (Syn.shift N) (Syn.shift x) ≐
      succ (pred (gv f (Syn.shift N) (Syn.shift x))) := by
    have e := hG.shift
    simpa [Fm.shift, Syn.shift] using e
  refine .orE (zero_or_succ (gv (qBody f) N (pairT N x))) ?_ ?_
  · -- `h = 0` makes every `q_i`, hence every `f_i`, vanish, so `g = 0`
    let Δ := (gv (qBody f) N (pairT N x) ≐ zero) :: Γ
    have h0 : Δ ⊢[PRAAx] gv (qBody f) N (pairT N x) ≐ zero := Prf.hyp0
    have h0s : Δ.map Fm.shift ⊢[PRAAx] gv (qBody f) (Syn.shift N) (pairT (Syn.shift N) (Syn.shift x)) ≐ zero := by
      have e := h0.shift
      simpa [Fm.shift, Syn.shift] using e
    have hz : Δ ⊢[PRAAx] gv f N x ≐ zero := by
      refine gv_all_zero f (.allI (.impI ?_))
      have hq := gv_eq_zero (qBody f) (i := var 0) h0s.wk
        (Prf.hyp0 : (lt (var 0) (Syn.shift N) :: Δ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift N))
      have hf := f_eq f (hGs.wk.wk : (lt (var 0) (Syn.shift N) :: Δ.map Fm.shift) ⊢[PRAAx] _) Prf.hyp0
      exact hf.eqTrans ((congrMul (.eqRefl _) hq).eqTrans (mul_zero _))
    exact succ_ne_zero' _ (hG.wk.eqSymm.eqTrans hz)
  · let Δ := (gv (qBody f) N (pairT N x) ≐ succ (pred (gv (qBody f) N (pairT N x)))) :: Γ
    have hH : Δ ⊢[PRAAx] gv (qBody f) N (pairT N x) ≐ succ (pred (gv (qBody f) N (pairT N x))) := Prf.hyp0
    have hHs : Δ.map Fm.shift ⊢[PRAAx] gv (qBody f) (Syn.shift N) (pairT (Syn.shift N) (Syn.shift x)) ≐
        succ (pred (gv (qBody f) (Syn.shift N) (pairT (Syn.shift N) (Syn.shift x)))) := by
      have e := hH.shift
      simpa [Fm.shift, Syn.shift] using e
    have gr : Δ ⊢[PRAAx] dvd (succ (pred (gv f N x * gv (qBody f) N (pairT N x)))) (gv f N x) := by
      refine gv_greatest f (.allI (.impI ?_))
      have p := point_dvd f (hGs.wk.wk : (lt (var 0) (Syn.shift N) :: Δ.map Fm.shift) ⊢[PRAAx] _) hHs.wk Prf.hyp0
      rw [show Syn.shift (pred (gv f N x * gv (qBody f) N (pairT N x))) =
        pred (gv f (Syn.shift N) (Syn.shift x) * gv (qBody f) (Syn.shift N) (pairT (Syn.shift N) (Syn.shift x)))
        by simp [Syn.shift]]
      exact p
    have hGH := pos_mul (hG.wk : Δ ⊢[PRAAx] _) hH
    have hle := dvd_le' hGH (dvd_congr_left hGH.eqSymm gr) (hG.wk : Δ ⊢[PRAAx] _)
    have eG := natEq (hG.wk : Δ ⊢[PRAAx] _); have eH := natEq hH
    have l1 : Δ ⊢[PRAAx] le (gv (qBody f) N (pairT N x)) one := by
      ipra_le sl hle + 𝔞 (pred (gv f N x)) * 𝔞 (pred (gv (qBody f) N (pairT N x))) using
        linear_combination (𝔞 (gv (qBody f) N (pairT N x)) - 1) * eG + 𝔞 (pred (gv f N x)) * eH
    have l2 : Δ ⊢[PRAAx] le one (gv (qBody f) N (pairT N x)) := by
      ipra_le 𝔞 (pred (gv (qBody f) N (pairT N x))) using linear_combination eH
    exact le_antisymm l1 l2

end LeanProofs.IPRA.DiophantineNumberTheory.GcdNormalize
