import IPRADerivations.Foundations.AuxiliaryEnvelope
import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.DiophantineNumberTheory.KhinchinBlockGeo
import IPRADerivations.Core.Header

/-!
# The dyadic majorant of the divergence modulus (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, §"One call to the divergence modulus
supplies the block": "The dyadic blocks `[2^k, 2^{k+1} − 1]`, `K ≤ k ≤ B`, include every integer from `s` to `D(s)`.
Monotonicity gives `1 ≤ Σ_{q=s}^{D(s)} ψ(q) ≤ Σ_{k=K}^B 2^k ψ(2^k)`."

For a natural-valued body `Ψ(q, x)` (the numerator of `ψ` over a fixed denominator):

* `block_le`: if `Ψ` does not increase on `[a, a + N)`, then `Σ_{i<N} Ψ(a + i) ≤ N Ψ(a)`;
* `dyadic`: given the block bounds `Σ_{i<2^{K+k}} Ψ(2^{K+k} + i) ≤ 2^{K+k} Ψ(2^{K+k})` for every `k < B`,
  `Σ_{q<2^{K+B}} Ψ(q) ≤ Σ_{q<2^K} Ψ(q) + Σ_{k<B} 2^{K+k} Ψ(2^{K+k})` — the dyadic majorant, by one
  quantifier-free induction splitting `[0, 2^{K+k+1})` at `2^{K+k}` (`Core.SumSplit.sum_split`).

The dyadic term `2^{K+k} Ψ(2^{K+k})` is the closed body `dyB Ψ` over `⟨K, x⟩` (`dy_at`).
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinDyadic

open_ipra
open LeanProofs.IPRA.Foundations.AuxiliaryEnvelope (sum_le_const)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockGeo (congrPw2)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- A non-increasing block: `Σ_{i<N} Ψ(a + i) ≤ N Ψ(a)`. -/
theorem block_le (Ψ : PTm 2) {a N x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 Ψ (Syn.shift a + var 0) (Syn.shift x)) (inst2 Ψ (Syn.shift a) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (ap2 (sumF (offB Ψ)) N (pairT a x)) (N * inst2 Ψ a x) := by
  refine sum_le_const (offB Ψ) (.allI (.impI ?_))
  rw [show Syn.shift (pairT a x) = pairT (Syn.shift a) (Syn.shift x) by simp [Syn.shift],
    show Syn.shift (inst2 Ψ a x) = inst2 Ψ (Syn.shift a) (Syn.shift x) by
      simp only [Syn.shift, inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp,
    inst2_offB]
  have p := Prf.impE (h.allOpen.wk (ψ := lt (var 0) (Syn.shift N))) Prf.hyp0
  exact le_congr (congrInst2 Ψ (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqSymm (.eqRefl _) p

/-- The dyadic term `2^{K+k} Ψ(2^{K+k})` over `0 = k`, `1 = ⟨K, x⟩`. -/
def dyB (Ψ : PTm 2) : PTm 2 :=
  pw two (fstT (var 1) + var 0) * Syn.subst ![pw two (fstT (var 1) + var 0), sndT (var 1)] Ψ

theorem inst2_dyB (Ψ : PTm 2) (k y : PTm n) :
    inst2 (dyB Ψ) k y = pw two (fstT y + k) * inst2 Ψ (pw two (fstT y + k)) (sndT y) := by
  have e : Syn.subst ![k, y] (Syn.subst ![pw two (fstT (var 1) + var 0), sndT (var 1)] Ψ) =
      inst2 Ψ (pw two (fstT y + k)) (sndT y) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext j; fin_cases j <;> simp [subst_ap2]
  show Syn.subst ![k, y] (dyB Ψ) = _
  unfold dyB
  rw [PTm.subst_mul, e]
  simp [subst_ap2]

theorem dy_at (Ψ : PTm 2) (k K x : PTm n) :
    Γ ⊢[PRAAx] inst2 (dyB Ψ) k (pairT K x) ≐ pw two (K + k) * inst2 Ψ (pw two (K + k)) x := by
  rw [inst2_dyB]
  have e1 : Γ ⊢[PRAAx] pw two (fstT (pairT K x) + k) ≐ pw two (K + k) := congrPw2 (congrAdd (fst_pair _ _) (.eqRefl _))
  exact congrMul e1 (congrInst2 Ψ e1 (snd_pair _ _))

/-- The dyadic majorant: `Σ_{q<2^{K+B}} Ψ ≤ Σ_{q<2^K} Ψ + Σ_{k<B} 2^{K+k} Ψ(2^{K+k})`. -/
theorem dyadic (Ψ : PTm 2) (K B x : PTm n)
    (hblk : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift B) ⟶
      le (ap2 (sumF (offB Ψ)) (pw two (Syn.shift K + var 0)) (pairT (pw two (Syn.shift K + var 0)) (Syn.shift x)))
        (pw two (Syn.shift K + var 0) * inst2 Ψ (pw two (Syn.shift K + var 0)) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (ap2 (sumF Ψ) (pw two (K + B)) x)
      (ap2 (sumF Ψ) (pw two K) x + ap2 (sumF (dyB Ψ)) B (pairT K x)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift B) ⟶
      le (ap2 (sumF Ψ) (pw two (Syn.shift K + var 0)) (Syn.shift x))
        (ap2 (sumF Ψ) (pw two (Syn.shift K)) (Syn.shift x) + ap2 (sumF (dyB Ψ)) (var 0) (pairT (Syn.shift K) (Syn.shift x)))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift]
      refine .impI ?_
      have e1 := natEq (congrAp2 (Γ := le zero B :: Γ) (sumF Ψ) (congrPw2 (add_zero K)) (.eqRefl x))
      have e2 := natEq (sum_zero (Γ := le zero B :: Γ) (dyB Ψ) (pairT K x))
      ipra_le 0 with e2 - e1
    · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift]
      refine .impI ?_
      let Θ : List (Fm PTm (n + 1)) := le (succ (var 0)) (Syn.shift B) ::
        (le (var 0) (Syn.shift B) ⟶
          le (ap2 (sumF Ψ) (pw two (Syn.shift K + var 0)) (Syn.shift x))
            (ap2 (sumF Ψ) (pw two (Syn.shift K)) (Syn.shift x) +
              ap2 (sumF (dyB Ψ)) (var 0) (pairT (Syn.shift K) (Syn.shift x)))) :: Γ.map Fm.shift
      have hle : Θ ⊢[PRAAx] le (var 0) (Syn.shift B) := le_trans (le_succ_self _) Prf.hyp0
      have ih : Θ ⊢[PRAAx] le (ap2 (sumF Ψ) (pw two (Syn.shift K + var 0)) (Syn.shift x))
          (ap2 (sumF Ψ) (pw two (Syn.shift K)) (Syn.shift x) +
            ap2 (sumF (dyB Ψ)) (var 0) (pairT (Syn.shift K) (Syn.shift x))) := Prf.impE Prf.hyp1 hle
      have hb : Θ ⊢[PRAAx] le (ap2 (sumF (offB Ψ)) (pw two (Syn.shift K + var 0))
            (pairT (pw two (Syn.shift K + var 0)) (Syn.shift x)))
          (pw two (Syn.shift K + var 0) * inst2 Ψ (pw two (Syn.shift K + var 0)) (Syn.shift x)) :=
        Prf.impE hblk.allOpen.wk.wk Prf.hyp0
      have eP : Θ ⊢[PRAAx] pw two (Syn.shift K + succ (var 0)) ≐
          pw two (Syn.shift K + var 0) + pw two (Syn.shift K + var 0) := by
        have a := (congrPw2 (Γ := Θ) (add_succ (Syn.shift K) (var 0))).eqTrans (pw_succ two (Syn.shift K + var 0))
        have a' := natEq a
        apply deriveNat; ipra_simps; linear_combination a'
      have e1 := natEq ((congrAp2 (Γ := Θ) (sumF Ψ) eP (.eqRefl (Syn.shift x))).eqTrans
        (sum_split Ψ (pw two (Syn.shift K + var 0)) (pw two (Syn.shift K + var 0)) (Syn.shift x)))
      have e2 := natEq (sum_succ' (Γ := Θ) (dyB Ψ) (var 0) (pairT (Syn.shift K) (Syn.shift x)))
      have e3 := natEq (dy_at (Γ := Θ) Ψ (var 0) (Syn.shift K) (Syn.shift x))
      ipra_le sl ih + sl hb with e2 + e3 - e1
  have h2 := Prf.allE B hall
  simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift] at h2
  exact .impE h2 (le_refl B)

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinDyadic
