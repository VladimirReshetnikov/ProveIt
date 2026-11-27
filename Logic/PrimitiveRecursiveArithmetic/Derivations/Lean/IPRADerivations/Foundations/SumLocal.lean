import IPRADerivations.Foundations.AuxiliaryEnvelope
import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.OrderCertificates

/-!
# Support localization of finite sums (`hurwitz_khinchin_ipra`, the (K11) count inside a gap)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`: the (K11) block constructed in a gap
covers only cells of that gap ("All added intervals are inside the gap in which they were constructed"), so its
measure over the whole grid is its measure over the gap. Generically:

* `sum_zero_of`: a sum of terms that all vanish is `0`;
* `sum_local`: if `f(c) = 0` for `c < L` and for `H ≤ c < N` (with `L ≤ H ≤ N`), then
  `Σ_{c<N} f(c) = Σ_{k<H−L} f(L + k)` — two splits (`Core.SumSplit.sum_split`) and two vanishing sums.

With `KhinchinBlockLocal.block_out` this turns `KhinchinBlock.block_cover`'s count over the whole grid into the
count over the cell's own fine cells, the hypothesis of `KhinchinRoundBits.cell_cov`.
-/

namespace LeanProofs.IPRA.Foundations.SumLocal

open_ipra exports

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- A sum of vanishing terms vanishes. -/
theorem sum_zero_of (f : PTm 2) {N x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ inst2 f (var 0) (Syn.shift x) ≐ zero)) :
    Γ ⊢[PRAAx] ap2 (sumF f) N x ≐ zero :=
  sum_zero_of_bounded f x N h

/-- Support localization: `f` vanishing below `L` and on `[H, N)` gives `Σ_{c<N} f = Σ_{k<H−L} f(L + k)`. -/
theorem sum_local (f : PTm 2) {L H N x : PTm n} (hLH : Γ ⊢[PRAAx] le L H) (hHN : Γ ⊢[PRAAx] le H N)
    (hlo : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift L) ⟶ inst2 f (var 0) (Syn.shift x) ≐ zero))
    (hhi : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (monus N H)) ⟶
      inst2 f (Syn.shift H + var 0) (Syn.shift x) ≐ zero)) :
    Γ ⊢[PRAAx] ap2 (sumF f) N x ≐ ap2 (sumF (offB f)) (monus H L) (pairT L x) := by
  have e1 := eq_add_of_le hLH
  have e2 := eq_add_of_le hHN
  have eN : Γ ⊢[PRAAx] N ≐ L + (monus H L + monus N H) := by
    ipra_lc natEq e2 + natEq e1
  have s1 := (congrAp2 (sumF f) eN (.eqRefl x)).eqTrans (sum_split f L (monus H L + monus N H) x)
  have s2 := sum_split (Γ := Γ) (offB f) (monus H L) (monus N H) (pairT L x)
  have z1 := sum_zero_of f hlo
  have e1s0 : Γ.map Fm.shift ⊢[PRAAx] Syn.shift H ≐ Syn.shift L + Syn.shift (monus H L) := by
    simpa [Fm.shift, Syn.shift] using e1.shift
  have z2 : Γ ⊢[PRAAx] ap2 (sumF (offB (offB f))) (monus N H) (pairT (monus H L) (pairT L x)) ≐ zero := by
    refine sum_zero_of _ (.allI (.impI ?_))
    have e1s : (lt (var 0) (Syn.shift (monus N H)) :: Γ.map Fm.shift) ⊢[PRAAx]
        Syn.shift H ≐ Syn.shift L + Syn.shift (monus H L) := e1s0.wk
    have p := Prf.impE (hhi.allOpen.wk (ψ := lt (var 0) (Syn.shift (monus N H)))) Prf.hyp0
    rw [show Syn.shift (pairT (monus H L) (pairT L x)) =
        pairT (Syn.shift (monus H L)) (pairT (Syn.shift L) (Syn.shift x)) by simp [Syn.shift],
      inst2_offB, inst2_offB]
    have ef := fst_pair (Γ := lt (var 0) (Syn.shift (monus N H)) :: Γ.map Fm.shift)
      (Syn.shift (monus H L)) (pairT (Syn.shift L) (Syn.shift x))
    have es := snd_pair (Γ := lt (var 0) (Syn.shift (monus N H)) :: Γ.map Fm.shift)
      (Syn.shift (monus H L)) (pairT (Syn.shift L) (Syn.shift x))
    have ei : (lt (var 0) (Syn.shift (monus N H)) :: Γ.map Fm.shift) ⊢[PRAAx]
        fstT (sndT (pairT (Syn.shift (monus H L)) (pairT (Syn.shift L) (Syn.shift x)))) +
            (fstT (pairT (Syn.shift (monus H L)) (pairT (Syn.shift L) (Syn.shift x))) + var 0) ≐
          Syn.shift H + var 0 := by
      have a := natEq ((congrFst es).eqTrans (fst_pair _ _))
      have b := natEq ef
      ipra_lc a + b - natEq e1s
    exact (congrInst2 f ei ((congrSnd es).eqTrans (snd_pair _ _))).eqTrans p
  ipra_lc natEq s1 + natEq s2 + natEq z1 + natEq z2

end LeanProofs.IPRA.Foundations.SumLocal
