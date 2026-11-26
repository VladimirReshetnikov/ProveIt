import IPRADerivations.AnalyticNumberTheory.SieveExpansion
import IPRADerivations.Core.Header

/-!
# The bilinear sieve estimate for natural weights

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, proof of `thm:finite-sieve`:
after expanding the square and applying `eq:crt-count` to every pair, the sum over the progression of a product of
two weighted divisor sums is `(x/q) Σ λ_d λ'_e / [d, e]` up to an error of at most `Σ |λ_d| |λ'_e|`.

For natural weight bodies `U`, `V` (standing for `λ_d / d`), `q = fst P ≥ 2`, `a = fst (snd P)` with
`gcd(a, q) = 1`, and

* `N = Σ_{m<X} [m ≡ a (mod q)] (Σ_{e<Z} [e ∣ m] λ'_e) (Σ_{d<Z} [d ∣ m] λ_d)` with `λ_d = d [d ≥ 1][gcd(d, q) = 1] U_d`
  (`SieveExpansion.lB`),
* `C = Σ_{d<Z} Σ_{e<Z} ind · U_d V_e · gcd(d, e) X` (the body `SievePairSum.Cm`; `gcd(d, e) U_d V_e = λ_d λ'_e / [d, e]`),
* `E = Σ_{d<Z} Σ_{e<Z} ind · U_d V_e · q d e` (the body `Em`; `d e U_d V_e = λ_d λ'_e`),

the two inequalities `q N ≤ C + E` (`bil_upper`) and `C ≤ q N + E` (`bil_lower`) hold, that is `|q N − C| ≤ E`.

* `Bm_split`, `Dm_split`: the bodies `Bm`, `Dm` of `SievePairSum` are `Cm + Em` and `Am + Em`;
* `kq`: under the two hypotheses the factor `χ q` of `SieveExpansion.expansion` is `q`.

The closed forms of `C` (through `SieveDiagonal`) and of `E` (a product of two sums) are not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveBilinear

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrEqb')
open LeanProofs.IPRA.AnalyticNumberTheory.SievePairCount (lc)
open LeanProofs.IPRA.AnalyticNumberTheory.SievePairSum (subst_ind subst_gcd' subst_cnt wB Am Bm Cm Dm inst3_Am inst3_Bm
  inst3_Cm inst3_Dm upper lower)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveExpansion (cB lB kT at1_kT expansion)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorExchange (LW)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)
open LeanProofs.IPRA.Foundations.DoubleSumScale (at1)
open LeanProofs.IPRA.Probability.Independence (dsum dsum_congr dsum_add inst3_add')

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem distrib (I W A B : PTm n) : Γ ⊢[PRAAx] I * (W * (A + B)) ≐ I * (W * A) + I * (W * B) := by
  ipra_ring

theorem ooq (q : PTm n) : Γ ⊢[PRAAx] (one * one) * q ≐ q := by
  ipra_ring

section Bilinear

variable (U V : PTm 2)

/-- `ind · U V · (q d e)` over `(d, e, ⟨X, ⟨q, ⟨a, w⟩⟩⟩)`. -/
def Em : PTm 3 :=
  SievePairBound.ind (var 0) (var 1) (fstT (sndT (var 2))) (fstT (sndT (sndT (var 2)))) *
    (wB U V * (fstT (sndT (var 2)) * (var 0 * var 1)))

theorem inst3_Em (i j x : PTm n) : inst3 (Em U V) i j x =
    SievePairBound.ind i j (fstT (sndT x)) (fstT (sndT (sndT x))) * (inst3 (wB U V) i j x * (fstT (sndT x) * (i * j))) := by
  simp only [inst3, Em, SievePairBound.ind, lc, LeanProofs.IPRA.PTm.subst_mul, LeanProofs.IPRA.PTm.subst_add,
    subst_eqb, LeanProofs.IPRA.PTm.subst_monus, LeanProofs.IPRA.PTm.subst_pred, subst_gcd', subst_cnt, subst_ap2,
    subst_pairT, subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero]

theorem Bm_pt (i j x : PTm n) : Γ ⊢[PRAAx] inst3 (Bm U V) i j x ≐ inst3 (Cm U V + Em U V) i j x := by
  rw [inst3_add', inst3_Bm, inst3_Cm, inst3_Em]
  exact distrib _ _ _ _

theorem Dm_pt (i j x : PTm n) : Γ ⊢[PRAAx] inst3 (Dm U V) i j x ≐ inst3 (Am U V + Em U V) i j x := by
  rw [inst3_add', inst3_Dm, inst3_Am, inst3_Em]
  exact distrib _ _ _ _

/-- `Σ Σ Bm = Σ Σ Cm + Σ Σ Em`. -/
theorem Bm_split (Z y : PTm n) :
    Γ ⊢[PRAAx] dsum (Bm U V) Z Z y ≐ dsum (Cm U V) Z Z y + dsum (Em U V) Z Z y :=
  (dsum_congr (Bm U V) (Cm U V + Em U V) (fun i j x => Bm_pt U V i j x) Z Z y).eqTrans (dsum_add _ _ _ _ _)

/-- `Σ Σ Dm = Σ Σ Am + Σ Σ Em`. -/
theorem Dm_split (Z y : PTm n) :
    Γ ⊢[PRAAx] dsum (Dm U V) Z Z y ≐ dsum (Am U V) Z Z y + dsum (Em U V) Z Z y :=
  (dsum_congr (Dm U V) (Am U V + Em U V) (fun i j x => Dm_pt U V i j x) Z Z y).eqTrans (dsum_add _ _ _ _ _)

/-- Under `q ≥ 1` and `gcd(a, q) = 1`, the factor `χ q` is `q`. -/
theorem kq {X P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P)) (ha : Γ ⊢[PRAAx] gcd (fstT (sndT P)) (fstT P) ≐ one) :
    Γ ⊢[PRAAx] at1 kT (pairT X P) ≐ fstT P := by
  rw [at1_kT]
  have s := snd_pair (Γ := Γ) X P
  have cq : Γ ⊢[PRAAx] fstT (sndT (pairT X P)) ≐ fstT P := congrFst s
  have ca : Γ ⊢[PRAAx] fstT (sndT (sndT (pairT X P))) ≐ fstT (sndT P) := congrFst (congrSnd s)
  have k1 : Γ ⊢[PRAAx] eqb (monus one (fstT (sndT (pairT X P)))) zero ≐ one :=
    (congrEqb' (congrMonus (.eqRefl _) cq) (.eqRefl _)).eqTrans (eqb_of_eq hq)
  have k2 : Γ ⊢[PRAAx] eqb (gcd (fstT (sndT (sndT (pairT X P)))) (fstT (sndT (pairT X P)))) one ≐ one :=
    (congrEqb' (congrGcd ca cq) (.eqRefl _)).eqTrans (eqb_of_eq ha)
  exact (congrMul (congrMul k1 k2) cq).eqTrans (ooq _)

/-- The expanded square, times `q`, is the double sum of the pair counts. -/
theorem qN {X Z P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P))
    (ha : Γ ⊢[PRAAx] gcd (fstT (sndT P)) (fstT P) ≐ one) :
    Γ ⊢[PRAAx] dsum (Am U V) Z Z (pairT X P) ≐
      fstT P * ap2 (sumF (LW (LW cB (lB V)) (sndB (lB U)))) X (pairT Z (pairT Z P)) :=
  (expansion U V X Z P).eqTrans (congrMul (kq hq ha) (.eqRefl _))

/-- `q N ≤ C + E`. -/
theorem bil_upper {X Z P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P))
    (ha : Γ ⊢[PRAAx] gcd (fstT (sndT P)) (fstT P) ≐ one) :
    Γ ⊢[PRAAx] le (fstT P * ap2 (sumF (LW (LW cB (lB V)) (sndB (lB U)))) X (pairT Z (pairT Z P)))
      (dsum (Cm U V) Z Z (pairT X P) + dsum (Em U V) Z Z (pairT X P)) :=
  le_congr (qN U V hq ha) (Bm_split U V Z (pairT X P)) (upper U V Z (pairT X P))

/-- `C ≤ q N + E`. -/
theorem bil_lower {X Z P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P))
    (ha : Γ ⊢[PRAAx] gcd (fstT (sndT P)) (fstT P) ≐ one) :
    Γ ⊢[PRAAx] le (dsum (Cm U V) Z Z (pairT X P))
      (fstT P * ap2 (sumF (LW (LW cB (lB V)) (sndB (lB U)))) X (pairT Z (pairT Z P)) +
        dsum (Em U V) Z Z (pairT X P)) :=
  le_congr (.eqRefl _) ((Dm_split U V Z (pairT X P)).eqTrans (congrAdd (qN U V hq ha) (.eqRefl _)))
    (lower U V Z (pairT X P))

end Bilinear

end LeanProofs.IPRA.AnalyticNumberTheory.SieveBilinear
