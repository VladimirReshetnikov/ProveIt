import IPRADerivations.AnalyticNumberTheory.SelbergLeibniz
import IPRADerivations.AnalyticNumberTheory.MobiusInversion
import IPRADerivations.AnalyticNumberTheory.SumReindex
import IPRADerivations.Core.MultiSums
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Reindex

/-!
# Associativity of the finite Dirichlet convolution

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, §"Selberg's symmetry
formula": "All convolution rearrangements below are rearrangements of finite divisor sums." For bodies
`f, g, h` (with a parameter `y`) and `m ≥ 1`,

  `(f * (g * h))(m) = ((f * g) * h)(m)`                                                (`conv_assoc`)

for the convolution `DirichletLeibniz.conv`. The proof writes the right side as the double sum
`Σ_{k ≤ m} Σ_{d ≤ m} [k ∣ m][d ∣ k] f(d) g(k/d) h(m/k)` (`rhs_row`: the inner range `d ≤ k` extends to
`d ≤ m` since larger `d` do not divide `k ≥ 1`, `MobiusBounds.sum_ext`), exchanges it (`Core/Fubini`),
and reindexes each column `k = d e` (`SumReindex.reindex_eq`, with `⌊m/d⌋ + 1` multiples of `d` up to
`m`, `multiples_upto`) to `Σ_{e ≤ m/d} [de ∣ m] f(d) g(e) h(m/(de))` (`col_pt`). The same sum is the
row `d` of the left side (`row_pt`), by `[d ∣ m][e ∣ m/d] = [de ∣ m]` (`MobiusInversion.dv_prod`) and
`⌊⌊m/d⌋/e⌋ = ⌊m/(de)⌋` (`quo_quo`).

With `SelbergLeibniz.selberg_leibniz` this gives `Λ * L = Λ * (Λ * 𝟏) = (Λ * Λ) * 𝟏`, the rearrangement
in the packet's `L² = 𝟏 * (Λ * Λ + 𝒟Λ)` (`lam_conv_L`, `selberg_divisor`).
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv DwB inst2_cvB inst2_DwB cv_at)
open LeanProofs.IPRA.AnalyticNumberTheory.SelbergLeibniz (lamF lam_conv_one selberg_leibniz)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (Lw)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversion (dv_prod shift_inst2)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (sum_ext shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (riB inst2_riB reindex_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (count_multiples quo_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (zero_mul_l congrEqb' congrSg)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Arithmetic of quotients -/

theorem pos_of_eq {t e : PTm n} (h : Γ ⊢[PRAAx] t ≐ succ e) : Γ ⊢[PRAAx] t ≐ succ (pred t) :=
  h.eqTrans (congrSucc ((pred_succ e).eqSymm.eqTrans (congrPred h.eqSymm)))

/-- `k mod a = k` for `k < a`. -/
theorem rem_small {k a : PTm n} (h : Γ ⊢[PRAAx] lt k a) : Γ ⊢[PRAAx] rem k a ≐ k := by
  have e := natEq (eq_add_of_le h)
  have ha : Γ ⊢[PRAAx] a ≐ succ (pred a) :=
    pos_of_eq (e := k + monus a (succ k)) (by apply deriveNat; ipra_simps; linear_combination e)
  refine (congrAp2 remF (.eqRefl _) ha).eqTrans (Prf.andE₂ (div_mod_unique (q := zero) ?_ (lt_congr (.eqRefl _) ha h)))
  ipra_ring

/-- `⌊⌊m/d⌋/e⌋ = ⌊m/(de)⌋` for `d, e ≥ 1`. -/
theorem quo_quo {m d e : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) :
    Γ ⊢[PRAAx] quo (quo m d) e ≐ quo m (d * e) := by
  have d1 := div_mod_at (Γ := Γ) (x := m) hd
  have d2 := div_mod_at (Γ := Γ) (x := quo m d) he
  have r1 : Γ ⊢[PRAAx] lt (rem m d) d := Prf.andE₂ d1
  have r2 : Γ ⊢[PRAAx] lt (rem (quo m d) e) e := Prf.andE₂ d2
  refine (quo_eq (pos_mul' hd he) (r := d * rem (quo m d) e + rem m d) ?_ ?_).eqSymm
  · ipra_lc natEq (Prf.andE₁ d1) + 𝔞 d * natEq (Prf.andE₁ d2)
  · ipra_le 𝔞 d * sl r2 + sl r1

/-- `Q + 1 + (d − 1) = d (⌊Q/d⌋ + 1) + (Q mod d)`, with atoms. -/
theorem quo_add_aux {Q d u r e : PTm n} (h1 : Γ ⊢[PRAAx] Q ≐ d * u + r) (h2 : Γ ⊢[PRAAx] d ≐ succ e) :
    Γ ⊢[PRAAx] succ Q + e ≐ d * succ u + r := by
  refine (congrAdd (congrSucc (h1.eqTrans (congrAdd (congrMul h2 (.eqRefl _)) (.eqRefl _)))) (.eqRefl _)).eqTrans ?_
  refine .eqTrans ?_ (congrAdd (congrMul h2.eqSymm (.eqRefl _)) (.eqRefl _))
  ipra_ring

/-- `#{k ≤ m : d ∣ k} = ⌊m/d⌋ + 1` for `d ≥ 1`. -/
theorem multiples_upto {Q d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ ⊢[PRAAx] ap2 (sumF Totient.mulBody) (succ Q) d ≐ succ (quo Q d) := by
  have dm := div_mod_at (Γ := Γ) (x := Q) hd
  exact (count_multiples hd).eqTrans (quo_eq hd (quo_add_aux (Prf.andE₁ dm) hd) (Prf.andE₂ dm))

theorem sg_pos {a : PTm n} (h : Γ ⊢[PRAAx] a ≐ succ (pred a)) : Γ ⊢[PRAAx] sg a ≐ one :=
  (congrSg h).eqTrans (sg_succ _)

theorem eqb_succ_zero (a : PTm n) : Γ ⊢[PRAAx] eqb (succ a) zero ≐ zero :=
  eqb_of_ne (.impI (succ_ne_zero Prf.hyp0))

/-! ## Bodies -/

section Assoc

variable (f g h : PTm 2)

/-- `[d ∣ m]` with `d ≥ 1`. -/
abbrev dv (d m : PTm n) : PTm n := sg d * eqb (rem m d) zero

/-- `(g * h)(k)` as a body over `0 = k`, `1 = y`. -/
abbrev cvF (g h : PTm 2) : PTm 2 := ap2 (sumF (cvB g h)) (succ (var 0)) (pairT (var 0) (var 1))

theorem inst2_cvF (k y : PTm n) : inst2 (cvF g h) k y = conv g h k y := by simp [inst2, subst_ap2]

/-- `[k ∣ m] [d ∣ k] f(d) g(k/d) h(m/k)` over `0 = k`, `1 = d`, `2 = ⟨m, y⟩`. -/
def aT : PTm 3 := (sg (var 0) * eqb (rem (fstT (var 2)) (var 0)) zero) *
  Syn.subst ![var 1, pairT (var 0) (sndT (var 2))] (cvB f g) *
  Syn.subst ![quo (fstT (var 2)) (var 0), sndT (var 2)] h

theorem inst3_aT (k d z : PTm n) : inst3 (aT f g h) k d z =
    dv k (fstT z) * inst2 (cvB f g) d (pairT k (sndT z)) * inst2 h (quo (fstT z) k) (sndT z) := by
  simp only [inst3, aT, PTm.subst_mul, subst_reindex2]
  simp

/-- `[de ∣ m] [e ≥ 1] f(d) g(e) h(m/(de))` over `0 = e`, `1 = ⟨d, ⟨m, y⟩⟩`. -/
def HB : PTm 2 := eqb (rem (fstT (sndT (var 1))) (fstT (var 1) * var 0)) zero * sg (var 0) *
  (Syn.subst ![fstT (var 1), sndT (sndT (var 1))] f * Syn.subst ![var 0, sndT (sndT (var 1))] g) *
  Syn.subst ![quo (fstT (sndT (var 1))) (fstT (var 1) * var 0), sndT (sndT (var 1))] h

theorem inst2_HB (e w : PTm n) : inst2 (HB f g h) e w =
    eqb (rem (fstT (sndT w)) (fstT w * e)) zero * sg e *
      (inst2 f (fstT w) (sndT (sndT w)) * inst2 g e (sndT (sndT w))) *
      inst2 h (quo (fstT (sndT w)) (fstT w * e)) (sndT (sndT w)) := by
  simp only [inst2, HB, PTm.subst_mul, subst_reindex2, subst_reindex2]
  simp

theorem HB_at (e d m y : PTm n) : Γ ⊢[PRAAx] inst2 (HB f g h) e (pairT d (pairT m y)) ≐
    eqb (rem m (d * e)) zero * sg e * (inst2 f d y * inst2 g e y) * inst2 h (quo m (d * e)) y := by
  rw [inst2_HB]
  have fd : Γ ⊢[PRAAx] fstT (pairT d (pairT m y)) ≐ d := fst_pair _ _
  have s1 : Γ ⊢[PRAAx] sndT (pairT d (pairT m y)) ≐ pairT m y := snd_pair _ _
  have fm : Γ ⊢[PRAAx] fstT (sndT (pairT d (pairT m y))) ≐ m := (congrFst s1).eqTrans (fst_pair _ _)
  have sy : Γ ⊢[PRAAx] sndT (sndT (pairT d (pairT m y))) ≐ y := (congrSnd s1).eqTrans (snd_pair _ _)
  exact congrMul (congrMul (congrMul (congrEqb' (congrAp2 remF fm (congrMul fd (.eqRefl _))) (.eqRefl _)) (.eqRefl _))
    (congrMul (congrInst2 f fd sy) (congrInst2 g (.eqRefl _) sy)))
    (congrInst2 h (congrAp2 quoF fm (congrMul fd (.eqRefl _))) sy)

/-! ## The left side, row by row -/

/-- For `d ≥ 1`: `[de ∣ m][e ≥ 1] f(d) g(e) h(m/(de)) = ([d ∣ m] f(d)) · [e ∣ m/d] g(e) h((m/d)/e)`. -/
theorem row_pt {e d m y : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ ⊢[PRAAx] inst2 (HB f g h) e (pairT d (pairT m y)) ≐
      (dv d m * inst2 f d y) * inst2 (cvB g h) e (pairT (quo m d) y) := by
  refine (HB_at f g h e d m y).eqTrans (.eqTrans ?_ (congrMul (.eqRefl _) (cv_at g h e (quo m d) y)).eqSymm)
  refine .orE (zero_or_succ e) ?_ ?_
  · let Δ : List (Fm PTm n) := (e ≐ zero) :: Γ
    have s0 : Δ ⊢[PRAAx] sg e ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    refine (zero_mul_l (zero_mul_l ((congrMul (.eqRefl _) s0).eqTrans (mul_zero _)) _) _).eqTrans ?_
    exact ((congrMul (.eqRefl _) (zero_mul_l (zero_mul_l s0 _) _)).eqTrans (mul_zero _)).eqSymm
  · let Δ : List (Fm PTm n) := (e ≐ succ (pred e)) :: Γ
    have he : Δ ⊢[PRAAx] e ≐ succ (pred e) := Prf.hyp0
    have dp := dv_prod (N := m) hd.wk he
    have qq := quo_quo (m := m) hd.wk he
    have sd : Δ ⊢[PRAAx] sg d ≐ one := sg_pos hd.wk
    have se := sg_pos he
    refine (congrMul (congrMul (congrMul dp.eqSymm se) (.eqRefl _)) (congrInst2 h qq.eqSymm (.eqRefl _))).eqTrans ?_
    refine .eqTrans ?_ (congrMul (congrMul (congrMul sd.eqSymm (.eqRefl _)) (.eqRefl _))
      (congrMul (congrMul se.eqSymm (.eqRefl _)) (.eqRefl _)))
    ipra_ring

/-- For `d ≥ 1`, the row `d` of `f * (g * h)` is `Σ_{e ≤ m/d} [de ∣ m] f(d) g(e) h(m/(de))`. -/
theorem lhs_row {d m y : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ ⊢[PRAAx] inst2 (cvB f (cvF g h)) d (pairT m y) ≐
      ap2 (sumF (HB f g h)) (succ (quo m d)) (pairT d (pairT m y)) := by
  refine (cv_at f (cvF g h) d m y).eqTrans ?_
  rw [inst2_cvF]
  have sc := sum_scale (Γ := Γ) (HB f g h) (cvB g h) (succ (quo m d)) (dv d m * inst2 f d y) (pairT (quo m d) y)
    (pairT d (pairT m y)) (.allI (.impI ?_))
  · refine .eqTrans ?_ sc.eqSymm
    ipra_ring
  · rw [shift_pairT, shift_pairT, shift_pairT,
      show Syn.shift (dv d m * inst2 f d y) = dv (Syn.shift d) (Syn.shift m) * inst2 f (Syn.shift d) (Syn.shift y) by
        rw [← shift_inst2]; simp [Syn.shift],
      show Syn.shift (quo m d) = quo (Syn.shift m) (Syn.shift d) by simp [Syn.shift]]
    exact row_pt f g h (shift_pos hd).wk

/-! ## The right side, row by row -/

/-- Row `k < m + 1` of `(f * g) * h`, extended to the rectangle `d ≤ m`. -/
theorem rhs_row {k m y : PTm n} (hk : Γ ⊢[PRAAx] lt k (succ m)) :
    Γ ⊢[PRAAx] inst2 (cvB (cvF f g) h) k (pairT m y) ≐
      inst2 (oB (aT f g h)) k (pairT (succ m) (pairT m y)) := by
  refine (cv_at (cvF f g) h k m y).eqTrans (.eqTrans ?_ (oB_at (aT f g h) k (succ m) (pairT m y)).eqSymm)
  rw [inst2_cvF]
  -- the row is `[k ∣ m] h(m/k) · Σ_{d ≤ m} [d ∣ k] f(d) g(k/d)`
  have sc := sum_scale (Γ := Γ) (rowB (aT f g h)) (cvB f g) (succ m) (dv k m * inst2 h (quo m k) y) (pairT k y)
    (pairT k (pairT m y)) (.allI (.impI ?_))
  · refine .eqTrans ?_ sc.eqSymm
    refine .orE (zero_or_succ k) ?_ ?_
    · let Δ : List (Fm PTm n) := (k ≐ zero) :: Γ
      have s0 : Δ ⊢[PRAAx] sg k ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
      exact (zero_mul_l (zero_mul_l s0 _) _).eqTrans (zero_mul_l (zero_mul_l (zero_mul_l s0 _) _) _).eqSymm
    · let Δ : List (Fm PTm n) := (k ≐ succ (pred k)) :: Γ
      have hk1 : Δ ⊢[PRAAx] k ≐ succ (pred k) := Prf.hyp0
      have ext : Δ ⊢[PRAAx] ap2 (sumF (cvB f g)) (succ m) (pairT k y) ≐ conv f g k y := by
        refine sum_ext (cvB f g) (fun Δ' a hs hl => ?_) (hk.wk : Δ ⊢[PRAAx] le (succ k) (succ m))
        rw [shift_pairT]
        refine (cv_at f g a _ _).eqTrans (zero_mul_l ?_ _)
        have hk' := (shift_pos hk1).weaken hs
        refine (congrMul (.eqRefl _) ((congrEqb' ((rem_small hl).eqTrans hk') (.eqRefl _)).eqTrans
          (eqb_succ_zero _))).eqTrans (mul_zero _)
      refine (congrMul (.eqRefl _) (congrMul ext.eqSymm (.eqRefl _))).eqTrans ?_
      ipra_ring
  · simp only [shift_pairT]
    rw [inst2_rowB,
      show Syn.shift (dv k m * inst2 h (quo m k) y) =
          dv (Syn.shift k) (Syn.shift m) * inst2 h (quo (Syn.shift m) (Syn.shift k)) (Syn.shift y) by
        rw [show quo (Syn.shift m) (Syn.shift k) = Syn.shift (quo m k) by simp [Syn.shift], ← shift_inst2]
        simp [Syn.shift]]
    refine (congrInst3 (aT f g h) (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_aT]
    have fm : (lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift) ⊢[PRAAx]
        fstT (pairT (Syn.shift m) (Syn.shift y)) ≐ Syn.shift m := fst_pair _ _
    have sy : (lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift) ⊢[PRAAx]
        sndT (pairT (Syn.shift m) (Syn.shift y)) ≐ Syn.shift y := snd_pair _ _
    refine (congrMul (congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF fm (.eqRefl _)) (.eqRefl _)))
      (congrInst2 (cvB f g) (.eqRefl _) (congrPairT (.eqRefl _) sy)))
      (congrInst2 h (congrAp2 quoF fm (.eqRefl _)) sy)).eqTrans ?_
    ipra_ring

/-! ## The columns -/

/-- For `d ≥ 1`, a column term is `[d ∣ k] H(k/d)`. -/
theorem col_pt {k d m y : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ ⊢[PRAAx] inst2 (colB (aT f g h)) k (pairT d (pairT m y)) ≐
      inst2 (riB (HB f g h)) k (pairT d (pairT d (pairT m y))) := by
  rw [inst2_colB, inst2_riB]
  refine (congrInst3 (aT f g h) (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans ?_
  rw [inst3_aT]
  have fm : Γ ⊢[PRAAx] fstT (pairT m y) ≐ m := fst_pair _ _
  have sy : Γ ⊢[PRAAx] sndT (pairT m y) ≐ y := snd_pair _ _
  refine (congrMul (congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF fm (.eqRefl _)) (.eqRefl _)))
    ((congrInst2 (cvB f g) (.eqRefl _) (congrPairT (.eqRefl _) sy)).eqTrans (cv_at f g d k y)))
    (congrInst2 h (congrAp2 quoF fm (.eqRefl _)) sy)).eqTrans ?_
  have fd : Γ ⊢[PRAAx] fstT (pairT d (pairT d (pairT m y))) ≐ d := fst_pair _ _
  refine .eqTrans ?_ (congrMul (congrEqb' (congrAp2 remF (.eqRefl _) fd) (.eqRefl _))
    ((congrInst2 (HB f g h) (congrAp2 quoF (.eqRefl _) fd) (snd_pair _ _)).eqTrans (HB_at f g h _ d m y))).eqSymm
  refine .orE (eq_or_ne (rem k d) zero) ?_ ?_
  · let Δ : List (Fm PTm n) := (rem k d ≐ zero) :: Γ
    have hr : Δ ⊢[PRAAx] rem k d ≐ zero := Prf.hyp0
    have er : Δ ⊢[PRAAx] eqb (rem k d) zero ≐ one := eqb_of_eq hr
    have kq : Δ ⊢[PRAAx] k ≐ d * quo k d :=
      (Prf.andE₁ (div_mod_at (Γ := Δ) (x := k) hd.wk)).eqTrans ((congrAdd (.eqRefl _) hr).eqTrans (add_zero _))
    have sd : Δ ⊢[PRAAx] sg d ≐ one := sg_pos hd.wk
    refine .orE (zero_or_succ (quo k d)) ?_ ?_
    · let Δ' : List (Fm PTm n) := (quo k d ≐ zero) :: Δ
      have q0 : Δ' ⊢[PRAAx] quo k d ≐ zero := Prf.hyp0
      have k0 : Δ' ⊢[PRAAx] sg k ≐ zero :=
        (congrSg (kq.wk.eqTrans ((congrMul (.eqRefl _) q0).eqTrans (mul_zero _)))).eqTrans sg_zero
      have sq0 : Δ' ⊢[PRAAx] sg (quo k d) ≐ zero := (congrSg q0).eqTrans sg_zero
      refine (zero_mul_l (zero_mul_l (zero_mul_l k0 _) _) _).eqTrans ?_
      exact ((congrMul (.eqRefl _) (zero_mul_l (zero_mul_l
        ((congrMul (.eqRefl _) sq0).eqTrans (mul_zero _)) _) _)).eqTrans (mul_zero _)).eqSymm
    · let Δ' : List (Fm PTm n) := (quo k d ≐ succ (pred (quo k d))) :: Δ
      have hq : Δ' ⊢[PRAAx] quo k d ≐ succ (pred (quo k d)) := Prf.hyp0
      have kq' : Δ' ⊢[PRAAx] k ≐ d * quo k d := kq.wk
      have hk : Δ' ⊢[PRAAx] k ≐ succ (pred k) := kq'.eqTrans ((pos_mul' hd.wk.wk hq).eqTrans
        (congrSucc (congrPred kq'.eqSymm)))
      have sk := sg_pos hk
      have sq := sg_pos hq
      refine (congrMul (congrMul (congrMul sk (congrEqb' (congrAp2 remF (.eqRefl _) kq') (.eqRefl _)))
        (congrMul (congrMul sd.wk er.wk) (.eqRefl _))) (congrInst2 h (congrAp2 quoF (.eqRefl _) kq') (.eqRefl _))).eqTrans ?_
      refine .eqTrans ?_ (congrMul er.wk (congrMul (congrMul (congrMul (.eqRefl _) sq) (.eqRefl _)) (.eqRefl _))).eqSymm
      ipra_ring
  · let Δ : List (Fm PTm n) := neg (rem k d ≐ zero) :: Γ
    have e0 : Δ ⊢[PRAAx] eqb (rem k d) zero ≐ zero := eqb_of_ne Prf.hyp0
    refine (zero_mul_l ((congrMul (.eqRefl _) (zero_mul_l ((congrMul (.eqRefl _) e0).eqTrans (mul_zero _)) _)).eqTrans
      (mul_zero _)) _).eqTrans ?_
    exact (zero_mul_l e0 _).eqSymm

/-- Column `d ≥ 1`: `Σ_{k ≤ m} [k ∣ m][d ∣ k] f(d) g(k/d) h(m/k) = Σ_{e ≤ m/d} H(e)`. -/
theorem col_eq {d m y : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ ⊢[PRAAx] ap2 (sumF (colB (aT f g h))) (succ m) (pairT d (pairT m y)) ≐
      ap2 (sumF (HB f g h)) (succ (quo m d)) (pairT d (pairT m y)) := by
  refine (sum_congr_bounded _ (riB (HB f g h)) _ (pairT d (pairT d (pairT m y))) (succ m) (.allI (.impI ?_))).eqTrans
    ((reindex_eq (HB f g h) (succ m) hd).eqTrans
      (congrAp2 (sumF (HB f g h)) (multiples_upto hd) (.eqRefl _)))
  simp only [shift_pairT]
  exact col_pt f g h (shift_pos hd).wk

/-- A column of the rectangle equals the corresponding row of `f * (g * h)`. -/
theorem col_row (d m y : PTm n) :
    Γ ⊢[PRAAx] inst2 (pB (aT f g h)) d (pairT (succ m) (pairT m y)) ≐ inst2 (cvB f (cvF g h)) d (pairT m y) := by
  rw [inst2_pB]
  refine (congrAp2 (sumF (colB (aT f g h))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  refine .orE (zero_or_succ d) ?_ ?_
  · let Δ : List (Fm PTm n) := (d ≐ zero) :: Γ
    have s0 : Δ ⊢[PRAAx] sg d ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    have hz : Δ ⊢[PRAAx] ap2 (sumF (colB (aT f g h))) (succ m) (pairT d (pairT m y)) ≐ zero := by
      refine (sum_congr_bounded _ (zero : PTm 2) (pairT d (pairT m y)) (pairT d (pairT m y)) (succ m)
        (.allI (.impI ?_))).eqTrans (sum_zeroB _ _)
      rw [show inst2 (zero : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift (pairT d (pairT m y))) = zero by simp [inst2],
        inst2_colB, shift_pairT]
      refine (congrInst3 (aT f g h) (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans ?_
      rw [inst3_aT]
      have s0' : (lt (var 0) (Syn.shift (succ m)) :: Δ.map Fm.shift) ⊢[PRAAx] sg (Syn.shift d) ≐ zero := by
        have a := (Prf.hyp0 : Δ ⊢[PRAAx] d ≐ zero).shift
        simp only [Fm.shift, Fm.subst_eq, ConciseIPRA.PTm.subst_zero] at a
        exact (congrSg (a.wk : (lt (var 0) (Syn.shift (succ m)) :: Δ.map Fm.shift) ⊢[PRAAx] Syn.shift d ≐ zero)).eqTrans sg_zero
      refine zero_mul_l ((congrMul (.eqRefl _) ((cv_at f g _ _ _).eqTrans (zero_mul_l (zero_mul_l s0' _) _))).eqTrans
        (mul_zero _)) _
    exact hz.eqTrans ((cv_at f (cvF g h) d m y).eqTrans (zero_mul_l (zero_mul_l s0 _) _)).eqSymm
  · let Δ : List (Fm PTm n) := (d ≐ succ (pred d)) :: Γ
    have hd : Δ ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
    exact (col_eq f g h hd).eqTrans (lhs_row f g h hd).eqSymm

/-- Associativity: `(f * (g * h))(m) = ((f * g) * h)(m)`. -/
theorem conv_assoc (m y : PTm n) :
    Γ ⊢[PRAAx] conv f (cvF g h) m y ≐ conv (cvF f g) h m y := by
  have r : Γ ⊢[PRAAx] conv (cvF f g) h m y ≐
      ap2 (sumF (oB (aT f g h))) (succ m) (pairT (succ m) (pairT m y)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [show Syn.shift (succ m) = succ (Syn.shift m) by simp [Syn.shift]]
    have hk : (lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (succ (Syn.shift m)) := by
      rw [show succ (Syn.shift m) = Syn.shift (succ m) by simp [Syn.shift]]; exact Prf.hyp0
    exact rhs_row f g h hk
  have l : Γ ⊢[PRAAx] ap2 (sumF (pB (aT f g h))) (succ m) (pairT (succ m) (pairT m y)) ≐ conv f (cvF g h) m y := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [show Syn.shift (succ m) = succ (Syn.shift m) by simp [Syn.shift]]
    exact col_row f g h _ _ _
  exact (r.eqTrans ((fubini (aT f g h) (succ m) (succ m) (pairT m y)).eqTrans l)).eqSymm

end Assoc

/-! ## Selberg's identity in divisor form -/

section SelbergDivisor

variable (w : PTm 2)

/-- A divisor term of `Λ_w * L_w` equals the one of `Λ_w * (Λ_w * 𝟏)`, for `m ≥ 1`. -/
theorem lamL_pt {d m y : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] inst2 (cvB (lamF w) (DwB w one)) d (pairT m y) ≐
      inst2 (cvB (lamF w) (cvF (lamF w) one)) d (pairT m y) := by
  refine (cv_at _ _ _ _ _).eqTrans (.eqTrans ?_ (cv_at _ _ _ _ _).eqSymm)
  rw [inst2_DwB, inst2_cvF, show inst2 (one : PTm 2) (quo m d) y = one by simp [inst2]]
  refine .orE (zero_or_succ d) ?_ ?_
  · let Δ : List (Fm PTm n) := (d ≐ zero) :: Γ
    have s0 : Δ ⊢[PRAAx] sg d ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    exact (zero_mul_l (zero_mul_l s0 _) _).eqTrans (zero_mul_l (zero_mul_l s0 _) _).eqSymm
  · let Δ : List (Fm PTm n) := (d ≐ succ (pred d)) :: Γ
    have hd : Δ ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
    refine .orE (eq_or_ne (rem m d) zero) ?_ ?_
    · let Δ' : List (Fm PTm n) := (rem m d ≐ zero) :: Δ
      have hr : Δ' ⊢[PRAAx] rem m d ≐ zero := Prf.hyp0
      have mq : Δ' ⊢[PRAAx] m ≐ d * quo m d :=
        (Prf.andE₁ (div_mod_at (Γ := Δ') (x := m) hd.wk)).eqTrans ((congrAdd (.eqRefl _) hr).eqTrans (add_zero _))
      have hq : Δ' ⊢[PRAAx] quo m d ≐ succ (pred (quo m d)) := by
        refine .orE (zero_or_succ (quo m d)) ?_ Prf.hyp0
        refine .botE _ (succ_ne_zero (a := pred m) ?_)
        have q0 : ((quo m d ≐ zero) :: Δ') ⊢[PRAAx] quo m d ≐ zero := Prf.hyp0
        exact (hm.wk.wk.wk.eqSymm.eqTrans (mq.wk.eqTrans ((congrMul (.eqRefl _) q0).eqTrans (mul_zero _))))
      refine congrMul (.eqRefl _) (congrMul (.eqRefl _) ?_)
      exact ((mul_comm _ _).eqTrans (one_mul _)).eqTrans (lam_conv_one w hq).eqSymm
    · let Δ' : List (Fm PTm n) := neg (rem m d ≐ zero) :: Δ
      have e0 : Δ' ⊢[PRAAx] sg d * eqb (rem m d) zero ≐ zero :=
        (congrMul (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans (mul_zero _)
      exact (zero_mul_l e0 _).eqTrans (zero_mul_l e0 _).eqSymm

/-- `(Λ_w * L_w)(m) = ((Λ_w * Λ_w) * 𝟏)(m)` for `m ≥ 1`. -/
theorem lam_conv_L {m y : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] conv (lamF w) (DwB w one) m y ≐ conv (cvF (lamF w) (lamF w)) one m y := by
  refine .eqTrans ?_ (conv_assoc (lamF w) (lamF w) one m y)
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  exact lamL_pt w (shift_pos hm).wk

/-- Selberg's identity in divisor form: `L_w(m)² = (𝟏 * 𝒟_w Λ_w)(m) + (𝟏 * (Λ_w * Λ_w))(m)`, i.e.
`L_w(m)² = Σ_{d ∣ m} L_w(d) Λ_w(d) + Σ_{k ∣ m} (Λ_w * Λ_w)(k)` for `m ≥ 1`. -/
theorem selberg_divisor {m y : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] Lw w m y * Lw w m y ≐
      conv (DwB w (lamF w)) one m y + conv (cvF (lamF w) (lamF w)) one m y :=
  (selberg_leibniz w hm).eqTrans (congrAdd (.eqRefl _) (lam_conv_L w hm))

end SelbergDivisor

end LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc
