import IPRADerivations.AnalyticNumberTheory.SymmetryPointwise
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# The symmetry bound (`pnt_ipra_constructive_2026-11-14`, `sb:symmetry-bound`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, Lemma `sb:symmetry`:
for `A(x) = Σ_{n≤x} (Λ(n) log n + (Λ * Λ)(n))`, "`|A(x) − 2x log x| ≤ 2048x`". The proof there: apply the comparison
error at `y = x/d` for every `d ≤ x`, use `|μ(d)| ≤ 1`, reverse the finite sums, and bound
`Σ_{d≤x} √(x/d)(log(x/d) + 1)` by a fourth-root sum. Here, scaled by `F = L!` with the finite `C = F c`:

* `mu_pm`: `μ⁺(d) + μ⁻(d) ≤ 1` (`par_le`: `[r = 0] + [r = 1] ≤ 1`);
* `stepA`/`stepB`, `baseA`/`baseB`: the summed comparison as two inequalities between Möbius-weighted sums,
  one step of `d` at a time, with opaque terms (the `ipra_le` certificates found by elimination);
* `i_step`, `sym₀`, `sym_sums`: one closed QF induction over `d ≤ x` that feeds `SymmetryPointwise.point_upper`
  and `point_lower` at `m = ⌊x/d⌋`, weighted by `μ⁺(d)` and `μ⁻(d)`;
* `sym_raw_upper`/`sym_raw_lower`: after the exact inversions (`SymmetrySum.symmetry_sum`, three instances of
  `MobiusSummatory.mobius_summatory` evaluated by `SymmetryInstances`),
  `A_w(x) + 2CFx ≤ 2F Σ_{n≤x} L_w(n) + 4C² + 146F² W(x) + 2F²x` and the reverse with the roles exchanged,
  `W(x) = Σ_{d≤x} (⌊(x/d)^{1/4}⌋ + 1)³`;
* `symmetry_upper`/`symmetry_lower`: with `W(x) ≤ 15x` (`FourthRootSum.fourth_root_sum`) and `0 ≤ C ≤ F`,
  `|A_w(x) − 2F Σ_{n≤x} L_w(n)| ≤ 2200 F² x` — the scaled symmetry bound, `c` eliminated.

Hypotheses: `x ≥ 1`, `K ≥ 1`, `(x+1)⁴ ≤ K`, `K (x+1)⁴ ≤ L`. The passage from `Σ L_w(n)` to `x log x − x` is
`HarmonicLogSum` with `WeightBridge`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SymmetryBound

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.TauLogAbel (CT c_nonneg)
open LeanProofs.IPRA.AnalyticNumberTheory.ComparisonEnvelope (le_mul2 harm_one)
open LeanProofs.IPRA.AnalyticNumberTheory.FourthRootSum (qr Q4 WB inst2_WB fourth_root_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetrySum (aPB aNB inst2_aP inst2_aN bL GxB symmetry_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusSummatory (bF gS mobius_summatory)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (RB RB_at Bs)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryInstances (tau_bs eps_bs tw_bs twB epsB sum_sg_one sum_sg_eps)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryPointwise (Hyp W point_upper point_lower le_Q4)
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (DwB)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrEqb' zero_ne_one' zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHyperbola (quo_le_self)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination (sg_le_one)
open LeanProofs.IPRA.AnalyticNumberTheory.TotientCorollaries (eqb_le_one)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## `μ⁺ + μ⁻ ≤ 1` and `⌊x/d⌋ ≥ 1` -/

theorem par_le (r : PTm n) : Γ ⊢[PRAAx] le (eqb r zero + eqb r one) one := by
  refine .orE (zero_or_succ r) ?_ ?_
  · let C : List (Fm PTm n) := (r ≐ zero) :: Γ
    have e1 : C ⊢[PRAAx] eqb r one ≐ zero := (congrEqb' Prf.hyp0 (.eqRefl _)).eqTrans (eqb_of_ne zero_ne_one')
    have b := eqb_le_one (Γ := C) r zero
    have z := natEq e1
    ipra_le sl b with z
  · let C : List (Fm PTm n) := (r ≐ succ (pred r)) :: Γ
    have e0 : C ⊢[PRAAx] eqb r zero ≐ zero :=
      eqb_of_ne (.impI (succ_ne_zero' _ ((Prf.hyp1 : ((r ≐ zero) :: C) ⊢[PRAAx] _).eqSymm.eqTrans Prf.hyp0)))
    have b := eqb_le_one (Γ := C) r one
    have z := natEq e0
    ipra_le sl b with z

/-- `μ⁺(d) + μ⁻(d) ≤ 1`, both with the factor `[d ≥ 1]`. -/
theorem mu_pm (d : PTm n) :
    Γ ⊢[PRAAx] le (sg d * Mobius.muP (succ d) d + sg d * Mobius.muN (succ d) d) one := by
  have p := le_mul2 (sg_le_one (Γ := Γ) d) (le_mul2 (eqb_le_one (Mobius.sq (succ d) d) zero)
    (par_le (rem (Mobius.om (succ d) d) two)))
  ipra_le sl p

/-- `⌊x/q⌋ ≥ 1` for `1 ≤ q ≤ x`. -/
theorem quo_pos {x q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (h : Γ ⊢[PRAAx] le q x) :
    Γ ⊢[PRAAx] quo x q ≐ succ (pred (quo x q)) := by
  have dm := div_mod_at (Γ := Γ) (x := x) hq
  refine .orE (zero_or_succ (quo x q)) ?_ Prf.hyp0
  let C : List (Fm PTm n) := (quo x q ≐ zero) :: Γ
  have e := natEq ((Prf.andE₁ dm).wk (ψ := quo x q ≐ zero)); have z := natEq (Prf.hyp0 : C ⊢[PRAAx] quo x q ≐ zero)
  have er : C ⊢[PRAAx] rem x q ≐ x := by apply deriveNat; ipra_simps; linear_combination -e - 𝔞 q * z
  have hl : C ⊢[PRAAx] lt x x := le_trans (le_congr (congrSucc er) (.eqRefl _) ((Prf.andE₂ dm).wk (ψ := quo x q ≐ zero))) (h.wk (ψ := quo x q ≐ zero))
  exact lt_irrefl x _ hl

/-! ## The generic summation step -/

/-- The upper invariant: `B⁺ + 2CF D⁺ + 2F L⁻ + 4C² E⁻ ≤ 2F L⁺ + 4C² E⁺ + B⁻ + 2CF D⁻ + 146F² W + 2F² N`. -/
abbrev IAf (bP bN lP lN oP oN eP eN w N F C : PTm n) : Fm PTm n :=
  le (bP + two * (C * (F * oP)) + two * (F * lN) + two * (two * (C * (C * eN))))
    (two * (F * lP) + two * (two * (C * (C * eP))) + bN + two * (C * (F * oN)) + num 146 * (F * F * w) +
      two * (F * F) * N)

/-- The lower invariant, the roles of `μ⁺` and `μ⁻` exchanged. -/
abbrev IBf (bP bN lP lN oP oN eP eN w N F C : PTm n) : Fm PTm n :=
  le (two * (F * lP) + two * (two * (C * (C * eP))) + bN + two * (C * (F * oN)))
    (bP + two * (C * (F * oP)) + two * (F * lN) + two * (two * (C * (C * eN))) + num 146 * (F * F * w) +
      two * (F * F) * N)

section Step
variable {bP bN lP lN oP oN eP eN w N bP1 bN1 lP1 lN1 oP1 oN1 eP1 eN1 w1 mp mn Bb B1 B2 B3 Bb0 Tw0 D0 m0 W0 Wm
  F C : PTm n}
  (lo : Γ ⊢[PRAAx] le (Bb0 + two * (C * (F * D0)))
    (F * Tw0 + two * (two * (C * (C * m0))) + (num 146 * (F * F * W0) + two * (F * F))))
  (up : Γ ⊢[PRAAx] le (F * Tw0 + two * (two * (C * (C * m0))))
    (Bb0 + two * (C * (F * D0)) + (num 146 * (F * F * W0) + two * (F * F))))
  (hμ : Γ ⊢[PRAAx] le (mp + mn) one)
  (eTw : Γ ⊢[PRAAx] Tw0 ≐ two * B1) (eD : Γ ⊢[PRAAx] D0 ≐ B2) (em : Γ ⊢[PRAAx] m0 ≐ B3)
  (eBb : Γ ⊢[PRAAx] Bb0 ≐ Bb) (eW : Γ ⊢[PRAAx] W0 ≐ Wm)
  (ebP : Γ ⊢[PRAAx] bP1 ≐ bP + mp * Bb) (ebN : Γ ⊢[PRAAx] bN1 ≐ bN + mn * Bb)
  (elP : Γ ⊢[PRAAx] lP1 ≐ lP + mp * B1) (elN : Γ ⊢[PRAAx] lN1 ≐ lN + mn * B1)
  (eoP : Γ ⊢[PRAAx] oP1 ≐ oP + mp * B2) (eoN : Γ ⊢[PRAAx] oN1 ≐ oN + mn * B2)
  (eeP : Γ ⊢[PRAAx] eP1 ≐ eP + mp * B3) (eeN : Γ ⊢[PRAAx] eN1 ≐ eN + mn * B3)
  (ew : Γ ⊢[PRAAx] w1 ≐ w + Wm)
include lo up hμ eTw eD em eBb eW ebP ebN elP elN eoP eoN eeP eeN ew

theorem stepA (ih : Γ ⊢[PRAAx] IAf bP bN lP lN oP oN eP eN w N F C) :
    Γ ⊢[PRAAx] IAf bP1 bN1 lP1 lN1 oP1 oN1 eP1 eN1 w1 (succ N) F C := by
  have p1 := le_scale mp lo; have p2 := le_scale mn up
  have p3 := le_scale (num 146 * (F * F * W0) + two * (F * F)) hμ
  have fTw := natEq eTw; have fD := natEq eD; have fm := natEq em; have fBb := natEq eBb; have fW := natEq eW
  have gbP := natEq ebP; have gbN := natEq ebN; have glP := natEq elP; have glN := natEq elN
  have goP := natEq eoP; have goN := natEq eoN; have geP := natEq eeP; have geN := natEq eeN; have gw := natEq ew
  ipra_le sl ih + sl p1 + sl p2 + sl p3 with
    𝔞 F * (𝔞 mn - 𝔞 mp) * fTw - 2 * 𝔞 C * 𝔞 F * (𝔞 mn - 𝔞 mp) * fD + 4 * 𝔞 C * 𝔞 C * (𝔞 mn - 𝔞 mp) * fm +
    (𝔞 mp - 𝔞 mn) * fBb - 146 * 𝔞 F * 𝔞 F * fW - gbP + gbN + 2 * 𝔞 F * glP - 2 * 𝔞 F * glN -
    2 * 𝔞 C * 𝔞 F * goP + 2 * 𝔞 C * 𝔞 F * goN + 4 * 𝔞 C * 𝔞 C * geP - 4 * 𝔞 C * 𝔞 C * geN +
    146 * 𝔞 F * 𝔞 F * gw

theorem stepB (ih : Γ ⊢[PRAAx] IBf bP bN lP lN oP oN eP eN w N F C) :
    Γ ⊢[PRAAx] IBf bP1 bN1 lP1 lN1 oP1 oN1 eP1 eN1 w1 (succ N) F C := by
  have p1 := le_scale mp up; have p2 := le_scale mn lo
  have p3 := le_scale (num 146 * (F * F * W0) + two * (F * F)) hμ
  have fTw := natEq eTw; have fD := natEq eD; have fm := natEq em; have fBb := natEq eBb; have fW := natEq eW
  have gbP := natEq ebP; have gbN := natEq ebN; have glP := natEq elP; have glN := natEq elN
  have goP := natEq eoP; have goN := natEq eoN; have geP := natEq eeP; have geN := natEq eeN; have gw := natEq ew
  ipra_le sl ih + sl p1 + sl p2 + sl p3 with
    -(𝔞 F * (𝔞 mn - 𝔞 mp) * fTw) + 2 * 𝔞 C * 𝔞 F * (𝔞 mn - 𝔞 mp) * fD - 4 * 𝔞 C * 𝔞 C * (𝔞 mn - 𝔞 mp) * fm +
    (𝔞 mn - 𝔞 mp) * fBb - 146 * 𝔞 F * 𝔞 F * fW + gbP - gbN - 2 * 𝔞 F * glP + 2 * 𝔞 F * glN +
    2 * 𝔞 C * 𝔞 F * goP - 2 * 𝔞 C * 𝔞 F * goN - 4 * 𝔞 C * 𝔞 C * geP + 4 * 𝔞 C * 𝔞 C * geN +
    146 * 𝔞 F * 𝔞 F * gw

end Step

section Base
variable {bP bN lP lN oP oN eP eN w F C : PTm n}
  (zbP : Γ ⊢[PRAAx] bP ≐ zero) (zbN : Γ ⊢[PRAAx] bN ≐ zero) (zlP : Γ ⊢[PRAAx] lP ≐ zero)
  (zlN : Γ ⊢[PRAAx] lN ≐ zero) (zoP : Γ ⊢[PRAAx] oP ≐ zero) (zoN : Γ ⊢[PRAAx] oN ≐ zero)
  (zeP : Γ ⊢[PRAAx] eP ≐ zero) (zeN : Γ ⊢[PRAAx] eN ≐ zero) (zw : Γ ⊢[PRAAx] w ≐ zero)
include zbP zbN zlP zlN zoP zoN zeP zeN zw

theorem baseA : Γ ⊢[PRAAx] IAf bP bN lP lN oP oN eP eN w zero F C := by
  have a1 := natEq zbP; have a2 := natEq zbN; have a3 := natEq zlP; have a4 := natEq zlN; have a5 := natEq zoP
  have a6 := natEq zoN; have a7 := natEq zeP; have a8 := natEq zeN; have a9 := natEq zw
  ipra_le 0 with -a1 + a2 + 2 * 𝔞 F * a3 - 2 * 𝔞 F * a4 - 2 * 𝔞 C * 𝔞 F * a5 + 2 * 𝔞 C * 𝔞 F * a6 +
    4 * 𝔞 C * 𝔞 C * a7 - 4 * 𝔞 C * 𝔞 C * a8 + 146 * 𝔞 F * 𝔞 F * a9

theorem baseB : Γ ⊢[PRAAx] IBf bP bN lP lN oP oN eP eN w zero F C := by
  have a1 := natEq zbP; have a2 := natEq zbN; have a3 := natEq zlP; have a4 := natEq zlN; have a5 := natEq zoP
  have a6 := natEq zoN; have a7 := natEq zeP; have a8 := natEq zeN; have a9 := natEq zw
  ipra_le 0 with a1 - a2 - 2 * 𝔞 F * a3 + 2 * 𝔞 F * a4 + 2 * 𝔞 C * 𝔞 F * a5 - 2 * 𝔞 C * 𝔞 F * a6 -
    4 * 𝔞 C * 𝔞 C * a7 + 4 * 𝔞 C * 𝔞 C * a8 + 146 * 𝔞 F * 𝔞 F * a9

end Base

/-! ## The concrete sums -/

/-- `L_w` as an inversion body: `g = 𝒟_w 𝟏`. -/
abbrev gL : PTm 2 := DwB wt one

/-- `Σ_{d≤N} [d ≥ 1] a(d) B_b(⌊x/d⌋)` with `y = (K, L!)`. -/
abbrev sm (a b : PTm 2) (N x K L : PTm n) : PTm n := ap2 (sumF (RB a b)) (succ N) (pairT x (pairT K (fact L)))

abbrev IA (N x K L : PTm n) : Fm PTm n :=
  IAf (sm aPB (bL wt) N x K L) (sm aNB (bL wt) N x K L) (sm aPB (bF gL) N x K L) (sm aNB (bF gL) N x K L)
    (sm aPB (bF one) N x K L) (sm aNB (bF one) N x K L) (sm aPB (bF epsB) N x K L) (sm aNB (bF epsB) N x K L)
    (ap2 (sumF WB) N x) N (fact L) (CT K x (fact L))

abbrev IB (N x K L : PTm n) : Fm PTm n :=
  IBf (sm aPB (bL wt) N x K L) (sm aNB (bL wt) N x K L) (sm aPB (bF gL) N x K L) (sm aNB (bF gL) N x K L)
    (sm aPB (bF one) N x K L) (sm aNB (bF one) N x K L) (sm aPB (bF epsB) N x K L) (sm aNB (bF epsB) N x K L)
    (ap2 (sumF WB) N x) N (fact L) (CT K x (fact L))

abbrev Hy (N x K L : PTm n) : Fm PTm n := le N x ⋏ (le one K ⋏ (le (Q4 x) K ⋏ le (K * Q4 x) L))

theorem sm_zero (a b : PTm 2) (x K L : PTm n) : Γ ⊢[PRAAx] sm a b zero x K L ≐ zero :=
  (sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) (RB_at _ _ _ _ _)).eqTrans
    ((congrAdd (.eqRefl _) (zero_mul_l (zero_mul_l sg_zero _) _)).eqTrans (add_zero _)))

theorem sm_succ (a b : PTm 2) (N x K L : PTm n) :
    Γ ⊢[PRAAx] sm a b (succ N) x K L ≐ sm a b N x K L +
      (sg (succ N) * inst2 a (succ N) (pairT K (fact L))) * Bs b (quo x (succ N)) (pairT K (fact L)) :=
  (sum_succ' _ _ _).eqTrans (congrAdd (.eqRefl _) (RB_at _ _ _ _ _))

theorem i_zero (x K L : PTm n) : Γ ⊢[PRAAx] IA zero x K L ⋏ IB zero x K L := by
  have z := fun (a b : PTm 2) => sm_zero (Γ := Γ) a b x K L
  have zw := sum_zero (Γ := Γ) WB x
  exact .andI (baseA (z _ _) (z _ _) (z _ _) (z _ _) (z _ _) (z _ _) (z _ _) (z _ _) zw)
    (baseB (z _ _) (z _ _) (z _ _) (z _ _) (z _ _) (z _ _) (z _ _) (z _ _) zw)

theorem congrW {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] W a ≐ W b :=
  have s := congrSucc (congrAp1 isqrtF (congrAp1 isqrtF h))
  congrMul (congrMul s s) s

theorem i_step {N x K L : PTm n} (h : Γ ⊢[PRAAx] Hy (succ N) x K L) (ih : Γ ⊢[PRAAx] IA N x K L ⋏ IB N x K L) :
    Γ ⊢[PRAAx] IA (succ N) x K L ⋏ IB (succ N) x K L := by
  have hd := Prf.andE₁ h
  have hK := Prf.andE₁ (Prf.andE₂ h)
  have hx4 := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have hL := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))
  have dpos : Γ ⊢[PRAAx] succ N ≐ succ (pred (succ N)) := congrSucc (pred_succ _).eqSymm
  have hm := quo_pos dpos hd
  have hmx := quo_le_self (Γ := Γ) N x
  have H : Hyp (pred (quo x (succ N))) K L x Γ := ⟨hK, le_congr hm (.eqRefl _) hmx, hx4, hL⟩
  have pu := point_upper H
  have pl := point_lower H
  have eTw := (congrAp2 (sumF twB) hm.eqSymm (.eqRefl (pairT K (fact L)))).eqTrans (tw_bs (Γ := Γ) _ _)
  have eD := (congrAp2 (sumF hB) hm.eqSymm hm.eqSymm).eqTrans (tau_bs (Γ := Γ) (quo x (succ N)) (pairT K (fact L))).eqSymm
  have em := hm.eqSymm.eqTrans (eps_bs (Γ := Γ) (quo x (succ N)) (pairT K (fact L))).eqSymm
  have eBb : Γ ⊢[PRAAx] Bs (bL wt) (succ (pred (quo x (succ N)))) (pairT K (fact L)) ≐
      Bs (bL wt) (quo x (succ N)) (pairT K (fact L)) := congrAp2 _ hm.eqSymm (.eqRefl _)
  have eW := congrW hm.eqSymm
  have hμ := mu_pm (Γ := Γ) (succ N)
  rw [← inst2_aP (succ N) (pairT K (fact L)), ← inst2_aN (succ N) (pairT K (fact L))] at hμ
  have ew := sum_succ' (Γ := Γ) WB N x
  rw [inst2_WB] at ew
  have s := fun (a b : PTm 2) => sm_succ (Γ := Γ) a b N x K L
  exact .andI (stepA pl pu hμ eTw eD em eBb eW (s _ _) (s _ _) (s _ _) (s _ _) (s _ _) (s _ _) (s _ _) (s _ _) ew
      (Prf.andE₁ ih))
    (stepB pl pu hμ eTw eD em eBb eW (s _ _) (s _ _) (s _ _) (s _ _) (s _ _) (s _ _) (s _ _) (s _ _) ew
      (Prf.andE₂ ih))

/-- Variables `0 = N`, `1 = x`, `2 = K`, `3 = L`. -/
private abbrev symF : Fm PTm 4 :=
  Hy (var 0) (var 1) (var 2) (var 3) ⟶ (IA (var 0) (var 1) (var 2) (var 3) ⋏ IB (var 0) (var 1) (var 2) (var 3))

private theorem sym₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] symF := by
  ipra_ind (⟨⟨le_QF _ _, le_QF _ _, le_QF _ _, le_QF _ _⟩, le_QF _ _, le_QF _ _⟩) [subst_le, subst_ap2, subst_ap1,
      subst_pairT]
  · exact .impI (i_zero _ _ _)
  · refine .impI ?_
    have h := (Prf.hyp0 : (Hy (succ (var 0)) (var 1) (var 2) (var 3) :: [symF]) ⊢[PRAAx]
      Hy (succ (var 0)) (var 1) (var 2) (var 3))
    have h' : (Hy (succ (var 0)) (var 1) (var 2) (var 3) :: [symF]) ⊢[PRAAx] Hy (var 0) (var 1) (var 2) (var 3) :=
      .andI (le_trans (le_succ_self _) (Prf.andE₁ h)) (Prf.andE₂ h)
    exact i_step h (Prf.impE Prf.hyp1 h')

/-- Both summed comparisons at `d ≤ x`. -/
theorem sym_sums {x K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hx4 : Γ ⊢[PRAAx] le (Q4 x) K)
    (hL : Γ ⊢[PRAAx] le (K * Q4 x) L) : Γ ⊢[PRAAx] IA x x K L ⋏ IB x x K L := by
  have i := inst (Γ := Γ) sym₀ (![x, x, K, L] : Fin 4 → PTm n)
  simp at i
  exact Prf.impE i (.andI (le_refl _) (.andI hK (.andI hx4 hL)))

/-! ## Inverting the sums -/

section Final
variable {bP bN lP lN oP oN eP eN w A Ls X1 X2 x F C : PTm n}
  (e1 : Γ ⊢[PRAAx] bP ≐ A + bN) (e2 : Γ ⊢[PRAAx] lP ≐ Ls + lN) (e3 : Γ ⊢[PRAAx] oP ≐ X1 + oN)
  (e5 : Γ ⊢[PRAAx] X1 ≐ x) (e4 : Γ ⊢[PRAAx] eP ≐ X2 + eN) (e6 : Γ ⊢[PRAAx] X2 ≐ one)
include e1 e2 e3 e5 e4 e6

theorem finA (ih : Γ ⊢[PRAAx] IAf bP bN lP lN oP oN eP eN w x F C) :
    Γ ⊢[PRAAx] le (A + two * (C * (F * x)))
      (two * (F * Ls) + two * (two * (C * C)) + num 146 * (F * F * w) + two * (F * F) * x) := by
  have f1 := natEq e1; have f2 := natEq e2; have f3 := natEq e3; have f5 := natEq e5; have f4 := natEq e4
  have f6 := natEq e6
  ipra_le sl ih with f1 - 2 * 𝔞 F * f2 + 2 * 𝔞 C * 𝔞 F * f3 + 2 * 𝔞 C * 𝔞 F * f5 - 4 * 𝔞 C * 𝔞 C * f4 -
    4 * 𝔞 C * 𝔞 C * f6

theorem finB (ih : Γ ⊢[PRAAx] IBf bP bN lP lN oP oN eP eN w x F C) :
    Γ ⊢[PRAAx] le (two * (F * Ls) + two * (two * (C * C)))
      (A + two * (C * (F * x)) + num 146 * (F * F * w) + two * (F * F) * x) := by
  have f1 := natEq e1; have f2 := natEq e2; have f3 := natEq e3; have f5 := natEq e5; have f4 := natEq e4
  have f6 := natEq e6
  ipra_le sl ih with -f1 + 2 * 𝔞 F * f2 - 2 * 𝔞 C * 𝔞 F * f3 - 2 * 𝔞 C * 𝔞 F * f5 + 4 * 𝔞 C * 𝔞 C * f4 +
    4 * 𝔞 C * 𝔞 C * f6

end Final

/-- `A_w(x) = Σ_{n≤x} (Λ_w(n) L_w(n) + (Λ_w * Λ_w)(n))`. -/
abbrev Aw (x K L : PTm n) : PTm n := ap2 (sumF (GxB wt)) (succ x) (pairT K (fact L))

/-- `Σ_{n≤x} L_w(n)`. -/
abbrev Ls (x K L : PTm n) : PTm n := ap2 (sumF (gS gL)) (succ x) (pairT K (fact L))

section Raw
variable {x K L : PTm n} (hx : Γ ⊢[PRAAx] le one x) (hK : Γ ⊢[PRAAx] le one K) (hx4 : Γ ⊢[PRAAx] le (Q4 x) K)
  (hL : Γ ⊢[PRAAx] le (K * Q4 x) L)
include hx hK hx4 hL

theorem sym_raw_upper :
    Γ ⊢[PRAAx] le (Aw x K L + two * (CT K x (fact L) * (fact L * x)))
      (two * (fact L * Ls x K L) + two * (two * (CT K x (fact L) * CT K x (fact L))) +
        num 146 * (fact L * fact L * ap2 (sumF WB) x x) + two * (fact L * fact L) * x) :=
  finA (symmetry_sum wt x _) (mobius_summatory gL x _) (mobius_summatory one x _) (sum_sg_one x _)
    (mobius_summatory epsB x _) (sum_sg_eps _ hx) (Prf.andE₁ (sym_sums hK hx4 hL))

theorem sym_raw_lower :
    Γ ⊢[PRAAx] le (two * (fact L * Ls x K L) + two * (two * (CT K x (fact L) * CT K x (fact L))))
      (Aw x K L + two * (CT K x (fact L) * (fact L * x)) + num 146 * (fact L * fact L * ap2 (sumF WB) x x) +
        two * (fact L * fact L) * x) :=
  finB (symmetry_sum wt x _) (mobius_summatory gL x _) (mobius_summatory one x _) (sum_sg_one x _)
    (mobius_summatory epsB x _) (sum_sg_eps _ hx) (Prf.andE₂ (sym_sums hK hx4 hL))

end Raw

/-! ## The scaled symmetry bound -/

theorem bound_upper {A Ls w x F C : PTm n}
    (raw : Γ ⊢[PRAAx] le (A + two * (C * (F * x)))
      (two * (F * Ls) + two * (two * (C * C)) + num 146 * (F * F * w) + two * (F * F) * x))
    (hC : Γ ⊢[PRAAx] le C F) (hx : Γ ⊢[PRAAx] le one x)
    (hw : Γ ⊢[PRAAx] le w (x + succ (two * two + two) * (two * x))) :
    Γ ⊢[PRAAx] le A (two * (F * Ls) + num 2200 * (F * F * x)) := by
  have p := le_mul2 hC hC
  have q := le_scale (F * F) hx
  have r := le_scale (num 146 * (F * F)) hw
  ipra_le sl raw + 2 * (𝔞 C * 𝔞 F * 𝔞 x) + 4 * sl p + 4 * sl q + sl r + 4 * (𝔞 F * 𝔞 F * 𝔞 x)

theorem bound_lower {A Ls w x F C : PTm n}
    (raw : Γ ⊢[PRAAx] le (two * (F * Ls) + two * (two * (C * C)))
      (A + two * (C * (F * x)) + num 146 * (F * F * w) + two * (F * F) * x))
    (hC : Γ ⊢[PRAAx] le C F)
    (hw : Γ ⊢[PRAAx] le w (x + succ (two * two + two) * (two * x))) :
    Γ ⊢[PRAAx] le (two * (F * Ls)) (A + num 2200 * (F * F * x)) := by
  have t := mul_le_mul_right (two * (F * x)) hC
  have r := le_scale (num 146 * (F * F)) hw
  ipra_le sl raw + sl t + sl r + 4 * (𝔞 C * 𝔞 C) + 6 * (𝔞 F * 𝔞 F * 𝔞 x)

/-- `C = F (H_x + H_K − H_{Kx}) ≤ F`. -/
theorem c_le {x K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hx : Γ ⊢[PRAAx] le one x) (hL : Γ ⊢[PRAAx] le (K * x) L) :
    Γ ⊢[PRAAx] le (CT K x (fact L)) (fact L) := by
  have h := harm_one hK hx hL
  have e := natEq (eq_add_of_le (c_nonneg hK hx hL))
  ipra_le sl h with e

section Bound
variable {x K L : PTm n} (hx : Γ ⊢[PRAAx] le one x) (hK : Γ ⊢[PRAAx] le one K) (hx4 : Γ ⊢[PRAAx] le (Q4 x) K)
  (hL : Γ ⊢[PRAAx] le (K * Q4 x) L)
include hx hK hx4 hL

omit hx hK hx4 in
theorem hKx : Γ ⊢[PRAAx] le (K * x) L := le_trans (le_scale K (le_Q4 x)) hL

/-- `sb:symmetry-bound`, upper half, scaled: `A_w(x) ≤ 2F Σ_{n≤x} L_w(n) + 2200 F² x`. -/
theorem symmetry_upper : Γ ⊢[PRAAx] le (Aw x K L) (two * (fact L * Ls x K L) + num 2200 * (fact L * fact L * x)) :=
  bound_upper (sym_raw_upper hx hK hx4 hL) (c_le hK hx (hKx hL)) hx (fourth_root_sum x)

/-- `sb:symmetry-bound`, lower half, scaled: `2F Σ_{n≤x} L_w(n) ≤ A_w(x) + 2200 F² x`. -/
theorem symmetry_lower : Γ ⊢[PRAAx] le (two * (fact L * Ls x K L)) (Aw x K L + num 2200 * (fact L * fact L * x)) :=
  bound_lower (sym_raw_lower hx hK hx4 hL) (c_le hK hx (hKx hL)) (fourth_root_sum x)

end Bound

end LeanProofs.IPRA.AnalyticNumberTheory.SymmetryBound
