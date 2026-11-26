import IPRADerivations.AnalyticNumberTheory.GcdPhiSum
import IPRADerivations.Probability.Independence
import IPRADerivations.Core.Header

/-!
# The diagonalization of the Selberg quadratic form

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, `eq:sieve-diagonal`:
`Q(λ) = Σ_{d,e ∈ D} λ_d λ_e / [d, e] = Σ_{r ∈ D} φ(r) y_r²` with `y_r = Σ_{r ∣ d} λ_d / d`; "substitute
`gcd(d, e) = Σ_{r ∣ d, r ∣ e} φ(r)` into the double sum and interchange three finite sums".

Since `1/[d, e] = gcd(d, e)/(d e)`, with `u_d = λ_d/d` this is the bilinear identity

  `Σ_{1 ≤ d ≤ Z} Σ_{e < N} u_d v_e gcd(d, e) = Σ_{r ≤ Z} φ(r) (Σ_{1 ≤ d ≤ Z, r ∣ d} u_d) (Σ_{e < N, r ∣ e} v_e)`

for arbitrary natural bodies `u`, `v` (signed weights are differences of such bodies, and the identity is bilinear).

* `Ab`, `Bb`: the bodies `[d ≥ 1][r ∣ d] u_d` and `[r ∣ e] v_e φ(r)` over the parameter `⟨r, y⟩`;
* `Lb`: the body `[d ≥ 1] u_d v_e gcd(d, e)`; `Lpt`: for `d ≤ Z` it is `Σ_{r ≤ Z}` of the product body
  (`GcdPhiSum.gcd_phi_sum` and `sum_scale`);
* `rowL`: one row `d`, after exchanging the sums over `e` and `r` (`fubini`);
* `diag`: `Σ_d Σ_e L(d, e) = Σ_{r ≤ Z} pB a2 (r)`, after exchanging the sums over `d` and `r` (`fubini`);
* `diag_term`: each summand `pB a2 (r)` is the product `(Σ_d A_d(r)) (Σ_e B_e(r))` (`sum_mul_sum`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveDiagonal

open_ipra
open LeanProofs.IPRA.Signum (sg sg_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg congrEqb')
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody)
open LeanProofs.IPRA.AnalyticNumberTheory.GcdPhiSum (gB gB_at gcd_phi_sum)
open LeanProofs.IPRA.Probability.Independence (row_pt col_pt sum_scale dsum sum_mul_sum pmB inst3_pmB)

variable {n : ℕ} {Γ : List (Fm PTm n)}

section Diagonal

variable (u v : PTm 2)

/-! ## The bodies -/

/-- `[d ≥ 1][r ∣ d] u_d` over `0 = d`, `1 = ⟨r, y⟩`. -/
def Ab : PTm 2 := sg (var 0) * eqb (rem (var 0) (fstT (var 1))) zero * Syn.subst ![var 0, sndT (var 1)] u
/-- `[r ∣ e] v_e φ(r)` over `0 = e`, `1 = ⟨r, y⟩`. -/
def Bb : PTm 2 :=
  eqb (rem (var 0) (fstT (var 1))) zero * Syn.subst ![var 0, sndT (var 1)] v *
    ap2 (sumF totBody) (fstT (var 1)) (fstT (var 1))

theorem inst2_Ab (d z : PTm n) : inst2 (Ab u) d z = sg d * eqb (rem d (fstT z)) zero * inst2 u d (sndT z) := by
  have hf : Syn.subst ![d, z] (Syn.subst ![var 0, sndT (var 1)] u) = inst2 u d (sndT z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, Ab, PTm.subst_mul, hf]
  simp

theorem inst2_Bb (e z : PTm n) :
    inst2 (Bb v) e z = eqb (rem e (fstT z)) zero * inst2 v e (sndT z) * phi (fstT z) := by
  have hf : Syn.subst ![e, z] (Syn.subst ![var 0, sndT (var 1)] v) = inst2 v e (sndT z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, Bb, PTm.subst_mul, hf]
  simp

theorem Ab_at (d r y : PTm n) :
    Γ ⊢[PRAAx] inst2 (Ab u) d (pairT r y) ≐ sg d * eqb (rem d r) zero * inst2 u d y := by
  rw [inst2_Ab]
  exact congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF (.eqRefl d) (fst_pair r y)) (.eqRefl zero)))
    (congrInst2 u (.eqRefl _) (snd_pair r y))

theorem Bb_at (e r y : PTm n) :
    Γ ⊢[PRAAx] inst2 (Bb v) e (pairT r y) ≐ eqb (rem e r) zero * inst2 v e y * phi r := by
  rw [inst2_Bb]
  exact congrMul (congrMul (congrEqb' (congrAp2 remF (.eqRefl e) (fst_pair r y)) (.eqRefl zero))
    (congrInst2 v (.eqRefl _) (snd_pair r y))) (congrAp2 (sumF totBody) (fst_pair r y) (fst_pair r y))

/-- The product body `A_d(r) B_e(r)` over `(d, e, ⟨r, y⟩)`. -/
abbrev cb : PTm 3 := pmB (Ab u) (Bb v)

theorem cb_at (d e r y : PTm n) :
    Γ ⊢[PRAAx] inst3 (cb u v) d e (pairT r y) ≐
      (sg d * inst2 u d y * inst2 v e y) * (eqb (rem d r) zero * eqb (rem e r) zero * phi r) := by
  rw [show inst3 (cb u v) d e (pairT r y) = inst2 (Ab u) d (pairT r y) * inst2 (Bb v) e (pairT r y) from
    inst3_pmB (Ab u) (Bb v) d e (pairT r y)]
  refine (congrMul (Ab_at u d r y) (Bb_at v e r y)).eqTrans ?_
  ipra_ring

/-- The product body with the sums over `e` and `r` outermost: over `(e, r, ⟨d, y⟩)`. -/
def a1 : PTm 3 := Syn.subst ![fstT (var 2), var 0, pairT (var 1) (sndT (var 2))] (cb u v)

theorem inst3_a1 (e r w : PTm n) : inst3 (a1 u v) e r w = inst3 (cb u v) (fstT w) e (pairT r (sndT w)) := by
  simp only [inst3, a1, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp

theorem a1_at (e r d y : PTm n) : Γ ⊢[PRAAx] inst3 (a1 u v) e r (pairT d y) ≐ inst3 (cb u v) d e (pairT r y) := by
  rw [inst3_a1]
  exact congrInst3 (cb u v) (fst_pair d y) (.eqRefl e) (congrPairT (.eqRefl r) (snd_pair d y))

/-- `[d ≥ 1] u_d v_e gcd(d, e)` over `(d, e, y)`. -/
def Lb : PTm 3 :=
  sg (var 0) * Syn.subst ![var 0, var 2] u * Syn.subst ![var 1, var 2] v * gcd (var 0) (var 1)

theorem inst3_Lb (d e y : PTm n) : inst3 (Lb u v) d e y = sg d * inst2 u d y * inst2 v e y * gcd d e := by
  have hu : Syn.subst ![d, e, y] (Syn.subst ![var 0, var 2] u) = inst2 u d y := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> rfl
  have hv : Syn.subst ![d, e, y] (Syn.subst ![var 1, var 2] v) = inst2 v e y := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> rfl
  have hg : Syn.subst ![d, e, y] (gcd (var 0) (var 1)) = gcd d e := by
    simp only [gcd, subst_ex2, ConciseIPRA.PTm.subst_succ]
    simp
  simp only [inst3, Lb, PTm.subst_mul, hu, hv, hg]
  simp

/-! ## The gcd as a sum over `r` -/

theorem row1 (r e d y : PTm n) :
    Γ ⊢[PRAAx] inst2 (rowB (a1 u v)) r (pairT e (pairT d y)) ≐
      (sg d * inst2 u d y * inst2 v e y) * inst2 gB r (pairT d e) :=
  (row_pt (a1 u v) e r (pairT d y)).eqTrans ((a1_at u v e r d y).eqTrans
    ((cb_at u v d e r y).eqTrans (congrMul (.eqRefl _) (gB_at r d e).eqSymm)))

theorem rsum (d e y R : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (rowB (a1 u v))) R (pairT e (pairT d y)) ≐
      (sg d * inst2 u d y * inst2 v e y) * ap2 (sumF gB) R (pairT d e) := by
  refine sum_scale (rowB (a1 u v)) gB R (sg d * inst2 u d y * inst2 v e y) (pairT d e) (pairT e (pairT d y))
    (.allI (.impI ?_))
  have hK : Syn.shift (sg d * inst2 u d y * inst2 v e y) =
      sg (Syn.shift d) * inst2 u (Syn.shift d) (Syn.shift y) * inst2 v (Syn.shift e) (Syn.shift y) := by
    simp [Syn.shift]
  simp only [shift_pairT]
  rw [hK]
  exact row1 u v _ _ _ _

/-- For `d ≤ Z`: `[d ≥ 1] u_d v_e gcd(d, e) = Σ_{r ≤ Z} A_d(r) B_e(r)`. -/
theorem Lpt {d e y Z : PTm n} (hd : Γ ⊢[PRAAx] lt d (succ Z)) :
    Γ ⊢[PRAAx] inst3 (Lb u v) d e y ≐ ap2 (sumF (rowB (a1 u v))) (succ Z) (pairT e (pairT d y)) := by
  rw [inst3_Lb]
  refine Prf.eqTrans ?_ (rsum u v d e y (succ Z)).eqSymm
  refine .orE (zero_or_succ d) ?_ ?_
  · have h0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] d ≐ zero := Prf.hyp0
    have kz : ((d ≐ zero) :: Γ) ⊢[PRAAx] sg d * inst2 u d y * inst2 v e y ≐ zero :=
      (congrMul (congrMul ((congrSg h0).eqTrans sg_zero) (.eqRefl _)) (.eqRefl _)).eqTrans
        (by ipra_ring)
    exact ((congrMul kz (.eqRefl _)).eqTrans (zero_mul _)).eqTrans
      ((congrMul kz (.eqRefl _)).eqTrans (zero_mul _)).eqSymm
  · have hpos : ((d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
    have hle : ((d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] le d Z := (succ_monus_succ _ _).eqSymm.eqTrans hd.wk
    exact congrMul (.eqRefl _) (gcd_phi_sum hpos hle).eqSymm

/-! ## Exchanging the sums -/

theorem ptE {d e y Z : PTm n} (hd : Γ ⊢[PRAAx] lt d (succ Z)) :
    Γ ⊢[PRAAx] inst2 (rowB (Lb u v)) e (pairT d y) ≐
      inst2 (oB (a1 u v)) e (pairT (succ Z) (pairT d y)) := by
  rw [inst2_oB]
  exact (row_pt (Lb u v) d e y).eqTrans ((Lpt u v hd).eqTrans
    (congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm)

/-- The row sums `Σ_{e<N} a1(e, r, ⟨d, y⟩)` as a body over `(d, r, ⟨N, y⟩)`. -/
def a2 : PTm 3 := Syn.subst ![var 1, pairT (fstT (var 2)) (pairT (var 0) (sndT (var 2)))] (pB (a1 u v))

theorem inst3_a2 (d r w : PTm n) :
    inst3 (a2 u v) d r w = inst2 (pB (a1 u v)) r (pairT (fstT w) (pairT d (sndT w))) := by
  simp only [inst3, inst2, a2, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp

theorem a2_at (d r N y : PTm n) :
    Γ ⊢[PRAAx] inst3 (a2 u v) d r (pairT N y) ≐ inst2 (pB (a1 u v)) r (pairT N (pairT d y)) := by
  rw [inst3_a2]
  exact congrInst2 _ (.eqRefl _) (congrPairT (fst_pair N y) (congrPairT (.eqRefl _) (snd_pair N y)))

theorem ptR (r d N y : PTm n) :
    Γ ⊢[PRAAx] inst2 (pB (a1 u v)) r (pairT N (pairT d y)) ≐ inst2 (rowB (a2 u v)) r (pairT d (pairT N y)) :=
  ((row_pt (a2 u v) d r (pairT N y)).eqTrans (a2_at u v d r N y)).eqSymm

/-- One row: `Σ_{e<N} L(d, e) = Σ_{r ≤ Z} Σ_{e<N} A_d(r) B_e(r)` for `d ≤ Z`. -/
theorem rowL {d N y Z : PTm n} (hd : Γ ⊢[PRAAx] lt d (succ Z)) :
    Γ ⊢[PRAAx] inst2 (oB (Lb u v)) d (pairT N y) ≐ inst2 (oB (a2 u v)) d (pairT (succ Z) (pairT N y)) := by
  rw [inst2_oB, inst2_oB]
  have hs : Syn.shift (succ Z) = succ (Syn.shift Z) := by simp [Syn.shift]
  have hd' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift d) (succ (Syn.shift Z)) := by
    simpa [Fm.shift, Syn.shift] using hd.shift
  have e1 : Γ ⊢[PRAAx] ap2 (sumF (rowB (Lb u v))) (fstT (pairT N y)) (pairT d (sndT (pairT N y))) ≐
      ap2 (sumF (rowB (Lb u v))) N (pairT d y) :=
    congrAp2 _ (fst_pair N y) (congrPairT (.eqRefl _) (snd_pair N y))
  have e2 : Γ ⊢[PRAAx] ap2 (sumF (rowB (Lb u v))) N (pairT d y) ≐
      ap2 (sumF (oB (a1 u v))) N (pairT (succ Z) (pairT d y)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [hs]
    exact ptE u v hd'.wk
  have e3 := fubini (Γ := Γ) (a1 u v) N (succ Z) (pairT d y)
  have e4 : Γ ⊢[PRAAx] ap2 (sumF (pB (a1 u v))) (succ Z) (pairT N (pairT d y)) ≐
      ap2 (sumF (rowB (a2 u v))) (succ Z) (pairT d (pairT N y)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    exact ptR u v _ _ _ _
  have e5 : Γ ⊢[PRAAx] ap2 (sumF (rowB (a2 u v))) (fstT (pairT (succ Z) (pairT N y)))
      (pairT d (sndT (pairT (succ Z) (pairT N y)))) ≐ ap2 (sumF (rowB (a2 u v))) (succ Z) (pairT d (pairT N y)) :=
    congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))
  exact e1.eqTrans (e2.eqTrans (e3.eqTrans (e4.eqTrans e5.eqSymm)))

/-- `eq:sieve-diagonal`, bilinear form: `Σ_{d ≤ Z} Σ_{e<N} [d ≥ 1] u_d v_e gcd(d, e) = Σ_{r ≤ Z} pB a2 (r)`. -/
theorem diag (N y Z : PTm n) :
    Γ ⊢[PRAAx] dsum (Lb u v) (succ Z) N y ≐
      ap2 (sumF (pB (a2 u v))) (succ Z) (pairT (succ Z) (pairT N y)) := by
  have hs : Syn.shift (succ Z) = succ (Syn.shift Z) := by simp [Syn.shift]
  have e1 : Γ ⊢[PRAAx] dsum (Lb u v) (succ Z) N y ≐
      ap2 (sumF (oB (a2 u v))) (succ Z) (pairT (succ Z) (pairT N y)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [hs]
    have hd : (lt (var 0) (succ (Syn.shift Z)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (succ (Syn.shift Z)) :=
      Prf.hyp0
    exact rowL u v hd
  exact e1.eqTrans (fubini (a2 u v) (succ Z) (succ Z) (pairT N y))

/-! ## The summands as products -/

theorem ptC (e r d y : PTm n) :
    Γ ⊢[PRAAx] inst2 (colB (a1 u v)) e (pairT r (pairT d y)) ≐ inst2 (rowB (cb u v)) e (pairT d (pairT r y)) :=
  (col_pt (a1 u v) e r (pairT d y)).eqTrans ((a1_at u v e r d y).eqTrans (row_pt (cb u v) d e (pairT r y)).eqSymm)

theorem ptD (d r N y : PTm n) :
    Γ ⊢[PRAAx] inst2 (colB (a2 u v)) d (pairT r (pairT N y)) ≐ inst2 (oB (cb u v)) d (pairT N (pairT r y)) := by
  refine (col_pt (a2 u v) d r (pairT N y)).eqTrans ((a2_at u v d r N y).eqTrans ?_)
  rw [inst2_pB, inst2_oB]
  have e1 : Γ ⊢[PRAAx] ap2 (sumF (colB (a1 u v))) (fstT (pairT N (pairT d y)))
      (pairT r (sndT (pairT N (pairT d y)))) ≐ ap2 (sumF (colB (a1 u v))) N (pairT r (pairT d y)) :=
    congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))
  have e2 : Γ ⊢[PRAAx] ap2 (sumF (colB (a1 u v))) N (pairT r (pairT d y)) ≐
      ap2 (sumF (rowB (cb u v))) N (pairT d (pairT r y)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    exact ptC u v _ _ _ _
  have e3 : Γ ⊢[PRAAx] ap2 (sumF (rowB (cb u v))) (fstT (pairT N (pairT r y)))
      (pairT d (sndT (pairT N (pairT r y)))) ≐ ap2 (sumF (rowB (cb u v))) N (pairT d (pairT r y)) :=
    congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))
  exact e1.eqTrans (e2.eqTrans e3.eqSymm)

/-- Each summand of `diag` is `(Σ_{d ≤ Z} [d ≥ 1][r ∣ d] u_d) · (Σ_{e<N} [r ∣ e] v_e φ(r))`. -/
theorem diag_term (r N y Z : PTm n) :
    Γ ⊢[PRAAx] inst2 (pB (a2 u v)) r (pairT (succ Z) (pairT N y)) ≐
      ap2 (sumF (Ab u)) (succ Z) (pairT r y) * ap2 (sumF (Bb v)) N (pairT r y) := by
  rw [inst2_pB]
  have e1 : Γ ⊢[PRAAx] ap2 (sumF (colB (a2 u v))) (fstT (pairT (succ Z) (pairT N y)))
      (pairT r (sndT (pairT (succ Z) (pairT N y)))) ≐ ap2 (sumF (colB (a2 u v))) (succ Z) (pairT r (pairT N y)) :=
    congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))
  have e2 : Γ ⊢[PRAAx] ap2 (sumF (colB (a2 u v))) (succ Z) (pairT r (pairT N y)) ≐
      dsum (cb u v) (succ Z) N (pairT r y) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    exact ptD u v _ _ _ _
  exact e1.eqTrans (e2.eqTrans (sum_mul_sum (Ab u) (Bb v) (succ Z) N (pairT r y)))

end Diagonal

end LeanProofs.IPRA.AnalyticNumberTheory.SieveDiagonal
