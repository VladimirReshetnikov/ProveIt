import Diophantine.Paper1982.NineReduce
import Diophantine.Paper1982.NineRatio
import Diophantine.Common.PolyFn
import Diophantine.Common.RefinedRelationCombining
import Diophantine.Paper1982.RecursivelyEnumerableQuartic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Jones 1982, §3: Matijasevič's reduction to nine unknowns

The quantities `b, R, N, G` of `NineReduce` and `h, s, w, φ, i, j` of `NineRatio` are integer
polynomials in `x` and the eight unknowns `ε, g − 1, h − 1, s − 1, w − 1, φ, i − 1, j − 1`.
The two square conditions, the divisibility (written `(JF)² ∣ (QF + J(H − C))²`, so that the
divisor is positive and the dividend nonnegative at every integer point) and the stacked
inequality are combined by the refined relation-combining theorem with one more unknown `n`,
each radicand `a` weighted by `a² + 2`.

`nine_unknowns`: every recursively enumerable set of positive integers is Diophantine with
nine unknowns.
-/

namespace Jones1982.Nine

open Diophantine MvPolynomial

/-- `rPolynomial` over the integers. -/
def rZ (x z b e g l n q θ lam : ℤ) : ℤ :=
  (g + e * q ^ 3 + l * q ^ 5 +
    (2 * (e - z * lam) * (1 + x * b ^ 5 + g) ^ 4 + lam * b ^ 5 + lam * b ^ 5 * q ^ 4) * q ^ 7) *
      (n ^ 2 - n) +
  (q ^ 3 - b * l + l + θ * lam * q ^ 3 + (b ^ 5 - 2) * q ^ 8) * (n ^ 2 - 1)

theorem rPolynomial_eq_rZ (x z b e g l n q θ lam : ℕ) :
    rPolynomial x z b e g l n q θ lam = rZ x z b e g l n q θ lam := by
  simp only [rPolynomial, rZ]

variable (ν : ℕ) (P : MvPolynomial (Fin (ν + 1)) ℤ) (z y : ℕ)

/-- The quantities at an integer point `(x, ε, g − 1, h − 1, s − 1, w − 1, φ, i − 1, j − 1, n)`. -/
noncomputable def varsOf (v : Fin 10 → ℤ) : Vars :=
  { R := rZ (v 0) z (v 0 * y + 1 + v 1) ((epoly ν 4 P z).eval ((v 0 * y + 1 + v 1) ^ 5))
      (v 2 + 1) ((lpoly ν 4).eval ((v 0 * y + 1 + v 1) ^ 5))
      ((((v 0 * y + 1 + v 1) ^ 5) ^ L4 ν) ^ 16) (((v 0 * y + 1 + v 1) ^ 5) ^ L4 ν)
      ((v 0 * y + 1 + v 1) ^ 5 - 2 * z) ((lampoly ν 4).eval ((v 0 * y + 1 + v 1) ^ 5))
    N := (((v 0 * y + 1 + v 1) ^ 5) ^ L4 ν) ^ 16
    b := v 0 * y + 1 + v 1
    g := v 2 + 1
    G := 32 * (v 0 * y + 1 + v 1) * ((v 0 * y + 1 + v 1) ^ 5) ^ (5 ^ ν)
    h := v 3 + 1
    s := v 4 + 1
    w := v 5 + 1
    φ := v 6
    i := v 7 + 1
    j := v 8 + 1 }

/-- The two radicands. -/
def rad (V : Vars) : Fin 2 → ℤ := ![(V.P ^ 2 - 1) * V.K ^ 2 + 1, V.D * V.F * V.I]

/-- Their weights. -/
def wt (V : Vars) : Fin 2 → ℤ := fun k => rad V k ^ 2 + 2

/-- The divisor, dividend and margin. -/
def dvsr (V : Vars) : ℤ := (V.J * V.F) ^ 2
def dvnd (V : Vars) : ℤ := (V.Q * V.F + V.J * (V.H - V.C)) ^ 2
def marg (V : Vars) : ℤ := V.K ^ 2 * V.G - 4 * (V.C - V.K * V.Y) ^ 2 * V.G - 8 * V.g * V.K ^ 2

/-- The combined value. -/
noncomputable def nineValue (v : Fin 10 → ℤ) : ℤ :=
  RefinedRelationCombiningPolynomial.value 2 (rad (varsOf ν P z y v)) (wt (varsOf ν P z y v))
    (v 9) (dvsr (varsOf ν P z y v)) (dvnd (varsOf ν P z y v)) (marg (varsOf ν P z y v))

/-! ### Polynomiality -/

/-- All eleven fields are polynomial functions. -/
structure PolyVars {σ : Type*} (V : (σ → ℤ) → Vars) : Prop where
  hR : PolyFn fun v => (V v).R
  hN : PolyFn fun v => (V v).N
  hb : PolyFn fun v => (V v).b
  hg : PolyFn fun v => (V v).g
  hG : PolyFn fun v => (V v).G
  hh : PolyFn fun v => (V v).h
  hs : PolyFn fun v => (V v).s
  hw : PolyFn fun v => (V v).w
  hφ : PolyFn fun v => (V v).φ
  hi : PolyFn fun v => (V v).i
  hj : PolyFn fun v => (V v).j

namespace PolyVars

variable {σ : Type*} {V : (σ → ℤ) → Vars} (h : PolyVars V)
include h

theorem pU : PolyFn fun v => (V v).U := (h.hN.pow 2).mul h.hw
theorem pY : PolyFn fun v => (V v).Y := (h.hN.pow 2).mul h.hs
theorem pM : PolyFn fun v => (V v).M := h.hR.mul h.pY
theorem pP : PolyFn fun v => (V v).P := ((PolyFn.const 2).mul (h.pM.pow 2)).mul h.pU
theorem pK : PolyFn fun v => (V v).K :=
  (h.hR.add (PolyFn.const 1)).add (h.hh.mul (h.pP.sub (PolyFn.const 1)))
theorem pA : PolyFn fun v => (V v).A := h.pM.mul (h.pU.add (PolyFn.const 1))
theorem pB' : PolyFn fun v => (V v).B' := ((PolyFn.const 2).mul h.hR).add (PolyFn.const 1)
theorem pW : PolyFn fun v => (V v).W := h.hb.mul h.hw
theorem pC : PolyFn fun v => (V v).C := (h.pB'.add h.pW).add h.hφ
theorem pJ : PolyFn fun v => (V v).J := ((PolyFn.const 4).mul h.pA).sub (PolyFn.const 5)
theorem pQ : PolyFn fun v => (V v).Q :=
  (((PolyFn.const 3).mul h.pW).mul h.pC).sub
    ((PolyFn.const 2).mul ((h.pW.pow 2).sub (PolyFn.const 1)))
theorem pD : PolyFn fun v => (V v).D :=
  (((h.pA.pow 2).sub (PolyFn.const 1)).mul (h.pC.pow 2)).add (PolyFn.const 1)
theorem pE : PolyFn fun v => (V v).E := ((h.hi.mul h.pJ).mul h.pD).mul (h.pC.pow 2)
theorem pF : PolyFn fun v => (V v).F :=
  (((h.pA.pow 2).sub (PolyFn.const 1)).mul (h.pE.pow 2)).add (PolyFn.const 1)
theorem pGp : PolyFn fun v => (V v).Gp :=
  h.pA.add (h.pF.mul (((h.pC.mul h.pD).add (PolyFn.const 1)).sub h.pA))
theorem pH : PolyFn fun v => (V v).H := h.pB'.add (h.hj.mul h.pC)
theorem pI : PolyFn fun v => (V v).I :=
  (((h.pGp.pow 2).sub (PolyFn.const 1)).mul (h.pH.pow 2)).add (PolyFn.const 1)

theorem pRad (k : Fin 2) : PolyFn fun v => rad (V v) k := by
  fin_cases k
  · exact (((h.pP.pow 2).sub (PolyFn.const 1)).mul (h.pK.pow 2)).add (PolyFn.const 1)
  · exact (h.pD.mul h.pF).mul h.pI

theorem pWt (k : Fin 2) : PolyFn fun v => wt (V v) k := ((h.pRad k).pow 2).add (PolyFn.const 2)

theorem pDvsr : PolyFn fun v => dvsr (V v) := (h.pJ.mul h.pF).pow 2
theorem pDvnd : PolyFn fun v => dvnd (V v) :=
  ((h.pQ.mul h.pF).add (h.pJ.mul (h.pH.sub h.pC))).pow 2
theorem pMarg : PolyFn fun v => marg (V v) :=
  (((h.pK.pow 2).mul h.hG).sub (((PolyFn.const 4).mul ((h.pC.sub (h.pK.mul h.pY)).pow 2)).mul
    h.hG)).sub (((PolyFn.const 8).mul h.hg).mul (h.pK.pow 2))

end PolyVars

theorem polyVars_varsOf : PolyVars (varsOf ν P z y) := by
  have hb : PolyFn fun v : Fin 10 → ℤ => v 0 * y + 1 + v 1 :=
    (((PolyFn.var 0).mul (PolyFn.const _)).add (PolyFn.const 1)).add (PolyFn.var 1)
  have hB : PolyFn fun v : Fin 10 → ℤ => (v 0 * y + 1 + v 1) ^ 5 := hb.pow 5
  have hq : PolyFn fun v : Fin 10 → ℤ => ((v 0 * y + 1 + v 1) ^ 5) ^ L4 ν := hB.pow _
  have hx : PolyFn fun v : Fin 10 → ℤ => v 0 := PolyFn.var 0
  have hz : PolyFn fun _ : Fin 10 → ℤ => (z : ℤ) := PolyFn.const _
  have he := PolyFn.polyEval (epoly ν 4 P z) hB
  have hl := PolyFn.polyEval (lpoly ν 4) hB
  have hlam := PolyFn.polyEval (lampoly ν 4) hB
  have hg : PolyFn fun v : Fin 10 → ℤ => v 2 + 1 := (PolyFn.var 2).add (PolyFn.const 1)
  have hn := hq.pow 16
  have hθ : PolyFn fun v : Fin 10 → ℤ => (v 0 * y + 1 + v 1) ^ 5 - 2 * (z : ℤ) :=
    hB.sub ((PolyFn.const 2).mul hz)
  refine ⟨?_, hn, hb, hg, ((PolyFn.const 32).mul hb).mul (hB.pow _),
    (PolyFn.var 3).add (PolyFn.const 1), (PolyFn.var 4).add (PolyFn.const 1),
    (PolyFn.var 5).add (PolyFn.const 1), PolyFn.var 6, (PolyFn.var 7).add (PolyFn.const 1),
    (PolyFn.var 8).add (PolyFn.const 1)⟩
  show PolyFn fun v => rZ (v 0) z (v 0 * y + 1 + v 1) ((epoly ν 4 P z).eval ((v 0 * y + 1 + v 1) ^ 5))
      (v 2 + 1) ((lpoly ν 4).eval ((v 0 * y + 1 + v 1) ^ 5))
      ((((v 0 * y + 1 + v 1) ^ 5) ^ L4 ν) ^ 16) (((v 0 * y + 1 + v 1) ^ 5) ^ L4 ν)
      ((v 0 * y + 1 + v 1) ^ 5 - 2 * z) ((lampoly ν 4).eval ((v 0 * y + 1 + v 1) ^ 5))
  unfold rZ
  exact ((((hg.add (he.mul (hq.pow 3))).add (hl.mul (hq.pow 5))).add
    ((((((PolyFn.const 2).mul (he.sub (hz.mul hlam))).mul
      ((((PolyFn.const 1).add (hx.mul (hb.pow 5))).add hg).pow 4)).add (hlam.mul (hb.pow 5))).add
        ((hlam.mul (hb.pow 5)).mul (hq.pow 4))).mul (hq.pow 7))).mul ((hn.pow 2).sub hn)).add
    ((((((hq.pow 3).sub (hb.mul hl)).add hl).add ((hθ.mul hlam).mul (hq.pow 3))).add
      (((hb.pow 5).sub (PolyFn.const 2)).mul (hq.pow 8))).mul ((hn.pow 2).sub (PolyFn.const 1)))

theorem polyFn_nineValue : PolyFn (nineValue ν P z y) := by
  have h := polyVars_varsOf ν P z y
  exact PolyFn.rcValue 2 (A := fun k v => rad (varsOf ν P z y v) k)
    (V := fun k v => wt (varsOf ν P z y v) k) h.pRad h.pWt (PolyFn.var 9) h.pDvsr h.pDvnd h.pMarg

/-! ### Relation combining -/

theorem weight_bound (a : ℤ) (w : ℂ) (hw : w ^ 2 = (a : ℂ)) : ‖w‖ ≤ ((a ^ 2 + 2 : ℤ) : ℝ) - 1 := by
  have hn : ‖w‖ ^ 2 = |(a : ℝ)| := by
    rw [← norm_pow, hw, Complex.norm_intCast]
  have ha : |(a : ℝ)| ≤ (a : ℝ) ^ 2 := by
    have : |a| ≤ a ^ 2 := by
      rcases eq_or_ne a 0 with rfl | h0
      · simp
      · have h1 : 1 ≤ |a| := Int.one_le_abs h0
        nlinarith [abs_mul_abs_self a, sq_abs a]
    exact_mod_cast this
  push_cast
  by_cases h1 : ‖w‖ ≤ 1
  · nlinarith
  · push Not at h1
    nlinarith

/-- `J ≠ 0` and `F ≠ 0` at every integer point. -/
theorem JF_ne_zero (V : Vars) : V.J * V.F ≠ 0 := by
  have hJ : V.J ≠ 0 := by simp only [Vars.J]; omega
  have hF : V.F ≠ 0 := by
    intro h0
    simp only [Vars.F] at h0
    have hE : V.E * (-((V.A ^ 2 - 1) * V.E)) = 1 := by linarith
    have hE1 := Int.eq_one_or_neg_one_of_mul_eq_one hE
    have hEsq : V.E ^ 2 = 1 := by rcases hE1 with h | h <;> rw [h] <;> norm_num
    have hA : V.A ^ 2 = 0 := by nlinarith
    have hA0 : V.A = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 hA
    have h5 : (5 : ℤ) ∣ V.E := by
      simp only [Vars.E, Vars.J, hA0]
      exact ⟨-(V.i * V.D * V.C ^ 2), by ring⟩
    rcases hE1 with h | h <;> rw [h] at h5 <;> omega
  exact mul_ne_zero hJ hF

theorem conds_iff_value (V : Vars) :
    V.Conds ↔ ∃ n : ℕ, RefinedRelationCombiningPolynomial.value 2 (rad V) (wt V) n (dvsr V)
      (dvnd V) (marg V) = 0 := by
  have hiff := RefinedRelationCombining.relationCombining_iff (rad V) (wt V) (dvsr V) (dvnd V)
    (marg V) (fun k => by simp only [wt]; nlinarith [sq_nonneg (rad V k)])
    (fun k w hw => weight_bound _ w hw) (by simp only [dvsr]; have := JF_ne_zero V; positivity)
    (by simp only [dvnd]; positivity)
  rw [← hiff]
  simp only [Vars.Conds, rad, wt, dvsr, dvnd, marg, Fin.forall_fin_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero]
  tauto

/-- The margin forces `K ≠ 0` and hence `8g < G`. -/
theorem g_lt_of_marg (V : Vars) (hG : 0 < V.G) (hg : 0 ≤ V.g) (h : 0 < marg V) : 8 * V.g < V.G := by
  simp only [marg] at h
  have hK : V.K ^ 2 ≠ 0 := by
    intro h0
    rw [h0] at h
    nlinarith [sq_nonneg (V.C - V.K * V.Y)]
  have hK2 : 0 < V.K ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hK)
  have h1 : 8 * V.g * V.K ^ 2 < V.G * V.K ^ 2 := by nlinarith [sq_nonneg (V.C - V.K * V.Y)]
  exact lt_of_mul_lt_mul_right h1 hK2.le

end Jones1982.Nine
