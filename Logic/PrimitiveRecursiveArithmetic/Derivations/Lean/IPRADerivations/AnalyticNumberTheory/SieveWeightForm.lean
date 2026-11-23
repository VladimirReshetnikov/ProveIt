import IPRADerivations.AnalyticNumberTheory.SieveWeightRows
import IPRADerivations.AnalyticNumberTheory.SieveWeightValues
import IPRADerivations.Foundations.SignedSums

/-!
# The quadratic form at the explicit sieve weights

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, `eq:sieve-normalization`:
"Since `μ(r)² = 1` on `D`, equations `eq:sieve-diagonal` and `eq:sieve-inversion` show that `Q(λ) = 1/G`."

With the common denominator `B = z!` and `P = ⟨q, ⟨a, z⟩⟩`, the weights are `λ = λ⁺ − λ⁻` with

  `U⁺ = uB μ⁺ Y⁺ + uB μ⁻ Y⁻`,   `U⁻ = uB μ⁺ Y⁻ + uB μ⁻ Y⁺`          (`UPw`, `UNw`),

where `Y^±` are the parts of the explicit vector (`SieveWeightValues`) and `uB` is the inversion
(`SieveWeightRows`); so `U⁺_d − U⁻_d = Σ_{r ≤ z, d ∣ r} μ(r/d) (Y⁺_r − Y⁻_r)`. For the bilinear forms
`G(U, V) = Σ_{d ≤ z} Σ_{e ≤ z} [d ≥ 1] u_d v_e gcd(d, e)` of `SieveClosedForms.bil_le`, the module derives

  `G(U⁺, U⁺) + G(U⁻, U⁻) = (G(U⁺, U⁻) + G(U⁻, U⁺)) + Σ_{r ≤ z} z! (Y⁺_r + Y⁻_r)`              (`form_value`),

for `q ≥ 1`: the signed quadratic form is `z! · A` with `A = Σ_{r ≤ z} μ(r)² [gcd(r, q) = 1] z!/φ(r)`, which is
`Q(λ) = 1/G` after division by `(z! G)² = A²`.

* `Ab_add`, `Bb_add`: the sums over multiples are additive in the weight;
* `alphaP`, `alphaN`, `betaP`, `betaN`: those sums for `U^±` in terms of the four double sums of
  `SieveInversion.dual_inversion`;
* `form_alg`, `form_zero`: the summand identity over opaque terms, from the two inversions, `Y⁺ Y⁻ = 0` and
  `φ (Y^±)² = z! Y^±`;
* `form_pt`: the summand identity at `r ≤ z`, through `SieveDiagonal.diag_term`;
* `sum_five`: a sum identity for five bodies with two parameters (`Foundations/SignedSums.sum_mix`);
* `form_value`: the sum over `r`, through `SieveDiagonal.diag`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightForm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg sg_zero)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody)
open LeanProofs.IPRA.AnalyticNumberTheory.TotientCorollaries (phi_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetrySum (aPB aNB)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveInversion (wB dual_inversion)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveDiagonal (Ab Ab_at Bb Bb_at a2 Lb diag diag_term)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveClosedForms (gU inst2_gU sgV inst2_sgV)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightRows (uB Ab_sum Bb_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightValues (y0P y0N YP YN YP_at YN_at aP_indep aN_indep Y_disj
  phi_YP phi_YN)
open LeanProofs.IPRA.Probability.Independence (dsum)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Algebra over opaque terms -/

theorem dist_a (SH g a b : PTm n) : Γ ⊢[PRAAx] SH * (g * (a + b)) ≐ SH * (g * a) + SH * (g * b) := by
  apply deriveNat; ipra_simps; ring

theorem dist_b (H Sg a b F : PTm n) :
    Γ ⊢[PRAAx] H * (Sg * (a + b)) * F ≐ H * (Sg * a) * F + H * (Sg * b) * F := by
  apply deriveNat; ipra_simps; ring

/-- The summand identity: `φ (α⁺ − α⁻)² = B (y⁺ + y⁻)`, cleared of signs. -/
theorem form_alg {t1 t2 t3 t4 yp yn φ B : PTm n} (e1 : Γ ⊢[PRAAx] t1 ≐ yp + t2) (e3 : Γ ⊢[PRAAx] t3 ≐ yn + t4)
    (hd : Γ ⊢[PRAAx] yp * yn ≐ zero) (hp : Γ ⊢[PRAAx] φ * (yp * yp) ≐ B * yp)
    (hn : Γ ⊢[PRAAx] φ * (yn * yn) ≐ B * yn) :
    Γ ⊢[PRAAx] (t1 + t4) * (φ * t1 + φ * t4) + (t3 + t2) * (φ * t3 + φ * t2) ≐
      ((t1 + t4) * (φ * t3 + φ * t2) + (t3 + t2) * (φ * t1 + φ * t4)) + B * (yp + yn) := by
  have a1 := natEq e1; have a3 := natEq e3; have ad := natEq hd; have ap := natEq hp; have an := natEq hn
  apply deriveNat; ipra_simps
  linear_combination 𝔞 φ * (𝔞 t1 + 𝔞 t4 - 𝔞 t3 - 𝔞 t2 + 𝔞 yp - 𝔞 yn) * (a1 - a3) + ap + an - 2 * 𝔞 φ * ad

/-- The summand identity at `r = 0`: every term vanishes. -/
theorem form_zero {t1 t2 t3 t4 yp yn φ B : PTm n} (hφ : Γ ⊢[PRAAx] φ ≐ zero) (hyp : Γ ⊢[PRAAx] yp ≐ zero)
    (hyn : Γ ⊢[PRAAx] yn ≐ zero) :
    Γ ⊢[PRAAx] (t1 + t4) * (φ * t1 + φ * t4) + (t3 + t2) * (φ * t3 + φ * t2) ≐
      ((t1 + t4) * (φ * t3 + φ * t2) + (t3 + t2) * (φ * t1 + φ * t4)) + B * (yp + yn) := by
  have aφ := natEq hφ; have ap := natEq hyp; have an := natEq hyn
  apply deriveNat; ipra_simps
  linear_combination (𝔞 t1 + 𝔞 t4 - 𝔞 t3 - 𝔞 t2) * (𝔞 t1 + 𝔞 t4 - 𝔞 t3 - 𝔞 t2) * aφ - 𝔞 B * ap - 𝔞 B * an

/-! ## A sum identity for five bodies -/

/-- `Σ L₁ + Σ L₂ = (Σ R₁ + Σ R₂) + Σ K` from the identity of the summands below the bound, where `K` has its own
parameter. -/
theorem sum_five (L1 L2 R1 R2 K : PTm 2) (N x p : PTm n)
    (h : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
      inst2 L1 (var 0) (Syn.shift x) + inst2 L2 (var 0) (Syn.shift x) ≐
        (inst2 R1 (var 0) (Syn.shift x) + inst2 R2 (var 0) (Syn.shift x)) + inst2 K (var 0) (Syn.shift p)) :
    Γ ⊢[PRAAx] ap2 (sumF L1) N x + ap2 (sumF L2) N x ≐
      (ap2 (sumF R1) N x + ap2 (sumF R2) N x) + ap2 (sumF K) N p := by
  have a := sum_mix (Γ := Γ) L1 L2 N x x
  have b := sum_mix (Γ := Γ) (mixB R1 R2) K N (pairT x x) p
  have c := sum_mix (Γ := Γ) R1 R2 N x x
  have m : Γ ⊢[PRAAx] ap2 (sumF (mixB L1 L2)) N (pairT x x) ≐
      ap2 (sumF (mixB (mixB R1 R2) K)) N (pairT (pairT x x) p) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    exact (mix_at L1 L2 _ _ _).eqTrans (h.eqTrans
      ((mix_at (mixB R1 R2) K _ _ _).eqTrans (congrAdd (mix_at R1 R2 _ _ _) (.eqRefl _))).eqSymm)
  exact a.eqSymm.eqTrans (m.eqTrans (b.eqTrans (congrAdd c (.eqRefl _))))

/-! ## Additivity of the sums over multiples in the weight -/

theorem Ab_add_pt (U1 U2 : PTm 2) (d s Y : PTm n) :
    Γ ⊢[PRAAx] inst2 (Ab (sndB (gU (addBody U1 U2)))) d (pairT s Y) ≐
      inst2 (Ab (sndB (gU U1))) d (pairT s Y) + inst2 (Ab (sndB (gU U2))) d (pairT s Y) := by
  have e : ∀ U : PTm 2, Γ ⊢[PRAAx] inst2 (Ab (sndB (gU U))) d (pairT s Y) ≐
      (sg d * eqb (rem d s) zero) * (eqb (gcd d (fstT (sndT Y))) one * inst2 U d (sndT Y)) := fun U => by
    refine (Ab_at _ d s Y).eqTrans ?_
    rw [inst2_sndB, inst2_gU]
    exact .eqRefl _
  have m := e (addBody U1 U2)
  rw [inst2_addBody] at m
  exact m.eqTrans ((dist_a _ _ _ _).eqTrans (congrAdd (e U1).eqSymm (e U2).eqSymm))

theorem Ab_add (U1 U2 : PTm 2) (N s Y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (Ab (sndB (gU (addBody U1 U2))))) N (pairT s Y) ≐
      ap2 (sumF (Ab (sndB (gU U1)))) N (pairT s Y) + ap2 (sumF (Ab (sndB (gU U2)))) N (pairT s Y) := by
  refine sum_add2 _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  exact Ab_add_pt U1 U2 _ _ _

theorem Bb_add_pt (U1 U2 : PTm 2) (e s Y : PTm n) :
    Γ ⊢[PRAAx] inst2 (Bb (sndB (sgV (addBody U1 U2)))) e (pairT s Y) ≐
      inst2 (Bb (sndB (sgV U1))) e (pairT s Y) + inst2 (Bb (sndB (sgV U2))) e (pairT s Y) := by
  have f : ∀ U : PTm 2, Γ ⊢[PRAAx] inst2 (Bb (sndB (sgV U))) e (pairT s Y) ≐
      eqb (rem e s) zero * ((sg e * eqb (gcd e (fstT (sndT Y))) one) * inst2 U e (sndT Y)) * phi s := fun U => by
    refine (Bb_at _ e s Y).eqTrans ?_
    rw [inst2_sndB, inst2_sgV]
    exact .eqRefl _
  have m := f (addBody U1 U2)
  rw [inst2_addBody] at m
  exact m.eqTrans ((dist_b _ _ _ _ _).eqTrans (congrAdd (f U1).eqSymm (f U2).eqSymm))

theorem Bb_add (U1 U2 : PTm 2) (N s Y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (Bb (sndB (sgV (addBody U1 U2))))) N (pairT s Y) ≐
      ap2 (sumF (Bb (sndB (sgV U1)))) N (pairT s Y) + ap2 (sumF (Bb (sndB (sgV U2)))) N (pairT s Y) := by
  refine sum_add2 _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  exact Bb_add_pt U1 U2 _ _ _

/-! ## The weights -/

/-- `U⁺ = uB μ⁺ Y⁺ + uB μ⁻ Y⁻`. -/
def UPw : PTm 2 := addBody (uB aPB YP) (uB aNB YN)
/-- `U⁻ = uB μ⁺ Y⁻ + uB μ⁻ Y⁺`. -/
def UNw : PTm 2 := addBody (uB aPB YN) (uB aNB YP)

/-- The double sum of `SieveInversion.dual_inversion` for `y` and `a`, at `s = r`, with `Z = z`. -/
abbrev tT (y a : PTm 2) (r P : PTm n) : PTm n :=
  dsum (wB y a) (succ (sndT (sndT P))) (succ (sndT (sndT P))) (pairT r P)

theorem alphaP {r X P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P)) :
    Γ ⊢[PRAAx] ap2 (sumF (Ab (sndB (gU UPw)))) (succ (sndT (sndT P))) (pairT r (pairT X P)) ≐
      tT YP aPB r P + tT YN aNB r P :=
  (Ab_add _ _ _ _ _).eqTrans (congrAdd (Ab_sum y0P aPB (fun i p p' => aP_indep i p p') hq)
    (Ab_sum y0N aNB (fun i p p' => aN_indep i p p') hq))

theorem alphaN {r X P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P)) :
    Γ ⊢[PRAAx] ap2 (sumF (Ab (sndB (gU UNw)))) (succ (sndT (sndT P))) (pairT r (pairT X P)) ≐
      tT YN aPB r P + tT YP aNB r P :=
  (Ab_add _ _ _ _ _).eqTrans (congrAdd (Ab_sum y0N aPB (fun i p p' => aP_indep i p p') hq)
    (Ab_sum y0P aNB (fun i p p' => aN_indep i p p') hq))

theorem betaP {r X P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P)) :
    Γ ⊢[PRAAx] ap2 (sumF (Bb (sndB (sgV UPw)))) (succ (sndT (sndT P))) (pairT r (pairT X P)) ≐
      phi r * tT YP aPB r P + phi r * tT YN aNB r P :=
  (Bb_add _ _ _ _ _).eqTrans (congrAdd (Bb_sum y0P aPB (fun i p p' => aP_indep i p p') hq)
    (Bb_sum y0N aNB (fun i p p' => aN_indep i p p') hq))

theorem betaN {r X P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P)) :
    Γ ⊢[PRAAx] ap2 (sumF (Bb (sndB (sgV UNw)))) (succ (sndT (sndT P))) (pairT r (pairT X P)) ≐
      phi r * tT YN aPB r P + phi r * tT YP aNB r P :=
  (Bb_add _ _ _ _ _).eqTrans (congrAdd (Bb_sum y0N aPB (fun i p p' => aP_indep i p p') hq)
    (Bb_sum y0P aNB (fun i p p' => aN_indep i p p') hq))

/-! ## The summand identity -/

/-- The diagonal body of `G(U, V)`: `r ↦ (Σ_d A_d(r)) (Σ_e B_e(r))`. -/
abbrev gT (U V : PTm 2) : PTm 2 := pB (a2 (sndB (gU U)) (sndB (sgV V)))

/-- `z! (Y⁺_r + Y⁻_r)` over `0 = r`, `1 = P`. -/
def kyB : PTm 2 := fact (sndT (sndT (var 1))) * (YP + YN)

theorem inst2_kyB (r P : PTm n) :
    inst2 kyB r P = fact (sndT (sndT P)) * (inst2 YP r P + inst2 YN r P) := by
  simp [inst2, kyB]

theorem YP_zero {r P : PTm n} (h : Γ ⊢[PRAAx] r ≐ zero) : Γ ⊢[PRAAx] inst2 YP r P ≐ zero := by
  rw [YP_at]
  exact (congrMul (.eqRefl _) (zero_mul_l (zero_mul_l ((congrSg h).eqTrans sg_zero) _) _)).eqTrans (mul_zero _)

theorem YN_zero {r P : PTm n} (h : Γ ⊢[PRAAx] r ≐ zero) : Γ ⊢[PRAAx] inst2 YN r P ≐ zero := by
  rw [YN_at]
  exact (congrMul (.eqRefl _) (zero_mul_l (zero_mul_l ((congrSg h).eqTrans sg_zero) _) _)).eqTrans (mul_zero _)

/-- The summand identity at `r ≤ z`. -/
theorem form_pt {r X P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P))
    (hr : Γ ⊢[PRAAx] lt r (succ (sndT (sndT P)))) :
    Γ ⊢[PRAAx]
      inst2 (gT UPw UPw) r (pairT (succ (sndT (sndT P))) (pairT (succ (sndT (sndT P))) (pairT X P))) +
        inst2 (gT UNw UNw) r (pairT (succ (sndT (sndT P))) (pairT (succ (sndT (sndT P))) (pairT X P))) ≐
      (inst2 (gT UPw UNw) r (pairT (succ (sndT (sndT P))) (pairT (succ (sndT (sndT P))) (pairT X P))) +
        inst2 (gT UNw UPw) r (pairT (succ (sndT (sndT P))) (pairT (succ (sndT (sndT P))) (pairT X P)))) +
        inst2 kyB r P := by
  have gpp := (diag_term (Γ := Γ) (sndB (gU UPw)) (sndB (sgV UPw)) r (succ (sndT (sndT P))) (pairT X P)
    (sndT (sndT P))).eqTrans (congrMul (alphaP hq) (betaP hq))
  have gnn := (diag_term (Γ := Γ) (sndB (gU UNw)) (sndB (sgV UNw)) r (succ (sndT (sndT P))) (pairT X P)
    (sndT (sndT P))).eqTrans (congrMul (alphaN hq) (betaN hq))
  have gpn := (diag_term (Γ := Γ) (sndB (gU UPw)) (sndB (sgV UNw)) r (succ (sndT (sndT P))) (pairT X P)
    (sndT (sndT P))).eqTrans (congrMul (alphaP hq) (betaN hq))
  have gnp := (diag_term (Γ := Γ) (sndB (gU UNw)) (sndB (sgV UPw)) r (succ (sndT (sndT P))) (pairT X P)
    (sndT (sndT P))).eqTrans (congrMul (alphaN hq) (betaP hq))
  rw [inst2_kyB]
  refine (congrAdd gpp gnn).eqTrans (Prf.eqTrans ?_ (congrAdd (congrAdd gpn gnp) (.eqRefl _)).eqSymm)
  refine .orE (zero_or_succ r) ?_ ?_
  · have h0 : ((r ≐ zero) :: Γ) ⊢[PRAAx] r ≐ zero := Prf.hyp0
    have hφ : ((r ≐ zero) :: Γ) ⊢[PRAAx] phi r ≐ zero := (congrAp2 (sumF totBody) h0 h0).eqTrans phi_zero
    exact form_zero hφ (YP_zero h0) (YN_zero h0)
  · have hr1 : ((r ≐ succ (pred r)) :: Γ) ⊢[PRAAx] r ≐ succ (pred r) := Prf.hyp0
    have hr' := hr.wk (ψ := r ≐ succ (pred r))
    have hrz : ((r ≐ succ (pred r)) :: Γ) ⊢[PRAAx] le r (sndT (sndT P)) :=
      (succ_monus_succ _ _).eqSymm.eqTrans hr'
    exact form_alg (dual_inversion YP hr1 hr') (dual_inversion YN hr1 hr') (Y_disj r P) (phi_YP hrz) (phi_YN hrz)

/-! ## The value of the quadratic form -/

/-- `G(U⁺, U⁺) + G(U⁻, U⁻) = (G(U⁺, U⁻) + G(U⁻, U⁺)) + Σ_{r ≤ z} z! (Y⁺_r + Y⁻_r)`. -/
theorem form_value {X P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P)) :
    Γ ⊢[PRAAx]
      dsum (Lb (sndB (gU UPw)) (sndB (sgV UPw))) (succ (sndT (sndT P))) (succ (sndT (sndT P))) (pairT X P) +
        dsum (Lb (sndB (gU UNw)) (sndB (sgV UNw))) (succ (sndT (sndT P))) (succ (sndT (sndT P))) (pairT X P) ≐
      (dsum (Lb (sndB (gU UPw)) (sndB (sgV UNw))) (succ (sndT (sndT P))) (succ (sndT (sndT P))) (pairT X P) +
        dsum (Lb (sndB (gU UNw)) (sndB (sgV UPw))) (succ (sndT (sndT P))) (succ (sndT (sndT P))) (pairT X P)) +
        ap2 (sumF kyB) (succ (sndT (sndT P))) P := by
  have d := fun (U V : PTm 2) => diag (Γ := Γ) (sndB (gU U)) (sndB (sgV V)) (succ (sndT (sndT P))) (pairT X P)
    (sndT (sndT P))
  have s : Γ ⊢[PRAAx]
      ap2 (sumF (gT UPw UPw)) (succ (sndT (sndT P)))
          (pairT (succ (sndT (sndT P))) (pairT (succ (sndT (sndT P))) (pairT X P))) +
        ap2 (sumF (gT UNw UNw)) (succ (sndT (sndT P)))
          (pairT (succ (sndT (sndT P))) (pairT (succ (sndT (sndT P))) (pairT X P))) ≐
      (ap2 (sumF (gT UPw UNw)) (succ (sndT (sndT P)))
          (pairT (succ (sndT (sndT P))) (pairT (succ (sndT (sndT P))) (pairT X P))) +
        ap2 (sumF (gT UNw UPw)) (succ (sndT (sndT P)))
          (pairT (succ (sndT (sndT P))) (pairT (succ (sndT (sndT P))) (pairT X P)))) +
        ap2 (sumF kyB) (succ (sndT (sndT P))) P := by
    refine sum_five _ _ _ _ _ _ _ _ ?_
    have hq' : (Γ.map Fm.shift) ⊢[PRAAx] le one (fstT (Syn.shift P)) := by
      simpa [Fm.shift, Syn.shift] using hq.shift
    have s1 : Syn.shift (pairT (succ (sndT (sndT P))) (pairT (succ (sndT (sndT P))) (pairT X P))) =
        pairT (succ (sndT (sndT (Syn.shift P))))
          (pairT (succ (sndT (sndT (Syn.shift P)))) (pairT (Syn.shift X) (Syn.shift P))) := by
      simp [Syn.shift]
    have s2 : Syn.shift (succ (sndT (sndT P))) = succ (sndT (sndT (Syn.shift P))) := by simp [Syn.shift]
    rw [s1, s2]
    exact form_pt hq'.wk Prf.hyp0
  exact (congrAdd (d UPw UPw) (d UNw UNw)).eqTrans (s.eqTrans (congrAdd (congrAdd (d UPw UNw) (d UNw UPw)) (.eqRefl _)).eqSymm)

end LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightForm
