import IPRADerivations.AnalyticNumberTheory.SieveRough
import IPRADerivations.AnalyticNumberTheory.SieveExpansion

/-!
# The quadratic majorant, summed over the progression

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, `eq:sieve-majorant`:
`1_{gcd(n, P) = 1} ≤ (Σ_{d ∈ D, d ∣ n} λ_d)²` when `λ_1 = 1`: "If `gcd(n, P) = 1`, only `d = 1` occurs, so both sides
equal one. Otherwise the left side is zero and the right side is a rational square", and its sum over the
progression.

For signed weights `λ = λ⁺ − λ⁻` with natural parts `λ^± = lB U^±` (`SieveExpansion.lB`), `a = λ⁺_1`, `b = λ⁻_1`,
the divisor sums `T^±(m) = Σ_{d<Z} [d ∣ m] λ^±_d`, the indicator `ρ(m) = rgh Z m` of having no divisor in `[2, Z)`
and `c(m) = [m ≡ a₀ (mod q)]`, the inequality `ρ(m) (a − b)² ≤ (T⁺(m) − T⁻(m))²` reads, cleared of signs,

  `(a² + b²) c ρ + (c T⁻ T⁺ + c T⁺ T⁻) ≤ (c T⁺ T⁺ + c T⁻ T⁻) + 2ab · c ρ`                         (`maj_pt`),

and summed over `m < X` (`majorant`), for `Z ≥ 2`:

  `(a² + b²) S + (N⁺⁻ + N⁻⁺) ≤ (N⁺⁺ + N⁻⁻) + 2ab · S`,

where `S = Σ_{m<X} c(m) ρ(m)` and `N^{st} = Σ_{m<X} c(m) T^t(m) T^s(m)` are the sums of
`SieveSquare.square_exchange`. That is `(λ_1)² S ≤ Σ_{m<X} c(m) (Σ_{d ∣ m} λ_d)²`.

* `amgm`: `2 x y ≤ x² + y²`; `maj_eq`, `maj_zero`: the two cases over opaque terms;
* `S0`, `aT`, `Lbody`, `Rbody`: the bodies over the common parameter `⟨Z, ⟨Z, P⟩⟩`;
* `SL`, `SR`: the two sums in closed form (`Independence.sum_scale`, `sum_add`).

Every `m` with no divisor in `[2, Z)` is counted by `S`; in particular the primes `m ≥ Z` of the progression.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveMajorant

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrEqb')
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorExchange (dvB LW)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveSquare (sqL_pt)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveExpansion (cB lB inst2_lB)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveRough (rB rgh rough_sum)
open LeanProofs.IPRA.Analysis.PowerSums (sum_le)
open LeanProofs.IPRA.Probability.Independence (sum_scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Algebra over opaque terms -/

/-- `2 x y ≤ x² + y²`. -/
theorem amgm (x y : PTm n) : Γ ⊢[PRAAx] le (two * (x * y)) (x * x + y * y) := by
  refine .orE (le_total x y) ?_ ?_
  · have e := natEq (eq_add_of_le (Prf.hyp0 : (le x y :: Γ) ⊢[PRAAx] le x y))
    refine le_of_eq_add (d := monus y x * monus y x) ?_
    ipra_lc (𝔞 y - 𝔞 x + 𝔞 (monus y x)) * e
  · have e := natEq (eq_add_of_le (Prf.hyp0 : (le y x :: Γ) ⊢[PRAAx] le y x))
    refine le_of_eq_add (d := monus x y * monus x y) ?_
    ipra_lc (𝔞 x - 𝔞 y + 𝔞 (monus x y)) * e

theorem maj_ring (c a b : PTm n) :
    Γ ⊢[PRAAx] (a * a + b * b) * (c * one) + ((c * b) * a + (c * a) * b) ≐
      ((c * a) * a + (c * b) * b) + (two * (a * b)) * (c * one) := by
  ipra_ring

/-- The case `ρ = 1`, `T⁺ = a`, `T⁻ = b`: both sides agree. -/
theorem maj_eq {c ρ a b TP TN : PTm n} (hρ : Γ ⊢[PRAAx] ρ ≐ one) (hP : Γ ⊢[PRAAx] TP ≐ a)
    (hN : Γ ⊢[PRAAx] TN ≐ b) :
    Γ ⊢[PRAAx] (a * a + b * b) * (c * ρ) + ((c * TN) * TP + (c * TP) * TN) ≐
      ((c * TP) * TP + (c * TN) * TN) + (two * (a * b)) * (c * ρ) := by
  have l : Γ ⊢[PRAAx] (a * a + b * b) * (c * ρ) + ((c * TN) * TP + (c * TP) * TN) ≐
      (a * a + b * b) * (c * one) + ((c * b) * a + (c * a) * b) :=
    congrAdd (congrMul (.eqRefl _) (congrMul (.eqRefl _) hρ))
      (congrAdd (congrMul (congrMul (.eqRefl _) hN) hP) (congrMul (congrMul (.eqRefl _) hP) hN))
  have r : Γ ⊢[PRAAx] ((c * TP) * TP + (c * TN) * TN) + (two * (a * b)) * (c * ρ) ≐
      ((c * a) * a + (c * b) * b) + (two * (a * b)) * (c * one) :=
    congrAdd (congrAdd (congrMul (congrMul (.eqRefl _) hP) hP) (congrMul (congrMul (.eqRefl _) hN) hN))
      (congrMul (.eqRefl _) (congrMul (.eqRefl _) hρ))
  exact l.eqTrans ((maj_ring c a b).eqTrans r.eqSymm)

theorem maj_zero0 (c a b TP TN : PTm n) :
    Γ ⊢[PRAAx] le ((a * a + b * b) * (c * zero) + ((c * TN) * TP + (c * TP) * TN))
      (((c * TP) * TP + (c * TN) * TN) + (two * (a * b)) * (c * zero)) := by
  ipra_le 𝔞 c * sl (amgm (Γ := Γ) TP TN)

/-- The case `ρ = 0`: a square is nonnegative. -/
theorem maj_zero {c ρ a b TP TN : PTm n} (hρ : Γ ⊢[PRAAx] ρ ≐ zero) :
    Γ ⊢[PRAAx] le ((a * a + b * b) * (c * ρ) + ((c * TN) * TP + (c * TP) * TN))
      (((c * TP) * TP + (c * TN) * TN) + (two * (a * b)) * (c * ρ)) :=
  le_congr (congrAdd (congrMul (.eqRefl _) (congrMul (.eqRefl _) hρ.eqSymm)) (.eqRefl _))
    (congrAdd (.eqRefl _) (congrMul (.eqRefl _) (congrMul (.eqRefl _) hρ.eqSymm))) (maj_zero0 c a b TP TN)

theorem lB_zero (U : PTm 2) (y : PTm n) : Γ ⊢[PRAAx] inst2 (lB U) zero y ≐ zero := by
  rw [inst2_lB]
  exact zero_mul _

/-! ## Bodies over the common parameter `⟨Z, ⟨Z, P⟩⟩` -/

/-- `c(m, P) · ρ(m)` over `0 = m`, `1 = ⟨Z, ⟨Z, P⟩⟩`. -/
def S0 : PTm 2 :=
  Syn.subst ![var 0, sndT (sndT (var 1))] cB * eqb (ap2 (sumF rB) (fstT (var 1)) (var 0)) zero

theorem inst2_S0 (m z : PTm n) :
    inst2 S0 m z = inst2 cB m (sndT (sndT z)) * eqb (ap2 (sumF rB) (fstT z) m) zero := by
  simp [inst2, S0]

theorem S0_at (m Z P : PTm n) :
    Γ ⊢[PRAAx] inst2 S0 m (pairT Z (pairT Z P)) ≐ inst2 cB m P * rgh Z m := by
  rw [inst2_S0]
  have s1 := snd_pair (Γ := Γ) Z (pairT Z P)
  have hP : Γ ⊢[PRAAx] sndT (sndT (pairT Z (pairT Z P))) ≐ P := (congrSnd s1).eqTrans (snd_pair Z P)
  exact congrMul (congrInst2 cB (.eqRefl _) hP)
    (congrEqb' (congrAp2 (sumF rB) (fst_pair Z (pairT Z P)) (.eqRefl _)) (.eqRefl _))

/-- `u(1, P)` as a body over `(m, ⟨Z, ⟨Z, P⟩⟩)`. -/
def aT (u : PTm 2) : PTm 2 := Syn.subst ![one, sndT (sndT (var 1))] u

theorem inst2_aT (u : PTm 2) (m z : PTm n) : inst2 (aT u) m z = inst2 u one (sndT (sndT z)) := by
  simp only [inst2, aT, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

theorem aT_at (u : PTm 2) (m Z P : PTm n) :
    Γ ⊢[PRAAx] inst2 (aT u) m (pairT Z (pairT Z P)) ≐ inst2 u one P := by
  rw [inst2_aT]
  have s1 := snd_pair (Γ := Γ) Z (pairT Z P)
  exact congrInst2 u (.eqRefl _) ((congrSnd s1).eqTrans (snd_pair Z P))

section Majorant

variable (UP UN : PTm 2)

/-- The sum body `c T^v T^u`. -/
abbrev Nb (u v : PTm 2) : PTm 2 := LW (LW cB v) (sndB u)

/-- `(a² + b²) · c ρ`. -/
def K1S : PTm 2 := (aT (lB UP) * aT (lB UP) + aT (lB UN) * aT (lB UN)) * S0
/-- `2ab · c ρ`. -/
def K2S : PTm 2 := (two * (aT (lB UP) * aT (lB UN))) * S0

/-- The left body `(a² + b²) c ρ + (c T⁻ T⁺ + c T⁺ T⁻)`. -/
def Lbody : PTm 2 := addBody (K1S UP UN) (addBody (Nb (lB UP) (lB UN)) (Nb (lB UN) (lB UP)))
/-- The right body `(c T⁺ T⁺ + c T⁻ T⁻) + 2ab c ρ`. -/
def Rbody : PTm 2 := addBody (addBody (Nb (lB UP) (lB UP)) (Nb (lB UN) (lB UN))) (K2S UP UN)

theorem inst2_K1S (m z : PTm n) : inst2 (K1S UP UN) m z =
    (inst2 (aT (lB UP)) m z * inst2 (aT (lB UP)) m z + inst2 (aT (lB UN)) m z * inst2 (aT (lB UN)) m z) *
      inst2 S0 m z := by
  simp only [inst2, K1S, LeanProofs.IPRA.PTm.subst_mul, LeanProofs.IPRA.PTm.subst_add]

theorem inst2_K2S (m z : PTm n) : inst2 (K2S UP UN) m z =
    (two * (inst2 (aT (lB UP)) m z * inst2 (aT (lB UN)) m z)) * inst2 S0 m z := by
  ipra_ind_simp [inst2, K2S]

theorem K1S_at (m Z P : PTm n) :
    Γ ⊢[PRAAx] inst2 (K1S UP UN) m (pairT Z (pairT Z P)) ≐
      (inst2 (lB UP) one P * inst2 (lB UP) one P + inst2 (lB UN) one P * inst2 (lB UN) one P) *
        inst2 S0 m (pairT Z (pairT Z P)) := by
  rw [inst2_K1S]
  exact congrMul (congrAdd (congrMul (aT_at _ m Z P) (aT_at _ m Z P)) (congrMul (aT_at _ m Z P) (aT_at _ m Z P)))
    (.eqRefl _)

theorem K2S_at (m Z P : PTm n) :
    Γ ⊢[PRAAx] inst2 (K2S UP UN) m (pairT Z (pairT Z P)) ≐
      (two * (inst2 (lB UP) one P * inst2 (lB UN) one P)) * inst2 S0 m (pairT Z (pairT Z P)) := by
  rw [inst2_K2S]
  exact congrMul (congrMul (.eqRefl _) (congrMul (aT_at _ m Z P) (aT_at _ m Z P))) (.eqRefl _)

/-! ## The pointwise majorant -/

theorem maj_pt {m Z P : PTm n} (hZ : Γ ⊢[PRAAx] lt one Z) :
    Γ ⊢[PRAAx] le (inst2 (Lbody UP UN) m (pairT Z (pairT Z P))) (inst2 (Rbody UP UN) m (pairT Z (pairT Z P))) := by
  have eL : Γ ⊢[PRAAx] inst2 (Lbody UP UN) m (pairT Z (pairT Z P)) ≐
      (inst2 (lB UP) one P * inst2 (lB UP) one P + inst2 (lB UN) one P * inst2 (lB UN) one P) *
          (inst2 cB m P * rgh Z m) +
        ((inst2 cB m P * ap2 (sumF (dvB (lB UN))) Z (pairT m P)) * ap2 (sumF (dvB (lB UP))) Z (pairT m P) +
          (inst2 cB m P * ap2 (sumF (dvB (lB UP))) Z (pairT m P)) * ap2 (sumF (dvB (lB UN))) Z (pairT m P)) := by
    rw [Lbody, inst2_addBody, inst2_addBody]
    exact congrAdd ((K1S_at UP UN m Z P).eqTrans (congrMul (.eqRefl _) (S0_at m Z P)))
      (congrAdd (sqL_pt cB (lB UP) (lB UN) m Z P) (sqL_pt cB (lB UN) (lB UP) m Z P))
  have eR : Γ ⊢[PRAAx] inst2 (Rbody UP UN) m (pairT Z (pairT Z P)) ≐
      ((inst2 cB m P * ap2 (sumF (dvB (lB UP))) Z (pairT m P)) * ap2 (sumF (dvB (lB UP))) Z (pairT m P) +
          (inst2 cB m P * ap2 (sumF (dvB (lB UN))) Z (pairT m P)) * ap2 (sumF (dvB (lB UN))) Z (pairT m P)) +
        (two * (inst2 (lB UP) one P * inst2 (lB UN) one P)) * (inst2 cB m P * rgh Z m) := by
    rw [Rbody, inst2_addBody, inst2_addBody]
    exact congrAdd (congrAdd (sqL_pt cB (lB UP) (lB UP) m Z P) (sqL_pt cB (lB UN) (lB UN) m Z P))
      ((K2S_at UP UN m Z P).eqTrans (congrMul (.eqRefl _) (S0_at m Z P)))
  refine le_congr eL.eqSymm eR.eqSymm ?_
  refine .orE (eq_or_ne (ap2 (sumF rB) Z m) zero) ?_ ?_
  · have hr : ((ap2 (sumF rB) Z m ≐ zero) :: Γ) ⊢[PRAAx] ap2 (sumF rB) Z m ≐ zero := Prf.hyp0
    have hρ : ((ap2 (sumF rB) Z m ≐ zero) :: Γ) ⊢[PRAAx] rgh Z m ≐ one := eqb_of_eq hr
    have hP := rough_sum (lB UP) (fun y => lB_zero UP y) (y := P) (hZ.wk (ψ := ap2 (sumF rB) Z m ≐ zero)) hr
    have hN := rough_sum (lB UN) (fun y => lB_zero UN y) (y := P) (hZ.wk (ψ := ap2 (sumF rB) Z m ≐ zero)) hr
    exact le_congr (.eqRefl _) (maj_eq hρ hP hN) (le_refl _)
  · have hρ : (neg (ap2 (sumF rB) Z m ≐ zero) :: Γ) ⊢[PRAAx] rgh Z m ≐ zero := eqb_of_ne Prf.hyp0
    exact maj_zero hρ

/-! ## The two sums -/

theorem k1_pt (m Z P : PTm n) :
    Γ ⊢[PRAAx] inst2 (K1S UP UN) m (pairT Z (pairT Z P)) ≐
      (inst2 (lB UP) one P * inst2 (lB UP) one P + inst2 (lB UN) one P * inst2 (lB UN) one P) *
        inst2 S0 m (pairT Z (pairT Z P)) := K1S_at UP UN m Z P

/-- `Σ_{m<X} (a² + b²) c ρ = (a² + b²) · S`. -/
theorem sum_K1 (X Z P : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (K1S UP UN)) X (pairT Z (pairT Z P)) ≐
      (inst2 (lB UP) one P * inst2 (lB UP) one P + inst2 (lB UN) one P * inst2 (lB UN) one P) *
        ap2 (sumF S0) X (pairT Z (pairT Z P)) := by
  refine sum_scale (K1S UP UN) S0 X _ (pairT Z (pairT Z P)) (pairT Z (pairT Z P)) (.allI (.impI ?_))
  have hK : Syn.shift (inst2 (lB UP) one P * inst2 (lB UP) one P + inst2 (lB UN) one P * inst2 (lB UN) one P) =
      inst2 (lB UP) one (Syn.shift P) * inst2 (lB UP) one (Syn.shift P) +
        inst2 (lB UN) one (Syn.shift P) * inst2 (lB UN) one (Syn.shift P) := by
    simp [Syn.shift]
  simp only [shift_pairT]
  rw [hK]
  exact K1S_at UP UN _ _ _

/-- `Σ_{m<X} 2ab c ρ = 2ab · S`. -/
theorem sum_K2 (X Z P : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (K2S UP UN)) X (pairT Z (pairT Z P)) ≐
      (two * (inst2 (lB UP) one P * inst2 (lB UN) one P)) * ap2 (sumF S0) X (pairT Z (pairT Z P)) := by
  refine sum_scale (K2S UP UN) S0 X _ (pairT Z (pairT Z P)) (pairT Z (pairT Z P)) (.allI (.impI ?_))
  have hK : Syn.shift (two * (inst2 (lB UP) one P * inst2 (lB UN) one P)) =
      two * (inst2 (lB UP) one (Syn.shift P) * inst2 (lB UN) one (Syn.shift P)) := by
    simp [Syn.shift]
  simp only [shift_pairT]
  rw [hK]
  exact K2S_at UP UN _ _ _

/-- `(λ_1)² S ≤ Σ_{m<X} c(m) (Σ_{d ∣ m} λ_d)²`, cleared of signs: for `Z ≥ 2`,
`(a² + b²) S + (N⁺⁻ + N⁻⁺) ≤ (N⁺⁺ + N⁻⁻) + 2ab S`. -/
theorem majorant {X Z P : PTm n} (hZ : Γ ⊢[PRAAx] lt one Z) :
    Γ ⊢[PRAAx] le
      ((inst2 (lB UP) one P * inst2 (lB UP) one P + inst2 (lB UN) one P * inst2 (lB UN) one P) *
          ap2 (sumF S0) X (pairT Z (pairT Z P)) +
        (ap2 (sumF (Nb (lB UP) (lB UN))) X (pairT Z (pairT Z P)) +
          ap2 (sumF (Nb (lB UN) (lB UP))) X (pairT Z (pairT Z P))))
      ((ap2 (sumF (Nb (lB UP) (lB UP))) X (pairT Z (pairT Z P)) +
          ap2 (sumF (Nb (lB UN) (lB UN))) X (pairT Z (pairT Z P))) +
        (two * (inst2 (lB UP) one P * inst2 (lB UN) one P)) * ap2 (sumF S0) X (pairT Z (pairT Z P))) := by
  have hZ' : (Γ.map Fm.shift) ⊢[PRAAx] lt one (Syn.shift Z) := by
    simpa [Fm.shift, Syn.shift] using hZ.shift
  have m : Γ ⊢[PRAAx] le (ap2 (sumF (Lbody UP UN)) X (pairT Z (pairT Z P)))
      (ap2 (sumF (Rbody UP UN)) X (pairT Z (pairT Z P))) := by
    refine sum_le _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    exact maj_pt UP UN hZ'.wk
  have sL : Γ ⊢[PRAAx] ap2 (sumF (Lbody UP UN)) X (pairT Z (pairT Z P)) ≐
      (inst2 (lB UP) one P * inst2 (lB UP) one P + inst2 (lB UN) one P * inst2 (lB UN) one P) *
          ap2 (sumF S0) X (pairT Z (pairT Z P)) +
        (ap2 (sumF (Nb (lB UP) (lB UN))) X (pairT Z (pairT Z P)) +
          ap2 (sumF (Nb (lB UN) (lB UP))) X (pairT Z (pairT Z P))) :=
    (sum_add (K1S UP UN) (addBody (Nb (lB UP) (lB UN)) (Nb (lB UN) (lB UP))) X _).eqTrans
      (congrAdd (sum_K1 UP UN X Z P) (sum_add _ _ X _))
  have sR : Γ ⊢[PRAAx] ap2 (sumF (Rbody UP UN)) X (pairT Z (pairT Z P)) ≐
      (ap2 (sumF (Nb (lB UP) (lB UP))) X (pairT Z (pairT Z P)) +
          ap2 (sumF (Nb (lB UN) (lB UN))) X (pairT Z (pairT Z P))) +
        (two * (inst2 (lB UP) one P * inst2 (lB UN) one P)) * ap2 (sumF S0) X (pairT Z (pairT Z P)) :=
    (sum_add (addBody (Nb (lB UP) (lB UP)) (Nb (lB UN) (lB UN))) (K2S UP UN) X _).eqTrans
      (congrAdd (sum_add _ _ X _) (sum_K2 UP UN X Z P))
  exact le_congr sL sR m

end Majorant

end LeanProofs.IPRA.AnalyticNumberTheory.SieveMajorant
