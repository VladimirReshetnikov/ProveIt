import IPRADerivations.DiophantineNumberTheory.KhinchinBlockScales
import IPRADerivations.Foundations.BoundedReflection

/-!
# The elementary estimates of the zeta finite contract (`zeta_functional_equation_ipra`)

Packet: `analytic-number-theory/zeta_functional_equation_ipra`, `finite_contract.md`, "Here are the elementary
estimates justifying the constants". Cleared of denominators:

* `sq_le_pow`: `(m + 1)² ≤ 2^m 2^m`, i.e. `n² ≤ 4^{n−1}` for `n ≥ 1`;
* `theta_term`: `4 n² 2^n ≤ 2^{3n²}` for `n ≥ 1`, i.e. "`4 n² 2^{−3n²} ≤ 2^{−n}`, because `n² ≤ 4^{n−1}` and
  `n² ≥ n`";
* `square_gap`: for `n = N + 1 + j`, `n² ≥ (N + 1)² + j`;
* `geo8`, `geo8_tail`: `7 Σ_{j<J} 8^j + 1 = 8^J`, so `4 Σ_{j<J} 8^j ≤ 8^J`: "the geometric tail has ratio at
  most `2^{−3}` and hence is at most twice its initial term";
* `norm1_mul`: `norm1` is submultiplicative on `(a + bi)(c + di)`:
  `|ac − bd| + (ad + bc) ≤ (a + b)(c + d)` (signs moved into the natural parts);
* `norm1_compare`: `x² + y² ≤ (x + y)² ≤ 2(x² + y²)`: "the usual modulus is at most `norm1` and `norm1` is at
  most twice the usual modulus" (squared).
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.ZetaFiniteContract

open_ipra exports
open LeanProofs.IPRA.Probability.FiniteCauchySchwarz (dist dist_sq)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## `n² ≤ 4^{n−1}` and the theta terms -/

/-- The invariant of `sq_le_pow`. -/
def sqInv (m : PTm n) : Fm PTm n := le (succ m * succ m) (pw two m * pw two m)

ipra_subst sqInv

/-- `(m + 1)² ≤ 2^m 2^m`. -/
theorem sq_le_pow (m : PTm n) : Γ ⊢[PRAAx] le (succ m * succ m) (pw two m * pw two m) := by
  have hall : Γ ⊢[PRAAx] Fm.all (sqInv (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · rw [subst_sqInv]
      simp only [Syn.subst_var, Syn.inst_zero]
      show Γ ⊢[PRAAx] le (succ zero * succ zero) (pw two zero * pw two zero)
      have e := natEq (pw_zero (Γ := Γ) (two : PTm n))
      ipra_le 0 with (𝔞 (pw two zero) + 1) * e
    · rw [subst_sqInv]
      simp only [Syn.subst_var, Syn.repl_zero]
      let Δ : List (Fm PTm (n + 1)) := sqInv (var 0) :: List.map Fm.shift ([] : List (Fm PTm n))
      show (sqInv (var 0) :: Γ.map Fm.shift) ⊢[PRAAx] le (succ (succ (var 0)) * succ (succ (var 0)))
        (pw two (succ (var 0)) * pw two (succ (var 0)))
      have ih : (sqInv (var 0) :: Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0) * succ (var 0))
          (pw two (var 0) * pw two (var 0)) := Prf.hyp0
      have e := natEq (pw_succ (Γ := sqInv (var 0) :: Γ.map Fm.shift) (two : PTm (n + 1)) (var 0))
      ipra_le 4 * sl ih + 3 * 𝔞 (var 0) * 𝔞 (var 0) + 4 * 𝔞 (var 0)
        with (𝔞 (pw two (succ (var 0))) + 2 * 𝔞 (pw two (var 0))) * e
  have a := Prf.allE m hall
  rw [subst_sqInv] at a
  simp only [Syn.subst_var, Syn.inst_zero] at a
  exact a

/-- `4 n² 2^n ≤ 2^{3n²}` for `n = m + 1`: the cleared form of `4 n² 2^{−3n²} ≤ 2^{−n}`. -/
theorem theta_term (m : PTm n) :
    Γ ⊢[PRAAx] le (num 4 * (succ m * succ m) * pw two (succ m)) (pw two (num 3 * (succ m * succ m))) := by
  have h1 := sq_le_pow (Γ := Γ) m
  have e1 := natEq (pw_succ (Γ := Γ) (two : PTm n) m)
  -- `2^{3n} = 2^n 2^n 2^n`
  have h3 : Γ ⊢[PRAAx] num 3 * succ m ≐ (succ m + succ m) + succ m := by ipra_ring
  have e3 := natEq ((congrPw2 h3).eqTrans ((pw_add (Γ := Γ) two (succ m + succ m) (succ m)).eqTrans
    (congrMul (pw_add (Γ := Γ) two (succ m) (succ m)) (.eqRefl _))))
  -- `2^{3n} ≤ 2^{3n²}`
  have hle : Γ ⊢[PRAAx] le (num 3 * succ m) (num 3 * (succ m * succ m)) := by
    ipra_le 3 * 𝔞 m * 𝔞 m + 3 * 𝔞 m
  have hz : Γ ⊢[PRAAx] zero + num 3 * succ m ≐ num 3 * succ m := by apply deriveNat; ipra_simps; try ring
  have hz' : Γ ⊢[PRAAx] zero + num 3 * (succ m * succ m) ≐ num 3 * (succ m * succ m) := by
    apply deriveNat; ipra_simps; try ring
  have mono := le_congr (congrPw2 hz) (congrPw2 hz') (pw_mono2 (K0 := zero) hle)
  ipra_le sl mono + 4 * 𝔞 (pw two (succ m)) * sl h1
    with e3 + (𝔞 (pw two (succ m)) * 𝔞 (pw two (succ m)) + 2 * 𝔞 (pw two (succ m)) * 𝔞 (pw two m)) * e1

/-- For `n = N + 1 + j`: `n² ≥ (N + 1)² + j`. -/
theorem square_gap (N j : PTm n) : Γ ⊢[PRAAx] le (succ N * succ N + j) ((succ N + j) * (succ N + j)) := by
  ipra_le 2 * 𝔞 N * 𝔞 j + 𝔞 j + 𝔞 j * 𝔞 j

/-! ## The geometric tail of ratio `1/8` -/

/-- `8^j` as a body. -/
abbrev g8B : PTm 2 := pw (num 8) (var 0)

def geo8Inv (J x : PTm n) : Fm PTm n := num 7 * ap2 (sumF g8B) J x + one ≐ pw (num 8) J

ipra_subst geo8Inv [subst_ap2]

/-- `7 Σ_{j<J} 8^j + 1 = 8^J`. -/
theorem geo8 (J x : PTm n) : Γ ⊢[PRAAx] num 7 * ap2 (sumF g8B) J x + one ≐ pw (num 8) J := by
  refine GeometricSum.sum_eq_pow g8B J x (by ipra_ring) (.allI (.impI ?_))
  simp [inst2, Syn.shift]
  exact .eqRefl _

/-- `4 Σ_{j<J} 8^j ≤ 8^J`: a geometric sum of ratio `1/8` is at most twice its largest term. -/
theorem geo8_tail (J x : PTm n) : Γ ⊢[PRAAx] le (num 4 * ap2 (sumF g8B) J x) (pw (num 8) J) := by
  have e := natEq (geo8 (Γ := Γ) J x)
  ipra_le 3 * 𝔞 (ap2 (sumF g8B) J x) + 1 with e

/-! ## The complex `norm1` -/

/-- `|x − y| ≤ x + y`. -/
theorem dist_le_sum (x y : PTm n) : Γ ⊢[PRAAx] le (dist x y) (x + y) := by
  refine .orE (le_total x y) ?_ ?_
  · let Θ : List (Fm PTm n) := le x y :: Γ
    have h : Θ ⊢[PRAAx] le x y := Prf.hyp0
    have e1 := natEq (h : Θ ⊢[PRAAx] monus x y ≐ zero)
    have e2 := natEq (eq_add_of_le h)
    ipra_le 2 * 𝔞 x with e1 - e2
  · let Θ : List (Fm PTm n) := le y x :: Γ
    have h : Θ ⊢[PRAAx] le y x := Prf.hyp0
    have e1 := natEq (h : Θ ⊢[PRAAx] monus y x ≐ zero)
    have e2 := natEq (eq_add_of_le h)
    ipra_le 2 * 𝔞 y with e1 - e2

/-- `norm1((a + bi)(c + di)) ≤ norm1(a + bi) norm1(c + di)`:
`|ac − bd| + (ad + bc) ≤ (a + b)(c + d)`. -/
theorem norm1_mul (a b c d : PTm n) :
    Γ ⊢[PRAAx] le (dist (a * c) (b * d) + (a * d + b * c)) ((a + b) * (c + d)) := by
  have h := dist_le_sum (Γ := Γ) (a * c) (b * d)
  ipra_le sl h

/-- `x² + y² ≤ (x + y)² ≤ 2(x² + y²)`. -/
theorem norm1_compare (x y : PTm n) :
    Γ ⊢[PRAAx] le (x * x + y * y) ((x + y) * (x + y)) ⋏ le ((x + y) * (x + y)) (two * (x * x + y * y)) := by
  have e := natEq (dist_sq (Γ := Γ) x y)
  exact .andI (by ipra_le 2 * 𝔞 x * 𝔞 y) (by ipra_le 𝔞 (dist x y) * 𝔞 (dist x y) with e)

/-! ## The ceiling binary logarithm `λ`

"For `n ≥ 1`, let `λ(n)` be the least `j ≤ n` such that `n ≤ 2^j` … This is a bounded search, hence primitive
recursive. It satisfies `n ≤ 2^{λ(n)}` and is the ceiling binary logarithm." As a bounded witness
(`Foundations/BoundedReflection.wit`) of the bit `[n ≤ 2^j]`: `clog_spec` (`n ≤ 2^{λ(n)}`, `λ(n) ≤ n`) and
`clog_least` (`j < λ(n)` gives `2^j < n`). At `n = 0` it returns `0`, as the contract stipulates. -/

/-- `[x ≤ 2^j]` over `0 = j`, `1 = x`. -/
abbrev fitB : PTm 2 := monus one (monus (var 1) (pw two (var 0)))

/-- `λ(x)`: the least `j ≤ x` with `x ≤ 2^j`. -/
abbrev clog (x : PTm n) : PTm n := LeanProofs.IPRA.Foundations.BoundedReflection.wit fitB (succ x) x

theorem inst2_fitB (j x : PTm n) : inst2 fitB j x = monus one (monus x (pw two j)) := by simp [inst2]

def ltPowInv (x : PTm n) : Fm PTm n := le x (pw two x)

ipra_subst ltPowInv

/-- `x ≤ 2^x`. -/
theorem le_pow_self (x : PTm n) : Γ ⊢[PRAAx] le x (pw two x) := by
  have hall : Γ ⊢[PRAAx] Fm.all (ltPowInv (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · rw [subst_ltPowInv]; simp only [Syn.subst_var, Syn.inst_zero]
      exact zero_le _
    · rw [subst_ltPowInv]; simp only [Syn.subst_var, Syn.repl_zero]
      let Δ : List (Fm PTm (n + 1)) := ltPowInv (var 0) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] le (var 0) (pw two (var 0)) := Prf.hyp0
      have hp := natEq (DiophantineNumberTheory.FLTMultiples.pw_pos (Γ := Δ) one (var 0))
      have e := natEq (pw_succ (Γ := Δ) (two : PTm (n + 1)) (var 0))
      show Δ ⊢[PRAAx] le (succ (var 0)) (pw two (succ (var 0)))
      ipra_le sl ih + 𝔞 (pred (pw two (var 0))) with e + hp
  have a := Prf.allE x hall
  rw [subst_ltPowInv] at a
  simp only [Syn.subst_var, Syn.inst_zero] at a
  exact a

/-- `x ≤ 2^{λ(x)}` and `λ(x) ≤ x`. -/
theorem clog_spec (x : PTm n) : Γ ⊢[PRAAx] le x (pw two (clog x)) ⋏ le (clog x) x := by
  have hfit : Γ ⊢[PRAAx] neg (inst2 fitB x x ≐ zero) := by
    rw [inst2_fitB]
    refine .impI ?_
    have h0 : ((monus one (monus x (pw two x)) ≐ zero) :: Γ) ⊢[PRAAx] monus x (pw two x) ≐ zero := le_pow_self x
    exact LeanProofs.IPRA.Foundations.BoundedReflection.one_ne_zero _
      ((monus_zero one).eqSymm.eqTrans ((congrMonus (.eqRefl _) h0).eqSymm.eqTrans Prf.hyp0))
  have ex := LeanProofs.IPRA.Foundations.BoundedReflection.ex_intro fitB hfit (le_refl (succ x))
  have el := LeanProofs.IPRA.Foundations.BoundedReflection.ex_elim fitB ex
  have hne := Prf.andE₂ el
  rw [inst2_fitB] at hne
  have hlt : Γ ⊢[PRAAx] lt (clog x) (succ x) := Prf.andE₁ el
  refine .andI ?_ (by ipra_le sl hlt)
  refine .orE (lt_or_le (pw two (clog x)) x) ?_ Prf.hyp0
  let Θ : List (Fm PTm n) := lt (pw two (clog x)) x :: Γ
  have h : Θ ⊢[PRAAx] lt (pw two (clog x)) x := Prf.hyp0
  have e2 := natEq (eq_add_of_le (le_trans (le_succ_self (pw two (clog x))) h))
  have hp : Θ ⊢[PRAAx] le one (monus x (pw two (clog x))) := by ipra_le sl h with e2
  exact .botE _ (.impE hne.wk hp)

/-- `j < λ(x)` gives `2^j < x`. -/
theorem clog_least {j x : PTm n} (hj : Γ ⊢[PRAAx] lt j (clog x)) : Γ ⊢[PRAAx] lt (pw two j) x := by
  have z := LeanProofs.IPRA.Foundations.BoundedReflection.ex_least fitB hj
  rw [inst2_fitB] at z
  exact LeanProofs.IPRA.Foundations.IntervalPacking.lt_of_monus_pos z

end LeanProofs.IPRA.AnalyticNumberTheory.ZetaFiniteContract

export_ipra AnalyticNumberTheory.ZetaFiniteContract (clog clog_spec le_pow_self)
