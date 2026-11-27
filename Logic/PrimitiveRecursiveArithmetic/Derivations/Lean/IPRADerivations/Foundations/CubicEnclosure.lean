import IPRADerivations.Foundations.CubicBisection

/-!
# The certified enclosure of the cubic root

Packet: `foundations/cifer_ipra_framework_2026-11-15`, `paper/sections/11_cubic.tex`, Theorem
`thm:cubic-enclosure` ("Certified enclosure"): there are primitive-recursive rational terms `l(x, q)`,
`u(x, q)` with `l ≤ u`, `F(l) ≤ x ≤ F(u)`, `u − l ≤ 2^{-q}`, and nested intervals. The same enclosure is
"Finite cubic bisection" with its fuel in `ipra_staged_contract_kernel_2026-11-15` and the certified cubic
name of `ipra_cfp_contract_compiler_2026-11-15`.

With the bisection run of `Foundations/CubicBisection` for a nonnegative rational input `x = p/q`
(`S_t` the state at stage `t`, endpoints `ℓ_t/2^t`, `u_t/2^t`):

* `enclosure_width`: at the stage `t = n + (p + 1)`, `u_t 2^n ≤ ℓ_t 2^n + 2^t`, i.e. the width
  `(u_t − ℓ_t)/2^t` is at most `2^{-n}`;
* `nested_step`, `nested_multi`: for every `j`, `2^j ℓ_t ≤ ℓ_{t+j}` and `u_{t+j} ≤ 2^j u_t`, i.e. the
  bracket of stage `t + j` lies inside the bracket of stage `t`.

* `nested_at`: the instance at a given `j`;
* `midpoint_close` (the regularity of the midpoint name `c = (l + u)/2`): for the midpoint numerators
  `m_t = ℓ_t + u_t` (over `2^{t+1}`), `m_{t+j} ≤ 2^j m_t + 2^j (p + 1)` and
  `2^j m_t ≤ m_{t+j} + 2^j (p + 1)`, i.e. `|c_{t+j} − c_t| ≤ (p + 1)/2^{t+1}`, half the width of the
  bracket of stage `t`.

* `endpoint_residual` (the estimate behind "The equation in represented form",
  `|F(c) − x| ≤ (3M² + 1)(u − l)`): with `FN(a) = a³ + a 4^t` the numerator of `F(a/2^t)`,
  `q FN(u_t) ≤ p 8^t + q (p + 1)(3u_t² + 4^t)` and `p 8^t ≤ q FN(ℓ_t) + q (p + 1)(3u_t² + 4^t)`, i.e.
  `|F(U_t) − x|` and `|F(L_t) − x|` are at most `(U_t − L_t)(3U_t² + 1)`.

The sign bracket itself is `cubic_bracket`. The final alignment with the regular-name convention and the
uniqueness of the represented root (`Foundations/StableCubicRoot` for rational roots) are not derived
here.
-/

namespace LeanProofs.IPRA.Foundations.CubicEnclosure

open_ipra exports
open LeanProofs.IPRA.Foundations.BisectionInvariant (bStep)
open LeanProofs.IPRA.Foundations.CubicBisection (cinit cc cubic_bisection cubic_bracket cubic_nested width_fuel)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The state of the cubic bisection at stage `t`. -/
abbrev St (t x : PTm k) : PTm k := Run cinit (bStep cc) t x

/-- `thm:cubic-enclosure`, the width: at the stage `n + (p + 1)` the width is at most `2^{-n}`. -/
theorem enclosure_width {x : PTm k} (hq : Γ ⊢[PRAAx] le one (sndT x)) (m : PTm k) :
    Γ ⊢[PRAAx] le (sndT (St (m + succ (fstT x)) x) * pw two m)
      (fstT (St (m + succ (fstT x)) x) * pw two m + pw two (m + succ (fstT x))) := by
  have hw := natEq (Prf.andE₂ (Prf.andE₂ (cubic_bisection hq (m + succ (fstT x)))))
  have hf := width_fuel (Γ := Γ) (succ (fstT x)) m
  ipra_le sl hf using linear_combination (-𝔟 (pw two m)) * hw

/-- One more stage of nestedness. -/
theorem nested_step {x t j : PTm k} (hq : Γ ⊢[PRAAx] le one (sndT x))
    (ih : Γ ⊢[PRAAx] le (pw two j * fstT (St t x)) (fstT (St (t + j) x)) ⋏
      le (sndT (St (t + j) x)) (pw two j * sndT (St t x))) :
    Γ ⊢[PRAAx] le (pw two (succ j) * fstT (St t x)) (fstT (St (t + succ j) x)) ⋏
      le (sndT (St (t + succ j) x)) (pw two (succ j) * sndT (St t x)) := by
  have ns := cubic_nested hq (t + j)
  have c := congrAp2 (rec2 cinit (bStep cc)) (add_succ (Γ := Γ) t j) (Prf.eqRefl x)
  have e₁ := natEq (congrFst c)
  have e₂ := natEq (congrSnd c)
  have p := natEq (pw_succ (Γ := Γ) two j)
  have ih₁ := Prf.andE₁ ih
  have ih₂ := Prf.andE₂ ih
  have n₁ := Prf.andE₁ ns
  have n₂ := Prf.andE₂ ns
  refine .andI ?_ ?_
  · ipra_le 2 * sl ih₁ + sl n₁ using rw [e₁, p]; ring
  · ipra_le 2 * sl ih₂ + sl n₂ using rw [e₂, p]; ring

theorem nested_base (x t : PTm k) :
    Γ ⊢[PRAAx] le (pw two zero * fstT (St t x)) (fstT (St (t + zero) x)) ⋏
      le (sndT (St (t + zero) x)) (pw two zero * sndT (St t x)) := by
  have c := congrAp2 (rec2 cinit (bStep cc)) (add_zero (Γ := Γ) t) (Prf.eqRefl x)
  have e₁ := natEq (congrFst c)
  have e₂ := natEq (congrSnd c)
  have p := natEq (pw_zero (Γ := Γ) (two : PTm k))
  refine .andI ?_ ?_
  · ipra_le 0 using rw [e₁, p]; ring
  · ipra_le 0 using rw [e₂, p]; ring

/-- `thm:cubic-enclosure`, nestedness: the bracket of stage `t + j` lies inside the bracket of stage
`t`. -/
theorem nested_multi {x : PTm k} (hq : Γ ⊢[PRAAx] le one (sndT x)) (t : PTm k) :
    Γ ⊢[PRAAx] Fm.all
      (le (pw two (var 0) * fstT (St (Syn.shift t) (Syn.shift x)))
          (fstT (St (Syn.shift t + var 0) (Syn.shift x))) ⋏
        le (sndT (St (Syn.shift t + var 0) (Syn.shift x)))
          (pw two (var 0) * sndT (St (Syn.shift t) (Syn.shift x)))) := by
  refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
  · have e : (le (pw two (var 0) * fstT (St (Syn.shift t) (Syn.shift x)))
          (fstT (St (Syn.shift t + var 0) (Syn.shift x))) ⋏
        le (sndT (St (Syn.shift t + var 0) (Syn.shift x)))
          (pw two (var 0) * sndT (St (Syn.shift t) (Syn.shift x)))).subst (Syn.inst zero) =
        (le (pw two zero * fstT (St t x)) (fstT (St (t + zero) x)) ⋏
          le (sndT (St (t + zero) x)) (pw two zero * sndT (St t x))) := by
      simp
    rw [e]
    exact nested_base x t
  · have e : (le (pw two (var 0) * fstT (St (Syn.shift t) (Syn.shift x)))
          (fstT (St (Syn.shift t + var 0) (Syn.shift x))) ⋏
        le (sndT (St (Syn.shift t + var 0) (Syn.shift x)))
          (pw two (var 0) * sndT (St (Syn.shift t) (Syn.shift x)))).subst (Syn.repl (succ (var 0))) =
        (le (pw two (succ (var 0)) * fstT (St (Syn.shift t) (Syn.shift x)))
            (fstT (St (Syn.shift t + succ (var 0)) (Syn.shift x))) ⋏
          le (sndT (St (Syn.shift t + succ (var 0)) (Syn.shift x)))
            (pw two (succ (var 0)) * sndT (St (Syn.shift t) (Syn.shift x)))) := by
      simp
    rw [e]
    have hq' := hq.shift
    have eq' : Fm.shift (le one (sndT x)) = le one (sndT (Syn.shift x)) := by simp [Fm.shift, Syn.shift]
    rw [eq'] at hq'
    exact nested_step hq'.wk Prf.hyp0

/-- Nestedness at a given number of further stages. -/
theorem nested_at {x : PTm k} (hq : Γ ⊢[PRAAx] le one (sndT x)) (t j : PTm k) :
    Γ ⊢[PRAAx] le (pw two j * fstT (St t x)) (fstT (St (t + j) x)) ⋏
      le (sndT (St (t + j) x)) (pw two j * sndT (St t x)) := by
  have a := Prf.allE j (nested_multi hq t)
  have e : (le (pw two (var 0) * fstT (St (Syn.shift t) (Syn.shift x)))
        (fstT (St (Syn.shift t + var 0) (Syn.shift x))) ⋏
      le (sndT (St (Syn.shift t + var 0) (Syn.shift x)))
        (pw two (var 0) * sndT (St (Syn.shift t) (Syn.shift x)))).subst (Syn.inst j) =
      (le (pw two j * fstT (St t x)) (fstT (St (t + j) x)) ⋏
        le (sndT (St (t + j) x)) (pw two j * sndT (St t x))) := by
    simp
  rw [e] at a
  exact a

/-- The midpoints of later brackets stay within half the width of the bracket of stage `t`. -/
theorem midpoint_close {x : PTm k} (hq : Γ ⊢[PRAAx] le one (sndT x)) (t j : PTm k) :
    Γ ⊢[PRAAx]
      le (fstT (St (t + j) x) + sndT (St (t + j) x))
          (pw two j * (fstT (St t x) + sndT (St t x)) + pw two j * succ (fstT x)) ⋏
        le (pw two j * (fstT (St t x) + sndT (St t x)))
          (fstT (St (t + j) x) + sndT (St (t + j) x) + pw two j * succ (fstT x)) := by
  have na := nested_at hq t j
  have n₁ := Prf.andE₁ na
  have n₂ := Prf.andE₂ na
  have w₁ := natEq (Prf.andE₂ (Prf.andE₂ (cubic_bisection hq t)))
  have w₂ := natEq (Prf.andE₂ (Prf.andE₂ (cubic_bisection hq (t + j))))
  refine .andI ?_ ?_
  · ipra_le 2 * sl n₂ + (𝔟 (fstT x) + 1) using linear_combination (-𝔟 (pw two j)) * w₁ + w₂
  · ipra_le 2 * sl n₁ + (𝔟 (fstT x) + 1) using linear_combination (-𝔟 (pw two j)) * w₁ + w₂

/-- The residual of the equation at the endpoints of the bracket is at most
`(U_t − L_t)(3U_t² + 1)`. -/
theorem endpoint_residual {x : PTm k} (hq : Γ ⊢[PRAAx] le one (sndT x)) (t : PTm k) :
    Γ ⊢[PRAAx]
      le (sndT x * (sndT (St t x) * sndT (St t x) * sndT (St t x) + sndT (St t x) * pw (num 4) t))
          (fstT x * pw (num 8) t +
            sndT x * succ (fstT x) * (num 3 * (sndT (St t x) * sndT (St t x)) + pw (num 4) t)) ⋏
        le (fstT x * pw (num 8) t)
          (sndT x * (fstT (St t x) * fstT (St t x) * fstT (St t x) + fstT (St t x) * pw (num 4) t) +
            sndT x * succ (fstT x) * (num 3 * (sndT (St t x) * sndT (St t x)) + pw (num 4) t)) := by
  have br := cubic_bracket hq t
  have lo := Prf.andE₁ br
  have hi := Prf.andE₁ (Prf.andE₂ br)
  have w := natEq (Prf.andE₂ (Prf.andE₂ br))
  refine .andI ?_ ?_
  · ipra_le sl lo + 𝔟 (sndT x) * (𝔟 (fstT x) + 1) * (𝔟 (fstT x) + 1) *
        (2 * 𝔟 (sndT (St t x)) + 𝔟 (fstT (St t x))) using rw [w]; ring
  · ipra_le sl hi + 𝔟 (sndT x) * (𝔟 (fstT x) + 1) * (𝔟 (fstT x) + 1) *
        (2 * 𝔟 (sndT (St t x)) + 𝔟 (fstT (St t x))) using rw [w]; ring

end LeanProofs.IPRA.Foundations.CubicEnclosure
