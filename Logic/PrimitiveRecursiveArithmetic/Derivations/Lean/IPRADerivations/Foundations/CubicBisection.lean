import IPRADerivations.Foundations.BisectionInvariant
import IPRADerivations.AnalyticNumberTheory.Valuation

/-!
# The bisection bracket of the cubic `y³ + y = x`

Packets (`docs/proofs/foundations`): `cifer_ipra_framework_2026-11-15`, Lemma `lem:cubic-bisect`
("Bisection invariant", `eq:cubic-invariant`); `ipra_cfp_contract_compiler_2026-11-15`, "Bisection
invariant"; `ipra_uniform_certificates`, the corollary "An explicit stable cubic root" (its bisection
bracket); `FINER-iPRA-framework-2026-11-16`, Theorem "Bisection invariant" for the cubic example.

This is the instance of `Foundations/BisectionInvariant` for `F(y) = y³ + y` and a nonnegative rational
input `x = p/q` (`q ≥ 1`), coded as the pair `x = ⟨p, q⟩`. At stage `t` the endpoints are `ℓ/2^t`, `u/2^t`,
and `F(a/2^t) ≤ p/q` is the integer inequality `q (a³ + a 4^t) ≤ p 8^t`:

* `CLo`, `CHi`: the two sign formulas; `lo2`, `hi2`: they are invariant under `a ↦ 2a`, `t ↦ t + 1`;
* `cc`: the test term `q (m³ + m 4^{t+1}) ∸ p 8^{t+1}`, zero exactly when `F ≤ x` at the midpoint;
  `midLo`, `midHi`: its two outcomes;
* `cinit`: the initial bracket `[0, p + 1]`, valid because `F(p + 1) ≥ p + 1 > p/q`;
* `cubic_bisection`, `cubic_bracket`: for every stage `t`, with `ℓ_t`, `u_t` the components of the state,
  `q (ℓ_t³ + ℓ_t 4^t) ≤ p 8^t ≤ q (u_t³ + u_t 4^t)` and `u_t = ℓ_t + (p + 1)`; that is,
  `F(L_t) ≤ x ≤ F(U_t)` and `U_t − L_t = (p + 1)/2^t`;
* `width_fuel` (the precision fuel behind `thm:cubic-enclosure`): `W · 2^n ≤ 2^{n + W}`, so at the stage
  `t = n + (p + 1)` the width `(p + 1)/2^t` is at most `2^{-n}`;
* `cubic_nested`: `2ℓ_t ≤ ℓ_{t+1}` and `u_{t+1} ≤ 2u_t`, the brackets are nested.

The signed input and the bracket `[−M, M]` of the CIFER packet, the precision fuel and the regular name of
the root are not derived here; strict monotonicity and stability of the root are
`Foundations/StableCubicRoot`.
-/

namespace LeanProofs.IPRA.Foundations.CubicBisection

open_ipra exports
open LeanProofs.IPRA.Foundations.TraceReflection (Run I3 run_succ)
open LeanProofs.IPRA.Foundations.BisectionInvariant (cAt bStep BInv bisection_at I3_congr₁ bis_nested)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `F(a/2^t) ≤ p/q`: variables `0 = a`, `1 = t`, `2 = x = ⟨p, q⟩`. -/
def CLo : Fm PTm 3 :=
  le (sndT (var 2) * (var 0 * var 0 * var 0 + var 0 * pw (num 4) (var 1))) (fstT (var 2) * pw (num 8) (var 1))

/-- `p/q ≤ F(a/2^t)`. -/
def CHi : Fm PTm 3 :=
  le (fstT (var 2) * pw (num 8) (var 1)) (sndT (var 2) * (var 0 * var 0 * var 0 + var 0 * pw (num 4) (var 1)))

theorem CLo_QF : CLo.QF := by unfold CLo; exact le_QF _ _
theorem CHi_QF : CHi.QF := by unfold CHi; exact le_QF _ _

theorem I3_CLo (a t x : PTm k) :
    I3 CLo a t x = le (sndT x * (a * a * a + a * pw (num 4) t)) (fstT x * pw (num 8) t) := by
  simp [I3, CLo, PTm.subst_num]

theorem I3_CHi (a t x : PTm k) :
    I3 CHi a t x = le (fstT x * pw (num 8) t) (sndT x * (a * a * a + a * pw (num 4) t)) := by
  simp [I3, CHi, PTm.subst_num]

/-- The test at a midpoint numerator `m` of stage `t + 1`; variables `0 = m`, `1 = t`, `2 = x`. -/
def cc : PTm 3 :=
  monus (sndT (var 2) * (var 0 * var 0 * var 0 + var 0 * pw (num 4) (succ (var 1))))
    (fstT (var 2) * pw (num 8) (succ (var 1)))

theorem cAt_cc (m t x : PTm k) :
    cAt cc m t x =
      monus (sndT x * (m * m * m + m * pw (num 4) (succ t))) (fstT x * pw (num 8) (succ t)) := by
  simp [cAt, cc, PTm.subst_num]

/-! ## The four rules -/

theorem lo2 {m : ℕ} {Θ : List (Fm PTm m)} (a t x : PTm m) (h : Θ ⊢[PRAAx] I3 CLo a t x) :
    Θ ⊢[PRAAx] I3 CLo (a + a) (succ t) x := by
  rw [I3_CLo] at h ⊢
  have e₄ := natEq (pw_succ (Γ := Θ) (num 4) t)
  have e₈ := natEq (pw_succ (Γ := Θ) (num 8) t)
  ipra_le 8 * sl h using rw [e₄, e₈]; ring

theorem hi2 {m : ℕ} {Θ : List (Fm PTm m)} (a t x : PTm m) (h : Θ ⊢[PRAAx] I3 CHi a t x) :
    Θ ⊢[PRAAx] I3 CHi (a + a) (succ t) x := by
  rw [I3_CHi] at h ⊢
  have e₄ := natEq (pw_succ (Γ := Θ) (num 4) t)
  have e₈ := natEq (pw_succ (Γ := Θ) (num 8) t)
  ipra_le 8 * sl h using rw [e₄, e₈]; ring

theorem midLo {m : ℕ} {Θ : List (Fm PTm m)} (a t x : PTm m) (h : Θ ⊢[PRAAx] cAt cc a t x ≐ zero) :
    Θ ⊢[PRAAx] I3 CLo a (succ t) x := by
  rw [I3_CLo]
  rw [cAt_cc] at h
  exact h

theorem midHi {m : ℕ} {Θ : List (Fm PTm m)} (a t x d : PTm m) (h : Θ ⊢[PRAAx] cAt cc a t x ≐ succ d) :
    Θ ⊢[PRAAx] I3 CHi a (succ t) x := by
  rw [I3_CHi]
  rw [cAt_cc] at h
  refine .orE (le_total _ _) ?_ Prf.hyp0
  exact succ_ne_zero' _ (Prf.eqTrans (Prf.eqSymm h.wk) Prf.hyp0)

/-! ## The initial bracket -/

/-- The initial state `⟨0, p + 1⟩`; variable `0 = x`. -/
def cinit : PTm 1 := pairT zero (succ (fstT (var 0)))

theorem cinit_at (x : PTm k) : Syn.subst ![x] cinit = pairT zero (succ (fstT x)) := by
  simp [cinit]

theorem base_lo (x : PTm k) : Γ ⊢[PRAAx] I3 CLo zero zero x := by
  rw [I3_CLo]
  have z₄ := natEq (pw_zero (Γ := Γ) (num 4 : PTm k))
  have z₈ := natEq (pw_zero (Γ := Γ) (num 8 : PTm k))
  ipra_le 𝔟 (fstT x) using rw [z₄, z₈]; ring

theorem base_hi {x : PTm k} (hq : Γ ⊢[PRAAx] le one (sndT x)) :
    Γ ⊢[PRAAx] I3 CHi (succ (fstT x)) zero x := by
  rw [I3_CHi]
  have z₄ := natEq (pw_zero (Γ := Γ) (num 4 : PTm k))
  have z₈ := natEq (pw_zero (Γ := Γ) (num 8 : PTm k))
  ipra_le sl hq * ((𝔟 (fstT x) + 1) * (𝔟 (fstT x) + 1) * (𝔟 (fstT x) + 1) + (𝔟 (fstT x) + 1))
      + (𝔟 (fstT x) + 1) * (𝔟 (fstT x) + 1) * (𝔟 (fstT x) + 1) + 1 using
    rw [z₄, z₈]; ring

theorem base {x : PTm k} (hq : Γ ⊢[PRAAx] le one (sndT x)) :
    Γ ⊢[PRAAx] BInv CLo CHi (pairT zero (succ (fstT x))) zero x (succ (fstT x)) := by
  have f := fst_pair (Γ := Γ) zero (succ (fstT x))
  have s := snd_pair (Γ := Γ) zero (succ (fstT x))
  refine .andI (I3_congr₁ CLo f.eqSymm (base_lo x)) (.andI (I3_congr₁ CHi s.eqSymm (base_hi hq)) ?_)
  ipra_lc natEq s - natEq f

/-! ## The bracket at every stage -/

/-- `lem:cubic-bisect`: the bisection invariant of the cubic chart at every stage. -/
theorem cubic_bisection {x : PTm k} (hq : Γ ⊢[PRAAx] le one (sndT x)) (t : PTm k) :
    Γ ⊢[PRAAx] BInv CLo CHi (Run cinit (bStep cc) t x) t x (succ (fstT x)) :=
  bisection_at CLo_QF CHi_QF lo2 hi2 midLo midHi cinit (by rw [cinit_at]; exact base hq) t

/-- The same with the sign conditions written out:
`q (ℓ³ + ℓ 4^t) ≤ p 8^t ≤ q (u³ + u 4^t)` and `u = ℓ + (p + 1)`. -/
theorem cubic_bracket {x : PTm k} (hq : Γ ⊢[PRAAx] le one (sndT x)) (t : PTm k) :
    Γ ⊢[PRAAx]
      le (sndT x * (fstT (Run cinit (bStep cc) t x) * fstT (Run cinit (bStep cc) t x) *
            fstT (Run cinit (bStep cc) t x) + fstT (Run cinit (bStep cc) t x) * pw (num 4) t))
          (fstT x * pw (num 8) t) ⋏
        (le (fstT x * pw (num 8) t)
            (sndT x * (sndT (Run cinit (bStep cc) t x) * sndT (Run cinit (bStep cc) t x) *
              sndT (Run cinit (bStep cc) t x) + sndT (Run cinit (bStep cc) t x) * pw (num 4) t)) ⋏
          (sndT (Run cinit (bStep cc) t x) ≐ fstT (Run cinit (bStep cc) t x) + succ (fstT x))) := by
  have h := cubic_bisection hq t
  have hl := Prf.andE₁ h
  have hh := Prf.andE₁ (Prf.andE₂ h)
  rw [I3_CLo] at hl
  rw [I3_CHi] at hh
  exact .andI hl (.andI hh (Prf.andE₂ (Prf.andE₂ h)))

/-- Nestedness (`thm:cubic-enclosure`, last clause): the bracket of stage `t + 1` lies inside the bracket of
stage `t`: `2ℓ_t ≤ ℓ_{t+1}` and `u_{t+1} ≤ 2u_t`. -/
theorem cubic_nested {x : PTm k} (hq : Γ ⊢[PRAAx] le one (sndT x)) (t : PTm k) :
    Γ ⊢[PRAAx]
      le (fstT (Run cinit (bStep cc) t x) + fstT (Run cinit (bStep cc) t x))
          (fstT (Run cinit (bStep cc) (succ t) x)) ⋏
        le (sndT (Run cinit (bStep cc) (succ t) x))
          (sndT (Run cinit (bStep cc) t x) + sndT (Run cinit (bStep cc) t x)) :=
  bis_nested (run_succ t x) (le_of_eq_add (Prf.andE₂ (Prf.andE₂ (cubic_bisection hq t))))

/-! ## The precision fuel -/

/-- `W · 2^n ≤ 2^{n + W}`: a bracket of width numerator `W` at stage `n + W` has width at most `2^{-n}`. -/
theorem width_fuel (W n : PTm k) : Γ ⊢[PRAAx] le (W * pw two n) (pw two (n + W)) := by
  have h : Γ ⊢[PRAAx] le (succ W) (pw two W) := lt_pw (le_refl two) W
  have e := natEq (pw_add (Γ := Γ) two n W)
  ipra_le 𝔟 (pw two n) * (sl h + 1) using rw [e]; ring

end LeanProofs.IPRA.Foundations.CubicBisection
