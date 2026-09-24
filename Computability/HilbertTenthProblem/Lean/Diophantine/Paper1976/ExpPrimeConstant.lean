import Diophantine.Common.ExpPolyZeros
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Theorem 4.4: prime-valued exponential polynomials are constant

`F(x) = Σᵢ Pᵢ(x) aᵢ^{Qᵢ(x)}` with integer polynomials `Pᵢ, Qᵢ`, `Qᵢ ≥ 0` on the nonnegative
integer grid and positive integers `aᵢ`. If `F` takes only prime values on the grid it is constant
there (`theorem_4_4`), and so is its real extension `Σᵢ Pᵢ(x) aᵢ^{Qᵢ(x)}` on all of `ℝⁿ`
(`theorem_4_4_real`).

One variable (`line_constant`): some prime `p` is a value infinitely often — either a value `p`
exceeds every `aᵢ`, and then Fermat's theorem gives `F(x₁ + kp(p−1)) ≡ p (mod p)`, hence `= p`, for
every `k`; or `F` is bounded and some value repeats infinitely often. The real exponential
polynomial `F(x) − p` then has arbitrarily large zeros, so it vanishes identically
(`Diophantine.expPoly_eq_zero_of_frequently`). Several variables: apply this on every coordinate
line, first through the grid and then, with real coordinates introduced one at a time, through
`ℝⁿ`.
-/

namespace JSWW1976

open Polynomial Diophantine

noncomputable section

/-! ### One variable -/

/-- The one-variable exponential polynomial on naturals. -/
def expSum1 {m : ℕ} (p q : Fin m → ℤ[X]) (a : Fin m → ℕ) (t : ℕ) : ℤ :=
  ∑ i, (p i).eval (t : ℤ) * (a i : ℤ) ^ ((q i).eval (t : ℤ)).toNat

/-- The same exponential polynomial on reals. -/
def expSumR1 {m : ℕ} (p q : Fin m → ℝ[X]) (a : Fin m → ℕ) (t : ℝ) : ℝ :=
  ∑ i, (p i).eval t * (a i : ℝ) ^ (q i).eval t

/-- A real exponential sum minus a constant is an `expPoly`. -/
theorem expSumR1_sub_eq {m : ℕ} (p q : Fin m → ℝ[X]) (a : Fin m → ℕ) (ha : ∀ i, 0 < a i)
    (c : ℝ) (t : ℝ) :
    expSumR1 p q a t - c = expPoly Finset.univ
      (fun o : Option (Fin m) => o.elim (C (-c)) p)
      (fun o : Option (Fin m) => o.elim 0 (fun i => C (Real.log (a i)) * q i)) t := by
  unfold expSumR1 expPoly
  rw [Fintype.sum_option]
  simp only [Option.elim, eval_C, eval_zero, Real.exp_zero, mul_one, eval_mul]
  rw [neg_add_eq_sub]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.rpow_def_of_pos (by exact_mod_cast ha i), mul_comm (Real.log _)]

/-- **A real exponential sum with arbitrarily large zeros of `F − c` is identically `c`.** -/
theorem expSumR1_const {m : ℕ} (p q : Fin m → ℝ[X]) (a : Fin m → ℕ) (ha : ∀ i, 0 < a i)
    (c : ℝ) (h : ∀ N : ℝ, ∃ t ≥ N, expSumR1 p q a t = c) : ∀ t, expSumR1 p q a t = c := by
  have hz := expPoly_eq_zero_of_frequently
    (fun o : Option (Fin m) => o.elim (C (-c)) p)
    (fun o : Option (Fin m) => o.elim 0 (fun i => C (Real.log (a i)) * q i)) Finset.univ
    (fun N => by
      obtain ⟨t, ht, htc⟩ := h N
      exact ⟨t, ht, by rw [← expSumR1_sub_eq p q a ha, htc, sub_self]⟩)
  intro t
  have := hz t
  rw [← expSumR1_sub_eq p q a ha] at this
  linarith

theorem eval_intCast_real (f : ℤ[X]) (t : ℕ) :
    ((f.eval (t : ℤ) : ℤ) : ℝ) = (f.map (Int.castRingHom ℝ)).eval (t : ℝ) := by
  rw [eval_map]
  have := eval₂_hom (Int.castRingHom ℝ) (t : ℤ) (p := f)
  simpa using this.symm

theorem expSum1_cast {m : ℕ} (p q : Fin m → ℤ[X]) (a : Fin m → ℕ)
    (hq : ∀ i (t : ℕ), 0 ≤ (q i).eval (t : ℤ)) (t : ℕ) :
    ((expSum1 p q a t : ℤ) : ℝ) = expSumR1 (fun i => (p i).map (Int.castRingHom ℝ))
      (fun i => (q i).map (Int.castRingHom ℝ)) a t := by
  unfold expSum1 expSumR1
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← eval_intCast_real, ← eval_intCast_real]
  congr 1
  have e : (((q i).eval (t : ℤ)).toNat : ℝ) = (((q i).eval (t : ℤ) : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (hq i t)]
  rw [← e, Real.rpow_natCast]

/-- Congruence of exponential sums at arguments congruent modulo `p (p − 1)`. -/
theorem expSum1_modEq {m : ℕ} (p q : Fin m → ℤ[X]) (a : Fin m → ℕ)
    (hq : ∀ i (t : ℕ), 0 ≤ (q i).eval (t : ℤ)) {r : ℕ} (hr : r.Prime)
    (hra : ∀ i, ¬ r ∣ a i) (u t : ℕ) (hut : ((r * (r - 1) : ℕ) : ℤ) ∣ (u : ℤ) - t) :
    (r : ℤ) ∣ expSum1 p q a u - expSum1 p q a t := by
  haveI := Fact.mk hr
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]
  unfold expSum1
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hP : (((p i).eval (u : ℤ) : ℤ) : ZMod r) = (((p i).eval (t : ℤ) : ℤ) : ZMod r) := by
    rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine dvd_trans (dvd_trans ⟨((r - 1 : ℕ) : ℤ), by push_cast; ring⟩ hut)
      (sub_dvd_eval_sub (u : ℤ) (t : ℤ) (p i))
  have hQ : ((q i).eval (u : ℤ)).toNat % (r - 1) = ((q i).eval (t : ℤ)).toNat % (r - 1) := by
    have hd' : ((r - 1 : ℕ) : ℤ) ∣ (q i).eval (u : ℤ) - (q i).eval (t : ℤ) :=
      dvd_trans (dvd_trans ⟨(r : ℤ), by push_cast; ring⟩ hut) (sub_dvd_eval_sub _ _ _)
    have he1 : (((q i).eval (u : ℤ)).toNat : ℤ) = (q i).eval (u : ℤ) := Int.toNat_of_nonneg (hq i u)
    have he2 : (((q i).eval (t : ℤ)).toNat : ℤ) = (q i).eval (t : ℤ) := Int.toNat_of_nonneg (hq i t)
    have : (((q i).eval (u : ℤ)).toNat : ℤ) % ((r - 1 : ℕ) : ℤ) =
        (((q i).eval (t : ℤ)).toNat : ℤ) % ((r - 1 : ℕ) : ℤ) :=
      Int.emod_eq_emod_iff_emod_sub_eq_zero.2 (Int.emod_eq_zero_of_dvd (by rw [he1, he2]; exact hd'))
    exact_mod_cast this
  have hA : ((a i : ℕ) : ZMod r) ^ (r - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one (by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact hra i)
  have hpow : ∀ e : ℕ, ((a i : ℕ) : ZMod r) ^ e = ((a i : ℕ) : ZMod r) ^ (e % (r - 1)) := by
    intro e
    conv_lhs => rw [← Nat.div_add_mod e (r - 1), pow_add, pow_mul, hA, one_pow, one_mul]
  rw [hP, hpow, hQ, ← hpow]

/-- **One variable**: a prime-valued exponential sum on the naturals is constant. -/
theorem line_constant {m : ℕ} (p q : Fin m → ℤ[X]) (a : Fin m → ℕ) (ha : ∀ i, 0 < a i)
    (hq : ∀ i (t : ℕ), 0 ≤ (q i).eval (t : ℤ))
    (hprime : ∀ t : ℕ, ∃ r : ℕ, r.Prime ∧ expSum1 p q a t = r) :
    ∀ t, expSum1 p q a t = expSum1 p q a 0 := by
  classical
  -- a value taken arbitrarily far out
  obtain ⟨c, hc⟩ : ∃ c : ℤ, ∀ N : ℕ, ∃ t ≥ N, expSum1 p q a t = c := by
    set M := ∑ i, a i
    by_cases hbig : ∃ t, (M : ℤ) < expSum1 p q a t
    · obtain ⟨t₀, ht₀⟩ := hbig
      obtain ⟨r, hr, hrt⟩ := hprime t₀
      refine ⟨r, fun N => ⟨t₀ + N * (r * (r - 1)), ?_, ?_⟩⟩
      · have : 1 ≤ r * (r - 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hr.ne_zero
          (by have := hr.two_le; omega))
        nlinarith
      · have hra : ∀ i, ¬ r ∣ a i := fun i hdvd => by
          have h1 := Nat.le_of_dvd (ha i) hdvd
          have h2 : a i ≤ M := Finset.single_le_sum (fun j _ => Nat.zero_le (a j))
            (Finset.mem_univ i)
          rw [hrt] at ht₀
          omega
        have hd := expSum1_modEq p q a hq hr hra (t₀ + N * (r * (r - 1))) t₀ ⟨N, by push_cast; ring⟩
        obtain ⟨r', hr', hrt'⟩ := hprime (t₀ + N * (r * (r - 1)))
        rw [hrt, hrt'] at hd
        have hd' : (r : ℤ) ∣ (r' : ℤ) := by
          have := dvd_add hd (dvd_refl (r : ℤ)); simpa using this
        have := (Nat.prime_dvd_prime_iff_eq hr hr').1 (Int.natCast_dvd_natCast.1 hd')
        rw [hrt', this]
    · push_neg at hbig
      let f : ℕ → Fin (M + 1) := fun t => ⟨(expSum1 p q a t).toNat, by
        have := hbig t
        obtain ⟨r, _, hr⟩ := hprime t
        rw [hr] at this ⊢
        simp only [Int.toNat_natCast]
        exact_mod_cast Nat.lt_succ_of_le (by exact_mod_cast this)⟩
      obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber f
      obtain ⟨t₁, ht₁⟩ := Set.infinite_coe_iff.1 hy |>.nonempty
      refine ⟨expSum1 p q a t₁, fun N => ?_⟩
      obtain ⟨t, ht, htN⟩ := (Set.infinite_coe_iff.1 hy).exists_gt N
      refine ⟨t, htN.le, ?_⟩
      have e1 : f t = y := ht
      have e2 : f t₁ = y := ht₁
      have := congrArg Fin.val (e1.trans e2.symm)
      simp only [f] at this
      obtain ⟨r, _, hr⟩ := hprime t
      obtain ⟨r₁, _, hr₁⟩ := hprime t₁
      rw [hr, hr₁] at this ⊢
      simp only [Int.toNat_natCast] at this
      rw [this]
  -- the real extension then equals `c` everywhere
  have hR := expSumR1_const (fun i => (p i).map (Int.castRingHom ℝ))
    (fun i => (q i).map (Int.castRingHom ℝ)) a ha (c : ℝ) (fun N => by
      obtain ⟨t, ht, htc⟩ := hc (⌈N⌉₊)
      refine ⟨t, le_trans (Nat.le_ceil N) (by exact_mod_cast ht), ?_⟩
      rw [← expSum1_cast p q a hq t, htc])
  intro t
  have h1 := hR t
  have h0 := hR ((0 : ℕ) : ℝ)
  rw [← expSum1_cast p q a hq t] at h1
  rw [← expSum1_cast p q a hq 0] at h0
  exact_mod_cast h1.trans h0.symm

/-! ### Several variables -/

section Several

variable {σ : Type*} [DecidableEq σ] {m : ℕ}

/-- `F(v) = Σᵢ Pᵢ(v) aᵢ^{Qᵢ(v)}` on the nonnegative integer grid. -/
def expSum (P Q : Fin m → MvPolynomial σ ℤ) (a : Fin m → ℕ) (v : σ → ℕ) : ℤ :=
  ∑ i, MvPolynomial.eval (fun j => (v j : ℤ)) (P i) *
    (a i : ℤ) ^ (MvPolynomial.eval (fun j => (v j : ℤ)) (Q i)).toNat

/-- The real extension `Σᵢ Pᵢ(x) aᵢ^{Qᵢ(x)}` on `ℝⁿ`. -/
def expSumR (P Q : Fin m → MvPolynomial σ ℤ) (a : Fin m → ℕ) (x : σ → ℝ) : ℝ :=
  ∑ i, MvPolynomial.eval₂ (Int.castRingHom ℝ) x (P i) *
    (a i : ℝ) ^ MvPolynomial.eval₂ (Int.castRingHom ℝ) x (Q i)

/-- An integer polynomial restricted to a coordinate line of the grid. -/
def lineZ (f : MvPolynomial σ ℤ) (v : σ → ℕ) (i : σ) : ℤ[X] :=
  MvPolynomial.eval₂ Polynomial.C (fun j => if j = i then X else C (v j : ℤ)) f

/-- An integer polynomial restricted to a real coordinate line. -/
def lineR (f : MvPolynomial σ ℤ) (x : σ → ℝ) (i : σ) : ℝ[X] :=
  MvPolynomial.eval₂ (Polynomial.C.comp (Int.castRingHom ℝ)) (fun j => if j = i then X else C (x j)) f

theorem lineZ_eval (f : MvPolynomial σ ℤ) (v : σ → ℕ) (i : σ) (t : ℕ) :
    (lineZ f v i).eval (t : ℤ) = MvPolynomial.eval (fun j => (Function.update v i t j : ℤ)) f := by
  have h := congrArg (fun φ : MvPolynomial σ ℤ →+* ℤ => φ f)
    (MvPolynomial.comp_eval₂Hom Polynomial.C (fun j => if j = i then X else C (v j : ℤ))
      (Polynomial.evalRingHom (t : ℤ)))
  simp only [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, Polynomial.coe_evalRingHom] at h
  rw [lineZ, h, MvPolynomial.eval]
  have hc : (Polynomial.evalRingHom (t : ℤ)).comp Polynomial.C = RingHom.id ℤ := by
    ext; simp
  rw [MvPolynomial.coe_eval₂Hom, hc]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

theorem lineR_eval (f : MvPolynomial σ ℤ) (x : σ → ℝ) (i : σ) (t : ℝ) :
    (lineR f x i).eval t = MvPolynomial.eval₂ (Int.castRingHom ℝ) (Function.update x i t) f := by
  have h := congrArg (fun φ : MvPolynomial σ ℤ →+* ℝ => φ f)
    (MvPolynomial.comp_eval₂Hom (Polynomial.C.comp (Int.castRingHom ℝ))
      (fun j => if j = i then X else C (x j)) (Polynomial.evalRingHom t))
  simp only [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, Polynomial.coe_evalRingHom] at h
  rw [lineR, h]
  have hc : (Polynomial.evalRingHom t).comp (Polynomial.C.comp (Int.castRingHom ℝ)) =
      Int.castRingHom ℝ := by
    ext; simp
  rw [hc]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

theorem expSum_line (P Q : Fin m → MvPolynomial σ ℤ) (a : Fin m → ℕ) (v : σ → ℕ) (i : σ)
    (t : ℕ) : expSum P Q a (Function.update v i t) =
      expSum1 (fun k => lineZ (P k) v i) (fun k => lineZ (Q k) v i) a t := by
  simp only [expSum, expSum1, lineZ_eval]

theorem expSumR_line (P Q : Fin m → MvPolynomial σ ℤ) (a : Fin m → ℕ) (x : σ → ℝ) (i : σ)
    (t : ℝ) : expSumR P Q a (Function.update x i t) =
      expSumR1 (fun k => lineR (P k) x i) (fun k => lineR (Q k) x i) a t := by
  simp only [expSumR, expSumR1, lineR_eval]

omit [DecidableEq σ] in
theorem eval₂_natCast (f : MvPolynomial σ ℤ) (v : σ → ℕ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (fun j => (v j : ℝ)) f =
      ((MvPolynomial.eval (fun j => (v j : ℤ)) f : ℤ) : ℝ) := by
  have := MvPolynomial.map_eval (Int.castRingHom ℝ) (fun j => (v j : ℤ)) f
  simp only [eq_intCast] at this
  rw [this, MvPolynomial.eval_map]
  rfl

omit [DecidableEq σ] in
theorem expSumR_natCast (P Q : Fin m → MvPolynomial σ ℤ) (a : Fin m → ℕ)
    (hQ : ∀ i (v : σ → ℕ), 0 ≤ MvPolynomial.eval (fun j => (v j : ℤ)) (Q i)) (v : σ → ℕ) :
    expSumR P Q a (fun j => (v j : ℝ)) = (expSum P Q a v : ℝ) := by
  unfold expSumR expSum
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast, eval₂_natCast]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have e : ((MvPolynomial.eval (fun j => (v j : ℤ)) (Q i)).toNat : ℝ) =
      ((MvPolynomial.eval (fun j => (v j : ℤ)) (Q i) : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (hQ i v)]
  rw [← e, Real.rpow_natCast]

variable [Fintype σ]

/-- **Theorem 4.4** on the grid: a prime-valued exponential polynomial is constant. -/
theorem theorem_4_4 (P Q : Fin m → MvPolynomial σ ℤ) (a : Fin m → ℕ) (ha : ∀ i, 0 < a i)
    (hQ : ∀ i (v : σ → ℕ), 0 ≤ MvPolynomial.eval (fun j => (v j : ℤ)) (Q i))
    (hprime : ∀ v : σ → ℕ, ∃ r : ℕ, r.Prime ∧ expSum P Q a v = r) :
    ∀ v w : σ → ℕ, expSum P Q a v = expSum P Q a w := by
  -- constancy along each coordinate line
  have hline : ∀ (u : σ → ℕ) (i : σ) (t : ℕ),
      expSum P Q a (Function.update u i t) = expSum P Q a u := by
    intro u i t
    have hq : ∀ k (s : ℕ), 0 ≤ (lineZ (Q k) u i).eval (s : ℤ) := fun k s => by
      rw [lineZ_eval]; exact hQ k _
    have hp : ∀ s : ℕ, ∃ r : ℕ, r.Prime ∧
        expSum1 (fun k => lineZ (P k) u i) (fun k => lineZ (Q k) u i) a s = r := fun s => by
      rw [← expSum_line]; exact hprime _
    have h1 := line_constant _ _ a ha hq hp t
    have h2 := line_constant _ _ a ha hq hp (u i)
    rw [← expSum_line] at h1 h2
    rw [h1, ← h2, Function.update_eq_self]
  -- change the coordinates one at a time
  intro v w
  classical
  have key : ∀ s : Finset σ, expSum P Q a (fun j => if j ∈ s then w j else v j) = expSum P Q a v := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      have e : (fun j => if j ∈ insert i s then w j else v j) =
          Function.update (fun j => if j ∈ s then w j else v j) i (w i) := by
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj]
      rw [e, hline, ih]
  have := key Finset.univ
  simp only [Finset.mem_univ, if_true] at this
  exact this.symm

/-- **Theorem 4.4**, the real extension: the exponential polynomial is constant on `ℝⁿ`. -/
theorem theorem_4_4_real (P Q : Fin m → MvPolynomial σ ℤ) (a : Fin m → ℕ) (ha : ∀ i, 0 < a i)
    (hQ : ∀ i (v : σ → ℕ), 0 ≤ MvPolynomial.eval (fun j => (v j : ℤ)) (Q i))
    (hprime : ∀ v : σ → ℕ, ∃ r : ℕ, r.Prime ∧ expSum P Q a v = r) :
    ∀ x : σ → ℝ, expSumR P Q a x = (expSum P Q a 0 : ℝ) := by
  classical
  have hgrid := theorem_4_4 P Q a ha hQ hprime
  have key : ∀ s : Finset σ, ∀ x : σ → ℝ, (∀ j ∉ s, ∃ n : ℕ, x j = n) →
      expSumR P Q a x = (expSum P Q a 0 : ℝ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro x hx
      choose v hv using fun j => hx j (Finset.notMem_empty j)
      have : x = fun j => (v j : ℝ) := funext hv
      rw [this, expSumR_natCast P Q a hQ, hgrid v 0]
    | insert i s hi ih =>
      intro x hx
      have hnat : ∀ n : ℕ, expSumR1 (fun k => lineR (P k) x i) (fun k => lineR (Q k) x i) a n =
          (expSum P Q a 0 : ℝ) := by
        intro n
        rw [← expSumR_line]
        refine ih _ fun j hj => ?_
        by_cases hji : j = i
        · subst hji; exact ⟨n, by simp⟩
        · rw [Function.update_of_ne hji]
          exact hx j (by simp [hji, hj])
      have hall := expSumR1_const _ _ a ha _ (fun N =>
        ⟨(⌈N⌉₊ : ℝ), Nat.le_ceil N, hnat _⟩)
      have := hall (x i)
      rwa [← expSumR_line, Function.update_eq_self] at this
  exact fun x => key Finset.univ x (fun j hj => absurd (Finset.mem_univ j) hj)

end Several

end

end JSWW1976
