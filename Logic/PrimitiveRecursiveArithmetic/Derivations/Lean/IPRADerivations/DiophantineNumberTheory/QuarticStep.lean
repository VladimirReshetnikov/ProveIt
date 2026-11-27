import IPRADerivations.DiophantineNumberTheory.Pythagoras

/-!
# The descent step for `x⁴ + y⁴ = z²`

Packet: `diophantine-number-theory/flt_ipra`, the step in the proof of Theorem `thm:four`.

A primitive solution `x, y ≥ 1`, `x⁴ + y⁴ = z²` with `x` odd and `y = 2y'` even yields a
solution with a smaller last coordinate (`primitive_step`). The Pythagorean parametrization
of `(x², y², z)` gives `x² + N² = M²`, `2y'² = M N`, `z = M² + N²`. Then `N = 2N'` is even
(else `x² + N²` would be an odd square plus an odd square, which is `2 mod 4`), `M = u²` and
`N' = v²`. The parametrization of `(x, 2v², u²)` gives `v² = R S`, `u² = R² + S²`, hence
`R = α²`, `S = β²` and `α⁴ + β⁴ = u²`, where `u ≤ M < z`.

The step is stated in continuation form (`Cont`): the case analysis hands explicit witnesses
to the continuation under the hypotheses of its case.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.Pythagoras

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `t⁴`. -/
abbrev q4 (t : PTm n) : PTm n := (t * t) * (t * t)

/-- A solution of `x⁴ + y⁴ = z²` with `x, y ≥ 1`. -/
abbrev sol (x y z : PTm n) : Fm PTm n :=
  (x ≐ succ (pred x)) ⋏ (y ≐ succ (pred y)) ⋏ (q4 x + q4 y ≐ z * z)

/-- A continuation: from a solution with last coordinate below `z`, under any extension `Δ`
of `Γ`, derive `φ`. -/
def Cont (Γ : List (Fm PTm n)) (z : PTm n) (φ : Fm PTm n) : Prop :=
  ∀ (Δ : List (Fm PTm n)), (∀ (ψ : Fm PTm n), Prf PRAAx Γ ψ → Prf PRAAx Δ ψ) →
    ∀ (a b c : PTm n), Prf PRAAx Δ (sol a b c) → Prf PRAAx Δ (lt c z) → Prf PRAAx Δ φ

theorem Cont.wk {z : PTm n} {φ : Fm PTm n} (k : Cont Γ z φ) (χ : Fm PTm n) : Cont (χ :: Γ) z φ :=
  fun Δ l => k Δ (fun ψ h => l ψ h.wk)

theorem Cont.apply {z x' y' z' : PTm n} {φ : Fm PTm n} (k : Cont Γ z φ) (hs : Γ ⊢[PRAAx] sol x' y' z')
    (hlt : Γ ⊢[PRAAx] lt z' z) : Γ ⊢[PRAAx] φ := k Γ (fun _ h => h) x' y' z' hs hlt

/-! ## Small facts -/

theorem congrGcd {a a' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] gcd a b ≐ gcd a' b' := by
  have h := Prf.eqCongr (Γ := Γ) (gcd (var 0) (var 1) : PTm 2) (σ := ![a, b]) (σ' := ![a', b'])
    (fun j => by fin_cases j <;> assumption)
  simp only [subst_ex2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, ConciseIPRA.PTm.subst_succ] at h
  exact h

theorem coprime_sq {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (h : Γ ⊢[PRAAx] gcd a b ≐ one) : Γ ⊢[PRAAx] gcd (a * a) (b * b) ≐ one := by
  have hbb := pos_mul hb hb
  have c₁ := gcd_comm_one hbb (coprime_mul ha h h)
  exact gcd_comm_one (pos_mul ha ha) (coprime_mul hbb c₁ c₁)

theorem le_sq {x : PTm n} (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) : Γ ⊢[PRAAx] le x (x * x) := by
  refine le_of_eq_add (d := x * pred x) ?_
  ipra_lc Groth.ι (IPRA.Q.mk Γ x) * natEq hx

theorem odd_sq {x a : PTm n} (h : Γ ⊢[PRAAx] x ≐ two * a + one) :
    Γ ⊢[PRAAx] x * x ≐ two * (two * (a * a) + two * a) + one := by
  refine withEq h fun e => ?_
  apply deriveNat; ipra_simps; rw [e]; ring

theorem odd_sum_alg {p q c a b : PTm n} (hp : Γ ⊢[PRAAx] p ≐ two * a + one) (hq : Γ ⊢[PRAAx] q ≐ two * b + one)
    (h : Γ ⊢[PRAAx] p * p + q * q ≐ c * c) :
    Γ ⊢[PRAAx] c * c ≐ two * (two * (a * a + a + b * b + b) + one) := by
  ipra_lc -natEq h + (Groth.ι (IPRA.Q.mk Γ p) + 2 * Groth.ι (IPRA.Q.mk Γ a) + 1) * natEq hp +
    (Groth.ι (IPRA.Q.mk Γ q) + 2 * Groth.ι (IPRA.Q.mk Γ b) + 1) * natEq hq

/-- An odd square plus an odd square is not a square. -/
theorem odd_sq_sum {p q c a b : PTm n} (φ : Fm PTm n) (hp : Γ ⊢[PRAAx] p ≐ two * a + one)
    (hq : Γ ⊢[PRAAx] q ≐ two * b + one) (h : Γ ⊢[PRAAx] p * p + q * q ≐ c * c) : Γ ⊢[PRAAx] φ := by
  have e := odd_sum_alg hp hq h
  refine .orE (even_or_odd c) ?_ ?_
  · -- `4c'² = 2(2K + 1)`, so `2c'² = 2K + 1`.
    refine even_ne_odd _ (k := half c * half c) (m := a * a + a + b * b + b) ?_
    refine mul_cancel two_pos.wk ?_
    refine withEq e.wk fun h₁ => withEq Prf.hyp0 fun h₂ => ?_
    apply deriveNat; ipra_simps; rw [h₂] at h₁; linear_combination h₁
  · refine even_ne_odd _ (k := two * (a * a + a + b * b + b) + one)
      (m := two * (half c * half c + half c)) ?_
    refine withEq e.wk fun h₁ => withEq Prf.hyp0 fun h₂ => ?_
    apply deriveNat; ipra_simps; rw [h₂] at h₁; linear_combination -h₁

/-- Two even numbers are not coprime. -/
theorem not_both_even {x y x' y' : PTm n} (φ : Fm PTm n) (hg : Γ ⊢[PRAAx] gcd x y ≐ one)
    (hx : Γ ⊢[PRAAx] x ≐ two * x') (hy : Γ ⊢[PRAAx] y ≐ two * y') : Γ ⊢[PRAAx] φ := by
  have d := gcd_greatest' two_pos (dvd_of_eq' two_pos hx) (dvd_of_eq' two_pos hy)
  exact succ_ne_zero' _ (succ_inj (eq_one_of_dvd_one two_pos (dvd_congr hg d)))

/-! ## The primitive step, in stages -/

theorem alg_final {u R S α β : PTm n} (f₃ : Γ ⊢[PRAAx] u * u ≐ R * R + S * S) (eR : Γ ⊢[PRAAx] R ≐ α * α)
    (eS : Γ ⊢[PRAAx] S ≐ β * β) : Γ ⊢[PRAAx] q4 α + q4 β ≐ u * u := by
  ipra_lc -natEq f₃ - (Groth.ι (IPRA.Q.mk Γ R) + Groth.ι (IPRA.Q.mk Γ α) * Groth.ι (IPRA.Q.mk Γ α)) * natEq eR -
    (Groth.ι (IPRA.Q.mk Γ S) + Groth.ι (IPRA.Q.mk Γ β) * Groth.ι (IPRA.Q.mk Γ β)) * natEq eS

/-- The new solution `(α, β, u)` with `u ≤ M < z`. -/
theorem step_D {z M N' u v R S : PTm n} {φ : Fm PTm n} (k : Cont Γ z φ)
    (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hN' : Γ ⊢[PRAAx] N' ≐ succ (pred N'))
    (hu : Γ ⊢[PRAAx] u ≐ succ (pred u)) (eM : Γ ⊢[PRAAx] M ≐ u * u)
    (e₃ : Γ ⊢[PRAAx] z ≐ M * M + (two * N') * (two * N')) (hvv : Γ ⊢[PRAAx] v * v ≐ succ (pred (v * v)))
    (f₂ : Γ ⊢[PRAAx] v * v ≐ R * S) (f₃ : Γ ⊢[PRAAx] u * u ≐ R * R + S * S)
    (f₄ : Γ ⊢[PRAAx] gcd R S ≐ one) (hS : Γ ⊢[PRAAx] S ≐ succ (pred S)) : Γ ⊢[PRAAx] φ := by
  have hR := pos_of_eq_mul hvv (f₂.eqTrans (mul_comm _ _))
  have eR := square_of_coprime hR f₄ f₂.eqSymm
  have eS := square_of_coprime hS (gcd_comm_one hS f₄) ((mul_comm _ _).eqTrans f₂.eqSymm)
  refine k.apply (x' := gcd R v) (y' := gcd S v) (z' := u)
    (.andI (gcd_pos hR) (.andI (gcd_pos hS) (alg_final f₃ eR eS))) ?_
  have l₁ := le_trans (le_sq hu) (le_congr eM (.eqRefl _) (le_refl _))
  have hNN := pos_mul (pos_mul two_pos hN') (pos_mul two_pos hN')
  have l₃ : Γ ⊢[PRAAx] lt (M * M) z := by
    refine le_of_eq_add (d := pred ((two * N') * (two * N'))) (e₃.eqTrans ?_)
    refine withEq hNN fun e => ?_
    apply deriveNat; ipra_simps; rw [e]; ring
  exact lt_of_le_of_lt (le_trans l₁ (le_sq hM)) l₃

theorem alg_C2 {x M N' u v : PTm n} (e₁ : Γ ⊢[PRAAx] x * x + (two * N') * (two * N') ≐ M * M)
    (eM : Γ ⊢[PRAAx] M ≐ u * u) (eN' : Γ ⊢[PRAAx] N' ≐ v * v) :
    Γ ⊢[PRAAx] x * x + (two * (v * v)) * (two * (v * v)) ≐ (u * u) * (u * u) := by
  refine withEq e₁ fun h₁ => withEq eM fun h₂ => withEq eN' fun h₃ => ?_
  apply deriveNat; ipra_simps; rw [h₃] at h₁; rw [h₂] at h₁; linear_combination h₁

/-- The second parametrization, of `(x, 2v², u²)`. -/
theorem step_C2 {x z M N' u v : PTm n} {φ : Fm PTm n} (k : Cont Γ z φ)
    (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hN' : Γ ⊢[PRAAx] N' ≐ succ (pred N')) (hu : Γ ⊢[PRAAx] u ≐ succ (pred u))
    (hv : Γ ⊢[PRAAx] v ≐ succ (pred v)) (eM : Γ ⊢[PRAAx] M ≐ u * u) (eN' : Γ ⊢[PRAAx] N' ≐ v * v)
    (e₁ : Γ ⊢[PRAAx] x * x + (two * N') * (two * N') ≐ M * M)
    (e₃ : Γ ⊢[PRAAx] z ≐ M * M + (two * N') * (two * N')) (e₄ : Γ ⊢[PRAAx] gcd M (two * N') ≐ one) :
    Γ ⊢[PRAAx] φ := by
  have h2N := pos_mul two_pos hN'
  -- `gcd(x, 2N') = 1`: a common divisor divides `M²` and `(2N')²`.
  have hxN : Γ ⊢[PRAAx] gcd x (two * N') ≐ one := by
    have hd := gcd_pos (B := two * N') hx
    have hdd := gcd_dvd' (b := two * N') hx
    have dNN := dvd_mul' hd (two * N') (Prf.andE₂ hdd)
    have dMM := dvd_congr e₁ (dvd_add' hd (dvd_mul' hd x (Prf.andE₁ hdd)) dNN)
    exact eq_one_of_dvd_one hd (dvd_congr (coprime_sq hM h2N e₄) (gcd_greatest' hd dMM dNN))
  have hxv := (congrGcd (.eqRefl _) (congrMul (.eqRefl _) eN')).eqSymm.eqTrans hxN
  have hvv := pos_mul hv hv
  have P := pyth_at hx hvv (alg_C2 e₁ eM eN') hxv
  exact step_D k hM hN' hu eM e₃ hvv (Prf.andE₁ (Prf.andE₂ P)) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ P)))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ P)))) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ P))))

/-- `M = u²` and `N' = v²`, from `M N' = y'²`. -/
theorem step_C {x z M N' y' : PTm n} {φ : Fm PTm n} (k : Cont Γ z φ)
    (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hN' : Γ ⊢[PRAAx] N' ≐ succ (pred N'))
    (e₁ : Γ ⊢[PRAAx] x * x + (two * N') * (two * N') ≐ M * M) (eY : Γ ⊢[PRAAx] M * N' ≐ y' * y')
    (e₃ : Γ ⊢[PRAAx] z ≐ M * M + (two * N') * (two * N')) (e₄ : Γ ⊢[PRAAx] gcd M (two * N') ≐ one) :
    Γ ⊢[PRAAx] φ := by
  have h2N := pos_mul two_pos hN'
  have hMN' := gcd_comm_one hM (coprime_dvd_left hN' (dvd_of_eq' hN' (w := two) (mul_comm _ _))
    (gcd_comm_one h2N e₄))
  have eM := square_of_coprime hM hMN' eY
  have eN' := square_of_coprime hN' (gcd_comm_one hN' hMN') ((mul_comm _ _).eqTrans eY)
  exact step_C2 k hx hM hN' (gcd_pos hM) (gcd_pos hN') eM eN' e₁ e₃ e₄

/-- `N` is even. -/
theorem step_B {x z M N y' : PTm n} {φ : Fm PTm n} (k : Cont Γ z φ)
    (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) (hxo : Γ ⊢[PRAAx] x ≐ two * half x + one)
    (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (e₁ : Γ ⊢[PRAAx] x * x + N * N ≐ M * M) (e₂ : Γ ⊢[PRAAx] two * (y' * y') ≐ M * N)
    (e₃ : Γ ⊢[PRAAx] z ≐ M * M + N * N) (e₄ : Γ ⊢[PRAAx] gcd M N ≐ one) : Γ ⊢[PRAAx] φ := by
  refine .orE (even_or_odd N) ?_ (odd_sq_sum _ hxo.wk Prf.hyp0 e₁.wk)
  have hNe : ((N ≐ two * half N) :: Γ) ⊢[PRAAx] N ≐ two * half N := Prf.hyp0
  have hN' := pos_of_eq_mul hN.wk hNe
  have sq : ((N ≐ two * half N) :: Γ) ⊢[PRAAx] N * N ≐ (two * half N) * (two * half N) := congrMul hNe hNe
  have eY : ((N ≐ two * half N) :: Γ) ⊢[PRAAx] M * half N ≐ y' * y' := by
    refine mul_cancel two_pos.wk ?_
    ipra_lc -natEq (e₂.wk (ψ := N ≐ two * half N)) - Groth.ι (IPRA.Q.mk _ M) * natEq hNe
  exact step_C (k.wk _) hx.wk hM.wk hN' ((congrAdd (.eqRefl _) sq).eqSymm.eqTrans e₁.wk) eY
    (e₃.wk.eqTrans (congrAdd (.eqRefl _) sq)) ((congrGcd (.eqRefl _) hNe).eqSymm.eqTrans e₄.wk)

theorem alg_P1 {x y y' z : PTm n} (hE : Γ ⊢[PRAAx] q4 x + q4 y ≐ z * z) (hy : Γ ⊢[PRAAx] y ≐ two * y') :
    Γ ⊢[PRAAx] (x * x) * (x * x) + (two * (two * (y' * y'))) * (two * (two * (y' * y'))) ≐ z * z := by
  refine withEq hE fun e₁ => withEq hy fun e₂ => ?_
  apply deriveNat; ipra_simps; rw [← e₁, e₂]; ring

/-- The step for a primitive solution with `x` odd and `y` even. -/
theorem primitive_step {x y z : PTm n} {φ : Fm PTm n} (k : Cont Γ z φ)
    (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) (hy : Γ ⊢[PRAAx] y ≐ succ (pred y))
    (hxo : Γ ⊢[PRAAx] x ≐ two * half x + one) (hye : Γ ⊢[PRAAx] y ≐ two * half y)
    (hg : Γ ⊢[PRAAx] gcd x y ≐ one) (hE : Γ ⊢[PRAAx] q4 x + q4 y ≐ z * z) : Γ ⊢[PRAAx] φ := by
  have hxx := pos_mul hx hx
  have hy' := pos_of_eq_mul hy hye
  have hH := pos_mul two_pos (pos_mul hy' hy')
  have eB : Γ ⊢[PRAAx] two * (two * (half y * half y)) ≐ y * y := by
    refine withEq hye fun e => ?_
    apply deriveNat; ipra_simps; rw [e]; ring
  have hg₁ := (congrGcd (.eqRefl _) eB).eqTrans (coprime_sq hx hy hg)
  have P := pyth_at hxx hH (alg_P1 hE hye) hg₁
  have e₂ := Prf.andE₁ (Prf.andE₂ P)
  have hM := pos_of_eq_mul hH (e₂.eqTrans (mul_comm _ _))
  exact step_B k hx hxo hM (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ P)))) (Prf.andE₁ P) e₂
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ P))) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ P))))

end LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep
