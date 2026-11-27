import IPRADerivations.Combinatorics.BinomialIdentities

/-!
# The binomial theorem

`∑_{k ≤ m} C(m, k) aᵏ = (a + 1)ᵐ`.

Bounded sums take one parameter, so the body reads `m` and `a` from the pair
`x = ⟨m, a⟩`: the summand is `C(fst x, k) · (snd x)ᵏ`. The weighted Pascal
sum splits each successor row. For the power weight, shifting the index
multiplies the sum by `a`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BinomialTheorem

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_zero' binom_self' pascal_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem congrBinom {a a' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] binom a b ≐ binom a' b' := by
  have h := Prf.eqCongr (Γ := Γ) (binom (var 0) (var 1) : PTm 2) (σ := ![a, b]) (σ' := ![a', b'])
    (fun j => by fin_cases j <;> assumption)
  simpa using h

theorem congrPw {a a' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] pw a b ≐ pw a' b' := congrAp2 powF h₂ h₁

/-! ## Pascal's rule for weighted sums -/

/-- The binomial weight at index `k`, with the upper index and the weight's
parameter stored as a pair. -/
abbrev weightedBody (g : PTm 2) : PTm 2 :=
  binom (fstT (var 1)) (var 0) * Syn.subst ![var 0, sndT (var 1)] g

theorem inst2_weighted (g : PTm 2) (k y : PTm n) :
    inst2 (weightedBody g) k y = binom (fstT y) k * inst2 g k (sndT y) := by
  have h : Syn.subst ![k, y] (Syn.subst ![var 0, sndT (var 1)] g) = inst2 g k (sndT y) := by
    simp only [inst2, Syn.subst_subst]
    congr 1
    funext j
    fin_cases j <;> simp
  simp only [weightedBody, inst2, PTm.subst_mul, h]
  simp [inst2]

theorem weighted_at (g : PTm 2) (k m x : PTm n) :
    Γ ⊢[PRAAx] inst2 (weightedBody g) k (pairT m x) ≐ binom m k * inst2 g k x := by
  rw [inst2_weighted]
  exact congrMul (congrBinom (fst_pair _ _) (.eqRefl _)) (congrInst2 g (.eqRefl _) (snd_pair _ _))

theorem weighted_pascal_at (g : PTm 2) {k m x : PTm n} (h : Γ ⊢[PRAAx] lt k m) :
    Γ ⊢[PRAAx] inst2 (shiftBody (weightedBody g)) k (pairT (succ m) x) ≐
      inst2 (addBody (shiftBody (weightedBody g)) (weightedBody (shiftBody g))) k (pairT m x) := by
  rw [inst2_addBody, inst2_shiftBody, inst2_shiftBody]
  have right := weighted_at (Γ := Γ) (shiftBody g) k m x
  rw [inst2_shiftBody] at right
  refine (weighted_at g (succ k) (succ m) x).eqTrans
    (.eqTrans ?_ (congrAdd (weighted_at g (succ k) m x) right).eqSymm)
  ipra_lc Groth.ι (IPRA.Q.mk Γ (inst2 g (succ k) x)) * natEq (pascal_at h)

/-- The binomial transform at `m+1` splits into the transforms at `m` of
the weight and its successor shift. -/
theorem weighted_pascal_sum (g : PTm 2) (m x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (weightedBody g)) (succ (succ m)) (pairT (succ m) x) ≐
      ap2 (sumF (weightedBody g)) (succ m) (pairT m x) +
        ap2 (sumF (weightedBody (shiftBody g))) (succ m) (pairT m x) := by
  have interior : Γ ⊢[PRAAx] ap2 (sumF (shiftBody (weightedBody g))) m (pairT (succ m) x) ≐
      ap2 (sumF (addBody (shiftBody (weightedBody g)) (weightedBody (shiftBody g)))) m (pairT m x) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [Syn.shift, subst_pairT, ConciseIPRA.PTm.subst_succ]
    exact weighted_pascal_at g Prf.hyp0
  have bottom : Γ ⊢[PRAAx] inst2 (weightedBody g) zero (pairT (succ m) x) ≐
      inst2 (weightedBody g) zero (pairT m x) :=
    (weighted_at g zero (succ m) x).eqTrans
      ((congrMul ((binom_zero' _).eqTrans (binom_zero' _).eqSymm) (.eqRefl _)).eqTrans
        (weighted_at g zero m x).eqSymm)
  have top : Γ ⊢[PRAAx] inst2 (shiftBody (weightedBody g)) m (pairT (succ m) x) ≐
      inst2 (weightedBody (shiftBody g)) m (pairT m x) := by
    rw [inst2_shiftBody]
    have right := weighted_at (Γ := Γ) (shiftBody g) m m x
    rw [inst2_shiftBody] at right
    exact (weighted_at g (succ m) (succ m) x).eqTrans
      ((congrMul ((binom_self' _).eqTrans (binom_self' _).eqSymm) (.eqRefl _)).eqTrans right.eqSymm)
  ipra_lc natEq (sum_shift (Γ := Γ) (weightedBody g) (succ m) (pairT (succ m) x)) +
    natEq (sum_succ' (Γ := Γ) (shiftBody (weightedBody g)) m (pairT (succ m) x)) + natEq interior +
    natEq (sum_add (Γ := Γ) (shiftBody (weightedBody g)) (weightedBody (shiftBody g)) m (pairT m x)) -
    natEq (sum_shift (Γ := Γ) (weightedBody g) m (pairT m x)) -
    natEq (sum_succ' (Γ := Γ) (weightedBody (shiftBody g)) m (pairT m x)) + natEq bottom + natEq top

/-! ## Bodies; variables `0 = k`, `1 = x` -/

/-- `C(fst x, k) (snd x)ᵏ`. -/
abbrev tBody : PTm 2 := binom (fstT (var 1)) (var 0) * pw (sndT (var 1)) (var 0)
/-- `snd x · C(fst x, k) (snd x)ᵏ`. -/
abbrev aBody : PTm 2 := sndT (var 1) * tBody
abbrev hBody : PTm 2 := addBody aBody (shiftBody tBody)

theorem inst2_t (k x : PTm n) : inst2 tBody k x = binom (fstT x) k * pw (sndT x) k := by
  simp [inst2]
theorem inst2_a (k x : PTm n) : inst2 aBody k x = sndT x * (binom (fstT x) k * pw (sndT x) k) := by
  simp [inst2]
theorem inst2_s (k x : PTm n) :
    inst2 (shiftBody tBody) k x = binom (fstT x) (succ k) * pw (sndT x) (succ k) := by
  rw [inst2_shiftBody, inst2_t]
theorem inst2_h (k x : PTm n) : inst2 hBody k x =
    sndT x * (binom (fstT x) k * pw (sndT x) k) + binom (fstT x) (succ k) * pw (sndT x) (succ k) := by
  rw [inst2_addBody, inst2_a, inst2_s]

/-! ## Pulling out the factor `snd x` -/

/-- Variables: `0 = N`, `1 = x`. -/
private abbrev mulF (f : PTm 2) : Fm PTm 2 :=
  ap2 (sumF (sndT (var 1) * f)) (var 0) (var 1) ≐ sndT (var 1) * ap2 (sumF f) (var 0) (var 1)

private theorem sum_mul_snd₀ (f : PTm 2) : ([] : List (Fm PTm 2)) ⊢[PRAAx] mulF f := by
  ipra_ind [subst_ap2, subst_sndT]
  · exact (sum_zero _ _).eqTrans ((mul_zero _).eqSymm.eqTrans (congrMul (.eqRefl _) (sum_zero _ _).eqSymm))
  · have e : inst2 (sndT (var 1) * f) (var 0 : PTm 2) (var 1) = sndT (var 1) * inst2 f (var 0) (var 1) := by
      simp [inst2]
    refine (sum_succ' _ (var 0) (var 1)).eqTrans ?_
    rw [e]
    refine withEq Prf.hyp0 fun e₁ => withEq (sum_succ' f (var 0) (var 1)) fun e₂ => ?_
    apply deriveNat; ipra_simps; rw [e₁, e₂]; ring

theorem sum_mul_snd (f : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (sndT (var 1) * f)) N x ≐ sndT x * ap2 (sumF f) N x := by
  have h := inst (Γ := Γ) (sum_mul_snd₀ f) (![N, x] : Fin 2 → PTm n)
  simpa using h

private abbrev powerWeight : PTm 2 := pw (var 1) (var 0)

private theorem weighted_power_body : weightedBody powerWeight = tBody := by
  simp [weightedBody, powerWeight, tBody]

private theorem shifted_power_weight_sum (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (weightedBody (shiftBody powerWeight))) N x ≐ sndT x * ap2 (sumF tBody) N x := by
  refine (sum_congr_bounded (weightedBody (shiftBody powerWeight)) aBody x x N (.allI (.impI ?_))).eqTrans
    (sum_mul_snd tBody N x)
  rw [inst2_weighted, inst2_shiftBody, inst2_a]
  have read : inst2 powerWeight (succ (var 0)) (sndT (Syn.shift x)) =
      pw (sndT (Syn.shift x)) (succ (var 0)) := by simp [inst2]
  rw [read]
  ipra_lc Groth.ι (IPRA.Q.mk _ (binom (fstT (Syn.shift x)) (var 0))) *
    natEq (pw_succ (sndT (Syn.shift x)) (var 0))

/-! ## The theorem -/

/-- `∑_{k ≤ m} C(m, k) aᵏ = (a + 1)ᵐ`, with the summand reading `m, a` from `⟨m, a⟩`;
variables `0 = m`, `1 = a`. -/
abbrev binomThmFormula : Fm PTm 2 :=
  ap2 (sumF tBody) (succ (var 0)) (pairT (var 0) (var 1)) ≐ pw (succ (var 1)) (var 0)

theorem binomial_open : ([] : List (Fm PTm 2)) ⊢[PRAAx] binomThmFormula := by
  ipra_ind [subst_ap2, subst_pairT]
  · refine (sum_succ' tBody zero _).eqTrans ?_
    rw [inst2_t]
    refine withEq (sum_zero (Γ := []) tBody (pairT zero (var 0))) fun e₁ =>
      withEq (binom_zero' (Γ := []) (fstT (pairT (zero : PTm 1) (var 0)))) fun e₂ =>
      withEq (pw_zero (Γ := []) (sndT (pairT (zero : PTm 1) (var 0)))) fun e₃ =>
      withEq (pw_zero (Γ := []) (succ (var 0) : PTm 1)) fun e₄ => ?_
    apply deriveNat; ipra_simps; rw [e₁, e₂, e₃, e₄]; ring
  · generalize hΓ : ([binomThmFormula] : List (Fm PTm 2)) = Γ₀
    have ih : Γ₀ ⊢[PRAAx] binomThmFormula := hΓ ▸ Prf.hyp0
    let m : PTm 2 := var 0
    let a : PTm 2 := var 1
    have step : Γ₀ ⊢[PRAAx] ap2 (sumF tBody) (succ (succ m)) (pairT (succ m) a) ≐
        ap2 (sumF tBody) (succ m) (pairT m a) +
          ap2 (sumF (weightedBody (shiftBody powerWeight))) (succ m) (pairT m a) := by
      simpa only [weighted_power_body] using weighted_pascal_sum (Γ := Γ₀) powerWeight m a
    have scale := (shifted_power_weight_sum (Γ := Γ₀) (succ m) (pairT m a)).eqTrans
      (congrMul (snd_pair m a) (.eqRefl _))
    ipra_lc natEq step + natEq scale + (1 + V Γ₀ 1) * natEq ih - natEq (pw_succ (Γ := Γ₀) (succ a) m)

theorem binomial : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 binomThmFormula := closeUniv 2 binomial_open

theorem binomial_at (m a : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF tBody) (succ m) (pairT m a) ≐ pw (succ a) m := by
  have h := inst (Γ := Γ) binomial_open (![m, a] : Fin 2 → PTm n)
  simpa using h

end LeanProofs.IPRA.Combinatorics.BinomialTheorem
