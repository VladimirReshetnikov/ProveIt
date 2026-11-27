import IPRADerivations.Combinatorics.BinomialTheorem
import IPRADerivations.Combinatorics.Fibonacci
import IPRADerivations.Probability.Independence

/-!
# The binomial transform and the Fibonacci convolution

Packet: `combinatorics/fibonacci_lucas_ipra` (theorem "Binomial convolution", (14)).

For a body `g(k, x)` put `B_m[g] = ∑_{k ≤ m} C(m, k) g(k, x)`; the summand reads `m` and `x` from
the pair `y = ⟨m, x⟩`.

* `pascal_sum`: `B_{m+1}[g] = B_m[g] + B_m[g(· + 1)]`, the finite binomial theorem's Pascal step
  for an arbitrary body: shift the index, apply Pascal's rule below the top term, split the sum;
* `fib_convolution`: `∑_{k ≤ m} C(m, k) F_{k+1} = F_{2m+1}` and `∑_{k ≤ m} C(m, k) F_k = F_{2m}`
  for every `m`, by a simultaneous quantifier-free induction: writing `A_m`, `B_m` for the two
  sums, the Pascal step gives `A_{m+1} = 2 A_m + B_m` and `B_{m+1} = A_m + B_m`.

* `luc_convolution` (15): `∑_{k ≤ m} C(m, k) L_k = L_{2m}`, from the two Fibonacci convolutions and
  `L_k + F_k = 2 F_{k+1}`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BinomialTransform

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_zero')
open LeanProofs.IPRA.Combinatorics.Fibonacci
open LeanProofs.IPRA.Probability.Independence (sum_scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The Pascal step -/

/-- `C(fst y, k) · g(k, snd y)`. -/
abbrev bgB (g : PTm 2) : PTm 2 :=
  binom (fstT (var 1)) (var 0) * Syn.subst ![var 0, sndT (var 1)] g

theorem inst2_bg (g : PTm 2) (k y : PTm n) :
    inst2 (bgB g) k y = binom (fstT y) k * inst2 g k (sndT y) :=
  BinomialTheorem.inst2_weighted g k y

theorem inst2_sbg (g : PTm 2) (k y : PTm n) :
    inst2 (shiftBody (bgB g)) k y = binom (fstT y) (succ k) * inst2 g (succ k) (sndT y) := by
  rw [inst2_shiftBody, inst2_bg]

theorem inst2_bgs (g : PTm 2) (k y : PTm n) :
    inst2 (bgB (shiftBody g)) k y = binom (fstT y) k * inst2 g (succ k) (sndT y) := by
  rw [inst2_bg, inst2_shiftBody]

theorem pas_pt (g : PTm 2) {k m x : PTm n} (h : Γ ⊢[PRAAx] lt k m) :
    Γ ⊢[PRAAx] inst2 (shiftBody (bgB g)) k (pairT (succ m) x) ≐
      inst2 (addBody (shiftBody (bgB g)) (bgB (shiftBody g))) k (pairT m x) :=
  BinomialTheorem.weighted_pascal_at g h

/-- `B_{m+1}[g] = B_m[g] + B_m[g(· + 1)]`. -/
theorem pascal_sum (g : PTm 2) (m x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (bgB g)) (succ (succ m)) (pairT (succ m) x) ≐
      ap2 (sumF (bgB g)) (succ m) (pairT m x) + ap2 (sumF (bgB (shiftBody g))) (succ m) (pairT m x) :=
  BinomialTheorem.weighted_pascal_sum g m x

/-! ## The Fibonacci convolution -/

/-- `F_{k+1}` and `F_k` as bodies. -/
abbrev fsB : PTm 2 := fibS (var 0)
abbrev fbB : PTm 2 := fib (var 0)

theorem inst2_fs (k x : PTm n) : inst2 fsB k x = fibS k := by simp [inst2]
theorem inst2_fb (k x : PTm n) : inst2 fbB k x = fib k := by simp [inst2]

/-- `A_m = ∑_{k ≤ m} C(m, k) F_{k+1}`. -/
abbrev Am (m : PTm n) : PTm n := ap2 (sumF (bgB fsB)) (succ m) (pairT m zero)
/-- `B_m = ∑_{k ≤ m} C(m, k) F_k`. -/
abbrev Bm (m : PTm n) : PTm n := ap2 (sumF (bgB fbB)) (succ m) (pairT m zero)

/-- `∑ C(m, k) F_{k+1}`, with `F_{k+1}` written through the shifted body of `F_k`. -/
theorem shift_fb (m : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (bgB (shiftBody fbB))) (succ m) (pairT m zero) ≐ Am m := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_bgs, inst2_bg, inst2_fb, inst2_fs]
  exact congrMul (.eqRefl _) (fib_succ _)

/-- `∑ C(m, k) F_{k+2} = A_m + B_m`. -/
theorem shift_fs (m : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (bgB (shiftBody fsB))) (succ m) (pairT m zero) ≐ Am m + Bm m := by
  have c : Γ ⊢[PRAAx] ap2 (sumF (bgB (shiftBody fsB))) (succ m) (pairT m zero) ≐
      ap2 (sumF (addBody (bgB fsB) (bgB fbB))) (succ m) (pairT m zero) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_bgs, inst2_addBody, inst2_bg, inst2_bg, inst2_fs, inst2_fs, inst2_fb]
    refine (congrMul (.eqRefl _) (fibS_succ _)).eqTrans ?_
    ipra_ring
  exact c.eqTrans (sum_add (bgB fsB) (bgB fbB) (succ m) (pairT m zero))

theorem conv_base : Γ ⊢[PRAAx] (Am (zero : PTm n) ≐ fibS (two * zero)) ⋏ (Bm (zero : PTm n) ≐ fib (two * zero)) := by
  have z : Γ ⊢[PRAAx] (two * zero : PTm n) ≐ zero := mul_zero _
  have b₀ : Γ ⊢[PRAAx] binom (fstT (pairT (zero : PTm n) zero)) zero ≐ one := binom_zero' _
  refine .andI ?_ ?_
  · have e := sum_succ' (Γ := Γ) (bgB fsB) zero (pairT (zero : PTm n) zero)
    rw [inst2_bg, inst2_fs] at e
    have a₁ := natEq e; have a₂ := natEq (sum_zero (Γ := Γ) (bgB fsB) (pairT (zero : PTm n) zero))
    have a₃ := natEq b₀; have a₄ := natEq ((congrFibS z).eqTrans (fibS_zero (Γ := Γ) (n := n)))
    have a₅ := natEq (fibS_zero (Γ := Γ) (n := n))
    apply deriveNat; ipra_simps
    linear_combination a₁ + a₂ + 𝔞(fibS (zero : PTm n)) * a₃ + a₅ - a₄
  · have e := sum_succ' (Γ := Γ) (bgB fbB) zero (pairT (zero : PTm n) zero)
    rw [inst2_bg, inst2_fb] at e
    have a₁ := natEq e; have a₂ := natEq (sum_zero (Γ := Γ) (bgB fbB) (pairT (zero : PTm n) zero))
    have a₄ := natEq ((congrFib z).eqTrans (fib_zero (Γ := Γ) (n := n)))
    have a₅ := natEq (fib_zero (Γ := Γ) (n := n))
    apply deriveNat; ipra_simps
    linear_combination a₁ + a₂ + 𝔞(binom (fstT (pairT (zero : PTm n) zero)) zero) * a₅ - a₄

theorem conv_step {m : PTm n}
    (ih : Γ ⊢[PRAAx] (Am m ≐ fibS (two * m)) ⋏ (Bm m ≐ fib (two * m))) :
    Γ ⊢[PRAAx] (Am (succ m) ≐ fibS (two * succ m)) ⋏ (Bm (succ m) ≐ fib (two * succ m)) := by
  have iA := natEq (Prf.andE₁ ih); have iB := natEq (Prf.andE₂ ih)
  have pA := natEq (pascal_sum (Γ := Γ) fsB m zero); have pB := natEq (pascal_sum (Γ := Γ) fbB m zero)
  have sA := natEq (shift_fs (Γ := Γ) m); have sB := natEq (shift_fb (Γ := Γ) m)
  have dS := natEq (fibS_two_succ (Γ := Γ) m); have dF := natEq (fib_two_succ (Γ := Γ) m)
  refine .andI ?_ ?_
  · ipra_lc pA + sA + 2 * iA + iB - dS
  · ipra_lc pB + sB + iA + iB - dF

/-- Variable: `0 = m`. -/
private abbrev convF : Fm PTm 1 :=
  (Am (var 0) ≐ fibS (two * var 0)) ⋏ (Bm (var 0) ≐ fib (two * var 0))

private theorem conv₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] convF := by
  ipra_ind (⟨trivial, trivial⟩) [subst_ap1, subst_ap2, subst_pairT, subst_fibS, subst_fib]
  · exact conv_base
  · exact conv_step Prf.hyp0

/-- The binomial convolution: `∑_{k ≤ m} C(m, k) F_{k+1} = F_{2m+1}` and
`∑_{k ≤ m} C(m, k) F_k = F_{2m}`. -/
theorem fib_convolution (m : PTm n) :
    Γ ⊢[PRAAx] (Am m ≐ fibS (two * m)) ⋏ (Bm m ≐ fib (two * m)) := by
  have h := inst (Γ := Γ) conv₀ (![m] : Fin 1 → PTm n)
  simpa using h

/-! ## The Lucas convolution -/

/-- `L_k` as a body. -/
abbrev lB : PTm 2 := luc (var 0)

theorem inst2_l (k x : PTm n) : inst2 lB k x = luc k := by simp [inst2]

/-- `∑_{k ≤ m} C(m, k) L_k`. -/
abbrev Lm (m : PTm n) : PTm n := ap2 (sumF (bgB lB)) (succ m) (pairT m zero)

theorem luc_pt (k y : PTm n) :
    Γ ⊢[PRAAx] inst2 (addBody (bgB lB) (bgB fbB)) k y ≐ two * inst2 (bgB fsB) k y := by
  rw [inst2_addBody, inst2_bg, inst2_bg, inst2_bg, inst2_l, inst2_fb, inst2_fs]
  ipra_lc 𝔞(binom (fstT y) k) * natEq (luc_eq (Γ := Γ) k)

/-- The Lucas convolution (15): `∑_{k ≤ m} C(m, k) L_k = L_{2m}`. -/
theorem luc_convolution (m : PTm n) : Γ ⊢[PRAAx] Lm m ≐ luc (two * m) := by
  have two_shift : Syn.shift (two : PTm n) = two := by simp [Syn.shift]
  have s₂' : Γ ⊢[PRAAx] ap2 (sumF (addBody (bgB lB) (bgB fbB))) (succ m) (pairT m zero) ≐ two * Am m := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [two_shift]
    exact luc_pt _ _
  have c := fib_convolution (Γ := Γ) m
  ipra_lc -natEq (sum_add (Γ := Γ) (bgB lB) (bgB fbB) (succ m) (pairT m zero)) + natEq s₂' + 2 * natEq (Prf.andE₁ c) -
    natEq (Prf.andE₂ c) - natEq (luc_eq (Γ := Γ) (two * m))

end LeanProofs.IPRA.Combinatorics.BinomialTransform
