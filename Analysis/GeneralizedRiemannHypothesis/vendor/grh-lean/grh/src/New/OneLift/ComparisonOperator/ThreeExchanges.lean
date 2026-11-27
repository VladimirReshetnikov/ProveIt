import Lib.SiegelWeil.Reproduction
import New.Determinant.Exchange.ExplicitMatching
import New.OneLift.ComparisonOperator.FirstFactors

/-!
# Three exchanges: the carrier, the third exchange and its left side as a theta series

The exchange identity (`New.Rows.exists_mul_stdClassSum_eq_integral_modKernel`) is applied three
times, until only a number is left of the twist. The first two exchanges evaluate a class sum of
twisted square kernels on the space S of signature (2m, m) as a multiple of the carrier φ° =
`New.Rows.carrierForm`, the theta lift of the constant function 1 from the definite group U(0, m) to
U(S). The third exchange equates a multiple of a double class sum of kernels with 𝖥_i =
`New.Data.choiceFn j i`, the function on U(W_j) given by the integral of the carrier against a theta
kernel. The modulus of the product of the three constants is given by the product Γ_j of Hecke
values at three pairs (ν, z) of a character and an integer.

Letters: the twist is ϑ, υ = `upsilonU1` is the splitting character on U(1), and I_m = E^m is the
standard definite space of rank m.

## Main definitions and results

* `New.Data.exchangePair`: three pairs for each `1 ≤ j ≤ m`, indexed by `none` and the two signs.
* `New.Data.heckeValueProd`: the product `Γ_j` of the values `Exchange.lValueProd` at the inverses
  of the characters of these pairs, twisted by a tame character or its inverse. It is not divided by
  its value at the trivial twist.
* `New.Rows.exists_mul_stdClassSum_eq_carrierForm`, from the first two exchanges: for even `m` and a
  character c of weight 0 that is tame for (𝔪, χ), the carrier is a constant γ of known size times a
  class sum of `New.Rows.carrierCoeff` times a theta kernel twisted by χ∘det.
* `New.Rows.carrierForm_mem_rapidOfLevel_and_isAdelicHol`: for even `m`, if there is a tame
  character of weight 0, the carrier lies in `New.Rows.rapidOfLevel` for every level. So it has full
  level and is rapidly decreasing. It is also holomorphic.
* `New.Data.exists_mul_thirdExchangeLeftSide_eq_choiceFn`,
  `New.Data.thirdExchangeLeftSide_eq_kernelClassSum`: a number times a double class sum of kernels
  is 𝖥_i, and this double sum is a theta series on U(W_j).

Notions from other files:
* `New.Data.chiM`, `New.Data.chiMLocal`: a fixed character χ of U(1)(𝔸) of weight 0 and its tame
  part ω, which is trivial off the chosen places and has order greater than 8m at each of them.
* `New.Data.goodForms`: The good forms on V: the image of the idempotent e₀ of ℂ[𝖦] acting on forms
  of principal level at the chosen places above p₀ and p₁.
* `New.Data.signsW`: Signs ±1 on the indices i in `New.Data.RowIndex` for W_j: −1 when
  `New.Data.basisNumber`(i) ≥ `New.Data.posRank` j, and +1 otherwise.
* `New.Rows.IsAdelicHol`: For every adelic g, the function h ↦ F(g·(h,1)) on the archimedean group
  is holomorphic of the given weight for the given order (`New.IsHolOfWeight`).
* `New.Data.kernelWeight`: The weight `New.staircaseWeight` on W_j for the pair (W_j, V°).

## Relation to the literature

The twisted theta kernel of an indefinite and a definite unitary group of equal rank, summed against
an explicit form, is a non-zero multiple of one fixed non-zero holomorphic, rapidly decreasing form
of level one, for even m. The factor has modulus given by Hecke L-values, so the twist survives only
as a number. Non-vanishing and holomorphy of the stable-range theta lift of a character are known in
the literature. Related work: J.-S. Li, Non-vanishing theorems for the cohomology of certain
arithmetic quotients, 1992; Gan–Qiu–Takeda, The regularized Siegel–Weil formula, 2014; T. Yang,
Theta liftings and Hecke L-functions, 1997.

The theta kernel of two definite unitary groups of the same even rank 2e with determinant data,
summed over the classes of one group, is a non-zero constant whose modulus, up to a fixed factor and
conductor norms, is a product of Hecke L-values at 1,…,e. This is the first step in turning the
twist into a number. It is Rallis's formula at equal rank 2e for a character, whose central value
folds by the functional equation into Hecke L-values at 1,…,e and a conductor power, with the
ramified local data computed explicitly. Related work: Yamana, L-functions and theta correspondence
for classical groups, 2014; C. Li, Geometric and arithmetic theta correspondences (§2.4–2.5), 2024;
Yang, Theta liftings and Hecke L-functions, 1997.

See `New.OneLift.ComparisonOperator.FirstFactors` and `New.OneLift.ComparisonOperator.ProductsSpan`
for related work.
-/

noncomputable section

/-!
## Pairs (ν, z) of the three exchanges and the products Γ_j of Hecke values

A pair (`New.Data.CriticalPair`) consists of a character `ν` of `U(1)(𝔸)` of weight `-c` whose tame
part `ψ` is trivial off the chosen places, and an integer `1 ≤ z ≤ t`, with `z ≤ c v ≤ 4 b` at every
infinite place `v`.
-/

namespace New.Data

open WeilData

variable {P : Parameters} (D : Data P)

/-- The point `z_±` of the pair of sign `s`: it is `m` for `s = 1` and `m / 2` for `s = -1`. -/
def signPoint (s : ℤˣ) : ℕ := if s = 1 then D.m else D.m / 2

/-- The number `z_* = 7 (m / 2) + k / 2`, the point of the pair of the third exchange. Here
`k = r + 1 - m` is the rank of the source. -/
def mainPairPoint : ℕ := 7 * (D.m / 2) + D.k / 2

/-- The rank `k` of the source satisfies `k + 6 ≤ t`, for `t = 5 r`. -/
lemma k_add_six_le_t : D.k + 6 ≤ D.t :=
  (Nat.add_le_add_right D.k_le_r 6).trans D.r_add_six_le_t

lemma signPoint_mem_Icc (s : ℤˣ) : D.signPoint s ∈ Set.Icc 1 D.t := by
  grind [signPoint, D.ten_thousand_le_m, D.hundred_mul_m_le_k, D.k_add_six_le_t]

/-- The point `z_* = D.mainPairPoint`, the point of the pair of the third exchange, lies in the
closed interval from `1` to `t = 5 r`. -/
lemma mainPairPoint_mem_Icc : D.mainPairPoint ∈ Set.Icc 1 D.t := by
  grind [mainPairPoint, D.ten_thousand_le_m, D.hundred_mul_m_le_k, D.k_add_six_le_t]

/-- The weight `w j v = D.liftWeight j v` of the character of the `j`-th lift at an infinite
place `v` is at least `k + t + 1`, with `k` the rank of the source and `t = 5 r`. This holds for
every natural number `j`. -/
lemma k_add_t_add_one_le_liftWeight (j : ℕ) (v : D.Φ) : D.k + D.t + 1 ≤ D.liftWeight j v := by
  grind [D.liftWeight_eq, D.k_add_t_add_one_le_halfGap]

variable {D} (j : D.LiftIndex)

/-- For a lift index `j`, that is `1 ≤ j ≤ m`, the weight `D.liftWeight j v` of the character of
the `j`-th lift at an infinite place `v` is at most `4 b`, where `b = D.b` is the real number
`exp D.logB` of the data. -/
lemma liftWeight_le_four_mul_b (v : D.Φ) : D.liftWeight j v ≤ 4 * D.b := by
  have hb_pos : 0 < D.b := Real.exp_pos D.logB
  linarith [D.liftWeight_le_two_mul_b (j := j) (by grind) v]

/-- For a lift index `j`, let `n = j + (t - 11 m - 1) / 2`; this is the exponent of the splitting
character `υ` in the character `ν_j = μ_j⁰ υ ^ n` of `exchangePair`. At every infinite place `v`,
the weight `D.liftWeight j v` of the `j`-th lift is at least `n + D.mainPairPoint`. -/
lemma exponent_add_mainPairPoint_le_liftWeight (v : D.Φ) :
    j + (D.t - 11 * D.m - 1) / 2 + D.mainPairPoint ≤ D.liftWeight j v := by
  obtain ⟨j, -, hj_le⟩ := j
  have hm_le : 100 * D.m ≤ D.k := D.hundred_mul_m_le_k
  have h_w : D.k + D.t + 1 ≤ D.liftWeight j v := D.k_add_t_add_one_le_liftWeight j v
  grind [mainPairPoint]

lemma chiMLocal_zpow_eq_one_of_not_isChosen (n : ℤ) (w : New.FinPlace D.E) (hw : ¬D.IsChosen w) :
    (D.chiMLocal ^ n) w = 1 := by
  rw [Pi.pow_apply, D.chiMLocal_eq_one_of_not_isChosen hw, one_zpow]

/-- The pairs of the three exchanges, indexed by `Option ℤˣ`: the sign `-1` belongs to the first,
the sign `1` to the second and `none` to the third exchange. Here `j` is a lift index
(`1 ≤ j ≤ m`), `w j v = D.liftWeight j v` is the weight and `μ_j⁰ = D.untwistedLiftChar j` the
untwisted part of the character of the `j`-th lift, `υ = upsilonU1`, `t = 5 r`, and `ω` is the tame
part of `χ`. For `none`: `ν_j = μ_j⁰ υ ^ n` with `n = j + (t - 11 m - 1) / 2`, of weight
`-(w j v - n)` at `v` and tame part `ω ^ j`, at the point `z_* = D.mainPairPoint`.
For a sign `s = ±1`: `ν_± = υ ^ (-z_±) χ ^ (± j)`, of weight `-z_±` at every place and tame part
`ω ^ (± j)`, at the point `z_± = D.signPoint s`. -/
noncomputable def exchangePair : Option ℤˣ → D.CriticalPair
  | none =>
    let n : ℕ := j + (D.t - 11 * D.m - 1) / 2
    have h_le (v : D.Φ) : n + D.mainPairPoint ≤ D.liftWeight j v :=
      exponent_add_mainPairPoint_le_liftWeight j v
    { character := D.untwistedLiftChar j * upsilonU1 ^ n
      negWeight v := D.liftWeight j v - n
      tamePart := D.chiMLocal ^ (j : ℤ)
      z := D.mainPairPoint
      -- `n ≤ w j v`, so the subtraction in `negWeight` is not truncated
      hasWeight := ((D.untwistedLiftChar_hasWeight j).mul_upsilonU1_pow n).of_weight_eq <|
        funext fun v ↦ by
        have hn_le : n ≤ D.liftWeight j v := le_self_add.trans (h_le v)
        omega
      tamePart_eq_one := chiMLocal_zpow_eq_one_of_not_isChosen j
      z_mem := D.mainPairPoint_mem_Icc
      le_negWeight v := Nat.le_sub_of_add_le' (h_le v)
      negWeight_le v := (Nat.mono_cast (Nat.sub_le _ n)).trans (liftWeight_le_four_mul_b j v) }
  | some s =>
    { character := (upsilonU1 ^ D.signPoint s)⁻¹ * D.chiM ^ ((s : ℤ) * j)
      negWeight _ := D.signPoint s
      tamePart := D.chiMLocal ^ ((s : ℤ) * j)
      z := D.signPoint s
      hasWeight := by simpa using!
        (hasWeight_upsilonU1_pow (D.signPoint s)).inv.mul (D.chiM_hasWeight.zpow (s * j))
      tamePart_eq_one := chiMLocal_zpow_eq_one_of_not_isChosen ((s : ℤ) * j)
      z_mem := D.signPoint_mem_Icc s
      le_negWeight _ := le_rfl
      negWeight_le v := by
                have h_le : D.signPoint s ≤ D.liftWeight j v := by
                  grind [D.signPoint_mem_Icc s, D.k_add_t_add_one_le_liftWeight j v]
                exact (Nat.mono_cast h_le).trans (liftWeight_le_four_mul_b j v) }

/-- The product of the Hecke values for the three pairs `(ν, z)` of `exchangePair j`,
twisted by `ϑ`. A twist consists of a character `ϑ.toAutChar` of U(1)(𝔸) with a tame part that is
non-trivial at every place of its finite set of places `ϑ.Q`. The factor of a pair is the real
number `Exchange.lValueProd` for the set of the chosen places and the places of `ϑ.Q`, the
character `(ν χ')⁻¹` and the integer `z`. Here `χ'` is `ϑ.toAutChar` for the pair `none` and
`ϑ.toAutChar ^ s` for the pair of sign `s`. -/
noncomputable def heckeValueProd (ϑ : D.Twist) : ℂ :=
  ∏ i : Option ℤˣ, (Exchange.lValueProd ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q)
    ((exchangePair j i).character * ϑ.toAutChar ^ ((i.getD 1 : ℤˣ) : ℤ))⁻¹ (exchangePair j i).z : ℝ)

end New.Data

namespace New.Rows

/-!
## Equal-rank theta class sums and the twisted carrier identity

The first two exchanges, for characters that are tame for a modulus 𝔪 (`New.Exchange.IsTameFor`).
Here m is positive. The two exchange lemmas also assume that m is even; the lemma on conjugating a
constant class sum does not.

Notation: θ_{a,b}[Ψ,P] is the theta kernel with characters a, b, a function Ψ on matrices mod 𝔪 and
a polynomial P. I_m is the standard definite space, `New.stdClassSum` is the class sum on it, and
`stdLevel` is the integral level. υ is the splitting character restricted to U(1).
-/

section Carrier

open Matrix MeasureTheory WeilData Exchange Space Pi
open NumberField (InfinitePlace)

variable (E : Type) [Field E] [CMType E] [WeilData E]

/-- The first exchange. Let `E` be a CM field, `m = 2e > 0`, and fix exponents `k τ` at the infinite
places `τ`. There is a constant `C` such that each character `α` of `U(1)(𝔸)` of weight `-k` that is
tame for `(𝔪, χ)` has a `γ` with (a) `‖γ‖ ^ 2 = C / lValueProd 𝔪.places (α⁻¹ υ ^ e) e`, and (b) `γ
Σ_h θ_{α,α}[χ ∘ det, ∏_τ det (y_τ) ^ k τ](g, h) = 1` for all `g` in `G E 1`, the adelic unitary
group of the standard definite space `I_m = stdSpace E (Fin m)`. The kernel `θ = modKernelStdSpace`
is the theta kernel of `I_m` with itself, `y_τ` is the `m × m` matrix of variables at `τ`, and
`Σ_h = stdClassSum` is the sum, with weights `1 / #Aut`, over the double cosets of the rational
points and `stdLevel`, the stabilizer of the standard lattice. -/
lemma exists_mul_stdClassSum_modKernelStdSpace_eq_one {m : ℕ} [NeZero m] (hm_even : Even m)
    (k : InfinitePlace E → ℕ) :
    ∃ C : ℝ, ∀ {𝔪 : Modulus E} {α : AutChar E} {χ : MulChar 𝔪.ResidueRing ℂ},
      IsTameFor 𝔪 α (fun τ : InfinitePlace E ↦ -k τ) χ → ∃ γ : ℂ,
        -- (a)
        ‖γ‖ ^ 2 = C / lValueProd 𝔪.places (α⁻¹ * upsilonU1 ^ (m / 2)) (m / 2) ∧
        -- (b)
        ∀ g : G E 1, γ * stdClassSum (stdLevel E (Fin m))
          (modKernelStdSpace (stdSpace E (Fin m)) α α 𝔪
            (fun x : Matrix (Fin m) (Fin m) 𝔪.ResidueRing ↦ χ x.det)
            (∏ τ : InfinitePlace E, variableMinor τ id id ^ k τ) g) = 1 := by
  -- `exists_mul_stdClassSum_eq_integral_modKernel` equates a multiple of the class sum of the
  -- kernel of `(W, I_m)` with an integral of the kernel of `(V', W)`. For `W = I_m` and `V' = 0`
  -- the data `χ ∘ det` and `1` are matched functions, and the integral is `1`.
  obtain ⟨C, h_match⟩ :=
    exists_mul_stdClassSum_eq_integral_modKernel (stdSpace E (Fin m)) (.sumEmpty Empty Empty)
      (stdSpace E Empty)
      (.emptySum Empty (Fin m)) (.emptySum Empty (Fin m)) (.sumEmpty (Fin m) Empty) rfl (d := m / 2)
      (by grind [Fintype.card_fin, Fintype.card_empty])
      (by grind [Fintype.card_fin, Fintype.card_empty, NeZero]) fun τ : InfinitePlace E ↦ Fin (k τ)
  refine ⟨C, fun {𝔪 α χ} h_tame ↦ ?_⟩
  obtain ⟨γ, h_norm, h_sum⟩ := h_match (by simpa using h_tame)
  refine ⟨γ, by simpa using h_norm, fun g ↦ ?_⟩
  convert! h_sum 0 (areMatched_det_one _ χ) α g
  -- With no rows to add, the polynomial `stackedDet` is the product of powers of determinants.
  · simp [stackedDet, ← det_reindex_self (.emptySum Empty (Fin m)), det_apply, variableMinor,
      stackedDetProd]
  -- Up to the factor `α (det x)⁻¹` the kernel with the zero space has the standard characters.
  · rw [← integral_modKernel_matchedPoly_of_isEmpty (stdSpace E (Fin m)) (.sumEmpty Empty Empty)
      (stdSpace E Empty) (.sumEmpty (Fin m) Empty) (𝔪 := 𝔪) (ι := fun τ ↦ Fin (k τ)) α 0 g]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simpa using (modKernel_twist _ _ 1 1 𝔪 1 α 1 _ x g).symm

/-- Let `E` be a CM field, `m > 0`, `I_m` the standard definite space of rank `m` and
`I_m⁻ = (stdSpace E (Fin m)).neg` the same space with its form negated. There is a number `n` of
norm 1 such that the following holds for every modulus `𝔪`, character `c` of `U(1)(𝔸)`, character
`χ` of the residue ring of `𝔪` and number `γ`. If `γ` times the class sum on `I_m`, at the integral
level `stdLevel`, of the theta kernel of `(I_m, I_m)` with characters `c⁻¹, c⁻¹` and function
`χ⁻¹ ∘ det` is the constant 1, then so is the conjugate of `γ` times `n / χ(η) ^ m` times the class
sum of the kernel of `(I_m⁻, I_m)` with characters `c υ ^ m, c υ ^ m` and function `χ ∘ det`. Here
`υ = upsilonU1` is the splitting character of `WeilData E` on the norm-one ideles, and
`η = 𝔪.normNegOne` is the unit mod 𝔪 that is the reduction of a chosen element of norm -1. -/
lemma exists_stdClassSum_modKernelStdSpace_neg_eq_one {m : ℕ} [NeZero m] :
    ∃ n : ℂ, ‖n‖ = 1 ∧ ∀ (𝔪 : Modulus E) (c : AutChar E) (χ : MulChar 𝔪.ResidueRing ℂ) (γ : ℂ),
      (∀ g : G E (1 : Fin m → ℤˣ), γ * stdClassSum (stdLevel E (Fin m))
        (modKernelStdSpace (stdSpace E (Fin m)) c⁻¹ c⁻¹ 𝔪
          (fun z : Matrix (Fin m) (Fin m) 𝔪.ResidueRing ↦ χ⁻¹ z.det) 1 g) = 1) →
      ∀ y : G E (-1 : Fin m → ℤˣ), star γ * stdClassSum (stdLevel E (Fin m))
        (fun h : Gf E (Fin m) ↦ n * (χ 𝔪.normNegOne ^ m)⁻¹ *
          modKernelStdSpace (stdSpace E (Fin m)).neg (c * upsilonU1 ^ m) (c * upsilonU1 ^ m) 𝔪
            (fun z : Matrix (Fin m) (Fin m) 𝔪.ResidueRing ↦ χ z.det) 1 y h) = 1 := by
  obtain ⟨n, hn, h_conj⟩ := exists_conj_modKernel_eq_mul_modKernel_neg (stdSpace E (Fin m))
    (stdSpace E (Fin m))
  refine ⟨n, hn, fun 𝔪 c χ γ h_sum y ↦ ?_⟩
  -- Conjugation scales `χ ∘ det` by `(χ η ^ m)⁻¹`, and kernels are linear in the function.
  have h_star : star γ * stdClassSum (stdLevel E (Fin m)) (fun h ↦
      n * modKernelStdSpace (stdSpace E (Fin m)).neg (c * upsilonU1 ^ m) (c * upsilonU1 ^ m) 𝔪
        (fun z ↦ (χ 𝔪.normNegOne ^ m)⁻¹ * χ z.det) 1 y h) = 1 := by
    simpa [map_classSum, h_conj, Units.smul_def, ← χ.star_apply'] using
      star_inj.2 (h_sum (G.neg.symm y))
  simpa [← smul_eq_mul, ← smul_def, ← modKernelBilin_apply, ← smul_assoc] using h_star

/-- Let `E` be a CM field and `m = 2e > 0`. There is a constant `C` such that each character `c` of
`U(1)(𝔸)` of weight 0 that is tame for `(𝔪, χ)` has a `γ` with (a) `‖γ‖ ^ 2 = C / (lValueProd (c⁻¹ υ
^ m, m) * lValueProd (c υ ^ e, e))`, and (b) `γ Σ_h carrierCoeff m c h · θ_{υ^m,c}[χ ∘ det, 1](x,
h) = φ°(x)` for all `x` in `G E (1 ⊕ᵥ -1)`, the adelic unitary group of the space `S` of signature
`(2m, m)`. The sum is the class sum on the finite adelic group `Gf` of the standard definite space
of rank `3m`, at the level `stdLevel`, and θ is the theta kernel of `S` and that space. -/
lemma exists_mul_stdClassSum_eq_carrierForm {m : ℕ} [NeZero m] (hm_even : Even m) :
    ∃ C : ℝ, ∀ {𝔪 : Modulus E} {c : AutChar E} {χ : MulChar 𝔪.ResidueRing ℂ},
      IsTameFor 𝔪 c 0 χ → ∃ γ : ℂ,
        -- (a) the size of the constant
        ‖γ‖ ^ 2 = C / (lValueProd 𝔪.places (c⁻¹ * upsilonU1 ^ m) m *
          lValueProd 𝔪.places (c * upsilonU1 ^ (m / 2)) (m / 2)) ∧
        -- (b) the carrier as a class sum
        ∀ x : G E (1 ⊕ᵥ -1), γ * stdClassSum (stdLevel E (Fin (2 * m) ⊕ Fin m))
          (fun h : Gf E (Fin (2 * m) ⊕ Fin m) ↦ carrierCoeff m c h *
            modKernelStdSpace (signedSpace E (1 ⊕ᵥ -1)) (upsilonU1 ^ m) c 𝔪
              (fun y : Matrix (Fin (2 * m) ⊕ Fin m) (Fin (2 * m) ⊕ Fin m) 𝔪.ResidueRing ↦ χ y.det)
              1 x h) = carrierForm E m x := by
  -- Two exchanges are chained by `mul_stdClassSum_eq_integral_mul_modKernel`. The first is
  -- `exists_mul_stdClassSum_modKernelStdSpace_eq_one` for `c⁻¹`, conjugated so that it lives on
  -- `I_m⁻`; the second is `exists_mul_stdClassSum_eq_integral_modKernel` with `W = I_m ⊕ S`,
  -- `V' = I_m⁻` and `V = I_{3m}`. The kernel on `W` then splits into the summand of `carrierCoeff`
  -- and the kernel on `S`. Below, `J` is `I_m` and `H` is `S`.
  let J : Space E (Fin m) 1 := stdSpace E (Fin m)
  let H := signedSpace E (1 ⊕ᵥ -1 : Fin (2 * m) ⊕ Fin m → ℤˣ)
  obtain ⟨C₁, h_full⟩ := exists_mul_stdClassSum_modKernelStdSpace_eq_one (m := m) E hm_even 0
  obtain ⟨C₂, h_match⟩ :=
    exists_mul_stdClassSum_eq_integral_modKernel (J.sum H) (.emptySum Empty _) J.neg 1
      (.trans (.emptySum ..) (.sumComm ..))
      (.sumAssoc ..) (by aesop) (d := m) (by simp +arith)
      (by grind [Fintype.card_sum, Fintype.card_fin, NeZero]) fun _ : InfinitePlace E ↦ Empty
  obtain ⟨n, hn_norm, h_conj⟩ := exists_stdClassSum_modKernelStdSpace_neg_eq_one E (m := m)
  refine ⟨C₁ * C₂, fun {𝔪 c χ} h_tame ↦ ?_⟩
  obtain ⟨γ₁, h_norm₁, h_sum₁⟩ := h_full h_tame.inv
  obtain ⟨γ₂, h_norm₂, h_sum₂⟩ := h_match (α := c * upsilonU1 ^ m) (χ := χ)
    (by simpa using h_tame.mul (hasWeight_upsilonU1_pow m))
  have h_eta_norm : ‖χ 𝔪.normNegOne‖ = 1 :=
    (χ.isOfFinOrder 𝔪.normNegOne.isUnit.isOfFinOrder).norm_eq_one
  refine ⟨γ₂ * star γ₁ * n / χ 𝔪.normNegOne ^ m, ?_, fun x ↦ ?_⟩
  · rw [inv_inv] at h_norm₁
    -- the character of the second exchange is `(c υ ^ m)⁻¹ υ ^ (2m) = c⁻¹ υ ^ m`
    rw [Fintype.card_fin, pow_add, mul_inv, mul_assoc, inv_mul_cancel_left] at h_norm₂
    -- `n` and `χ η` have norm 1, so the square norms of `γ₁` and `γ₂` multiply.
    simp [mul_pow, hn_norm, h_eta_norm, h_norm₁, h_norm₂, field]
  -- The conjugate of the first exchange: the class sum on `I_m` of kernels of `(I_m⁻, I_m)` is
  -- constant on `U(I_m⁻)`.
  have h_neg := h_conj 𝔪 c χ γ₁ (by simpa using h_sum₁)
  -- The kernel on `I_m ⊕ H` is a product of two kernels.
  have h_seesaw (b : AutChar E) (g : G E (1 : Fin m → ℤˣ)) (h : G E 1) :
      modKernel (J.sum H) (stdSpace E _) (c * b) 1 𝔪 (χ ·.toCols₂.det) 1 (.sum (g, x)) h =
        modKernel J (stdSpace E _) c 1 𝔪 1 1 g h *
          modKernel H (stdSpace E (Fin (2 * m) ⊕ Fin m)) b 1 𝔪 (χ ·.det) 1 x h := by
    simpa using modKernel_sum_left J (stdSpace E _) c 1 𝔪 H b 1 (χ ·.det) 1 1 g x h
  -- The second exchange, with the datum `Ψ' = 1`, is summed over the classes of `I_m` by `h_neg`:
  -- a multiple of a double class sum of kernels of `(W, I_{3m})` is the integral of the kernel of
  -- `(I_m⁻, H)` with datum 1.
  have h_move := mul_stdClassSum_eq_integral_mul_modKernel J.neg H (β' := 1) h_tame.1
    (P := ∏ τ, variableMinor τ Sum.inr id ^ (2 * m)) (g := x) h_neg
    (Ψ' := 1) (fun _ _ ↦ rfl) fun Φ Ψ h_partner h ↦ by
      simpa [det_apply, two_mul, ← tsub_tsub, variableMinor, stackedDetProd, matchedPoly,
        pairedDetProd] using! h_sum₂ 0 h_partner 1 (.sum ((1, h), x))
  simp_rw [mul_classSum, classSum_comm (G := Gf E (Fin m))] at h_move
  -- Split the kernel on `W`; the result is the claim times `c (det x)` on both sides.
  have h_split :
      stdClassSum (stdLevel E (Fin (2 * m) ⊕ Fin m)) (fun h ↦
        stdClassSum (stdLevel E (Fin m)) fun g ↦ γ₂ * star γ₁ * (n * (χ 𝔪.normNegOne ^ m)⁻¹ *
          (modKernelStdSpace J c 1 𝔪 1 1 (1, g) h *
            modKernelStdSpace H (upsilonU1 ^ m) 1 𝔪 (χ ·.det) 1 x h))) =
        ∫ y : G E (-1), modKernel J.neg H (c * upsilonU1 ^ m) 1 𝔪 1
          (∏ τ, variableMinor τ Sum.inr id ^ (2 * m)) y x ∂J.neg.quotMeasure := by
    simpa [h_seesaw] using h_move
  simpa [modKernel, mul_left_comm _ _⁻¹, mul_assoc, ← mul_classSum, field, carrierCoeff,
    pairTheta, pairWeil, modDatum, Modulus.liftFn_one, Modulus.isConjDisjoint_places,
    schrodingerOp_boxIndicator, carrierForm, lift, integral_const_mul] using h_split

end Carrier

/-! ## The carrier as a nonzero holomorphic rapidly decreasing form -/

section CarrierProperties

open Exchange Matrix Function MeasureTheory SiegelWeil Finset Sum Heisenberg.IsVacuum Space
open NumberField (InfinitePlace RingOfIntegers)

variable {E : Type} [Field.{0} E] [CMType E] [WeilData E]

/-- Let `E` be a CM field and `m` a nonzero even natural number, and let `E` have a character `c` of
`U(1)(𝔸)` of weight 0 that is tame for some `(𝔪, χ)`: its tame part is non-trivial exactly at the
places of `𝔪 ≠ 1` and induces `χ`. The carrier `carrierForm E m` is the theta lift of the constant 1
from `U(0, m)` to `U(S)`, with `S = signedSpace E (1 ⊕ᵥ -1)` of signature `(2m, m)`. (a) For every
integer `N` of `E` the carrier lies in `rapidOfLevel S N`: it is continuous, invariant under the
rational points of `U(S)` on the left and under the principal congruence subgroup `K(N)` on the
right, and rapidly decreasing. (b) There is an order `o`, an injective integer numbering of the
basis of `S` with the positive vectors before the negative ones (`IsPosFirstOrder`), for which the
carrier is holomorphic (`IsAdelicHol`): each left translate, restricted to the real group, extends
analytically to the products `h b` with `b` invertible and `o`-triangular. -/
lemma carrierForm_mem_rapidOfLevel_and_isAdelicHol {m : ℕ} [NeZero m] (hm_even : Even m)
    {𝔪 : Modulus E} {c : AutChar E} {χ : MulChar 𝔪.ResidueRing ℂ} (h_tame : IsTameFor 𝔪 c 0 χ) :
    -- (a)
    (∀ N : RingOfIntegers E, carrierForm E m ∈ rapidOfLevel (signedSpace E (1 ⊕ᵥ -1)) N) ∧
    -- (b)
    ∃ o : Fin (2 * m) ⊕ Fin m → ℤ, IsPosFirstOrder (1 ⊕ᵥ -1) o ∧
      IsAdelicHol o (fun _ : InfinitePlace E ↦ 0 ⊕ᵥ 3 * m) (carrierForm E m) := by
  -- By `exists_mul_stdClassSum_eq_carrierForm`, the carrier is a finite combination of theta
  -- kernels `θ h` with polynomial 1; level, rapid decay and holomorphy are read off from these
  -- kernels.
  let V : Space E (Fin (2 * m) ⊕ Fin m) (1 ⊕ᵥ -1) := signedSpace E (1 ⊕ᵥ -1)
  let θ (h : Gf E (Fin (2 * m) ⊕ Fin m)) (x : G E (1 ⊕ᵥ -1)) : ℂ :=
    modKernelStdSpace V (WeilData.upsilonU1 ^ m) c 𝔪 (fun y ↦ χ y.det) 1 x h
  obtain ⟨ι, _, coef, h, h_comb⟩ : ∃ (ι : Type) (_ : Fintype ι) (coef : ι → ℂ) (h : ι → Gf E _),
      (fun x ↦ ∑ i, coef i * θ (h i) x) = carrierForm E m := by
    obtain ⟨C, h_carrier⟩ := exists_mul_stdClassSum_eq_carrierForm (m := m) E hm_even
    obtain ⟨γ, -, h_class_sum⟩ := h_carrier h_tame
    simp only [classSum, finsum_eq_sum_of_fintype, Rat.smul_def, mul_sum, ← mul_assoc,
      ← funext_iff] at h_class_sum
    -- the class sum is now a finite sum: read off the index type, the coefficients and the points
    exact ⟨_, _, _, _, h_class_sum⟩
  -- `hψ` is the weight instance that `isAdelicHol_pairTheta` needs.
  have ⟨h𝔪, ψ, hψ, _⟩ := h_tame
  have h_mem (N : RingOfIntegers E) (g : Gf E (Fin (2 * m) ⊕ Fin m)) : θ g ∈ rapidOfLevel V N := by
    -- Level one: on `stdLevel` the factor `c (det k)⁻¹` cancels against `χ (det k)`.
    have h_level : HasLevel (θ g) (⟨stdLevel E _, isOpen_stdLevel⟩ : OpenSubgroup _) := by
      simp [θ, V, ↓Subtype.forall', modKernel_mul_stdLevel_left, h_tame.apply_det, Pi.smul_def,
        mul_comm, χ.apply_eq_zero_iff]
    -- Rapid decay: `χ (det y) ≠ 0` makes `y` invertible.
    have h_rapid : V.IsRapid (θ g) := isRapid_modKernel _ _ _ _ h𝔪
      (fun y hy ↦ ⟨y⁻¹, y.nonsing_inv_mul (χ.apply_ne_zero_iff.1 hy)⟩) _ _
    -- A theta kernel is continuous and invariant under the rational points.
    have h_aut : V.IsAutomorphic (θ g) :=
      ⟨by fun_prop [modKernel], (pairThetaKer ..).theta_rat_mul, _, h_level⟩
    exact ⟨⟨h_aut, h_rapid⟩, fun ⟨k, hk⟩ ↦ funext (h_level k hk.1)⟩
  let o : Fin (2 * m) ⊕ Fin m → ℤ := (fun i ↦ -1 - (i : ℤ)) ⊕ᵥ fun i ↦ (i : ℤ)
  have h_first : IsPosFirstOrder (1 ⊕ᵥ -1) o := by
    simp [o, IsPosFirstOrder, Injective]
    -- the positive indices get negative values, the negative ones values at least 0
    lia
  -- The polynomial 1 is a product of zeroth powers of minors, so its Fock vector is holomorphic.
  have h_vacuum : Fock.polyVector _ 1 ∈ holomorphicData (E := E) (1 ⊕ᵥ -1)
      (1 : Fin (2 * m) ⊕ Fin m → ℤˣ) o (fun _ ↦ 0 ⊕ᵥ 3 * m) (fun _ ↦ m) 0 := by
    simpa +arith using
      (prod_variableMinor_mem_holomorphicData h_first (Embedding.inl (β := Fin m)) 0 _).2
  rw [← h_comb]
  refine ⟨fun N ↦ ?_, o, h_first, fun g ↦ .sum _ fun i ↦ isAdelicHol_pairTheta h_vacuum g⟩
  have h_one_mul (i : ι) : 1 * θ (h i) ∈ rapidOfLevel V N := by simpa using h_mem N (h i)
  simpa using mul_sum_mem_rapidOfLevel (c := coef) h_one_mul

omit [WeilData E] in
/-- Let `E` be a CM field and `m > 0`. In the Fock space `PairFock` of the pair
`(U(0, m), U(2m, m))`, let `v` be the vector of the polynomial `∏_τ det (y⁻_τ) ^ (2m)`, where `τ`
runs over the infinite places and `y⁻_τ` is the `m × m` block of variables in the negative rows of
`U(2m, m)`. Then `⟨v, Ω(u, 1) v⟩ = ⟨v, v⟩` for every `u` in `GInf E (-1)`, the product over `τ` of
copies of the compact group `U(0, m)`.
Here `Ω = realPairWeil 0 0` is the real Weil representation of the pair with both weights `0`, and
`⟨·, ·⟩ = Fock.fockInner` is the sesquilinear form of the Fock space. -/
lemma fockInner_realPairWeil_variableMinor_pow_eq_self {m : ℕ} [NeZero m]
    (u : GInf E (-1 : Fin m → ℤˣ)) :
    let v : PairFock E (-1 : Fin m → ℤˣ) (1 ⊕ᵥ -1 : Fin (2 * m) ⊕ Fin m → ℤˣ) :=
      Fock.polyVector (realSigns E (homSigns (-1) (1 ⊕ᵥ -1)))
        (∏ τ : InfinitePlace E, variableMinor τ inr id ^ (2 * m))
    Fock.fockInner v (realPairWeil 0 0 (u, 1) v) = Fock.fockInner v v := by
  intro v
  let negMinorPoly : MvPolynomial (InfinitePlace E × (Fin (2 * m) ⊕ Fin m) × Fin m) ℂ :=
    ∏ τ, variableMinor τ inr id ^ (2 * m)
  -- every variable of a minor in the rows `inr` has sign 1
  have h_supp : negMinorPoly ∈
      MvPolynomial.supported ℂ {p | realSigns E (homSigns (-1) (1 ⊕ᵥ -1)) p = 1} := by
    refine prod_mem fun τ _ ↦ pow_mem ?_ (2 * m)
    rw [variableMinor, det_apply']
    refine sum_mem fun σ _ ↦ mul_mem (intCast_mem _ _) (prod_mem fun k _ ↦ ?_)
    simp [pairSign]
  -- each `g` scales `negMinorPoly` by the `2m`-th powers of its determinants
  have h_scale (g : GInf E (-1 : Fin m → ℤˣ)) :
      linSubst (Fock.complexLinearPart (pairHomInf (s' := 1 ⊕ᵥ -1) (g⁻¹, 1))) negMinorPoly =
        (∏ τ, principalMinor (g τ) (fun k ↦ (-1 : Fin m → ℤˣ) k = -1) ^ (2 * m)) •
          negMinorPoly := by
    simp [negMinorPoly, linSubst_variableMinor (κ := -1) (elim_inr _ _) injective_id, smul_pow,
      prod_smul]
  let μ : ℂ := holMinorsPi (-1) (fun _ _ ↦ 3 * m) u
  have h_coeff : polyMatrixCoeff (-1) (1 ⊕ᵥ -1) 0 0 negMinorPoly u 1 =
      polyMatrixCoeff (-1) (1 ⊕ᵥ -1) 0 0 negMinorPoly 1 1 * μ * starRingEnd ℂ μ := by
    have h_three : (2 * m + m : ℤ) = 3 * m := by ring
    simpa [h_three] using polyMatrixCoeff_eq_holMinorsPi_mul_conj (-1) (1 ⊕ᵥ -1) negMinorPoly h_supp
      (ν := 0) (c := fun _ ↦ 2 * m) 0 0 (by simpa using h_scale) u
  -- `μ` is a product of powers of determinants of unitary matrices
  have h_unit : μ * starRingEnd ℂ μ = 1 := by
    simp [μ, holMinorsPi, holMinors, ← prod_mul_distrib, ← mul_zpow, Complex.mul_conj',
      GeneralLinearGroup.det_ne_zero]
  simpa [v, negMinorPoly, polyMatrixCoeff, mul_assoc, h_unit, Prod.mk_one_one] using h_coeff

/-- Let `E` be a CM field. For every positive `m`, even or odd, the carrier `φ° = carrierForm E m`
is not zero. It is the theta lift of the constant 1 from the definite group U(0, m) to U(S), S of
signature (2m, m). -/
lemma carrierForm_ne_zero {m : ℕ} [NeZero m] : carrierForm E m ≠ 0 := by
  -- If the lift vanished, `realConv_eq_zero_of_lift_eq_zero` would give `∫ ⟨v, Ω(u, 1) v⟩ du = 0`
  -- over the compact real group. But `⟨v, Ω(u, 1) v⟩ = ⟨v, v⟩` for all `u`, so the integrand is a
  -- nonzero constant.
  let v : PairFock E (-1 : Fin m → ℤˣ) (1 ⊕ᵥ -1 : Fin (2 * m) ⊕ Fin m → ℤˣ) :=
    Fock.polyVector _ (∏ τ : InfinitePlace E, variableMinor τ inr id ^ (2 * m))
  have hv_ne : v ≠ 0 := by simp [v, prod_eq_zero_iff, inr_injective, injective_id]
  have h_fockInner_const (u : GInf E (-1)) :
      Fock.fockInner v (realPairWeil 0 0 (u, 1) v) = Fock.fockInner v v :=
    fockInner_realPairWeil_variableMinor_pow_eq_self u
  have : CompactSpace (USign (-1 : Fin m → ℤˣ)) := by
    rw [show USign (-1 : Fin m → ℤˣ) = U 1 by simp [U]]
    infer_instance
  intro h_lift_zero
  -- The modulus is trivial, so the finite part of the datum is the vacuum, which is sharp.
  have h_sharp := isSharp_vacuumDatum_of_mul_eq_one (𝔪 := unitModulus E)
    (S := (stdSpace E (Fin m)).neg) (F := 1)
    (signedSpace E (1 ⊕ᵥ -1 : Fin (2 * m) ⊕ Fin m → ℤˣ)) 1 (by simp) 0 (by subsingleton) (by simp)
    (by simp)
  have h_conv : realConv (fun u ↦ Fock.fockInner v (realPairWeil 0 0 (u, 1) v)) (fun _ ↦ 1) = 0 :=
    realConv_eq_zero_of_lift_eq_zero h_sharp v (by simp)
      (by simp [IsAutomorphic.mem_rapidFunctions, isAutomorphic_const]) (by simp [NeZero.pos])
      h_lift_zero 0 (by simp [h_fockInner_const])
  -- The integrand is the constant `⟨v, v⟩`, which is not zero.
  simpa [realConv, h_fockInner_const, eq_zero_of_modelInner_self.mt hv_ne,
    measureReal_univ_ne_zero] using congrFun h_conv 1

end CarrierProperties

end New.Rows

namespace New.Data

/-!
## The third exchange

The exchange identity for the spaces `W = E^{3m} ⊕ W'`, `V″` and `S`, summed over the classes of
`E^{3m}`, equates a double class sum of kernels with the function `𝖥_i = choiceFn j i`, up to a
number whose modulus depends on the twist only through Hecke values and norms. Here `V″` is the
standard definite space on `FirstFactorIndex j`. The characters are `χ' = twistedChiMPow ϑ j`,
`ν″ = firstFactorChar ϑ j` and `ν♭ υ ^ m = carrierChar j`, where `ν♭ = ν″ / χ'` does not depend on
the twist.

The datum of the left side becomes a product at a smaller level. This is stated for rows `w` modulo
`ϖ²` of which the rows of `Λ` are combinations. For the rows of `Λ` stacked above `ϖ • 1`, the
level `rowFixingLevel` is `J_Λ` and `columnDatum` is the datum `Ψ_Λ` on `W_j`.
-/

section LineIdentity

open Function Fintype Matrix Rows WeilData Sum Additive
variable {P : Parameters} {D : Data P}

open NumberField (InfinitePlace)

/-- The quotient `(carrierChar j)⁻¹ / χ'` times `υ ^ (3m + mainPairPoint)`, with `χ'` the character
`twistedChiMPow ϑ j`, is `ϑ⁻¹` divided by `μ_j⁰ υ ^ n`, the character of `exchangePair j none`. Here
`μ_j⁰ = D.untwistedLiftChar j` and `n = j + (t - 11 m - 1) / 2`. -/
private lemma carrierChar_inv_div_twistedChiMPow_mul_upsilonU1_pow (ϑ : D.Twist) (j : D.LiftIndex) :
    (carrierChar j)⁻¹ / twistedChiMPow ϑ.toTameChar j * upsilonU1 ^
      (2 * D.m + D.m + D.mainPairPoint) =
      ϑ.toAutChar⁻¹ / (D.untwistedLiftChar j * upsilonU1 ^ (j.val + (D.t - 11 * D.m - 1) / 2)) := by
  apply_fun ofMul
  simp [twistedChiMPow, carrierChar, untwistedLiftChar]
  -- compare the exponents of each character
  match_scalars <;> grind [mainPairPoint]

/-- The character `χ'⁻¹ υ ^ m`, with `χ' = twistedChiMPow ϑ j`, is `ϑ⁻¹` divided by
`υ ^ (-m) χ ^ j`, the character of `exchangePair j (some 1)`. -/
private lemma twistedChiMPow_inv_mul_upsilonU1_pow (ϑ : D.Twist) (j : D.LiftIndex) :
    (twistedChiMPow ϑ.toTameChar j)⁻¹ * upsilonU1 ^ D.m =
      ϑ.toAutChar⁻¹ / ((upsilonU1 ^ D.m)⁻¹ * D.chiM ^ j.val) := by
  rw [twistedChiMPow, div_eq_mul_inv ϑ.toAutChar⁻¹, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv,
    mul_assoc]

/-- The character `χ' υ ^ (m / 2)`, with `χ' = twistedChiMPow ϑ j`, is `ϑ` divided by
`υ ^ (-m / 2) χ ^ (-j)`, the character of `exchangePair j (some (-1))`. -/
private lemma twistedChiMPow_mul_upsilonU1_pow (ϑ : D.Twist) (j : D.LiftIndex) :
    twistedChiMPow ϑ.toTameChar j * upsilonU1 ^ (D.m / 2) =
      ϑ.toAutChar / ((upsilonU1 ^ (D.m / 2))⁻¹ / D.chiM ^ j.val) := by
  rw [twistedChiMPow, div_eq_mul_inv ϑ.toAutChar, inv_div, div_inv_eq_mul, mul_left_comm, mul_assoc]

variable (ϑ : D.Twist) (j : D.LiftIndex)

/-- The space `W' = W_j ⊕ (E^j)⁻ ⊕ E^{3m-j} ⊕ W♭` of the third exchange, where `W♭` is the standard
definite space on the `6m + 1` indices `D.FlatIndex`. Its basis is indexed by `FirstFactorIndex j`,
like that of the definite space `V″`, and `padSigns j` gives the signs on the first three
summands. -/
abbrev enlargedSpace : Space D.E (FirstFactorIndex j) (padSigns j ⊕ᵥ 1) :=
  ((D.spaceW j).sum ((stdSpace D.E (Fin j)).neg.sum
    (stdSpace D.E (Fin (2 * D.m + (D.m - j)))))).sum (stdSpace D.E D.FlatIndex)

/-- The point `(g, 1, 1, h♭)` of `U(W')`, with `h♭` the class of the index `i`. -/
abbrev enlargedPoint (i : ChoiceIndex j) (g : New.G D.E (D.signsW j)) :
    New.G D.E (n := FirstFactorIndex j) (padSigns j ⊕ᵥ 1) :=
  .sum (.sum (g, 1), (1, i.rowChoice.classRep))

/-- The list of the positive, then the negative basis vectors of `W = E^{3m} ⊕ W'`. -/
def signOrder : (Fin (D.posRank j) ⊕ AddedIndex j) ⊕ Fin D.m ≃ D.CarrierIndex ⊕ FirstFactorIndex
  j :=
  .ofBijective
    (regroupEquiv j ∘ Sum.map (D.rowIndexOfNumber ∘ Fin.val) inr ⊕ᵥ inr ∘ inl ∘ negIndex j) <| by
    -- an injection between sets of equal size; `↓` counts the indices before they are unfolded
    simp [↓card_rowIndex, ↓bijective_iff_injective_and_card, Injective, rowIndexOfNumber, negIndex,
      regroupEquiv]
    -- different basis numbers give different vectors
    grind [Equiv.injective]

/-- The left side lists the signs of `W = E^{3m} ⊕ W'` with `W' = W_j ⊕ (E^j)⁻ ⊕ E^{3m-j} ⊕ W♭`:
sign `1` on the `3m` indices `D.CarrierIndex` of `E^{3m}`, the signs `padSigns j` on the first three
summands of `W'`, and sign `1` on the definite space `W♭` of rank `6m + 1`. The bijection
`signOrder j` lists the basis of `W` in two blocks, and `blockSigns` is `1` on the first block and
`-1` on the second, which has `m` vectors. So the first block holds the positive and the second the
negative basis vectors. -/
lemma signs_eq_blockSigns_signOrder :
    (1 : D.CarrierIndex → ℤˣ) ⊕ᵥ (padSigns j ⊕ᵥ 1) = blockSigns (signOrder j) := by
  rw [blockSigns, Equiv.eq_comp_symm]
  ext1 ((a | l) | b)
  · -- the first `D.posRank j` basis vectors of `W_j` have sign `1`
    simp [signOrder, signsW, rowIndexOfNumber, regroupEquiv]
    grind
  · rcases l with _ | _ | _ <;> simp [signOrder, regroupEquiv]
  · -- the negative vectors are those of `(E^j)⁻` and the later basis vectors of `W_j`
    simp [signOrder, signsW, rowIndexOfNumber, negIndex, apply_dite (padSigns j)]
    grind

/-- The invariant trace character `ψ^inv_Λ`: the sum over `γ` in `GL_{3m}` modulo `ϖ²` of the
additive character `traceChar Λ` at `x γ`, for `x` reduced modulo `ϖ²`. -/
def invariantTraceChar (Λ : Matrix D.CarrierIndex (FirstFactorIndex j)
  (D.untwistedModulus 2).ResidueRing)
    (x : Matrix (FirstFactorIndex j) D.CarrierIndex (D.twistModulus ϑ 2).ResidueRing) : ℂ :=
  ∑ γ : GL D.CarrierIndex (D.untwistedModulus 2).ResidueRing,
    traceChar Λ (x.map (forgetTwist ϑ.toTameChar) * γ.val)

/-- The invariant trace character `ψ^inv_Λ = invariantTraceChar ϑ j Λ` is invariant under right
multiplication of its argument `x` by an invertible matrix `γ` over the residue ring of
`D.twistModulus ϑ 2`. -/
lemma invariantTraceChar_mul
    (Λ : Matrix D.CarrierIndex (FirstFactorIndex j) (D.untwistedModulus 2).ResidueRing)
    (x : Matrix (FirstFactorIndex j) D.CarrierIndex (D.twistModulus ϑ 2).ResidueRing)
    (γ : GL D.CarrierIndex (D.twistModulus ϑ 2).ResidueRing) :
    invariantTraceChar ϑ j Λ (x * γ.val) = invariantTraceChar ϑ j Λ x :=
  Finset.sum_equiv (.mulLeft (γ.map (forgetTwist ϑ.toTameChar))) (by simp)
    (by simp [Matrix.mul_assoc])

/-- The character of the residue ring modulo `D.twistModulus ϑ 2 = ϖ² Q`, with `ϖ` the product of
the chosen places and `Q` the product of the places of `ϑ`, that comes from the tame part of
`twistedChiMPow ϑ j`, the product `χ' = χ^j ϑ` of the fixed character `D.chiM` and the twist. -/
abbrev twistedChiMod : MulChar (D.twistModulus ϑ 2).ResidueRing ℂ :=
  (D.twistModulus ϑ 2).charOfTamePart (D.liftTamePart ϑ j)

/-- The theta kernel of `(W, V″)` in the third exchange: `W = E^{3m} ⊕ W'`, and `V″` is the standard
definite space on `FirstFactorIndex j`. The characters are `twistedChiMPow ϑ j * carrierChar j` and
`ν″ = firstFactorChar ϑ j`, the character of the `j`-th lift times a power of υ; here
`carrierChar j` is `ν″ υ ^ m / twistedChiMPow ϑ j`, which is free of the twist. The datum is `Ψ`,
and the polynomial is `stackedDetProd` of the constant rows `constantRows` of `i`, read through the
bijection `posEquiv j` between its column indices and the positive part of the basis. It is taken at
the point `(h', g, 1, 1, h♭)` of `U(W)` and the point `h` of `U(V″)`. -/
def thirdExchangeKernel (i : ChoiceIndex j) (g : New.G D.E (D.signsW j))
    (Ψ : Matrix (FirstFactorIndex j) (D.CarrierIndex ⊕ FirstFactorIndex j)
      (D.twistModulus ϑ 2).ResidueRing → ℂ)
    (h' : Gf D.E D.CarrierIndex) (h : Gf D.E (FirstFactorIndex j)) : ℂ :=
  modKernelStdSpace ((stdSpace D.E D.CarrierIndex).sum (enlargedSpace j))
    (twistedChiMPow ϑ j * carrierChar j) (firstFactorChar ϑ j) (D.twistModulus ϑ 2) Ψ
    (renameRowsCols id (signOrder j ∘ inl)
      (stackedDetProd (posEquiv j) (constantRows j i.rowChoice (D.shortRows i.rowChoice))))
    (.sum ((1, h'), enlargedPoint j i g)) h

/-- The left side of the third exchange: the class sum over `U(V″)` of the kernel with the datum
`(x' x″) ↦ χ' (det x″) ψ^inv_Λ (x″⁻¹ x')`, summed over the classes `h'` of `E^{3m}` against the
coefficients `carrierCoeff` at `h'`. -/
def thirdExchangeLeftSide (i : ChoiceIndex j) (g : New.G D.E (D.signsW j)) : ℂ :=
  stdClassSum (stdLevel D.E D.CarrierIndex) fun h' ↦ carrierCoeff D.m (twistedChiMPow ϑ j) h' *
    stdClassSum (stdLevel D.E (FirstFactorIndex j)) (thirdExchangeKernel ϑ j i g (fun x ↦
      twistedChiMod ϑ j x.toCols₂.det *
        invariantTraceChar ϑ j i.matrix (x.toCols₂⁻¹ * x.toCols₁)) h')

/-- The identity `ν″ υ ^ m = χ' (ν♭ υ ^ m)` of characters, with `ν″ = firstFactorChar ϑ j`,
`χ' = twistedChiMPow ϑ j` and `ν♭ υ ^ m = carrierChar j`, a character that does not depend on
`ϑ`. -/
lemma firstFactorChar_mul_upsilonU1_pow :
    firstFactorChar ϑ j * upsilonU1 ^ D.m = twistedChiMPow ϑ j * carrierChar j := by
  apply_fun ofMul
  simp [firstFactorChar, liftChar, twistedChiMPow, carrierChar, untwistedLiftChar]
  -- compare the exponents of each character
  match_scalars <;> grind

/-- Let `D` be admissible data, `ϑ` a twist and `j` a lift index, `1 ≤ j ≤ m`. Let
`χ' = twistedChiMPow ϑ j = χ^j ϑ`. The character `carrierChar j` does not depend on `ϑ` and has
trivial tame part. The product of the two is tame for `D.twistModulus ϑ 2 = ϖ² Q`, with `ϖ` the
product of the chosen places and `Q` that of the places of `ϑ`: its tame part is non-trivial exactly
at the places of `ϖ² Q ≠ 1` and induces `twistedChiMod ϑ j`, the character of the residue ring given
by the tame part of `χ'`. Its weight at an infinite place `τ` is `m` minus the size of
`DetIndex j τ`, the index set of the determinants at `τ` in the polynomial of the third exchange. -/
lemma isTameFor_twistedChiMPow_mul_carrierChar :
    Exchange.IsTameFor (D.twistModulus ϑ 2) (twistedChiMPow ϑ j * carrierChar j)
      (fun τ : InfinitePlace D.E ↦ card (Fin D.m) - card (DetIndex j τ)) (twistedChiMod ϑ j) := by
  have h_weight : (fun τ : InfinitePlace D.E ↦ (card (Fin D.m) : ℤ) - card (DetIndex j τ)) =
      0 + fun τ : InfinitePlace D.E ↦ ↑(D.m + firstFactorCharExp j) - (D.liftWeight j τ : ℤ) := by
    simp [← card_detIndex_add_firstFactorCharExp j]
  rw [h_weight]
  exact (isTameFor_twistedChiMPow (c := 2) j ϑ).mul (carrierChar_hasWeight j)

/-- Let `D` be admissible data, `j` a lift index (`1 ≤ j ≤ m`) and `W = E^{3m} ⊕ W'`, where
`W' = W_j ⊕ (E^j)⁻ ⊕ E^{3m-j} ⊕ W♭`: the space `W_j = D.spaceW j`, its padding, and the definite
space `W♭` on the `6m + 1` indices `D.FlatIndex`. The variables at an infinite place `τ` form a
matrix with rows the basis of `W`, listed by sign through `signOrder j`, and `2m` positive and `m`
negative columns. For complex matrices `η_{τ k}` with `2m` rows, `matchedPoly` is the product of a
power of the determinant of the negative block and of the `det (η_{τ k} y_τ)`, with `y_τ` the
positive block. The choice `i` consists of a class of `U(W♭)` and lists `i.rows τ k` of `2m` row
indices, `k < D.reducedHalfGap`. The matrices `constantRows` have as rows either basis vectors of
`W_j` and the padding, or the rows `i.rows τ k` of `D.shortRows i`, an invertible matrix over `E`
with small rows in the lattice of the class, read at `τ` by the embedding `Φ τ`. For them
`matchedPoly` involves only the rows of `W'`: it is `paddedMinorProd j`, a product of minors in the
rows of `W_j` and the padding, times the determinants `pairedDetProd` in the rows of `W♭`. The maps
`renameRowsCols` place each factor in its block of rows. -/
lemma matchedPoly_constantRows (i : D.RowChoice) :
    matchedPoly (.refl (Fin (2 * D.m) ⊕ Fin D.m)) (signOrder j) (constantRows j i (D.shortRows i)) =
      renameRowsCols inr id (renameRowsCols inl id (paddedMinorProd j) * renameRowsCols inr id
        (pairedDetProd
          (fun (τ : InfinitePlace D.E) (r : D.FlatIndex) (c : Fin (2 * D.m)) ↦ .X ⟨τ, r, inl c⟩)
          fun (τ : InfinitePlace D.E) (k : Fin D.reducedHalfGap) ↦
            ((D.shortRows i).map (Φ τ)).submatrix (i.rows τ k) id)) := by
  simp [signOrder, matchedPoly, pairedDetProd, variableMinor, ← mul_assoc, paddedMinorProd,
    prod_sigma,
    AlgHom.map_det, Matrix.map, ← Finset.prod_mul_distrib, negIndex, constantRows, regroupEquiv]
  -- What is left: the exponent of the negative minor, the positive minors of `paddedMinorProd`, and
  -- the determinants on `W♭`. The last two agree entry by entry.
  congr! 4
  · omega
  · rw [← Fin.prod_const]
    congr!
    aesop (add simp [Matrix.mul_apply, inclMatrix, posRowIndex, Matrix.one_apply])
  · simp [← ext_iff, Matrix.mul_apply]

-- Keeps definitional checks from unfolding `Finset.prod`.
seal Finset.prod in
/-- Let `D` be admissible data over the CM field `D.E`, `ϑ` a twist, `j` a lift index, `g` a point
of the adelic group `New.G D.E (D.signsW j)` of `W_j = D.spaceW j`, and `i : ChoiceIndex j` a
choice: a matrix `Λ = i.matrix` modulo `ϖ²` (`ϖ` the product of the chosen places), a class `h♭` of
the definite group `U(W♭)` and lists of rows. The left side integrates, over the unitary group of
the space `S = signedSpace` of signature `(2m, m)` modulo its rational points (`quotMeasure`), the
carrier `carrierForm`, the theta lift of 1 from `U(0, m)`, times the theta kernel `modKernel` of
`S` and `enlargedSpace j = W_j ⊕ (E^j)⁻ ⊕ E^{3m-j} ⊕ W♭` at `enlargedPoint j i g = (g, 1, 1, h♭)`.
Its characters are `υ ^ m`, with `υ = upsilonU1` the splitting character on the norm-one ideles,
and `carrierChar j`, which does not depend on `ϑ`. Its polynomial is the product of minors
`paddedMinorProd j` on the first three summands times the determinants on `W♭` formed with the rows
of `i`. Its finite datum, on matrices modulo `D.twistModulus ϑ 2 = ϖ² Q` (`Q` the product of the
places of `ϑ`), is `ψ^inv_Λ = invariantTraceChar ϑ j Λ`, the sum of the translates of the additive
character `ψ_Λ = traceChar Λ` under `GL_{3m}(𝒪/ϖ²)`. The function `choiceFn j i` is the same
integral with the datum `ψ_Λ` modulo `ϖ²`, and the left side is `#GL_{3m}(𝒪/ϖ²)` times it: the
carrier has full level, so every translate gives the same integral. -/
lemma integral_carrierForm_mul_eq_card_mul_choiceFn (i : ChoiceIndex j)
    (g : New.G D.E (D.signsW j)) :
    ∫ x : New.G D.E (1 ⊕ᵥ -1), carrierForm D.E D.m x *
      modKernel (signedSpace D.E (1 ⊕ᵥ -1)) (enlargedSpace j) (upsilonU1 ^ D.m) (carrierChar j)
        (D.twistModulus ϑ 2) (invariantTraceChar ϑ j i.matrix)
        (renameRowsCols inl id (paddedMinorProd j) * renameRowsCols inr id (pairedDetProd
          (fun (τ : InfinitePlace D.E) (r : D.FlatIndex) (c : Fin (2 * D.m)) ↦ .X ⟨τ, r, inl c⟩)
          fun (τ : InfinitePlace D.E) (k : Fin D.reducedHalfGap) ↦
            ((D.shortRows i.rowChoice).map (Φ τ)).submatrix (i.rowChoice.rows τ k) id))
        x (enlargedPoint j i g) ∂(signedSpace D.E (1 ⊕ᵥ -1)).quotMeasure =
      card (GL D.CarrierIndex (D.untwistedModulus 2).ResidueRing) * choiceFn j i g := by
  obtain ⟨h_rapid, h_level⟩ :=
    (carrierForm_mem_rapidOfLevel_and_isAdelicHol D.m_even
      (isTameFor_twistedChiMPow (c := 2) j ϑ)).1 1
  have h_full : HasLevel (carrierForm D.E D.m) (stdLevel D.E D.CarrierIndex) := fun k hk ↦ congrFun
    (h_level ⟨k, ((unitModulus D.E).mem_principalLevel_iff (by simp) ⟨k, hk⟩).2 (by subsingleton)⟩)
  exact integral_mul_modKernel_sum_translates _ (enlargedSpace j) (carrierChar_hasWeight j) h_rapid
    h_full (𝔪' := D.twistModulus ϑ 2) levelModulus_ideal_le (traceChar i.matrix) _ _

/-- The third exchange. There are a constant `C` and numbers `c ϑ`, one for each twist `ϑ`, with two
properties. First, `‖c ϑ‖ ^ 2` is `C` divided by `heckeValueProd j ϑ`, the product over the three
pairs `(ν, z)` of `exchangePair j` of the squared `L`-values at `1, …, z` of `(ν ϑ ^ (± 1))⁻¹`,
without the factors at the chosen places and `ϑ.Q`, and of powers of the norms of these places.
Second, for every choice `i : ChoiceIndex j` and every point `g` of the adelic unitary group of
`W_j = D.spaceW j`, the product of `c ϑ` and `thirdExchangeLeftSide ϑ j i g` is `choiceFn j i g`,
the integral of the carrier `carrierForm` against a theta kernel. -/
lemma exists_mul_thirdExchangeLeftSide_eq_choiceFn : ∃ (C : ℂ) (c : D.Twist → ℂ), ∀ ϑ : D.Twist,
    ‖c ϑ‖ ^ 2 = C / heckeValueProd j ϑ ∧
    ∀ (i : ChoiceIndex j) (g : New.G D.E (D.signsW j)),
      c ϑ * thirdExchangeLeftSide ϑ j i g = choiceFn j i g := by
  -- Apply `exists_mul_stdClassSum_eq_integral_modKernel` to `W = E^{3m} ⊕ W'`, `V″` and the space
  -- of signature `(2m, m)`, and sum it over the classes of `E^{3m}`;
  -- `exists_mul_stdClassSum_eq_carrierForm` turns the square kernel of the latter space into the
  -- carrier. The datum `ψ^inv_Λ` costs the constant `N`.
  have card_V : card (FirstFactorIndex j) = card D.CarrierIndex + 2 * D.mainPairPoint := by
    simp [↓card_rowIndex] -- `↓` counts the indices before they are unfolded
    grind [mainPairPoint]
  have h_large : 2 * card (Fin D.m) + 2 ≤ card (D.CarrierIndex ⊕ FirstFactorIndex j) := by
    grind [card_sum, card_fin]
  choose C₃ c₃ hc₃_norm h_third using
    exists_mul_stdClassSum_eq_integral_modKernel
      ((stdSpace D.E D.CarrierIndex).sum (enlargedSpace j)) (.refl _)
      (signedSpace D.E (1 ⊕ᵥ -1)) 1 (posEquiv j) (signOrder j) (signs_eq_blockSigns_signOrder j)
      card_V h_large (DetIndex j)
  choose C₁₂ c₁₂ hc₁₂_norm h_carrier using exists_mul_stdClassSum_eq_carrierForm D.E D.m_even
  have h_tame (ϑ : D.Twist) : Exchange.IsTameFor (D.twistModulus ϑ 2) (twistedChiMPow ϑ j) 0
    (twistedChiMod ϑ j) :=
    isTameFor_twistedChiMPow (c := 2) j ϑ
  have h_tame₃ (ϑ : D.Twist) := isTameFor_twistedChiMPow_mul_carrierChar ϑ j
  let N : ℕ := card (GL D.CarrierIndex (D.untwistedModulus 2).ResidueRing)
  refine ⟨C₃ * (C₁₂ / N ^ 2),
    fun ϑ ↦ c₃ (h_tame₃ ϑ) * (c₁₂ (h_tame ϑ) / N), fun ϑ ↦ ⟨?_, fun i g ↦ ?_⟩⟩
  · -- the three products of Hecke values are the three factors of `heckeValueProd`
    simp [← Complex.ofReal_pow, mul_pow, div_pow, heckeValueProd, places_twistModulus,
      exchangePair,
      hc₃_norm, hc₁₂_norm, signPoint, ← division_def, div_right_comm _ (_ * _), div_mul_div_comm]
    -- what is left are the characters of the three pairs
    rw [carrierChar_inv_div_twistedChiMPow_mul_upsilonU1_pow, twistedChiMPow_inv_mul_upsilonU1_pow,
      twistedChiMPow_mul_upsilonU1_pow]
  · have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 card_ne_zero
    suffices h_mul : c₃ (h_tame₃ ϑ) * c₁₂ (h_tame ϑ) * thirdExchangeLeftSide ϑ j i g =
        N * choiceFn j i g by
      simp only [← mul_div_assoc, div_mul_eq_mul_div, h_mul, mul_div_cancel_left₀ _ hN]
    rw [← integral_carrierForm_mul_eq_card_mul_choiceFn ϑ]
    refine mul_stdClassSum_eq_integral_mul_modKernel _ (enlargedSpace j) (h_tame ϑ).1
      (h_carrier (h_tame ϑ))
      (invariantTraceChar_mul ϑ j i.matrix) (K := thirdExchangeKernel ϑ j i g) fun Φ Ψ hΦΨ h' ↦ ?_
    rw [← matchedPoly_constantRows, eq_div_of_mul_eq'' (firstFactorChar_mul_upsilonU1_pow ϑ j)]
    exact h_third (h_tame₃ ϑ) (constantRows j i.rowChoice (D.shortRows i.rowChoice)) hΦΨ _ _

/-- The product datum `Ψ^×` at `x = (x' x″)`, with `x″` square: the datum `columnDatum` of the rows
`w` on the columns of `x″` at `W_j`, times `ψ^inv_Λ (x')` if the other columns of `x″` are those of
`1` (`FixesColsOff`), and `0` otherwise. -/
def productDatum {a : Type} [Fintype a]
    (w : Matrix a (FirstFactorIndex j) (D.untwistedModulus 2).ResidueRing)
    (Λ : Matrix D.CarrierIndex (FirstFactorIndex j) (D.untwistedModulus 2).ResidueRing)
    (x : Matrix (FirstFactorIndex j) (D.CarrierIndex ⊕ FirstFactorIndex j)
      (D.twistModulus ϑ 2).ResidueRing) : ℂ :=
  columnDatum (twistedChiMod ϑ j) (forgetTwist ϑ.toTameChar) w (.trans .inl .inl)
      (x.toCols₂.submatrix id (inl ∘ inl)) *
    if FixesColsOff (r := D.RowIndex) (.trans .inl .inl) x.toCols₂ then
      invariantTraceChar ϑ j Λ x.toCols₁ else 0

-- Keeps definitional checks from unfolding `Finset.univ`.
seal Finset.univ in
/-- Let `D` be admissible data, `ϑ` a twist, `j` a lift index, `W_j = D.spaceW j`, and `V″` the
standard definite space on `FirstFactorIndex j`, which contains the indices of `W_j` through
`.trans .inl .inl`. Let `w` be a finite family of rows modulo `ϖ²` (`ϖ` the product of the chosen
places) indexed by `FirstFactorIndex j`, and `i` a choice: a matrix `Λ = i.matrix` modulo `ϖ²`, a
class `h♭` and lists of rows. On the left, `thirdExchangeKernel` is the theta kernel of
`(W, V″)`, `W = E^{3m} ⊕ enlargedSpace j`, at `((h', g, 1, 1, h♭), h)`. Its datum `productDatum` at
`(x' x″)` is `columnDatum` of `w`, a function of the columns of `x″` at `W_j`, times
`invariantTraceChar ϑ j Λ x'` if the other columns of `x″` are those of `1`, and `0` otherwise.
It is summed over the classes `h'` of the finite adelic group `Gf` of `E^{3m}`, at the integral
level `stdLevel`, against `carrierCoeff`, a class sum of theta kernels of `(E^m, E^{3m})`. The
result is one theta kernel of `(W_j, V″)` at `(g, h)`. Its characters are `charW` of the descent
pair `D.descentPair ϑ j` (the data of the `j`-th lift) and `firstFactorChar ϑ j` (the character of
that lift times a power of the splitting character), its datum is `columnDatum` of `w`, and its
polynomial is `letterPoly` of the vector `leftSideSeries ϑ j i h` of the Weyl module with column
counts `colsPlus`. The coordinates of this vector are formed from the kernels at `h` of the summands
of `W` other than `W_j`. -/
lemma stdClassSum_thirdExchangeKernel_productDatum {a : Type} [Fintype a]
    (w : Matrix a (FirstFactorIndex j) (D.untwistedModulus 2).ResidueRing) (i : ChoiceIndex j)
    (g : New.G D.E (D.signsW j)) (h : Gf D.E (FirstFactorIndex j)) :
    stdClassSum (stdLevel D.E D.CarrierIndex) (fun h' : Gf D.E D.CarrierIndex ↦ carrierCoeff D.m
      (twistedChiMPow ϑ j) h' * thirdExchangeKernel ϑ j i g (productDatum ϑ j w i.matrix) h' h) =
    modKernelStdSpace (D.spaceW j) (D.descentPair ϑ j).charW (firstFactorChar ϑ j)
      (D.twistModulus ϑ 2)
      (columnDatum (twistedChiMod ϑ j) (forgetTwist ϑ.toTameChar) w (.trans .inl .inl))
      (letterPoly (D.signsW j) (untwistedDescentPair j).numbering 1
        (untwistedDescentPair j).colsPlus
        (leftSideSeries ϑ j i h)) g h := by
  -- Expand `leftSideSeries` in coordinates. Each term on the right is then one kernel on the index
  -- set of `W_j ⊕ (E^j)⁻ ⊕ W^add`, with `W^add` the definite space on `AddedIndex j`, and
  -- `regroupEquiv j` relabels the left side to match.
  rw [pi_eq_sum_univ' (leftSideSeries ϑ j i h), modKernelStdSpace, ← modKernelBilin_apply]
  simp [thirdExchangeKernel, ← firstFactorChar_mul_upsilonU1_pow, leftSideSeries, modKernelStdSpace,
    mul_classSum,
    ← classSum_sum, mul_left_comm (modKernel ..), mul_assoc, -mul_ite, ← Finset.mul_sum,
    mul_comm (modKernel (.sum ..) ..), ← modKernel_sum_left, Pi.single_apply]
  congr! with h'
  have h_sign : ((1 : D.CarrierIndex → ℤˣ) ⊕ᵥ (padSigns j ⊕ᵥ 1)) ∘ regroupEquiv j =
      D.signsW j ⊕ᵥ (-1 ⊕ᵥ 1) := by
    ext1 (_ | _ | _ | _ | _) <;> rfl
  -- `erw` is needed: the kernels are stated on index types that agree only after unfolding
  erw [← modKernel_reindex (regroupEquiv ..).symm h_sign (.refl _) rfl,
    ← map_sum ((modKernelBilin ..) _), modKernelBilin_apply]
  -- compare the two kernels argument by argument
  congr! 1
  · -- the first spaces
    ext1
    simp [GeneralLinearGroup.ext_iff, Space.reindex, Space.sum, regroupEquiv, Matrix.one_apply]
  · -- the first characters: `W_j` has `m - j` negative signs, and `υ ^ m = υ ^ (m - j) * υ ^ j`
    grind [pow_sub_mul_pow, negCount_signsW, descentPair]
  · -- the finite data
    unfold productDatum
    congr! 2
    simp [addedDatum, invariantTraceChar, ← ite_and, regroupEquiv]
    congr
    simp [← ext_iff, Matrix.mul_apply, inclMatrix, forall_and, -sum_sum_type, Matrix.one_apply]
    tauto
  · -- the polynomials: the stacked determinants are the sum over the coordinates of
    -- `paddedMinorProd`
    simpa [signOrder, Prod.map_comp_map, ← comp_assoc] using!
      renameRowsCols_stackedDetProd_eq_sum j _ inl (inr ∘ inr)
  · -- the points, entry by entry
    apply G.ext_adeleMatrix
    simp [← ext_iff, Prod.ext_iff, funext_iff, New.U.sum, regroupEquiv, Matrix.one_apply]
    aesop (add simp regroupEquiv)

-- Keeps definitional checks from unfolding `Finset.prod`.
seal Finset.prod in
/-- Let `D` be admissible data, `ϑ` a twist, `j` a lift index, `W_j = D.spaceW j`, and `V″` the
standard definite space on `FirstFactorIndex j`, which contains the indices of `W_j`. Let `i` be a
choice with matrix `Λ = i.matrix` modulo `ϖ²` (`ϖ` the product of the chosen places), and `w` rows
modulo `ϖ²` of which those of `Λ` are combinations: `u * w = Λ`. Both sides are class sums
`stdClassSum` over `U(V″)` of `thirdExchangeKernel`, the theta kernel of
`(E^{3m} ⊕ enlargedSpace j, V″)` at a point formed from `h'`, `g` and `i`. On the left the level is
the integral level `stdLevel` and the datum is `(x' x″) ↦ χ' (det x″) ψ^inv_Λ (x″⁻¹ x')`, where
`χ' = twistedChiMod ϑ j` is a character of the residue ring and `ψ^inv_Λ = invariantTraceChar ϑ j Λ`
is the sum of the translates of the additive character `traceChar Λ` under `GL_{3m}(𝒪/ϖ²)`. On the
right the level is `rowFixingLevel`, cut out by the matrices that are `1` in the columns outside
`W_j` and fix `w`, and the datum `productDatum` is `columnDatum` of `w` on the columns of `x″` at
`W_j` times `ψ^inv_Λ (x')` if the other columns of `x″` are those of `1`, and `0` otherwise. -/
lemma stdClassSum_thirdExchangeKernel_eq_productDatum {a : Type} [Fintype a]
    {w : Matrix a (FirstFactorIndex j) (D.untwistedModulus 2).ResidueRing} {i : ChoiceIndex j}
    {u : Matrix D.CarrierIndex a (D.untwistedModulus 2).ResidueRing} (hw : u * w = i.matrix)
    (g : New.G D.E (D.signsW j)) (h' : Gf D.E D.CarrierIndex) :
    stdClassSum (stdLevel D.E (FirstFactorIndex j)) (thirdExchangeKernel ϑ j i g
      (fun x : Matrix (FirstFactorIndex j) (D.CarrierIndex ⊕ FirstFactorIndex j)
        (D.twistModulus ϑ 2).ResidueRing ↦
        twistedChiMod ϑ j x.toCols₂.det *
          invariantTraceChar ϑ j i.matrix (x.toCols₂⁻¹ * x.toCols₁)) h') =
    stdClassSum (rowFixingLevel (D.levelPlaces ϑ) w (r := D.RowIndex) (.trans .inl .inl))
      (thirdExchangeKernel ϑ j i g (productDatum ϑ j w i.matrix) h') := by
  -- `ψ^inv_Λ` is invariant under the matrices that fix the rows `w`, hence those of `Λ`.
  have h_inv (A : GL (FirstFactorIndex j) (D.twistModulus ϑ 2).ResidueRing)
      (hA : A ∈ rowStabilizer (forgetTwist ϑ.toTameChar) w (r := D.RowIndex) (.trans .inl .inl))
      (x : Matrix (FirstFactorIndex j) D.CarrierIndex (D.twistModulus ϑ 2).ResidueRing) :
      invariantTraceChar ϑ j i.matrix (A.val * x) = invariantTraceChar ϑ j i.matrix x := by
    simp [invariantTraceChar, traceChar, Matrix.mul_assoc, trace_mul_comm (A.val.map _), ← hw, hA.2]
  refine (stdClassSum_rowStabilizer_eq (isTameFor_twistedChiMPow_mul_carrierChar ϑ j) ?_
    (forgetTwist ϑ.toTameChar) w _ h_inv).symm
  rw [signs_eq_blockSigns_signOrder]
  -- the real group of `V″` fixes the polynomial of the kernel
  simpa using! realPairWeil_stackedDetProd (signOrder j) _ rfl (constantRows j i.rowChoice _) 1

/-- If `u * w` is the matrix `Λ` of `i`, the left side of the third exchange is the theta
series `kernelClassSum` on `U(W_j)`: the class sum, at the level cut out by the rows `w`, of kernels
with the vectors `leftSideSeries ϑ j i h`. -/
lemma thirdExchangeLeftSide_eq_kernelClassSum {a : Type} [Fintype a]
    {w : Matrix a (FirstFactorIndex j) (D.untwistedModulus 2).ResidueRing} {i : ChoiceIndex j}
    {u : Matrix D.CarrierIndex a (D.untwistedModulus 2).ResidueRing} (hw : u * w = i.matrix)
    (g : New.G D.E (D.signsW j)) :
    thirdExchangeLeftSide ϑ j i g = kernelClassSum (D.descentPair ϑ j) (firstFactorChar ϑ j) w
      (.trans .inl .inl)
      (leftSideSeries ϑ j i) g := by
  simp_rw [thirdExchangeLeftSide, stdClassSum_thirdExchangeKernel_eq_productDatum ϑ j hw,
    mul_classSum,
    classSum_comm (G := Gf D.E D.CarrierIndex), stdClassSum_thirdExchangeKernel_productDatum]
  rfl

end LineIdentity

/-!
## Level and holomorphy of 𝖥_i

Conventions: `New.Data.spaceW j` is the space W_j, `New.Data.orderW j` its order with positive
vectors first, `New.Data.conjHolomorphicWeight j` the weight of the parameter −`New.Data.paramW`,
and `New.Data.kernelWeight j` the weight of the complementary theta kernel.
-/

section NaturalFormHolomorphic

open Matrix Rows Function
open NumberField (InfinitePlace)
variable {P : Parameters} {D : Data P} {j : D.LiftIndex}

/-- A good form `F` on `W_j`, as a function on `U(W_j)`, lies in `New.Rows.rapidOfLevel` for every
level `a` divisible by `New.Data.piM`: it is automorphic of level `a` and rapidly decreasing. -/
lemma goodForms_mem_rapidOfLevel (F : D.goodForms (D.spaceW j))
    {a : NumberField.RingOfIntegers D.E} (ha : D.piM ∣ a) :
    (F : New.G D.E (D.signsW j) → ℂ) ∈ rapidOfLevel (D.spaceW j) a := by
  obtain ⟨⟨⟨f, hf_form⟩, hf_principal⟩, -⟩ := F
  have h_level : HasLevel f D.chosenLevel := Space.mem_levelSpace_formRep_iff.1 hf_principal
  exact ⟨hf_form.mem_rapidFunctions D.isCuspKernel_typeKernel_paramW,
    fun k ↦ funext (h_level k (D.principalLevel_le_chosenLevel ha k.prop))⟩

/-- Let `D` be admissible data, `j` a lift index, `W_j = D.spaceW j` with signs `D.signsW j`, and
`V″` the standard definite space on `FirstFactorIndex j`. The data of the `j`-th lift at the trivial
twist, `untwistedDescentPair j`, number the basis of `W_j` (`numbering`) and give at each infinite
place `τ` a partition `μ⁺` with `colsPlus τ h` columns of height `h`. Let `ξ` be a vector of the
Weyl module of weight `μ⁺`, in the coordinates `WeylIndexFamily`. The polynomial `letterPoly … ξ` is
that of `ξ` with the variable `(τ, i, h)` replaced by the sum of the variables `(τ, i, a)` over the
basis vectors `a` of `W_j` of sign `+1` and number `h`. Its vector `v = Fock.polyVector` in the Fock
space of `(W_j, V″)`, whose coordinates have the product signs `realSigns (homSigns …)`, lies in
`holomorphicData`: every matrix coefficient `x ↦ ℓ (Ω (x, 1) v)` on the real group of `W_j` is
holomorphic for the order `orderW j` of the basis, of weight `u - u°`. Here
`u = conjHolomorphicWeight j` is the weight of the conjugates of good forms, `u° = kernelWeight j`
that of the complementary theta kernel, and `Ω = realPairWeil γ e` is the real Weil representation
of the pair with the weights `γ τ = negCount (D.signsW j)`, the number of negative signs of `W_j`,
and `e τ = firstFactorCharExp j - D.liftWeight j τ`, the weight of `firstFactorChar` at `τ`. -/
lemma polyVector_letterPoly_mem_holomorphicData (ξ : WeylIndexFamily
    (fun _ : InfinitePlace D.E ↦ FirstFactorIndex j) (untwistedDescentPair j).colsPlus → ℂ) :
    Fock.polyVector (realSigns D.E (homSigns (D.signsW j) (1 : FirstFactorIndex j → ℤˣ)))
        (letterPoly (D.signsW j) (untwistedDescentPair j).numbering 1
          (untwistedDescentPair j).colsPlus ξ) ∈
      holomorphicData (D.signsW j) 1 (orderW j) (conjHolomorphicWeight j - kernelWeight j)
        (fun _ : InfinitePlace D.E ↦ Exchange.negCount (D.signsW j))
        fun τ : InfinitePlace D.E ↦ firstFactorCharExp j + -D.liftWeight j τ := by
  -- The definite group acts on these polynomials by a linear substitution, so their Fock vectors
  -- are holomorphic as soon as that of the highest vector is.
  have h_fit : (D.descentPair TameChar.one j).FitsParams D.paramW :=
    D.fitsParams_descentPair TameChar.one j
  have h_inj : Injective (D.paramW 1) := (h_fit.paramsCorrespond 1).hasGap_left.injective
  simp only [Pi.sub_def, conjHolomorphicWeight_eq_add_kernelWeight, add_sub_cancel_right]
  refine mem_holomorphicData_of_highestVector (e' := 0) (Fock.polyVector _ ∘ₗ letterPoly _ _ _ _)
    (by simp [Injective, Fin.val_inj]) (fun y η ↦ ?_)
    (letterPoly_highestVector_mem_holomorphicData isPosFirstOrder_orderW (paramW_lt_of_orderW_lt 1)
      h_inj
      (h_fit.numbering_eq 1) _ h_fit.colsPlus_eq_zero).2
  -- `erw` sees through the composite linear map
  erw [realPairWeil_fockLetters, star_mulVec]
  simp [letterPoly, weylRep, ← mulVec_transpose, comp_def, conjTranspose_transpose]

/-- The function `𝖥_i = choiceFn j i` on `U(W_j)` is a multiple of the theta series
`kernelClassSum` for the trivial twist, at the level cut out by the rows of `Λ = i.matrix`. -/
lemma exists_choiceFn_eq_mul_kernelClassSum (i : ChoiceIndex j) :
    ∃ c : ℂ, choiceFn j i = fun g : New.G D.E (D.signsW j) ↦
      c * kernelClassSum (D.descentPair (1 : D.Twist) j) (firstFactorChar (1 : D.Twist) j) i.matrix
        (.trans .inl .inl) (leftSideSeries (1 : D.Twist) j i) g := by
  obtain ⟨C, c, h_third⟩ := exists_mul_thirdExchangeLeftSide_eq_choiceFn j
  refine ⟨c 1, funext fun g ↦ ?_⟩
  rw [← (h_third 1).2 i g, thirdExchangeLeftSide_eq_kernelClassSum 1 j i.matrix.one_mul]

/-- For a good form `F` on `W_j`, the product of `F` with the function `choiceFn j i` on `U(W_j)`
is automorphic of level `D.piM ^ 2` and rapidly decreasing. -/
lemma mul_choiceFn_mem_rapidOfLevel (F : D.goodForms (D.spaceW j)) (i : ChoiceIndex j) :
    (F : New.G D.E (D.signsW j) → ℂ) * choiceFn j i ∈ rapidOfLevel (D.spaceW j) (D.piM ^ 2) := by
  -- `𝖥_i` is a finite combination of kernels of `(W_j, V″)` with data modulo `ϖ²`.
  obtain ⟨c, h_series⟩ := exists_choiceFn_eq_mul_kernelClassSum i
  simp only [h_series, kernelClassSum, classSum, finsum_eq_sum_of_fintype,
    Rat.smul_def, Finset.mul_sum, ← mul_assoc]
  refine mul_sum_mem_rapidOfLevel fun _ ↦ mul_modKernel_mem_rapidOfLevel
    D.ideal_untwistedModulus_eq_span (fun v hv ↦ ?_)
    (goodForms_mem_rapidOfLevel F (dvd_pow_self D.piM two_ne_zero)) _ _ _
  -- The tame part of the character of the kernels is trivial off the modulus.
  exact (D.descentPair (1 : D.Twist) j).tame_eq_one v (places_levelModulus.ge.mt hv)

/-- The function `choiceFn j i` on `U(W_j)` is holomorphic for the order `orderW j`, of weight
`u″ = u - u°`. Here `u = conjHolomorphicWeight j` and `u° = kernelWeight j`. -/
lemma isAdelicHol_choiceFn (i : ChoiceIndex j) :
    IsAdelicHol (orderW j) (conjHolomorphicWeight j - kernelWeight j) (choiceFn j i) := by
  -- `𝖥_i` is a finite combination of kernels of `(W_j, V″)` with polynomials in the positive
  -- letters, and each of these kernels is holomorphic.
  obtain ⟨c, h_series⟩ := exists_choiceFn_eq_mul_kernelClassSum i
  simp only [h_series, kernelClassSum, classSum, finsum_eq_sum_of_fintype,
    Rat.smul_def, Finset.mul_sum, ← mul_assoc]
  exact fun g ↦ .sum _ fun _ ↦ isAdelicHol_pairTheta (polyVector_letterPoly_mem_holomorphicData _) g

end NaturalFormHolomorphic

end New.Data

end
