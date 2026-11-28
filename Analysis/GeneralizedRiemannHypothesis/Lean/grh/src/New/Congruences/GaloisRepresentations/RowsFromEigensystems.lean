import New.Congruences.GaloisRepresentations.RowsAndColumnsFromLabels
import New.OneLift.ComparisonOperator.ExchangeData
import New.Spanning.SecondMoment.SpanningTheorem

/-!
# Main summand conditions on Hodge–Tate jumps and existence of main summands for Hecke eigensystems

This file passes from Hecke eigensystems of forms to the main summands (`New.Selmer.IsMainSummand`)
that enter the Selmer groups. The Hodge–Tate jumps occurring for the main summands of the descent
pairs (W_j, V_j) satisfy the numerical conditions `New.Selmer.IsMainSummandWeights`. Each such jump
is small or near `∓ w_j`, and few jumps are small. At a pair of conjugate embeddings at most
rank-many jumps are negative.

## Main definitions and results

* `New.Selmer.isMainSummandWeights_mainPair`: the single jump of a main pair obeys
  `New.Selmer.IsMainSummandWeights` in rank `1`.
* `New.Selmer.isMainSummandWeights_descentPair`: the jumps built from `New.Data.targetParameter` and
  `New.Data.liftWeight` obey `New.Selmer.IsMainSummandWeights` in rank `D.r`.
* `New.Selmer.exists_isMainSummand_of_isRepOfType`: take a representation `R` with admissible labels
  whose shifted jumps obey `New.Selmer.IsMainSummandWeights`. Assume its traces are limits of the
  values of `b`. Then it gives a representation `T` with `New.Selmer.IsMainSummand O b T`.
* `New.Selmer.exists_isMainSummand_descentPair`: a Hecke eigensystem of a good form on
  `D.spaceW D.m` gives a main summand for each descent pair of the trivial twist.

Notions from other files:
* `New.Selmer.IsMainSummandWeights D r t J`: numerical conditions on the jumps `J σ`, a multiset of
  integers for each complex embedding `σ` of the CM field `D.E`.
* `New.Selmer.IsMainSummand O z T`: `T` is like a main summand, and for every twist of the pair `O`
  by a tame character `ϑ` the normalised representation attached to a lift of the system `z` has the
  trace of `T` twisted by `ϑ⁻¹` plus a string of powers of the inverse cyclotomic character.
* `New.Selmer.IsLiftSetting O c ϑ`: the descent pair `O` fits the twist `ϑ` and the labels `c` are
  admissible.
* `New.Selmer.IsRepOfType O k J c S R`: `R` is a conjugate self-dual representation of level `S`
  (`New.Selmer.IsConjSelfDualOfLevel`) with jumps `J`, and inertia at the chosen places acts through
  the roots of the labels `c`.
* `New.Data.goodForms`, `New.Data.eigenPart`: the image of the idempotent e₀ on forms of principal
  level at the chosen places, and the forms on which the Hecke operators act by given scalars.

## Relation to the literature

The Galois representation of each eigenform in a space of theta lifts has the trace of a twisted
block, which does not depend on the twist, plus a string of powers of the inverse cyclotomic
character. This shape follows from the unramified theta correspondence. Related work: Rallis,
Langlands' functoriality and the Weil representation, 1982; Khare–Larsen–Savin, Functoriality and
the inverse Galois problem, 2008; Arias-de-Reyna–Dieulefait–Shin–Wiese, Compatible systems of
symplectic Galois representations III, 2015.
-/

namespace New.Selmer

/-! ## The jumps of descent pairs and of main pairs satisfy the conditions on a main summand -/

section RowJumps

open NumberField Multiset Data Int

variable {P : Parameters} {D : Data P}

/-- The sign `cmSign` of a complex embedding (`1` on the CM type, `-1` off it) changes under complex
conjugation. -/
@[simp]
lemma cmSign_star (σ : D.E →+* ℂ) : cmSign (E := D.E) (star σ) = -cmSign σ := by
  grind [cmSign, neg_neg, Φ_mk_eq_or_star_eq, InfinitePlace.mk_eq_iff]

/-- Let `D` be admissible data (`Data P`) over the CM field `D.E`, with rank `r = D.r`, number of
lifts `m = D.m`, `k = D.k = r + 1 - m` and `t = D.t = 5 r`. At a complex embedding `σ` of `D.E`,
over the infinite place `v`, the `q`-th jump (Hodge–Tate weight) of the `j`-th descent pair is the
integer `u = t / 2 - ε (λ_q + w_j)`. Here `t / 2` is integer division, `ε = cmSign σ` is `1` on the
CM type and `-1` off it, `λ_q = D.targetParameter v q` is the fixed parameter of the rank `r` group
and `w_j = D.liftWeight j v` is minus the weight of the character of the `j`-th lift. For
`q + 1 < k` the jump is high: `|ε u + w_j| ≤ t`. -/
lemma abs_descentPair_weight_add_liftWeight_le (j : ℕ) (σ : D.E →+* ℂ) {q : ℕ} (hq : q + 1 < D.k)
    {u : ℤ}
    (hu : u = D.t / 2 -
      cmSign σ * (D.targetParameter (InfinitePlace.mk σ) q + D.liftWeight j (InfinitePlace.mk σ))) :
    |cmSign σ * u + D.liftWeight j (InfinitePlace.mk σ)| ≤ D.t := by
  -- The left side is `|± t / 2 - targetParameter q|`, with `|targetParameter q| ≤ k / 2` and
  -- `k ≤ t`.
  have hk_le : D.k ≤ D.t := D.k_le_r.trans (Nat.le_of_add_right_le D.r_add_six_le_t)
  have hσ : (cmSign σ : ℤ) = 1 ∨ (cmSign σ : ℤ) = -1 := Int.isUnit_iff.1 (cmSign σ).isUnit
  rw [targetParameter_eq, ite_eq_left hq] at hu
  grind

/-- Let `D` be admissible data over the CM field `D.E`, with `r = D.r`, `m = D.m`, `k = D.k` and
`Δ = D.gap`. Let `1 ≤ j ≤ m` (`D.LiftIndex`). At a complex embedding `σ` over the infinite place
`v`, the `q`-th jump (Hodge–Tate weight) of the `j`-th descent pair is the integer
`u = t / 2 - ε (λ_q + w_j)`, with `t = D.t`, `ε = cmSign σ = ±1` (`1` on the CM type),
`λ_q = D.targetParameter v q` and `w_j = D.liftWeight j v`, minus the weight of the character of
the `j`-th lift. For `k ≤ q + 1 ≤ r` the jump is low: `Δ / 4 ≤ |u| ≤ 2 m Δ`. -/
lemma le_natAbs_descentPair_jump_and_le {j : ℕ} (hj : j ∈ D.LiftIndex) (σ : D.E →+* ℂ) {q : ℕ}
    (hq_ge : D.k ≤ q + 1) (hq_lt : q < D.r) {u : ℤ}
    (hu : u = D.t / 2 -
      cmSign σ * (D.targetParameter (InfinitePlace.mk σ) q + D.liftWeight j (InfinitePlace.mk σ))) :
    D.gap ≤ 4 * u.natAbs ∧ u.natAbs ≤ 2 * D.m * D.gap := by
  -- With `i = q + 2 - k` in `[1, m]` we have `targetParameter q + w_j = (j - i + 1 / 2) Δ`, of
  -- modulus in `[Δ / 2, m Δ]`, and `t / 2 ≤ Δ / 4`.
  obtain ⟨hj_pos, hj_le⟩ : 1 ≤ j ∧ j ≤ D.m := hj
  obtain ⟨i, hi⟩ : ∃ i : ℕ, q + 2 - D.k = i := ⟨_, rfl⟩
  have h_rank : D.r + 1 = D.k + D.m := D.r_add_one
  have ht_le : D.k + D.t + 1 ≤ D.halfGap := D.k_add_t_add_one_le_halfGap
  have h_gap : D.gap = 2 * D.halfGap := rfl
  have hi_bound : D.gap ≤ i * D.gap ∧ i * D.gap ≤ D.m * D.gap :=
    ⟨Nat.le_mul_of_pos_left _ (by omega), Nat.mul_le_mul_right _ (by omega)⟩
  have hj_bound : D.gap ≤ j * D.gap ∧ j * D.gap ≤ D.m * D.gap :=
    ⟨Nat.le_mul_of_pos_left _ hj_pos, by gcongr⟩
  have h_apart : i * D.gap ≤ j * D.gap ∨ (j + 1) * D.gap ≤ i * D.gap :=
    (le_or_gt i j).imp (Nat.mul_le_mul_right _) (Nat.mul_le_mul_right _)
  rw [targetParameter_eq, ite_eq_right hq_ge.not_gt, hi, liftWeight_eq, liftWeight_eq] at hu
  rw [add_one_mul] at h_apart
  rw [mul_assoc]
  obtain hσ | hσ : (cmSign σ : ℤ) = 1 ∨ (cmSign σ : ℤ) = -1 := Int.isUnit_iff.1 (cmSign σ).isUnit
  all_goals
    rw [hσ] at hu
    omega

/-- Let `D` be admissible data, `1 ≤ j ≤ m = D.m` and `σ` a complex embedding of the CM field `D.E`
over the infinite place `v`. The jumps (Hodge–Tate weights) of the `j`-th descent pair at `σ` are
the `r = D.r` integers `t / 2 - ε (λ_q + w_j)`, `q < r`, where `t = D.t`, `ε = cmSign σ = ±1`,
`λ_q = D.targetParameter v q` and `w_j = D.liftWeight j v` is minus the weight of the character of
the `j`-th lift. If `2 m Δ ≤ B` and `B + t < w_j`, with `Δ = D.gap`, then exactly `m` of them have
modulus at most `B`. -/
lemma countP_low_weights_descentPair {j : ℕ} (hj : j ∈ D.LiftIndex) (σ : D.E →+* ℂ) {B : ℕ}
    (hB_ge : 2 * D.m * D.gap ≤ B) (hB_lt : B + D.t < D.liftWeight j (InfinitePlace.mk σ)) :
    countP (fun u : ℤ ↦ u.natAbs ≤ B) ((Multiset.range D.r).map fun q : ℕ ↦ (D.t / 2 -
      cmSign σ * (D.targetParameter (InfinitePlace.mk σ) q + D.liftWeight j (InfinitePlace.mk σ)) :
        ℤ)) = D.m := by
  set v : D.Φ := InfinitePlace.mk σ
  have h_iff (q : ℕ) (hq : q ∈ Multiset.range D.r) :
      (D.t / 2 - cmSign σ * (D.targetParameter v q + D.liftWeight j v) : ℤ).natAbs ≤ B ↔
        D.k ≤ q + 1 := by
    refine ⟨fun h_le ↦ le_of_not_gt fun h_lt ↦ ?_, fun h_ge ↦ ?_⟩
    · exact (lt_natAbs_of_abs_add_liftWeight_le hB_lt
      (abs_descentPair_weight_add_liftWeight_le j σ h_lt rfl)).not_ge h_le
    · exact (le_natAbs_descentPair_jump_and_le hj σ h_ge (mem_range.1 hq) rfl).2.trans hB_ge
  have h_count (N : ℕ) :
      card ((Multiset.range N).filter fun q : ℕ ↦ D.k ≤ q + 1) = N + 1 - D.k := by
    induction N with
    | zero => simpa using (Nat.sub_eq_zero_of_le D.k_pos).symm
    | succ N ih => grind [range_succ, filter_cons_of_pos, filter_cons_of_neg, card_cons]
  rw [countP_map, filter_congr h_iff, h_count, D.r_add_one, Nat.add_sub_cancel_left]

/-- Let `1 ≤ j ≤ m` (`D.LiftIndex`, `m = D.m`). At a complex embedding `σ`, over the infinite place
`v`, take as jumps (Hodge–Tate weights) the `r = D.r` integers `t / 2 - ε (λ_q + w_j)`, `q < r`, of
the `j`-th descent pair. Here `t = D.t`, `ε = cmSign σ` is `1` on the CM type and `-1` off it,
`λ_q = D.targetParameter v q` is the fixed parameter of the rank `r` group, and
`w_j = D.liftWeight j v` is minus the weight of the character of the lift. These jumps satisfy
`IsMainSummandWeights D r t`. -/
lemma isMainSummandWeights_descentPair {j : ℕ} (hj : j ∈ D.LiftIndex) :
    IsMainSummandWeights D D.r D.t fun σ : D.E →+* ℂ ↦ (Multiset.range D.r).map fun q : ℕ ↦
      D.t / 2 -
      cmSign σ * (D.targetParameter (InfinitePlace.mk σ) q + D.liftWeight j
        (InfinitePlace.mk σ)) := by
  refine
    { rank_mem := ⟨D.nat_le_of_hasLogBound, le_rfl⟩
      t_le := le_rfl
      low_or_high := ⟨j, hj.2, fun σ u hu ↦ ?_⟩
      card_small_le σ := ?_
      card_neg_le σ := ?_ }
  · obtain ⟨q, hq, rfl⟩ := mem_map.1 hu
    exact (le_or_gt D.k (q + 1)).imp (le_natAbs_descentPair_jump_and_le hj σ · (mem_range.1 hq) rfl)
      (abs_descentPair_weight_add_liftWeight_le j σ · rfl)
  · rw [countP_low_weights_descentPair hj σ D.nat_le_of_hasLogBound D.nat_lt_of_hasLogBound,
    mul_comm]
    exact Nat.mul_le_mul_right D.m D.k_le_r
  · -- the `q`-th jumps at `σ` and at its conjugate have sum `2 (t/2) ≥ 0`, so at most one is
    -- negative
    rw [InfinitePlace.mk_conjugate_eq σ, cmSign_star, Units.val_neg]
    induction D.r with
    | zero => simp
    | succ N ih => grind [range_succ, map_cons, countP_cons]

/-- Let `p` be a critical pair of the data `D`: an integer `z = p.z` and a character of `U(1)` of
weight `-c`, with `c = p.negWeight`. Let it be a main pair for `j` (`IsMainPair`): in particular
`m < z ≤ r` and `w_j + r - t ≤ c ≤ w_j`, where `m = D.m`, `r = D.r`, `t = D.t = 5 r` and
`w_j = D.liftWeight j` is minus the weight of the character of the `j`-th lift. At a complex
embedding `σ` over the infinite place `v`, with `ε = cmSign σ = ±1`, the jump (Hodge–Tate weight)
of `p` is `u = z - 1 - ε c v`. It is high: `|ε u + w_j v| ≤ t`. -/
lemma abs_mainPair_weight_add_liftWeight_le {p : D.CriticalPair} {j : ℕ} (hp : p.IsMainPair j)
    (σ : D.E →+* ℂ) {u : ℤ} (hu : u = p.z - 1 - (cmSign σ : ℤ) * p.negWeight (InfinitePlace.mk σ)) :
    |cmSign σ * u + D.liftWeight j (InfinitePlace.mk σ)| ≤ D.t := by
  obtain ⟨hz_gt : D.m < p.z, hz_le : p.z ≤ D.r⟩ := hp.z_mem
  set v : D.Φ := InfinitePlace.mk σ
  have hc_le : p.negWeight v ≤ D.liftWeight j v := hp.negWeight_le v
  have hc_ge : D.liftWeight j v + D.r ≤ p.negWeight v + D.t := hp.le_negWeight v
  have ht : D.t = 5 * D.r := rfl
  rw [abs_le]
  obtain hσ | hσ : (cmSign σ : ℤ) = 1 ∨ (cmSign σ : ℤ) = -1 := Int.isUnit_iff.1 (cmSign σ).isUnit
  all_goals
    rw [hσ] at hu ⊢
    omega

/-- Let `p` be a main pair for `j` (`IsMainPair`): an integer `z = p.z` and a character of `U(1)` of
weight `-c`, `c = p.negWeight`, with in particular `m < z ≤ r` and `w_j + r - t ≤ c ≤ w_j`, where
`w_j = D.liftWeight j` is minus the weight of the character of the `j`-th lift. At a complex
embedding `σ` over the infinite place `v`, take the single jump (Hodge–Tate weight)
`z - 1 - ε c v`, with `ε = cmSign σ` equal to `1` on the CM type and `-1` off it. These jumps
satisfy `IsMainSummandWeights D 1 (2 z - 1)`, the conditions on the jumps of a rank one
representation that is paired with `2 z - 1` consecutive powers of the inverse cyclotomic character:
each is low or within `t` of `-ε w_j`, few are small, and at most one at `σ` and its conjugate is
negative. -/
lemma isMainSummandWeights_mainPair {p : D.CriticalPair} {j : ℕ} (hp : p.IsMainPair j) :
    IsMainSummandWeights D 1 (2 * p.z - 1) fun σ : D.E →+* ℂ ↦
      {(p.z - 1 - cmSign σ * p.negWeight (InfinitePlace.mk σ) : ℤ)} := by
  have ht : D.t = 5 * D.r := rfl
  obtain ⟨hz_gt : D.m < p.z, hz_le : p.z ≤ D.r⟩ := hp.z_mem
  refine
    { rank_mem := ⟨le_rfl, by omega⟩
      t_le := by omega
      low_or_high :=
        ⟨j, hp.j_mem.2, fun σ u hu ↦ .inr
          (abs_mainPair_weight_add_liftWeight_le hp σ (mem_singleton.1 hu))⟩
      card_small_le σ := ?_
      card_neg_le σ := ?_ }
  · have hw_large : 2 * D.halfGap ^ 2 + D.t < D.liftWeight j (InfinitePlace.mk σ) :=
      D.nat_lt_of_hasLogBound
    have h_large : 2 * D.halfGap ^ 2 < (p.z - 1 - cmSign σ * p.negWeight (InfinitePlace.mk σ) :
      ℤ).natAbs :=
      lt_natAbs_of_abs_add_liftWeight_le hw_large (abs_mainPair_weight_add_liftWeight_le hp σ rfl)
    simp [countP_eq_zero.2, h_large]
  · -- The jumps at `σ` and at its conjugate have the sum `2 (z - 1) ≥ 0`.
    rw [InfinitePlace.mk_conjugate_eq σ, cmSign_star, Units.val_neg, ← cons_zero, ← cons_zero]
    grind [countP_cons, countP_zero]

end RowJumps

/-! ## One main summand for all twists, and main summands from eigensystems of good forms -/

section RowsExist

open Matrix Polynomial Fintype Filter Data GaloisRep AutChar LinearMap Space Subtype
  SiegelWeil Finset

variable {P : Parameters} {D : Data P}

section DescentPair

variable {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] {O : DescentPair D.E r n} {ℓ : ℕ}
  [ThePrime ℓ]

omit [DecidableEq r] in
/-- Let `r` and `n` be nonempty. Suppose that, for all `X`, the Hecke polynomial at `w` of rank `n`
with eigenvalues `s` equals `qPochhammer q t (α X) = ∏_{l < t} (1 - q ^ l α X)` times the Hecke
polynomial of rank `r` with eigenvalues `z` at `β X`, where `q` is the norm of `w`. Comparing the
linear terms gives `s 1 = β z 1 + (∑_{i < t} q ^ i) α z 0`. -/
lemma apply_one_eq_of_heckePolyEval_eq (r_pos : 0 < Fintype.card r) (n_pos : 0 < Fintype.card n)
    {w : FinPlace D.E} {s z : ℕ → ℂ} {t : ℕ} {α β : ℂ} (h_eq : ∀ X : ℂ,
      heckePolyEval n w s X = qPochhammer w.q t (α * X) * heckePolyEval r w z (β * X)) :
    s 1 = β * z 1 + (∑ i ∈ Finset.range t, (w.q : ℂ) ^ i) * α * z 0 := by
  have deriv_eq : -deriv (fun X ↦ heckePolyEval n w s X) 0 = -deriv (fun X ↦
      qPochhammer w.q t (α * X) * heckePolyEval r w z (β * X)) 0 := by rw [funext h_eq]
  simp (disch := fun_prop) only [heckePolyEval, qPochhammer, smul_eq_mul, deriv_fun_mul,
    deriv_fun_finsetProd, deriv_fun_sum, deriv_fun_pow] at deriv_eq
  simpa [← sum_mul, zero_pow_eq, n_pos, r_pos, sum_range_succ'] using deriv_eq

/-- Let `O` be a descent pair over the CM field `D.E` of the data `D`: two spaces of dimensions
`r < n`, a character `μ = O.u1Char` of `U(1)` of weight `O.weight`, and chosen places
`O.chosenPlace i`. Put `t = O.rankDiff = n - r` and assume `r - t = 2 a`. Let `c` give for each
chosen place a polynomial over its residue field, admissible for `O` and the trivial twist
(`IsLiftSetting`). Let `R` be an `r`-dimensional `ℓ`-adic Galois representation of `D.E` that is
conjugate self-dual, unramified off the places that `O` allows (empty extra level), has jumps
(Hodge–Tate weights) `J`, and whose inertia at the chosen places acts through the roots of `c`
(`IsRepOfType`). Lower the jumps at each embedding `σ` by `a - cmSign σ * O.weight v`, with `v` the
place of `σ` and `cmSign σ = ±1`, and suppose that they obey the numerical conditions
`IsMainSummandWeights`. Then `R` twisted by the avatar of `O.hasWeight.inv.toAlgebraic 0 a`, the
algebraic Hecke character `μ⁻¹(x / x̄) |x| ^ a`, is like a main summand (`IsMainSummandLike`) with
the lowered jumps and string length `t`. -/
lemma IsRepOfType.isMainSummandLike_twistByChar [PadicIso ℓ]
    {c : (i : O.ChosenIndex) → (ResField (O.chosenPlace i))[X]} {J : (D.E →+* ℂ) → Multiset ℤ}
    {R : GalRep ℓ D.E r} (hR : IsRepOfType O (Fintype.card r) J c ∅ R)
    (hO : IsLiftSetting O c 1) {a : ℤ} (ha : (Fintype.card r - O.rankDiff : ℤ) = 2 * a)
    (hJ : IsMainSummandWeights D (Fintype.card r) O.rankDiff fun σ : D.E →+* ℂ ↦
      (J σ).map fun u : ℤ ↦ u - (a - cmSign σ * O.weight (NumberField.InfinitePlace.mk σ))) :
    IsMainSummandLike D O.rankDiff (fun σ : D.E →+* ℂ ↦
        (J σ).map fun u : ℤ ↦ u - (a - cmSign σ * O.weight (NumberField.InfinitePlace.mk σ)))
      (twistByChar (O.hasWeight.inv.toAlgebraic 0 a).avatar R) := by
  -- the tame part of `O.u1Char⁻¹` is trivial off the chosen places, as it is a power of `chiMLocal`
  have ψ_inv_eq_one : ∀ w : FinPlace D.E, ¬D.IsChosen w → O.tamePart⁻¹ w = 1 := by
    obtain ⟨j, -, hψ : O.tamePart = D.chiMLocal ^ (j : ℤ) * (1 : D.Twist).tamePart⟩ :=
      hO.exists_tamePart_eq_chiMLocal_zpow_mul
    aesop

  have h_weight_eq : (O.rankDiff - 1 : ℕ) + (2 * a - 0) = (card r - 1 : ℕ) := by
    grind [IsLiftSetting]
  have h_type (σ : D.E →+* ℂ) (u : ℤ) : u + -(O.hasWeight.inv.toAlgebraic 0 a).val.2.toAdd σ =
      u - (a - cmSign σ * O.weight (NumberField.InfinitePlace.mk σ)) := by
    simp [HasWeight.toAlgebraic, IsHeckeOfType.toAlgebraic, cmSign, apply_ite, sub_eq_add_neg]
    grind
  -- the twist is a representation of a type, its jumps lowered by the infinity type of the
  -- character
  have h_twist_type := hR.twist_avatar O.hasWeight.inv 0 a h_weight_eq hO ψ_inv_eq_one
  simp only [h_type] at h_twist_type
  exact h_twist_type.isMainSummandLike hO hJ

/-- Let the nonzero form `y` of the descent pair `V` of ranks `0 < r < n` lift the system `b` of
Hecke eigenvalues, and let `H` be its Hecke polynomial at a split place `w` of norm `q` away from
the places of `V` and their conjugates. Then minus the coefficient of `X ^ (n - 1)` in `H` is
`q ^ t ν / ν' * b w 1 + (∑_{i < t} q ^ i) ν`. Here `t = n - r`, `ν = V.charW.frobValue r w` and
`ν' = V.charV.frobValue n w`: for a character `χ` of `U(1)` and rank `N`, `χ.frobValue` is the value
at a uniformizer at `w` of the Hecke character `x ↦ χ(x / x̄) υ(x) ^ (-N)`, times `q ^ (N / 2)`. -/
lemma neg_coeff_eq_of_hasLiftHeckePolynomial [DecidableEq n] (r_pos : 0 < Fintype.card r)
    {V : DescentPair D.E r n} {y : V.FormV} {b : FinPlace D.E → ℕ → ℂ}
    (hy_lifts : V.HasLiftHeckePolynomial y b)
    (hy_ne : (y : Gf D.E n → WeylIndex n V.columnCount → ℂ) ≠ 0) {w : FinPlace D.E}
    (hw_split : star w ≠ w) (hw_off : w ∉ V.places.conjClosure) {H : ℂ[X]}
    (hH : HasHeckePolyAt (y : Gf D.E n → WeylIndex n V.columnCount → ℂ) w hw_split H) :
    -H.coeff (Fintype.card n - 1) =
      w.q ^ V.rankDiff * V.charW.frobValue r w / V.charV.frobValue n w * b w 1 +
        (∑ i ∈ Finset.range V.rankDiff, (w.q : ℂ) ^ i) * V.charW.frobValue r w := by

  have monic : H.IsMonicOfDegree (card n) := hH.isMonicOfDegree hy_ne
  -- `y` is spherical at `w` with Hecke eigenvalues `s j`
  obtain ⟨y_sph, s, rfl : H = heckePoly w.q (card n) s, y_hecke⟩ := hH
  obtain ⟨-, poly_s⟩ := hasHeckePolynomial_of_heckeSplit y_sph y_hecke
  obtain ⟨-, poly_lift⟩ := hy_lifts w hw_split hw_off
  set ν : ℂ := V.charW.frobValue r w
  -- `y` is nonzero, so its Hecke polynomial at `w` is that of the lift of `b`
  have hecke_eq (X : ℂ) : heckePolyEval n w s X = qPochhammer w.q V.rankDiff (ν * X) *
      heckePolyEval r w (b w) (w.q ^ V.rankDiff * ν / V.charV.frobValue n w * X) :=
    (smul_left_inj hy_ne).1 ((poly_s X).symm.trans (poly_lift X))
  have s_zero : s 0 = 1 := by simpa using ((isMonicOfDegree_iff _ _).1 monic).2
  have b_zero : b w 0 = 1 := by
    simpa [heckePolyEval, qPochhammer, zero_pow_eq, s_zero] using (hecke_eq 0).symm
  have coeff_eq : -(heckePoly w.q (card n) s).coeff (card n - 1) = s 1 := by
    simp [Nat.sub_sub_self V.rank_lt.pos]
  rw [coeff_eq, apply_one_eq_of_heckePolyEval_eq r_pos V.rank_lt.pos hecke_eq, b_zero, mul_one]

/-- The identity of traces at Frobenius elements. Let `O` be a descent pair over `D.E` of ranks
`r < n` with character `μ = O.u1Char`, let `c` be admissible labels for it and the trivial twist
(`IsLiftSetting`), and let `r - (n - r) = 2 a`. Let the descent pair `V` have character `μ ϑ`, with
`ϑ` tame, and let the eigenform `y` on `V` with Hecke polynomials `H` lift the system `b` of Hecke
eigenvalues. Then for most Frobenius elements `g = x.frob` at places `w = x.place`, minus the
coefficient of `X ^ (n - 1)` in `H w`, times `normalizingAvatar V g`, equals `θ₀(g) θ(g) b w 1`
plus the sum of the first `n - r` powers of the inverse cyclotomic character at `g`. An avatar is
the `ℓ`-adic Galois character of an algebraic Hecke character; `θ₀` and `θ` are those of
`ϑ.hasWeight.inv.toAlgebraic 0 0`, that is `ϑ⁻¹(x / x̄)`, and of `O.hasWeight.inv.toAlgebraic 0 a`,
that is `μ⁻¹(x / x̄) |x| ^ a`; `normalizingAvatar V` is the one made in the same way from the
inverse of the character `V.charW` of the space of rank `r`, with weight `-r`. Complex numbers are
carried to `ℓ`-adic ones by the isomorphism `ι.ιℓ`. -/
lemma eventually_trace_frob_eq_of_hasLiftHeckePolynomial (ι : PadicIso ℓ) [DecidableEq n]
    {c : (i : O.ChosenIndex) → (ResField (O.chosenPlace i))[X]} (hO : IsLiftSetting O c 1) {a : ℤ}
    (ha : (Fintype.card r - O.rankDiff : ℤ) = 2 * a) {ϑ : D.TameChar} {V : DescentPair D.E r n}
    (hμ : V.u1Char = O.u1Char * ϑ.toAutChar) {y : V.FormV} {b : FinPlace D.E → ℕ → ℂ}
    (hy_lifts : V.HasLiftHeckePolynomial y b) {H : FinPlace D.E → ℂ[X]}
    (hy_eig : IsEigenform (y : Gf D.E n → WeylIndex n V.columnCount → ℂ) H) :
    ∀ᶠ x : FrobeniusDatum D.E in mostFrobenii D.E,
      -((normalizingAvatar V x.frob).val * ι.ιℓ ((H x.place).coeff (Fintype.card n - 1))) =
        ((ϑ.hasWeight.inv.toAlgebraic 0 0).avatar x.frob).val *
            (((O.hasWeight.inv.toAlgebraic 0 a).avatar x.frob).val * ι.ιℓ (b x.place 1)) +
          ∑ e ∈ Finset.range V.rankDiff, cyclotomicInv ℓ D.E (PadicAlgCl ℓ) x.frob ^ e := by
  classical
  have n_even : 2 ∣ card n := by grind [IsLiftSetting]
  obtain ⟨hy_ne, hH⟩ := hy_eig
  set θ₀ : AlgHeckeChar D.E := ϑ.hasWeight.inv.toAlgebraic 0 0
  set θ : AlgHeckeChar D.E := O.hasWeight.inv.toAlgebraic 0 a
  filter_upwards [eventually_mostFrobenii
      (hH.and (eventually_notMem_star_notMem ℓ (.image V.placeAt ⊤))) fun _ ↦ id,
    θ₀.eventually_avatar_frob, θ.eventually_avatar_frob] with
    x ⟨hx_eig, hx_off, hx_star_off, hℓ⟩ avatar_θ₀ avatar_θ
  obtain ⟨hw_split, hx_poly⟩ := hx_eig x.prime_q
  have hw_off : x.place ∉ V.places.conjClosure := by aesop
  -- the values of `θ₀` and `θ` at the place multiply to `q ^ (n - r) / ν'`, where `ν'` is the
  -- `frobValue` of `V.charV`
  have char_eq : (x.place.q : ℂ) ^ V.rankDiff / V.charV.frobValue n x.place =
      heckeCoeff θ₀.val.1 ∅ x.place * heckeCoeff θ.val.1 ∅ x.place := by
    simp [θ₀, θ, HasWeight.toAlgebraic, field, HeckeChar.atUniformizer, heckeCoeff, hμ, ← ha,
      AutChar.frobValue, zpow_sub₀, Exchange.spaceChar_rankTwist n_even, FinPlace.coe_q_eq_sq_sqrt,
      pow_sub₀, O.rank_lt.le]
    ring
  have ν_ne : V.charW.frobValue r x.place ≠ 0 := by
    simp [AutChar.frobValue, HeckeChar.atUniformizer]
  have normalised_eq : (V.charW.frobValue r x.place)⁻¹ * -(H x.place).coeff (card n - 1) =
      heckeCoeff θ₀.val.1 ∅ x.place * heckeCoeff θ.val.1 ∅ x.place * b x.place 1 +
        ∑ e ∈ .range V.rankDiff, (x.place.q : ℂ) ^ e := by
    rw [neg_coeff_eq_of_hasLiftHeckePolynomial hO.odd.1.pos hy_lifts hy_ne hw_split hw_off hx_poly,
      ← char_eq]
    field
  rw [avatar_θ₀, avatar_θ, cyclotomicInv_frob x hℓ,
    normalizingAvatar_eq_of_isFrob_inv x.isPlaceOver hℓ 1 (by simpa using x.isFrob_inv)]
  simpa [mul_assoc] using congrArg ι.ιℓ normalised_eq

/-- Let `O` be a descent pair of ranks `r < n`, with weight `w` and `t = n - r`. Assume that the
labels `c` are admissible for `O` and the trivial twist (`IsLiftSetting`), and that `R` is a
representation with these labels, jumps `J` and empty level (`IsRepOfType`) whose trace at each `g`
is the limit of the Hecke eigenvalues `b v 1` along most Frobenius elements tending to `g`, at
places `v`, carried to `ℓ`-adic numbers by the isomorphism `ι.ιℓ : ℂ ≃+* ℚ̄_ℓ`. Assume also that the
jumps `J σ`, lowered by `(r - t) / 2 - cmSign σ * w v` with `v` the infinite place of `σ` and
`cmSign σ` equal to `1` on the CM type and `-1` off it, obey the numerical conditions
`IsMainSummandWeights`. Then there is a `T` with `IsMainSummand O b T`: a main summand that gives
the traces of the representations attached to the lifts of `b` for all tame twists of `O`. -/
lemma exists_isMainSummand_of_isRepOfType (ι : PadicIso ℓ) [DecidableEq n]
    {c : (i : O.ChosenIndex) → (ResField (O.chosenPlace i))[X]}
    (hO : IsLiftSetting O c 1) (b : FinPlace D.E → ℕ → ℂ) (J : (D.E →+* ℂ) → Multiset ℤ)
    (R : GalRep ℓ D.E r) (hR : IsRepOfType O (Fintype.card r) J c ∅ R)
    (h_trace : ∀ g : Gal(Ω/D.E), Tendsto (fun x : FrobeniusDatum D.E ↦ ι.ιℓ (b x.place 1))
      (mostFrobeniiAt D.E g) (nhds (R g).val.trace))
    (hJ : IsMainSummandWeights D (Fintype.card r) O.rankDiff fun σ : D.E →+* ℂ ↦
      (J σ).map fun u : ℤ ↦ u - ((Fintype.card r - O.rankDiff) / 2 -
        cmSign σ * O.weight (NumberField.InfinitePlace.mk σ))) :
    ∃ T : GalRep ℓ D.E r, IsMainSummand O b T := by
  -- `T` is `R` twisted by the avatar of the algebraic character `θ` made from `O.u1Char⁻¹`. The
  -- identity of traces at `g` is the limit of the identities at Frobenius elements tending to `g`.
  obtain ⟨r_odd, t_odd⟩ := hO.odd
  obtain ⟨a, ha⟩ : 2 ∣ (card r - O.rankDiff : ℤ) := by grind
  rw [ha, Int.mul_ediv_cancel_left a two_ne_zero] at hJ
  let θ : AlgHeckeChar D.E := O.hasWeight.inv.toAlgebraic 0 a
  refine ⟨twistByChar θ.avatar R, ⟨_, hR.isMainSummandLike_twistByChar hO ha hJ⟩, ?_⟩
  intro ϑ V y H S hμ hy_lifts hy_eig hS g
  -- the avatar of `θ₀` is `ϑ.invAvatar`
  let θ₀ : AlgHeckeChar D.E := ϑ.hasWeight.inv.toAlgebraic 0 0
  -- `S` is attached to `H`, and `normalizingAvatar V` is continuous
  have lim_lift : Tendsto
      (fun x ↦ -((normalizingAvatar V x.frob).val * ι.ιℓ ((H x.place).coeff (card n - 1))))
      (mostFrobeniiAt D.E g)
      (nhds (-((normalizingAvatar V g).val * (S g).val.charpoly.coeff (card n - 1)))) :=
    ((tendsto_mostFrobeniiAt fun s ↦ (normalizingAvatar V s).val).mul
      (hS.tendsto_charpoly_coeff g (card n - 1))).neg
  have lim_summand : Tendsto
      (fun x ↦ (θ₀.avatar x.frob).val * ((θ.avatar x.frob).val * ι.ιℓ (b x.place 1)))
      (mostFrobeniiAt D.E g) (nhds ((θ₀.avatar g).val * ((θ.avatar g).val * (R g).val.trace))) :=
    (tendsto_mostFrobeniiAt fun s ↦ (θ₀.avatar s).val).mul
      ((tendsto_mostFrobeniiAt fun s ↦ (θ.avatar s).val).mul (h_trace g))
  let string (s : Gal(Ω/D.E)) : PadicAlgCl ℓ :=
    ∑ e ∈ .range V.rankDiff, cyclotomicInv ℓ D.E (PadicAlgCl ℓ) s ^ e
  have lim_string : Tendsto (fun x : FrobeniusDatum D.E ↦ string x.frob) (mostFrobeniiAt D.E g)
      (nhds (string g)) := tendsto_mostFrobeniiAt string
  have trace_eq : -((normalizingAvatar V g).val * (S g).val.charpoly.coeff (card n - 1)) =
      (θ₀.avatar g).val * ((θ.avatar g).val * (R g).val.trace) + string g :=
    tendsto_nhds_unique_of_eventuallyEq lim_lift (lim_summand.add lim_string)
      ((eventually_trace_frob_eq_of_hasLiftHeckePolynomial ι hO ha hμ hy_lifts hy_eig).filter_mono
        inf_le_left)
  -- the trace of `S g` is minus the coefficient of `X ^ (n - 1)` in its characteristic polynomial
  have trace_S : (S g).val.trace = -(S g).val.charpoly.coeff (card n - 1) := by
    simp [trace_eq_neg_charpoly_nextCoeff (S g).val, nextCoeff, O.rank_lt.pos.ne']
  simpa [trace_S, TameChar.invAvatar, Units.smul_def] using trace_eq

/-- Let the weight `(d, κ)` give at each infinite place `v` of the CM field `D.E` (the type `D.Φ`) a
shape `d v` and an integer `κ v`, and suppose that its doubled Harish-Chandra parameter is
`D.paramW`, twice the target parameter `λ_q = D.targetParameter v q` in rank `r = D.r`. Put
`t = D.t`, and at a complex embedding `σ` over `v` let `ε = cmSign σ` be `1` on the CM type and
`-1` off it. Then the jumps (Hodge–Tate weights) of `(d, κ)` at `σ`, lowered by
`(r - t) / 2 + ε w` for any integer `w`, are the numbers `t / 2 - ε (λ_q + w)` for `q < r`. -/
lemma map_jumps_sub_eq_map_targetParameter {d : D.Φ → ℕ → ℕ} {κ : D.Φ → ℤ}
    (hκ : IsHCParam d κ D.paramW) (σ : D.E →+* ℂ) (w : ℤ) :
    (jumps (d, κ) D.r σ).map (fun u : ℤ ↦ u - ((D.r - D.t) / 2 + cmSign σ * w)) =
      (Multiset.range D.r).map fun q : ℕ ↦
        (D.t / 2 - cmSign σ * (D.targetParameter (NumberField.InfinitePlace.mk σ) q + w) : ℤ) := by
  rw [jumps, Multiset.map_map]
  refine Multiset.map_congr rfl fun q hq ↦ ?_
  set v : D.Φ := NumberField.InfinitePlace.mk σ
  have h_param : 2 * D.targetParameter v q =
      2 * (κ v + ∑ h ∈ Finset.Ioo q D.r, (d v h : ℤ)) + D.r - 1 - 2 * q := by
    have h_entry := hκ.eq_hcParameter v (D.rowIndexOfNumber q)
    simp only [card_rowIndex, hcParameter, diagramWeight_apply, Nat.cast_sum] at h_entry
    grind [Data.rowIndexOfNumber, paramW, decreasingPosition_paramW, Multiset.mem_range]
  simp only [Function.comp_apply, cmSign, Nat.cast_sum, apply_ite Units.val, Units.val_neg,
    Units.val_one]
  grind [Data.t, D.r_odd]

/-- A nonzero function with Hecke polynomial `Q w` at every split place `w` off the chosen places
and their conjugates is an eigenform for the system `Q`. -/
theorem _root_.New.Data.isEigenform_of_hasHeckePolyAt [DecidableEq n] (D : Data P) {M : Type}
    {f : Gf D.E n → M → ℂ} (hf : f ≠ 0) {Q : FinPlace D.E → ℂ[X]}
    (h_eig : ∀ (w : FinPlace D.E) (hw : D.IsSplitOffLevel w), HasHeckePolyAt f w hw.isSplit (Q w)) :
    IsEigenform f Q := by
  classical
  -- Almost every `w` has `w` and `star w` off `chosenPlace`; if its norm is prime it is also split.
  refine ⟨hf, (eventually_notMem_star_notMem 1 (Finset.image D.chosenPlace ⊤)).mono ?_⟩
  exact fun w h_off h_prime ↦ ⟨_, h_eig w ⟨isSplit_of_q_prime h_prime, by simp_all⟩⟩

end DescentPair

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let the Hecke eigenvalues `p (w, i)` occur in a nonzero good form on `D.spaceW D.m`: a form of
principal level at the chosen places, in the image of the idempotent `D.e₀`. Let `O` be the `j`-th
descent pair of the trivial twist, `1 ≤ j ≤ m = D.m`: its two spaces have dimensions `r = D.r` and
`r + t`, `t = D.t`, and its character has weight `-D.liftWeight j`. Then some `r`-dimensional
`ℓ`-adic Galois representation `T` of `D.E` has `IsMainSummand O` for `p`. -/
theorem exists_isMainSummand_descentPair {ℓ : ℕ} [ThePrime ℓ] (ι : PadicIso ℓ)
    {p : FinPlace D.E × ℕ → ℂ}
    (h_ne_bot : D.goodForms (D.spaceW D.m) ⊓ D.eigenPart (D.spaceW D.m) p ≠ ⊥) (j : D.LiftIndex) :
    ∃ T : GalRep ℓ D.E D.RowIndex,
      IsMainSummand (D.descentPair TameChar.one j) (fun (w : FinPlace D.E) (i : ℕ) ↦ p (w, i))
        T := by
  classical
  -- A nonzero good form `z` with system `p` is not killed by the idempotent of some good tuple `c`.
  -- Its algebraic form `L z` is an eigenform with labels `c`; `exists_isMainSummand_of_isRepOfType`
  -- makes the main summand out of the attached representation.
  set W : Space D.E D.RowIndex (D.signsW D.m) := D.spaceW D.m
  obtain ⟨z, ⟨hz_good, hz_eig⟩, hz_ne : z ≠ 0⟩ := (Submodule.ne_bot_iff _).1 h_ne_bot
  obtain ⟨d, κ, hκ : IsHCParam d κ D.paramW⟩ :=
    Exchange.exists_isHCParam_of_hasGap D.hasGap_signsY_paramW
  -- `L` sends a form on `W` to its algebraic form of weight `(d, κ)`, a function on `Gf`
  let L : W.Form (typeKernel D.paramW _) →ₗ[ℂ] Gf D.E D.RowIndex → WeylIndex D.RowIndex d → ℂ :=
    (AlgForm D.RowIndex d κ).subtype ∘ₗ (W.toAlgForm hκ).toLinearMap
  have L_equiv (g : Gf D.E D.RowIndex) (y : W.Form (typeKernel D.paramW _)) :
      L (W.formRep _ g y) = rightRegular ℂ _ _ g (L y) :=
    congrArg Subtype.val (toAlgForm_formRep hκ g y)
  -- the action of the product of the finite groups at the chosen places
  let π : Representation ℂ D.chosenGL (D.principalForms W) := D.principalRep W
  let O : DescentPair D.E D.RowIndex (D.RowIndex ⊕ Fin D.t) := D.descentPair .one j
  -- `e₀` fixes `z` and is the sum of the `tupleIdem c` over the good tuples `c`
  have h_fixed : π.asAlgebraHom D.e₀ z = z := (D.isCentralProj_e₀.1.map _).mem_range_iff.1 hz_good
  obtain ⟨c : ∀ i : O.ChosenIndex, (ResField (O.chosenPlace i))[X], hc_good, hcz_ne⟩ :
      ∃ c ∈ D.goodTupleFamilies, π.asAlgebraHom (tupleIdem D.RowIndex c) z ≠ 0 :=
    D.goodTupleFamilies.exists_ne_zero_of_sum_ne_zero (by simpa [e₀] using h_fixed.trans_ne hz_ne)
  have h_setting : IsLiftSetting O c 1 := isLiftSetting_descentPair D 1 j hc_good
  have h_level : L z ∈ levelSpace (rightRegular ℂ (Gf D.E D.RowIndex) _) D.chosenLevel := by
    simp [← L_equiv, mem_levelSpace.1 z.property]
  have h_form : L z ∈ (stdSpace D.E D.RowIndex).forms (d, κ) := (toAlgForm _ hκ z.val).property
  have h_eig : IsEigenform (L z) fun w : FinPlace D.E ↦
      heckePoly w.q (card D.RowIndex) fun i : ℕ ↦ p (w, i) := by
    refine D.isEigenform_of_hasHeckePolyAt (by simpa [L]) fun w hw ↦
      ⟨levelSpace_anti (maxCompactAt_le_levelOf hw.notMem_conjClosure) h_level,
        fun i ↦ p (w, i), rfl, fun i ↦ ?_⟩
    -- `L` commutes with the Hecke operators, and these act on `z` by the scalars `p`
    have h_scalar : heckeSplit (W.formRep _) hw.isSplit i z.val = p (w, i) • z.val := by
      rw [← D.coe_heckeOperator_apply _ hw, (D.mem_eigenPart _).1 hz_eig, Submodule.coe_smul]
    rw [← map_heckeSplit hw.isSplit i L, h_scalar, map_smul]
  obtain ⟨R : GalRep ℓ D.E D.RowIndex, hR⟩ :=
    (sphericalCompat_std Classical.ofNonempty h_form h_eig).1
  -- at a chosen place, `GL_r(O_w)` acts on `L z` through `π`: a parahoric type with one block
  have h_type (i : O.ChosenIndex) : HasParahoricType (L z) (O.isConjApart_chosenPlace.star_ne i i)
      (.refl D.RowIndex) 0 1 (1 : Fin 0 → MulChar (ResField (O.chosenPlace i)) ℂ)
      fun x ↦ L (π (Pi.mulSingle i x) z) := by
    refine ⟨by simp, fun k x hk hx ↦ ?_⟩
    obtain rfl : reduceGL k = x := Units.ext hx
    -- on `z`, the lift of the reduction of `k` that defines `π` acts as `k` itself
    have h_lift := apply_liftResidue_eq z _ (reduceFamily_ofSplitPlace (w := D.chosenPlace) i k)
    simpa [-GeneralLinearGroup.val_det_apply] using!
      ((congrArg L h_lift).trans (L_equiv _ z.val)).symm
  refine exists_isMainSummand_of_isRepOfType ι h_setting _ (jumps (d, κ) (card D.RowIndex)) R ?_
    (fun g ↦ ?_) ?_
  · -- the level is maximal off the chosen places and their conjugates; at the chosen place `i`
    -- the idempotent of the label `c i` does not kill `z`, or else `tupleIdem c` would
    have L_inj : Function.Injective (L.domRestrict (D.principalForms W)) := fun _ ↦ by simp [L]
    have h_label (i : O.ChosenIndex) : HasProductLabel (L z)
        (O.isConjApart_chosenPlace.star_ne i i) (faithfulChar (ResField (O.chosenPlace i)))
        (card D.RowIndex)
        ((c i).scaleRoots (charName (faithfulChar (ResField (O.chosenPlace i))) 1).val) 1 _ :=
      HasParahoricType.hasProductLabel _ L_inj
        (fun h_zero ↦ hcz_ne (piTensorElem_apply_eq_zero i h_zero)) (h_type i) nofun nofun
    convert isRepOfType_of_hasProductLabel h_setting h_form h_eig hR
      (fun v _ hv ↦ levelSpace_anti (maxCompactAt_le_levelOf hv) h_level) h_label
    simp
  · -- the trace and the first Hecke eigenvalue are minus the coefficients of `X ^ (r - 1)`
    have h_trace : (R g).val.trace = -(R g).val.charpoly.coeff (D.r - 1) := by
      rw [trace_eq_neg_charpoly_coeff, card_rowIndex]
    have h_hecke (w : FinPlace D.E) :
        p (w, 1) = -(heckePoly w.q (card D.RowIndex) fun i : ℕ ↦ p (w, i)).coeff (D.r - 1) := by
      rw [card_rowIndex]
      simp [Nat.sub_sub_self D.r_odd.pos]
    simpa only [h_trace, h_hecke, map_neg, id_eq] using
      (hR.tendsto_charpoly_coeff g (D.r - 1)).neg
  · -- the shifted jumps are those of `isMainSummandWeights_descentPair`
    have h_weight (v : D.Φ) : O.weight v = -D.liftWeight j v := rfl
    have h_rankDiff : O.rankDiff = D.t := by simp [DescentPair.rankDiff]
    simpa only [card_rowIndex, h_rankDiff, h_weight, mul_neg, sub_neg_eq_add,
      map_jumps_sub_eq_map_targetParameter hκ] using isMainSummandWeights_descentPair j.property

end RowsExist

end New.Selmer
