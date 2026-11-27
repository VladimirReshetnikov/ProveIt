import Lib.SiegelWeil.RallisInner.SharpData
import Lib.Weil.CompactLift.DefiniteThetaLift

/-!
# Theta lift of an algebraic form to a larger definite unitary group and its Hecke polynomials

This file constructs the theta lift from the definite unitary group of rank n to that of rank n + s.
The lift is used to separate the Galois representation of a form from those of its lifts. The file
also records how the monic and the reciprocal normalisations of the Hecke polynomial are related.

## Main definitions and results

* `New.exists_theta_lift_heckePoly`: the theta lift of a nonzero form is a nonzero form whose Hecke
  polynomial at split places is the twisted old one times a string of linear factors.

Notions from other files:
* `New.AutChar.HasWeight`: `b.HasWeight c 1` says that `b u = ∏_v u_v ^ c v` whenever `u` has
  integral finite part.
* `New.WeilData`: Weil data on a stably unramified E. They consist of ȷ in E with ȷ = −ȷ̄, Im τȷ > 0
  for every τ in the CM type and (1 − ȷ⁻¹)/2 integral; a finite idele α for which the completed
  integers Ô are self-dual under (z, u) ↦ ψ_f(ȷαᾱzu); and a splitting character υ equal to −1 at
  uniformisers of the places w with w = w̄.

## Relation to the literature

Known result: Theta lift to larger rank, the step that reduces even rank to odd rank. Here a
non-zero theta lift in the convergent range from definite U(n) to U(n+s), with s > n, replaces
endoscopic transfer. It keeps spherical places, and its Hecke polynomials are twisted and gain the
string of a character of U(1). Source: Blasius, Rogawski, Motives for Hilbert modular forms, Invent.
Math. 114 (1993) and Shin, Ann. of Math. 173 (2011) for the idea (endoscopic transfer to odd rank);
Harris, Soudry, Taylor, Invent. Math. 112 (1993) for theta lifts with a varying character.
-/

/-!
## The monic Hecke polynomial and the reciprocal one

The two normalisations of the Hecke polynomial at a place `w` agree: `New.heckePoly` (monic of
degree `n` if `t 0 = 1`) at `x ≠ 0` is `x ^ n` times the reciprocal one, `New.heckePolyEval`, at
`x⁻¹`.
-/

/-- At `x ≠ 0` the monic Hecke polynomial at the place `w`, with coefficients built from `t`, is
`x ^ n` times the reciprocal one, `heckePolyEval`, at `x⁻¹`, where `n = card n`:
`∑ (-1)^j q^(j choose 2) t j x^(n - j) = x^n ∑ (-x⁻¹)^j q^(j choose 2) t j`, with `q` the norm of
`w` and `j` running from `0` to `n`. -/
lemma New.eval_heckePoly {E n : Type*} [Field E] [NumberField E] [Fintype n] (w : FinPlace E)
    (t : ℕ → ℂ) {x : ℂ} (hx_ne : x ≠ 0) :
    (heckePoly w.q (Fintype.card n) t).eval x = x ^ Fintype.card n * heckePolyEval n w t x⁻¹ := by
  -- Term by term, `x ^ (n - j) = x ^ n * x⁻¹ ^ j` for `j ≤ n`.
  rw [heckePoly, heckePolyEval, Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  simp [pow_sub₀ x hx_ne (Finset.mem_range_succ_iff.mp hj), neg_pow x⁻¹]
  ring

/-!
## Theta lift to a larger definite group and Hecke polynomials

`New.stdSpace E n` is the sum of `n` norm forms. `New.AlgForm n κ e` and `New.Space.forms` are
smooth algebraic forms of a given weight. `New.maxCompactAt n w` is the maximal compact subgroup at
`w` and `w̄`. `New.HasHeckePolyAt f w hw P` says that `f` is a spherical Hecke eigenform at the
split place `w` with Hecke polynomial `P`. For a character `b` of `U(1)`, `hb.toAlgebraic k j`
(`New.AutChar.HasWeight.toAlgebraic`) is the algebraic Hecke character
`b (x / x̄) υ ^ (-k) |x| ^ (j - k / 2)`. `New.heckeCoeff ψ ∅ w` is `ψ` at a uniformiser.
-/

namespace New

open NumberField Space SiegelWeil Fintype

variable {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]

open Matrix Algebra Valued G Gf Polynomial AutChar Set Filter

/-- Let `x` be an integral matrix with `xᴴ * x = 0`, let `B` be a finite set of places with
`stdLevel E n ⊓ trivialOn n B ≤ H`, and let `N ≠ 0` have its principal level inside `H`. Let
`z = N⁻¹ • idem B'`, with `B'` the closure of `B` under conjugation, and let `b` be a character
of `U(1)` of weight `c`. Then an integral `g` such that `z * D i j` is integral for
`D = g⁻¹ - 1` lies in `H` and fixes, under the Weil representation, the vacuum translated by
`z • x`. -/
private lemma mem_inf_stabilizer_of_integral {m : Type} [Fintype m] [DecidableEq m]
    {H : Subgroup (Gf E n)} {b : AutChar E} {c : InfinitePlace E → ℤ} (hb : b.HasWeight c 1)
    {x : Matrix m n (𝔸f E)} (hx_int : ∀ (i : m) (j : n), x i j ∈ Ô E) (hx_iso : xᴴ * x = 0)
    {B : Finset (FinPlace E)} (hB_off : stdLevel E n ⊓ trivialOn n (B : Set (FinPlace E)) ≤ H)
    {N : ℕ} (hN : N ≠ 0) (hN_cong : (principalLevel n (N : 𝓞 E) : Set (Gf E n)) ⊆ H.carrier)
    (z : 𝔸f E) (hz : z = (N : E)⁻¹ • idem (SetLike.coe B).conjClosure)
    {g : Gf E n} {D : Matrix n n (𝔸f E)} (hD : (g.val.val)⁻¹ = D + 1) (hg : g ∈ stdLevel E n)
    (hzD : ∀ i j : n, z * D i j ∈ Ô E) :
    g ∈ H ⊓ (MulAction.stabilizer _
      (finHeisenbergOp ((stdSpace E n).hom (stdSpace E m)) (matrixToVec (z • x))
        (vacElem ((stdSpace E n).hom (stdSpace E m))) :
        𝒮 ((stdSpace E n).hom (stdSpace E m)))).comap
        ((pairWeil (stdSpace E n) (stdSpace E m) 1 b).comp
          (.prod (.inr (GInf E 1) (Gf E n)) 1)).toHomUnits := by
  constructor
  · -- The part of `g⁻¹` above `B` is congruent to `1` modulo `N`; it cancels that of `g`.
    have h_cut : componentOn n B g⁻¹ ∈ H := by
      refine hN_cong ⟨componentOn_mem_stdLevel (inv_mem hg), fun i j ↦ ⟨z * D i j, hzD i j, ?_⟩⟩
      -- `N` acts on the adeles through `E`; in that form `simp` computes the entry.
      change _ = (N : E) • (z * D i j)
      simp [hz, hN, hD, componentOn, U.cutAt, cutGL, sub_smul]
    refine (mul_mem_cancel_left h_cut).mp (hB_off ?_)
    simp_all [componentOn_mem_stdLevel, mul_mem]
  · -- `g` moves the translation by the integral `x * z • D`, with trivial phase as `xᴴ * x = 0`.
    have h_vac : finHeisenbergOp ((stdSpace E n).hom (stdSpace E m)) (matrixToVec (x * z • D))
        (vacElem _) = vacElem _ :=
      finHeisenbergOp_vacElem fun _ ↦ sum_mem (by simp [hx_int, hzD, mul_mem])
    refine (pairWeil_apply ..).trans (.trans ?_
      (congrArg (finHeisenbergOp _ (matrixToVec (z • x))) h_vac))
    -- The point `g` of the product group is `((1, g), 1, 1)`.
    have h_pt : ((MonoidHom.inr (GInf E (1 : n → ℤˣ)) (Gf E n)).prod 1) g =
        (((1, g), 1, 1) : G E (1 : n → ℤˣ) × G E (1 : m → ℤˣ)) := rfl
    -- The finite part of `onHom` acts on the translation as a Kronecker product (`G.onHom_snd`).
    rw [omega_finHeisenbergOp, ← map_smul, G.onHom_snd, kronecker_mulVec_eq_matrixToVec,
      vecToMatrix_matrixToVec,
      ← pairWeil_apply, h_pt, pairWeil_eq_smul_of_projOn_eq ⊤]
    · simp [hb.apply_det_eq_one, hg, hD, hx_iso, x.mul_add, Dᴴ.mul_assoc, add_comm,
        finHeisenbergOp_finHeisenbergOp]
    -- the three side conditions of `pairWeil_eq_smul_of_projOn_eq`
    all_goals simp [hg]

omit [WeilData E] in
/-- Let `z` be a finite adele, let `g` be integral at every place where `z` is integral (the places
off `{w | 1 < v (z w)}`), and let `D = g⁻¹ - 1`. If for an integral matrix `u` every entry
`z * D p j + ∑ k, u p k * D k j` is integral, then every entry of `D` is integral: at a place `w`,
a largest entry of a column of `D` that is not integral would force `z` to be integral at `w`. -/
private lemma mem_Ô_of_mul_add_sum_mem_Ô {z : 𝔸f E} {g : Gf E n}
    (hg : g ∈ localLevel n {w : FinPlace E | 1 < v (z w)}ᶜ) {D : Matrix n n (𝔸f E)}
    (hD_def : D = g⁻¹.val.val - 1) {u : n → n → 𝔸f E} (hu : ∀ p k : n, u p k ∈ Ô E)
    (h_int : ∀ p j : n, z * D p j + ∑ k : n, u p k * D k j ∈ Ô E) (i j : n) : D i j ∈ Ô E := by
  refine mem_Ô.mpr fun w ↦ ?_
  have h_nonempty : Nonempty n := ⟨i⟩
  obtain ⟨p, hp⟩ := Finite.exists_max fun i' : n ↦ v (D i' j w)
  refine (hp i).trans (le_of_not_gt fun h_big ↦ ?_)
  -- `O` is the set of adeles whose valuation at `w` is at most that of `D p j`.
  let O : AddSubgroup (𝔸f E) := (v.comap (evalAt w)).leAddSubgroup (v (D p j w))
  have h_sum : ∑ k : n, u p k * D k j ∈ O :=
    sum_mem fun k _ ↦ by simp [O, mul_le_of_le_one_of_le, mem_Ô.mp, hu, hp]
  have h_all : z * D p j + ∑ k : n, u p k * D k j ∈ O := (mem_Ô.mp (h_int p j) w).trans h_big.le
  have hzD_mem : z * D p j ∈ O := (O.add_mem_cancel_right h_sum).mp h_all
  -- so `z` is integral at `w`, where `g⁻¹` is then integral, and `D p j` too
  have hw : w ∈ {w : FinPlace E | 1 < v (z w)}ᶜ := by simpa [O, h_big.pos] using hzD_mem
  have h_one : (1 : Matrix n n (𝔸f E)) p j ∈ Ô E := by simp [Matrix.one_apply, ite_mem]
  have hD_le : v (D p j w) ≤ 1 := by
    rw [hD_def]
    exact v.map_sub_le ((hg w hw).isIntMatrix_inv p j) (mem_Ô.mp h_one w)
  exact h_big.not_ge hD_le

/-- Let the row `ρ p` of `x` be the unit vector at `p`, let `g` be integral at every place where
the finite adele `z` is integral, and let `D = g⁻¹ - 1`. Unless `g` is integral with every
entry `z * D i j` integral, the Weil matrix coefficient at `g` of `F`, the vacuum translated by
`z • x`, is `0`. -/
private lemma weilMatrixCoeff_finHeisenbergOp_eq_zero {m : Type} [Fintype m] [DecidableEq m]
    {b : AutChar E} {x : Matrix m n (𝔸f E)} {ρ : n ↪ m} (hρ : ∀ i : n, x (ρ i) = Pi.single i 1)
    {z : 𝔸f E} {g : Gf E n} (hg : g ∈ localLevel n {w : FinPlace E | 1 < v (z w)}ᶜ)
    {F : 𝒮 ((stdSpace E n).hom (stdSpace E m))}
    (hF_def : F = finHeisenbergOp ((stdSpace E n).hom (stdSpace E m)) (matrixToVec (z • x))
      (vacElem ((stdSpace E n).hom (stdSpace E m))))
    {D : Matrix n n (𝔸f E)} (hD_def : D = g⁻¹.val.val - 1)
    (hg_not : ¬(g ∈ stdLevel E n ∧ ∀ i j : n, z * D i j ∈ Ô E)) :
    weilMatrixCoeff b F F g = 0 := by
  -- The coefficient at `g` is an average over integral `u` of terms that vanish unless
  -- `z • x * (g⁻¹ - 1) + u * g⁻¹` is integral, and that forces `g` and `z • D` to be integral.
  subst hF_def
  have hD : (g.val.val)⁻¹ = D + 1 := by simp [hD_def]
  -- Write `ω(g) vacElem` through the projection on vacua (`omega_vacElem`) and translate both
  -- vectors by `-z • x`, so that the left one is the vacuum.
  -- The point of the product group is `((1, g), 1, 1)`, the form that `onHom_fin` takes.
  have h_pt : (((1, g), 1) : G E (1 : n → ℤˣ) × G E (1 : m → ℤˣ)) = ((1, g), 1, 1) := rfl
  rw [weilMatrixCoeff, pairWeil_apply, h_pt, onHom_fin, omega_finHeisenbergOp, omega_vacElem,
    ← dataInner_finHeisenbergOp _ (-matrixToVec (z • x))]
  simp [finHeisenbergOp_finHeisenbergOp, Prod.mk_one_one, onHom_snd, mulVec_smul]
  -- `simp` leaves a product of scalars and an inner product; it is enough that the last vanishes:
  -- the inner product of the vacuum with a translate of `ω(g) P ω(g⁻¹)` of the vacuum.
  refine .inr (.inr (.inr ?_))
  show dataInner _ (vacElem _)
      (finHeisenbergOp _ (-(z • matrixToVec x) + _) (ω _ _ (projOn _ univ (ω _ _ (vacElem _))))) = 0
  -- The inner projection is a mean over integral `u`, so it is enough that each term vanishes
  -- (`map_projOn_eq_const`). The projection that fixes the left vacuum, moved to the right, kills
  -- translates of the vacuum by vectors that are not integral.
  rw [← projOn_vacElem (S := ⊤), dataInner_projOn]
  -- The three operators applied in turn are one composite `L`, the form of `map_projOn_eq_const`.
  rw [← ContinuousLinearMap.comp_apply (finHeisenbergOp _ _),
    ← ContinuousLinearMap.comp_apply (projOn _ ⊤),
    map_projOn_eq_const _ (projOn _ ⊤ ∘L finHeisenbergOp _ _ ∘L _) (c := 0), map_zero]
  simp [rep_apply_apply, stdLattice.mem_stdLattice, onHom_snd, Prod.mk_one_one,
    finHeisenbergOp_finHeisenbergOp, matrixToVec, projOn_finHeisenbergOp, mem_integralBox]
  show ∀ u : m × n → 𝔸f E, (∀ (a : m) (b : n), u (a, b) ∈ Ô E) →
    (∀ (a : m) (b : n),
      -(z * x a b) +
          z * (kroneckerMap (fun y₁ y₂ ↦ y₁ * y₂) 1 (g.val.val)⁻¹ᵀ *ᵥ matrixToVec x) (a, b) +
        (kroneckerMap (fun y₁ y₂ ↦ y₁ * y₂) 1 (g.val.val)⁻¹ᵀ *ᵥ u) (a, b) ∈ Ô E) → _
  intro u hu h_int
  -- The condition at row `ρ p`, where `x` has the unit vector at `p`.
  replace h_int (p j : n) : z * D p j + ∑ k : n, u (ρ p, k) * D k j ∈ Ô E := by
    simpa [hρ, hD, hu, mulVec_eq_sum, sum_prod_type, mul_add, ← add_assoc, Pi.single_apply,
      matrixToVec, Matrix.one_apply, Finset.sum_add_distrib,
        add_mem_cancel_right] using h_int (ρ p) j
  -- `D` is integral, since `g⁻¹` is integral wherever `z` is
  have hD_int (i j : n) : D i j ∈ Ô E :=
    mem_Ô_of_mul_add_sum_mem_Ô (u := fun p k ↦ u (ρ p, k)) hg hD_def (fun p k ↦ hu (ρ p) k)
      h_int i j
  have hzD (i j : n) : z * D i j ∈ Ô E := by
    simpa (disch := simp [hu, hD_int, mul_mem, sum_mem]) [add_mem_cancel_right] using h_int i j
  have hg_int : g ∈ stdLevel E n := inv_mem_iff.mp <| mem_stdLevel.mpr <| by
    simp [hD, hD_int, Matrix.one_apply, ite_mem, add_mem_cancel_right]
  exact absurd ⟨hg_int, hzD⟩ hg_not

/-- Let `H` be an open subgroup of `Gf E n`, let `b` be a character of `U(1)` of weight `c` with
trivial tame part, and let `2 * card n ≤ card m`. Then there exist a set `S` of finite places
avoiding every `w` with `maxCompactAt n w ≤ H`, a Schwartz datum `F` on
`Hom(stdSpace E n, stdSpace E m)`, a level `J ≤ H` and a number `mass` such that `F` is sharp for
`b`, `S` and `J` (`IsSharp`). Sharpness means: `⟨F, F⟩ ≠ 0`; `F` lies in the finite part and is a
vacuum off `S` (fixed by the projection `projOn` on vacua at every set of places disjoint from `S`)
and clean (true here as all signs of the standard spaces are `1`); at finite points `g` integral off
`S`, the coefficient `⟨F, ω(g) F⟩` of the Weil action `ω` (built from `b`) is `⟨F, F⟩` on
`J ⊓ stdLevel E n` and zero elsewhere, where `stdLevel E n` is the stabiliser `K₀` of `Ô ^ n`; and
`mass` is the quotient of `⟨F, F⟩` by the index `[K₀ : J ⊓ K₀]`. -/
lemma exists_isSharp_of_two_mul_card_le {m : Type} [Fintype m] [DecidableEq m]
    {H : Subgroup (Gf E n)}
    (hH : IsOpen H.carrier) {b : AutChar E} {c : InfinitePlace E → ℤ} (hb : b.HasWeight c 1)
    (h_rank : 2 * card n ≤ card m) :
    ∃ S : Set (FinPlace E),
      (∀ w : FinPlace E, maxCompactAt n w ≤ H → w ∉ S) ∧
      ∃ F : 𝒮 ((stdSpace E n).hom (stdSpace E m)), ∃ J ≤ H, ∃ mass : ℂ,
        IsSharp (S := stdSpace E n) (T := stdSpace E m) b S F J mass := by
  classical
  -- The datum is the vacuum translated by `z • x`, with `x` an integral isotropic frame and `z`
  -- the inverse of a level `N` at the bad places `B` of `H` and their conjugates, zero elsewhere.
  -- `J` is its stabiliser in `H`, and `S` the set of places where `z` is not integral.
  -- The rows `ρ i` of `x` form the identity matrix.
  obtain ⟨x, hx_int, hx_iso, ρ, hρ⟩ := exists_integral_isotropic_frame (E := E) h_rank
  -- `H` contains the integral elements that are trivial at `B`, and those congruent to `1` mod `N`.
  obtain ⟨B, hB, hB_off⟩ := exists_inf_trivialOn_le hH
  obtain ⟨N, hN, hN_cong⟩ := exists_principalLevel_subset (hH.mem_nhds H.one_mem)
  let z : 𝔸f E := (N : E)⁻¹ • idem (SetLike.coe B).conjClosure
  let S : Set (FinPlace E) := {w | 1 < v (z w)}
  let F : 𝒮 ((stdSpace E n).hom (stdSpace E m)) :=
    finHeisenbergOp _ (matrixToVec (z • x)) (vacElem _)
  let J : Subgroup (Gf E n) := H ⊓ (MulAction.stabilizer _ F).comap
    ((pairWeil (stdSpace E n) (stdSpace E m) 1 b).comp
      (.prod (.inr (GInf E 1) (Gf E n)) 1)).toHomUnits
  -- Only the fields `vacuum_off` and `weilMatrixCoeff_eq` of `IsSharp` need an argument. Where
  -- `H` contains the maximal compact subgroup, `w` is not in `B`, so `z` is `0` there.
  refine ⟨S, fun w hw ↦ by simp [hB w hw, S, z, smul_def], F, J, inf_le_left,
    dataInner _ F F / stdLevelIndex J,
    { self_ne_zero := by simp [F, dataInner_finHeisenbergOp]
      mem_finitePart := finHeisenbergOp_mem_finitePart _ vacElem_mem_finitePart
      vacuum_off := fun A _ hA ↦ ?_
      weilMatrixCoeff_eq := fun g hg ↦ ?_
      mass_eq := rfl
      -- all signs of the standard spaces are `1`, so `F` is clean
      clean := fun _ ↦ by simp [IsClean] }⟩
  · -- Off `S` the translation is integral, so `F` is the vacuum there. The closure of `A` under
    -- conjugation is `A` together with its conjugate, and both are disjoint from `S`.
    have hz : idem A.conjClosure * z ∈ Ô E := by
      refine idem_mul_mem_Ô.mpr ?_
      rintro _ (h | h) <;> simpa [← v_star_apply, S, z] using hA.le_compl_left h
    simp [F, ← mul_assoc, hz, hx_int, matrixToVec, projOn_finHeisenbergOp, mem_integralBox, mul_mem]
  -- On `J`, which fixes `F`, the coefficient is constant.
  refine .symm (ite_eq_iff'.mpr ⟨fun hg_mem ↦ ?_, fun hg_not ↦ ?_⟩)
  · obtain ⟨⟨-, hg_fix⟩, -⟩ := hg_mem
    exact congrArg _ hg_fix.symm
  -- Off `J ⊓ stdLevel E n` it vanishes, since an integral `g` with `z • D` integral lies in `J`.
  let D : Matrix n n (𝔸f E) := g⁻¹.val.val - 1
  have hD : (g.val.val)⁻¹ = D + 1 := by simp [D]
  refine .symm (weilMatrixCoeff_finHeisenbergOp_eq_zero hρ hg rfl rfl fun ⟨hg_int, hzD⟩ ↦ ?_)
  exact hg_not
    ⟨mem_inf_stabilizer_of_integral hb hx_int hx_iso hB_off hN hN_cong z rfl hD hg_int hzD, hg_int⟩

omit [WeilData E] [DecidableEq n] in
/-- Let `t` and `t'` give the Hecke polynomials at `w` of ranks `card n` and `card n + s`, the
second of degree `card n + s`. Suppose that for all `X` their reciprocal polynomials `heckePolyEval`
satisfy `R' X = R (μ * X) * qPochhammer w.q s (ν * X)` (`qPochhammer w.q s Y` is a product over
`l < s` of factors linear in `q_w ^ l * Y`), where `R` is built from `t` and `R'` from `t'`, and let
`μ * a = 1` and `θ l = q_w ^ l * ν * a` for `l < s`. Then the second Hecke polynomial, with its
roots multiplied by `a`, is the first one times `∏ l < s, (X - θ l)`. -/
private lemma scaleRoots_heckePoly_eq (w : FinPlace E) {s : ℕ} {t t' : ℕ → ℂ} {μ ν a : ℂ}
    (θ : Fin s → ℂ)
    (h_deg : (heckePoly w.q (card (Fin (card n + s))) t').natDegree = card (Fin (card n + s)))
    (h_eigval : ∀ X : ℂ, heckePolyEval (Fin (card n + s)) w t' X =
      heckePolyEval n w t (μ * X) * qPochhammer w.q s (ν * X))
    (h_scale : μ * a = 1) (h_root : ∀ l : Fin s, θ l = w.q ^ (l : ℕ) * ν * a) :
    (heckePoly w.q (card (Fin (card n + s))) t').scaleRoots a =
      heckePoly w.q (card n) t * ∏ l : Fin s, (X - C (θ l)) := by
  have ha_ne : a ≠ 0 := right_ne_zero_of_mul_eq_one h_scale
  -- Compare the two polynomials at every `x ≠ 0`: there a Hecke polynomial is `x ^ n` times
  -- `heckePolyEval` at `x⁻¹`, and `h_eigval` at `a / x` splits the left side into the two factors.
  refine eq_of_infinite_eval_eq _ _ <|
    infinite_of_finite_compl ((eventually_cofinite_ne 0).mono fun x hx ↦ ?_)
  rw [eval_mul, eval_heckePoly w t hx, ← mul_div_cancel₀ x ha_ne, scaleRoots_eval_mul,
    eval_heckePoly w t' (div_ne_zero hx ha_ne), h_deg, ← mul_assoc,
    ← mul_pow, h_eigval, eval_prod, card_fin, pow_add, ← Fin.prod_const s, mul_mul_mul_comm,
    qPochhammer, Finset.prod_range, ← Finset.prod_mul_distrib, mul_div_cancel₀ x ha_ne, inv_div,
    mul_div_assoc', h_scale, one_div]
  -- What is left is one linear factor for each `l < s`.
  exact congrArg _ (Finset.prod_congr rfl fun l _ ↦ by simp [h_root, field])

omit [WeilData E] [DecidableEq n] in
/-- Let `c ≤ e`, `card n < s`, and let `κ'` agree with `κ` below `card n`, be `e - c` at `card n`
and `0` above. Then in rank `card n` the weight `(κ, e)` is also `(κ', c + κ' (card n))`, so a
parameter `l` of `(κ, e)` in rank `card n` and a parameter `l'` of `(κ', 0)` in rank `card n + s`
correspond. -/
private lemma paramsCorrespond_of_isHCParam {κ κ' : InfinitePlace E → ℕ → ℕ}
    {e c : InfinitePlace E → ℤ} {s : ℕ} (hc : c ≤ e)
    (hκ : κ' = fun (v : InfinitePlace E) (h : ℕ) ↦
      if h < card n then κ v h else if h = card n then (e v - c v).toNat else 0)
    (hs : card n < s) {l : InfinitePlace E → n → ℤ} {l' : InfinitePlace E → Fin (card n + s) → ℤ}
    (hl : IsHCParam (n := n) κ e l) (hl' : IsHCParam (n := Fin (card n + s)) κ' 0 l') :
    ParamsCorrespond 0 c l l' 1 1 := by
  -- `hcParameter` reads `κ'` only at heights below `card n`, where it is `κ`, and
  -- `c + κ' (card n) = c + (e - c) = e`; so `l` is also a parameter of `(κ', c + κ' (card n))`.
  have h_hcParameter_eq (w : InfinitePlace E) (p : ℕ) :
      hcParameter κ' (fun τ ↦ c τ + (κ' τ (card n) : ℤ)) (card n) w p =
        hcParameter κ e (card n) w p := by
    have h_sum : (Finset.Ioo p (card n)).sum (κ' w) = (Finset.Ioo p (card n)).sum (κ w) :=
      Finset.sum_congr rfl fun h hh ↦ by grind
    have h_top : c w + (κ' w (card n) : ℤ) = e w := by grind [Pi.le_def]
    simp only [hcParameter, diagramWeight_apply, h_sum, h_top]
  have hl_weight : IsHCParam (n := n) κ' (fun τ ↦ c τ + (κ' τ (card n) : ℤ)) l := by
    simpa only [IsHCParam, h_hcParameter_eq] using hl
  have h_lift_weight : IsLiftWeight n (Fin (card n + s)) κ' c (fun τ ↦ c τ + (κ' τ (card n) : ℤ)) :=
    ⟨by grind [card_fin], by simp [hs.pos], rfl⟩
  exact (hl_weight.paramsCorrespond_iff h_lift_weight).mpr hl'

omit [DecidableEq n] in
/-- The scalars of the theta lift at the place `w` cancel: `q_w ^ s * frobValue 1 n w`, divided by
`b.frobValue (Fin (card n + s)) w` (scalars at `w` built from powers of `√q_w` and values at a
uniformiser) and multiplied by the value at `w` of the algebraic Hecke character
`hb.toAlgebraic s s`, is `1`. Here `b` is a character of `U(1)` of weight `c`. -/
private lemma frobValue_div_mul_heckeCoeff_eq_one {b : AutChar E} {c : InfinitePlace E → ℤ}
    (hb : b.HasWeight c 1) (s : ℕ) (w : FinPlace E) :
    w.q ^ s * frobValue 1 n w / b.frobValue (Fin (card n + s)) w *
      heckeCoeff (hb.toAlgebraic s s).val.fst ∅ w = 1 := by
  simp [HasWeight.toAlgebraic, frobValue, w.coe_q_eq_sq_sqrt, HeckeChar.atUniformizer, heckeCoeff,
    AutChar.spaceChar, zpow_sub₀, zpow_mul (_ : ℂ), field]
  -- What is left is a rearrangement of powers of `√q_w` and of `υ` at a uniformiser.
  ring

omit [DecidableEq n] in
/-- For `l < s`, the value at `w` of the algebraic Hecke character `hb.toAlgebraic (card n + s)
(s - l)` is `q_w ^ l * frobValue 1 n w` times that of `hb.toAlgebraic s s`. Here `b` is a character
of `U(1)` of weight `c`. -/
private lemma heckeCoeff_toAlgebraic_eq {b : AutChar E} {c : InfinitePlace E → ℤ}
    (hb : b.HasWeight c 1) {s : ℕ} (w : FinPlace E) (l : Fin s) :
    heckeCoeff (hb.toAlgebraic (card n + s) (s - l)).val.fst ∅ w =
      w.q ^ (l : ℕ) * frobValue 1 n w * heckeCoeff (hb.toAlgebraic s s).val.fst ∅ w := by
  simp [HasWeight.toAlgebraic, frobValue, w.coe_q_eq_sq_sqrt, HeckeChar.atUniformizer, heckeCoeff,
    AutChar.spaceChar, zpow_add₀, zpow_sub₀, zpow_mul (_ : ℂ), field]

/-- Rallis' inner product formula makes the theta lift injective on forms of level `J`. Let `b` be
a character of `U(1)` of weight `c`, `v` an edge from type `l` to type `l'` (`IsEdge`), `Ψ` sharp
for `b` and a level `J` (`IsSharp`), and `2 * card n < card n + s`. If the algebraic form of `y`
is not zero and is fixed by `J`, then the algebraic form of the lift of `y` by `v ⊗ Ψ` is not
zero. -/
private lemma toAlgForm_formLift_ne_zero {κ κ' : InfinitePlace E → ℕ → ℕ}
    {e c : InfinitePlace E → ℤ} {s : ℕ} {b : AutChar E} (hb : b.HasWeight c 1)
    {l : InfinitePlace E → n → ℤ} {l' : InfinitePlace E → Fin (card n + s) → ℤ}
    (hl : IsHCParam (n := n) κ e l) (hl' : IsHCParam (n := Fin (card n + s)) κ' 0 l')
    {v : Fock.fockSpace (realSigns E (homSigns 1 1))}
    (h_edge : IsEdge (realPairWeil 0 c) (typeKernel l 1) (typeKernel l' 1) v)
    (h_rank : 2 * card n < card (Fin (card n + s)))
    {S : Set (FinPlace E)} {Ψ : 𝒮 ((stdSpace E n).hom (stdSpace E (Fin (card n + s))))}
    {J : Subgroup (Gf E n)} {mass : ℂ} (h_sharp : IsSharp b S Ψ J mass)
    {y : (stdSpace E n).Form (typeKernel l 1)}
    (hJ : J ≤ rightStabilizer (toAlgForm (stdSpace E n) hl y).val)
    (hy_ne : (toAlgForm (stdSpace E n) hl y).val ≠ 0) :
    (toAlgForm (stdSpace E (Fin (card n + s))) hl'
      (formLift (pairThetaKer (stdSpace E n) (stdSpace E (Fin (card n + s))) 1 b)
        (typeKernel l 1) (typeKernel l' 1) (integrated _ v Ψ) y)).val ≠ 0 := by
  intro h_zero
  have hy_level : HasLevel y J := fun k hk ↦ by
    simp [← ofAlgForm_toAlgForm hl, algFormCoeff, hJ hk _]
  obtain ⟨A, -, h_rallis⟩ := rallis_inner_product_cosetTerm h_edge h_rank
  have hy : y = 0 := (h_rallis 1 b h_sharp y hy_level).1
    ((toAlgForm _ hl').map_eq_zero_iff.mp (Submodule.coe_eq_zero.mp h_zero))
  simp [hy] at hy_ne

omit [DecidableEq n] in
/-- Let `F ≠ 0` be a form of rank `card n + s` that is spherical at the split place `w`
(`star w ≠ w`), and on which the Hecke polynomial operator at `X` acts by `qPochhammer w.q s
(frobValue 1 n w * X) * heckePolyEval n w t (r * X)`, with `qPochhammer w.q s Y` a product over
`l < s` of factors linear in `q_w ^ l * Y`, where `r = q_w ^ s * frobValue 1 n w / b.frobValue (Fin
(card n + s)) w` and `b` is a character of `U(1)` of weight `c`. Then `F` has a Hecke polynomial `Q`
at `w` (`HasHeckePolyAt`), and `Q` with its roots multiplied by the value at `w` of
`hb.toAlgebraic s s` is `heckePoly w.q (card n) t` times `∏ l < s, (X - θ l)`, where `θ l` is the
value at `w` of `hb.toAlgebraic (card n + s) (s - l)`. -/
private lemma exists_hasHeckePolyAt_scaleRoots_eq {κ' : InfinitePlace E → ℕ → ℕ} {s : ℕ}
    {b : AutChar E} {c : InfinitePlace E → ℤ} (hb : b.HasWeight c 1) {w : FinPlace E}
    (hw : star w ≠ w) {t : ℕ → ℂ}
    {F : Gf E (Fin (card n + s)) → WeylIndex (Fin (card n + s)) κ' → ℂ} (hF_ne : F ≠ 0)
    (hF_sph : HasHeckePolynomial
      (rightRegular ℂ (Gf E (Fin (card n + s))) (WeylIndex (Fin (card n + s)) κ' → ℂ)) hw
      (fun X : ℂ ↦ qPochhammer w.q s (frobValue 1 n w * X) *
        heckePolyEval n w t (w.q ^ s * frobValue 1 n w / b.frobValue (Fin (card n + s)) w * X))
      F) :
    ∃ Q : ℂ[X],
      HasHeckePolyAt F w hw Q ∧
      Q.scaleRoots (heckeCoeff (hb.toAlgebraic s s).val.fst ∅ w) =
        heckePoly w.q (card n) t *
          ∏ l : Fin s, (X - C (heckeCoeff (hb.toAlgebraic (card n + s) (s - l)).val.fst ∅ w)) := by
  -- The operators `T_i` act on `F` by scalars `t' i`; these give its Hecke polynomial `Q`.
  obtain ⟨t', ht'⟩ : ∃ t' : ℕ → ℂ, ∀ i,
      heckeSplit (rightRegular ℂ (Gf E (Fin (card n + s))) (WeylIndex (Fin (card n + s)) κ' → ℂ))
        hw i F = t' i • F :=
    (exists_heckeSplit_eq_smul _).imp fun _ h_all ↦ h_all F hF_sph
  obtain ⟨hF_spherical, hF_eigval⟩ := hF_sph
  have hF_eig : HasHeckePolyAt F w hw (heckePoly w.q (card (Fin (card n + s))) t') :=
    ⟨hF_spherical, t', rfl, ht'⟩
  -- Two expressions for the eigenvalue of the Hecke polynomial on `F ≠ 0`.
  have h_eigval (X : ℂ) : heckePolyEval (Fin (card n + s)) w t' X =
      heckePolyEval n w t (w.q ^ s * frobValue 1 n w / b.frobValue (Fin (card n + s)) w * X) *
        qPochhammer w.q s (frobValue 1 n w * X) := by
    obtain ⟨-, hF_eigval'⟩ := hasHeckePolynomial_of_heckeSplit hF_spherical ht'
    rw [mul_comm, ← smul_left_inj hF_ne, ← hF_eigval X]
    exact (hF_eigval' X).symm
  refine ⟨_, hF_eig, ?_⟩
  -- The constants of `hasHeckePolynomial_formLift` are values of the algebraic characters.
  exact scaleRoots_heckePoly_eq w
    (fun l ↦ heckeCoeff (hb.toAlgebraic (card n + s) (s - l)).val.fst ∅ w)
    (hF_eig.isMonicOfDegree hF_ne).natDegree_eq h_eigval
    (frobValue_div_mul_heckeCoeff_eq_one hb s w) (heckeCoeff_toAlgebraic_eq hb w)

/-- Theta lift by `s > n` steps. Let `f ≠ 0` be a form of rank `n ≥ 1` and weight `(κ, e)`, and let
`b` be a character of `U(1)` of weight `c ≤ e` with trivial tame part (`b u = ∏ u_v^{c v}` for `u`
with integral finite part). Let `κ' v h` be `κ v h` for `h < n`, `e v - c v` for `h = n` and `0` for
`h > n`. There is a form `F` of rank `n + s` and weight `(κ', 0)` such that (a) `F ≠ 0`; (b) `F` is
fixed by `K_w` wherever `f` is; (c) at such a split `w`, if `f` has Hecke polynomial `P`, then `F`
has a Hecke polynomial `Q`, and `Q` with its roots multiplied by the value of `hb.toAlgebraic s s`
at `w` equals `P * ∏ l < s, (X - θ l)`, where `θ l` is the value of `hb.toAlgebraic (n + s) (s - l)`
at `w`. Here `hb.toAlgebraic` gives the algebraic Hecke characters `b(x/x̄) υ(x)^{−k} |x|^{j−k/2}`,
evaluated at a uniformiser at `w` (`heckeCoeff`). -/
lemma exists_theta_lift_heckePoly [Nonempty n] {κ κ' : InfinitePlace E → ℕ → ℕ}
    {e : InfinitePlace E → ℤ} {s : ℕ} {c : InfinitePlace E → ℤ} {b : AutChar E}
    (hb : b.HasWeight c 1) (hc : c ≤ e)
    (hκ : κ' = fun (v : InfinitePlace E) (h : ℕ) ↦
      if h < card n then κ v h else if h = card n then (e v - c v).toNat else 0)
    (f : AlgForm n κ e) (hf_ne : f.val ≠ 0) (hs : card n < s) :
    ∃ F ∈ (stdSpace E (Fin (card n + s))).forms (κ', 0),
      F ≠ 0 ∧
      ∀ {w : FinPlace E},
        f.val ∈ sphericalAt (rightRegular ℂ (Gf E n) (WeylIndex n κ → ℂ)) w →
        F ∈ sphericalAt
          (rightRegular ℂ (Gf E (Fin (card n + s))) (WeylIndex (Fin (card n + s)) κ' → ℂ)) w ∧
        ∀ {hw : star w ≠ w} {P : ℂ[X]},
          HasHeckePolyAt f.val w hw P →
          ∃ Q : ℂ[X],
            HasHeckePolyAt F w hw Q ∧
            Q.scaleRoots (heckeCoeff (hb.toAlgebraic s s).val.fst ∅ w) =
              P * ∏ l : Fin s,
                (X - C (heckeCoeff (hb.toAlgebraic (card n + s) (s - l)).val.fst ∅ w)) := by
  -- `F` is the theta lift of `f` by the datum made of joint harmonics at infinity and a sharp
  -- finite datum. Rallis' formula shows `F ≠ 0`, and `hasHeckePolynomial_formLift` transfers the
  -- Hecke eigenvalues.
  obtain ⟨l, hl⟩ : ∃ l, IsHCParam (n := n) κ e l := ⟨_, isHCParam_hcParameter n κ e⟩
  obtain ⟨l', hl'⟩ : ∃ l', IsHCParam (n := Fin (card n + s)) κ' 0 l' :=
    ⟨_, isHCParam_hcParameter (Fin (card n + s)) κ' 0⟩
  have h_rank : 2 * card n < card (Fin (card n + s)) := by grind [card_fin]
  -- In rank `n` the weight `(κ, e)` is also `(κ', c + κ' (card n))`: the columns below `card n`
  -- agree, and `c + (e - c) = e`. So `l` and `l'` correspond (`paramsCorrespond_of_isHCParam`),
  -- which gives the datum at infinity: a Fock vector `v`, an edge from type `l` to type `l'`.
  obtain ⟨v, h_edge⟩ : ∃ v, IsEdge (realPairWeil 0 c) (typeKernel l 1) (typeKernel l' 1) v :=
    ⟨_, (paramsCorrespond_of_isHCParam hc hκ hs hl hl').isEdge_jointHarmonic⟩
  -- The finite datum `Ψ`: sharp for a level `J` that fixes `f` (a smooth form has an open
  -- stabiliser), with bad set `S` avoiding the places where `f` is spherical.
  obtain ⟨S, hS, Ψ, J, hJ, mass, h_sharp⟩ :=
    exists_isSharp_of_two_mul_card_le (H := rightStabilizer f.val)
      (Submodule.mem_inf.mp f.property).left hb h_rank.le
  -- `v ⊗ Ψ` is an arrow: it lifts forms of type `l` to forms of type `l'`.
  have h_arr : IsArrow (pairThetaKer (stdSpace E n) (stdSpace E (Fin (card n + s))) 1 b)
      (typeKernel l 1) (typeKernel l' 1) (integrated _ v Ψ) :=
    (h_edge.isArrow 1 b h_sharp.mem_finitePart).left
  -- Write `f` as the algebraic form attached to an adelic form `y`, and lift `y`.
  obtain ⟨y, rfl⟩ := (toAlgForm (stdSpace E n) hl).surjective f
  let y' : (stdSpace E (Fin (card n + s))).Form (typeKernel l' 1) :=
    formLift (pairThetaKer (stdSpace E n) (stdSpace E (Fin (card n + s))) 1 b) (typeKernel l 1)
      (typeKernel l' 1) (integrated _ v Ψ) y
  let F : Gf E (Fin (card n + s)) → WeylIndex (Fin (card n + s)) κ' → ℂ := (toAlgForm _ hl' y').val
  -- By Rallis' formula the lift is injective on forms of level `J`, as `2 * n < n + s`.
  have hF : F ≠ 0 := toAlgForm_formLift_ne_zero hb hl hl' h_edge h_rank h_sharp hJ hf_ne
  refine ⟨F, (toAlgForm _ hl' y').property, hF, fun {w} h_sph ↦ ?_⟩
  -- Where `f` is spherical, the datum is the vacuum.
  have h_le : maxCompactAt n w ≤ rightStabilizer ((stdSpace E n).toAlgForm hl y).val := by
    simpa [funext_iff, LE.le] using h_sph
  have h_vac : projOn _ {w} (integrated _ v Ψ) = integrated _ v Ψ :=
    h_sharp.vacuum_off {w} v (Set.disjoint_singleton_right.mpr (hS w h_le))
  refine ⟨fun k ↦ ?_, ?_⟩
  · -- `k` acts on the lift through the datum, and it fixes the vacuum at `w`.
    have h_transl :
        rightRegular ℂ (Gf E (Fin (card n + s))) (WeylIndex (Fin (card n + s)) κ' → ℂ)
            (k : Gf E (Fin (card n + s))) F =
          (toAlgForm _ hl' ((stdSpace E (Fin (card n + s))).formRep (typeKernel l' 1) k y')).val :=
      congrArg Subtype.val (toAlgForm_formRep hl' k y').symm
    rw [h_transl, h_arr.formRep_formLift 1, pairWeil_eq_smul_of_projOn_eq _ h_vac]
    · simp [F, y', Prod.mk_one_one]
    -- the two side conditions of `pairWeil_eq_smul_of_projOn_eq`
    all_goals simp
  rintro hw P ⟨-, t, rfl, ht⟩
  -- The eigenvalue of the Hecke polynomial on `y` comes from the `t j`; on the lift it is
  -- rescaled and multiplied by `qPochhammer`, the factor of the `s` new steps.
  have hy_sph :
      HasHeckePolynomial ((stdSpace E n).formRep (typeKernel l 1)) hw (heckePolyEval n w t) y :=
    (hasHeckePolynomial_toAlgForm_iff _ hl).mp (hasHeckePolynomial_of_heckeSplit h_sph ht)
  have hF_sph : HasHeckePolynomial
      (rightRegular ℂ (Gf E (Fin (card n + s))) (WeylIndex (Fin (card n + s)) κ' → ℂ)) hw
      (fun X ↦ qPochhammer w.q s (frobValue 1 n w * X) *
        heckePolyEval n w t (w.q ^ s * frobValue 1 n w / b.frobValue (Fin (card n + s)) w * X))
      F :=
    (hasHeckePolynomial_toAlgForm_iff _ hl').mpr <| hasHeckePolynomial_formLift (card_fin _)
      (by simp [CharUnramifiedAt]) (hb.charUnramifiedAt rfl rfl) hw h_vac h_arr hy_sph
  exact exists_hasHeckePolyAt_scaleRoots_eq hb hw hF hF_sph

end New
