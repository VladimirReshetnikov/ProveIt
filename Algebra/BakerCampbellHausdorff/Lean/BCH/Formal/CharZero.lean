/-
# The formal BCH theorem over an arbitrary field of characteristic zero

`BCH.Formal.LieSeries` proves the formal BCH theorem for `𝕂 = ℝ` or `ℂ`, because
its proof passes through the analytic Lie-series property. The article states it
over an arbitrary field of characteristic zero (Theorem 1.1(a), Theorem 3.6).
This file removes the restriction by base change, using that all the
coefficients involved are rational.

The bridge is Dynkin's identity `Zₙ = (1/n) R(Zₙ)`. Since `R(a)` is by
definition a linear combination of right-nested brackets of the generators,
`R(a)` is a Lie polynomial for *every* `a` (`R_mem_lieGen`), so the identity
immediately gives the theorem. The identity itself is transported:

* `mapCoeff f : 𝕂₁⟨X, Y⟩ →+* 𝕂₂⟨X, Y⟩` is the coefficientwise ring homomorphism
  induced by a ring homomorphism `f` of the coefficient fields; it commutes with
  the scalar action through `f` (`mapCoeff_smul`), fixes the generators, and
  commutes with `bchHom` and with `R` (`mapCoeff_bchHom`, `mapCoeff_R`).
* Over `ℚ` the identity follows from the case `𝕂 = ℝ` because
  `mapCoeff (Rat.castHom ℝ)` is injective (`bchHom_eq_inv_smul_R_rat`).
* Over any field of characteristic zero it follows from the case `ℚ` by applying
  `mapCoeff (Rat.castHom 𝕂)` (`bchHom_eq_inv_smul_R_charZero`).

The results are `bchHom_eq_inv_smul_R_charZero`, `bchHom_eq_dynkin_charZero` and
`bchHom_mem_lieGen_charZero`.
-/
import BCH.Formal.Dynkin
import BCH.Formal.LieSeries

open Finset

attribute [local instance 100] LieRing.ofAssociativeRing

namespace BCH

section MapCoeff

variable {𝕂₁ 𝕂₂ : Type*} [Field 𝕂₁] [Field 𝕂₂] (f : 𝕂₁ →+* 𝕂₂)

/-- The coefficientwise ring homomorphism `𝕂₁⟨X, Y⟩ → 𝕂₂⟨X, Y⟩` induced by a ring
homomorphism of the coefficient fields. -/
noncomputable def mapCoeff : FreeTwo 𝕂₁ →+* FreeTwo 𝕂₂ :=
  MonoidAlgebra.mapRingHom (FreeMonoid (Fin 2)) f

@[simp]
lemma coeff_mapCoeff (a : FreeTwo 𝕂₁) (w : FreeMonoid (Fin 2)) :
    (mapCoeff f a).coeff w = f (a.coeff w) :=
  MonoidAlgebra.coeff_mapRingHom _ _ _

lemma mapCoeff_single (w : FreeMonoid (Fin 2)) (c : 𝕂₁) :
    mapCoeff f (MonoidAlgebra.single w c) = MonoidAlgebra.single w (f c) :=
  MonoidAlgebra.mapRingHom_single _ _ _

lemma mapCoeff_injective (hf : Function.Injective f) : Function.Injective (mapCoeff f) := by
  intro a b hab
  refine MonoidAlgebra.coeff_injective ?_
  ext w
  exact hf (by rw [← coeff_mapCoeff f a w, ← coeff_mapCoeff f b w, hab])

/-- The coefficient map is compatible with the scalar action, through `f`. -/
lemma mapCoeff_smul (c : 𝕂₁) (a : FreeTwo 𝕂₁) :
    mapCoeff f (c • a) = f c • mapCoeff f a := by
  refine MonoidAlgebra.coeff_injective ?_
  ext w
  rw [coeff_mapCoeff, MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    Finsupp.smul_apply, coeff_mapCoeff, smul_eq_mul, smul_eq_mul, map_mul]

lemma mapCoeff_lie (a b : FreeTwo 𝕂₁) :
    mapCoeff f ⁅a, b⁆ = ⁅mapCoeff f a, mapCoeff f b⁆ := by
  rw [Ring.lie_def, Ring.lie_def, map_sub, map_mul, map_mul]

@[simp]
lemma mapCoeff_gen (i : Fin 2) : mapCoeff f (gen 𝕂₁ i) = gen 𝕂₂ i := by
  rw [gen, gen, mapCoeff_single, map_one]

@[simp]
lemma mapCoeff_genX : mapCoeff f (genX 𝕂₁) = genX 𝕂₂ := mapCoeff_gen f 0

@[simp]
lemma mapCoeff_genY : mapCoeff f (genY 𝕂₁) = genY 𝕂₂ := mapCoeff_gen f 1

/-- `f` maps the inverse of a natural number to the inverse of that natural number. -/
lemma map_natCast_inv (m : ℕ) : f ((m : 𝕂₁)⁻¹) = ((m : 𝕂₂))⁻¹ := by
  rw [map_inv₀, map_natCast]

lemma mapCoeff_expBlock (X Y : FreeTwo 𝕂₁) (d : ℕ) :
    mapCoeff f (expBlock 𝕂₁ X Y d) = expBlock 𝕂₂ (mapCoeff f X) (mapCoeff f Y) d := by
  rw [expBlock, expBlock, map_sum]
  refine sum_congr rfl fun p _ => ?_
  rw [mapCoeff_smul, map_mul, map_pow, map_pow, map_natCast_inv]

lemma mapCoeff_uBlock (X Y : FreeTwo 𝕂₁) (d : ℕ) :
    mapCoeff f (uBlock 𝕂₁ X Y d) = uBlock 𝕂₂ (mapCoeff f X) (mapCoeff f Y) d := by
  rw [uBlock, uBlock]
  split_ifs
  · exact map_zero _
  · exact mapCoeff_expBlock f X Y d

lemma mapCoeff_powBlock (X Y : FreeTwo 𝕂₁) :
    ∀ k n : ℕ, mapCoeff f (powBlock 𝕂₁ X Y k n) =
      powBlock 𝕂₂ (mapCoeff f X) (mapCoeff f Y) k n
  | 0, n => by
    rw [powBlock_zero, powBlock_zero]
    split_ifs
    · exact map_one _
    · exact map_zero _
  | k + 1, n => by
    rw [powBlock_succ, powBlock_succ, map_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [map_mul, mapCoeff_uBlock, mapCoeff_powBlock X Y k]

/-- The homogeneous components are natural in the coefficient field. -/
lemma mapCoeff_bchHom (X Y : FreeTwo 𝕂₁) (n : ℕ) :
    mapCoeff f (bchHom 𝕂₁ X Y n) = bchHom 𝕂₂ (mapCoeff f X) (mapCoeff f Y) n := by
  rw [bchHom, bchHom, map_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mapCoeff_smul, mapCoeff_powBlock, map_mul, map_pow, map_neg, map_one, map_natCast_inv]

lemma mapCoeff_rbList : ∀ l : List (Fin 2), mapCoeff f (rbList 𝕂₁ l) = rbList 𝕂₂ l
  | [] => map_zero _
  | [i] => mapCoeff_gen f i
  | i :: j :: rest => by
    rw [rbList, rbList, mapCoeff_lie, mapCoeff_gen, mapCoeff_rbList (j :: rest)]

lemma mapCoeff_rb (w : FreeMonoid (Fin 2)) : mapCoeff f (rb 𝕂₁ w) = rb 𝕂₂ w :=
  mapCoeff_rbList f _

/-- The right Dynkin operator is natural in the coefficient field. -/
lemma mapCoeff_R (a : FreeTwo 𝕂₁) : mapCoeff f (R a) = R (mapCoeff f a) := by
  have hc : (mapCoeff f a).coeff = Finsupp.mapRange f (map_zero f) a.coeff := by
    ext w
    rw [coeff_mapCoeff, Finsupp.mapRange_apply]
  rw [R_apply, R_apply, hc, Finsupp.sum_mapRange_index (fun w => by rw [zero_smul]),
    map_finsuppSum]
  exact Finsupp.sum_congr fun w _ => by rw [mapCoeff_smul, mapCoeff_rb]

end MapCoeff

section LieMem

variable {𝕂 : Type*} [Field 𝕂]

/-- A scalar multiple of a Lie polynomial is a Lie polynomial. -/
lemma smul_mem_lieGen (c : 𝕂) {a : FreeTwo 𝕂} (ha : a ∈ lieGen 𝕂) : c • a ∈ lieGen 𝕂 := by
  rw [← LieSubalgebra.mem_toSubmodule]
  exact (lieGen 𝕂).toSubmodule.smul_mem c ((LieSubalgebra.mem_toSubmodule _).mpr ha)

lemma gen_mem_lieGen : ∀ i : Fin 2, gen 𝕂 i ∈ lieGen 𝕂
  | 0 => genX_mem_lieGen
  | 1 => genY_mem_lieGen

/-- Every right-nested bracket of generators is a Lie polynomial. -/
lemma rbList_mem_lieGen : ∀ l : List (Fin 2), rbList 𝕂 l ∈ lieGen 𝕂
  | [] => (lieGen 𝕂).zero_mem
  | [i] => gen_mem_lieGen i
  | i :: j :: rest =>
    (lieGen 𝕂).lie_mem (gen_mem_lieGen i) (rbList_mem_lieGen (j :: rest))

lemma rb_mem_lieGen (w : FreeMonoid (Fin 2)) : rb 𝕂 w ∈ lieGen 𝕂 := rbList_mem_lieGen _

/-- The image of the right Dynkin operator consists of Lie polynomials: `R a` is a linear
combination of right-nested brackets of the generators, for every `a`. -/
theorem R_mem_lieGen (a : FreeTwo 𝕂) : R a ∈ lieGen 𝕂 := by
  rw [R_apply, Finsupp.sum]
  exact sum_mem_lieGen _ fun w _ => smul_mem_lieGen _ (rb_mem_lieGen w)

end LieMem

section CharZero

variable {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂]

/-- Dynkin's identity `Zₙ = (1/n) R(Zₙ)` over `ℚ`, transported from the case `𝕂 = ℝ`
along the injective coefficient map `mapCoeff (Rat.castHom ℝ)`. -/
theorem bchHom_eq_inv_smul_R_rat {n : ℕ} (hn : 0 < n) :
    bchHom ℚ (genX ℚ) (genY ℚ) n = (n : ℚ)⁻¹ • R (bchHom ℚ (genX ℚ) (genY ℚ) n) := by
  have hinj : Function.Injective (mapCoeff (Rat.castHom ℝ)) :=
    mapCoeff_injective _ Rat.cast_injective
  refine hinj ?_
  rw [mapCoeff_smul, mapCoeff_R, mapCoeff_bchHom, mapCoeff_genX, mapCoeff_genY,
    map_natCast_inv]
  exact bchHom_eq_inv_smul_R hn

/-- **Dynkin's identity over any field of characteristic zero**: `Zₙ = (1/n) R(Zₙ)`. -/
theorem bchHom_eq_inv_smul_R_charZero {n : ℕ} (hn : 0 < n) :
    bchHom 𝕂 (genX 𝕂) (genY 𝕂) n = (n : 𝕂)⁻¹ • R (bchHom 𝕂 (genX 𝕂) (genY 𝕂) n) := by
  have h := congrArg (mapCoeff (Rat.castHom 𝕂)) (bchHom_eq_inv_smul_R_rat hn)
  rwa [mapCoeff_bchHom, mapCoeff_genX, mapCoeff_genY, mapCoeff_smul, mapCoeff_R,
    mapCoeff_bchHom, mapCoeff_genX, mapCoeff_genY, map_natCast_inv] at h

/-- **Theorem 3.6, the formal BCH theorem, over an arbitrary field of characteristic zero**:
every homogeneous component `Zₙ(X, Y)` of `log(e^X e^Y)` in the free algebra `𝕂⟨X, Y⟩` is a
Lie polynomial in `X` and `Y`. -/
theorem bchHom_mem_lieGen_charZero (n : ℕ) : bchHom 𝕂 (genX 𝕂) (genY 𝕂) n ∈ lieGen 𝕂 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [bchHom_zero]
    exact (lieGen 𝕂).zero_mem
  · rw [bchHom_eq_inv_smul_R_charZero hn]
    exact smul_mem_lieGen _ (R_mem_lieGen _)

/-- **Theorem 4.1, equation (4.2), over an arbitrary field of characteristic zero**:
`Zₙ = (1/n) ∑_w c(w) R(w)`, with `c(w)` the coefficients of `Zₙ`. -/
theorem bchHom_eq_dynkin_charZero {n : ℕ} (hn : 0 < n) :
    bchHom 𝕂 (genX 𝕂) (genY 𝕂) n =
      (n : 𝕂)⁻¹ • (bchHom 𝕂 (genX 𝕂) (genY 𝕂) n).coeff.sum (fun w c => c • rb 𝕂 w) := by
  rw [← R_apply]
  exact bchHom_eq_inv_smul_R_charZero hn

end CharZero

end BCH
