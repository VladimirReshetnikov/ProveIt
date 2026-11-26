import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.DiophantineNumberTheory.Coprime
import IPRADerivations.Core.ProdLemmas

/-!
# The positive half-angle roots of a Ravi triangle

Packet: `geometry/mollweide_circle_ipra`, the positive-root layer of Sections 3 and 6
(`lem:positive-root`, `lem:unit-equations`, `lem:four-products`, (3.7)/(3.10) and (3.12), `lem:cot-basic`,
`thm:cotangent-law` cleared). All quantities of the certified triangle are positive, so they are taken
as natural numbers: Ravi parameters `x, y, z ≥ 1` with `s = x + y + z`, `a = y + z`, `b = z + x`,
`c = x + y`, and half-angle components `s_A, c_A, …` given by their cleared squares (3.6)

  `b c s_A² = y z`, `b c c_A² = s x`, `c a s_B² = z x`, `c a c_B² = s y`, `a b s_C² = x y`, `a b c_C² = s z`.

* `pos_root` (`lem:positive-root`): `u² = v²` with `u, v ≥ 0` gives `u = v`;
* `unit_A`, … (`lem:unit-equations`): `s_A² + c_A² = 1`, cancelling the positive `b c`;
* `prod1`–`prod4` (`lem:four-products`, (3.8)): `c s_A c_B = y c_C`, `c c_A s_B = x c_C`, `c c_A c_B = s s_C`,
  `c s_A s_B = z s_C`, by comparing squares times the positive `(bc)(ca)(ab)`;
* `area_A`, … ((3.7), (3.10)): `b c s_A c_A = K` for `K² = s x y z`; `side_A` ((3.12)): `a = 2 d s_A c_A`
  for `2 K d = a b c`;
* `cot_A`, … (`lem:cot-basic`, i.e. `thm:cotangent-law` cleared): `r c_A = x s_A` for `r s = K`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.MollweideRoots

open_ipra
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (sq_inj)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Ring certificates -/

section Ring

variable {R : Type*} [CommRing R] {x y z sA cA sB cB sC cC K d r : R}

theorem unit_ring (hs : (z + x) * (x + y) * (sA * sA) = y * z) (hc : (z + x) * (x + y) * (cA * cA) = (x + y + z) * x) :
    (z + x) * (x + y) * (sA * sA + cA * cA) = (z + x) * (x + y) * 1 := by
  linear_combination hs + hc

theorem prod1_ring (hsA : (z + x) * (x + y) * (sA * sA) = y * z) (hcB : (x + y) * (y + z) * (cB * cB) = (x + y + z) * y)
    (hcC : (y + z) * (z + x) * (cC * cC) = (x + y + z) * z) :
    ((z + x) * (x + y) * ((x + y) * (y + z)) * ((y + z) * (z + x))) * ((x + y) * sA * cB * ((x + y) * sA * cB)) =
      ((z + x) * (x + y) * ((x + y) * (y + z)) * ((y + z) * (z + x))) * (y * cC * (y * cC)) := by
  linear_combination ((x + y) ^ 2 * ((y + z) * (z + x)) * ((x + y) * (y + z) * (cB * cB))) * hsA +
    ((x + y) ^ 2 * ((y + z) * (z + x)) * (y * z)) * hcB - (y ^ 2 * ((z + x) * (x + y)) * ((x + y) * (y + z))) * hcC

theorem prod2_ring (hcA : (z + x) * (x + y) * (cA * cA) = (x + y + z) * x) (hsB : (x + y) * (y + z) * (sB * sB) = z * x)
    (hcC : (y + z) * (z + x) * (cC * cC) = (x + y + z) * z) :
    ((z + x) * (x + y) * ((x + y) * (y + z)) * ((y + z) * (z + x))) * ((x + y) * cA * sB * ((x + y) * cA * sB)) =
      ((z + x) * (x + y) * ((x + y) * (y + z)) * ((y + z) * (z + x))) * (x * cC * (x * cC)) := by
  linear_combination ((x + y) ^ 2 * ((y + z) * (z + x)) * ((x + y) * (y + z) * (sB * sB))) * hcA +
    ((x + y) ^ 2 * ((y + z) * (z + x)) * ((x + y + z) * x)) * hsB - (x ^ 2 * ((z + x) * (x + y)) * ((x + y) * (y + z))) * hcC

theorem prod3_ring (hcA : (z + x) * (x + y) * (cA * cA) = (x + y + z) * x) (hcB : (x + y) * (y + z) * (cB * cB) = (x + y + z) * y)
    (hsC : (y + z) * (z + x) * (sC * sC) = x * y) :
    ((z + x) * (x + y) * ((x + y) * (y + z)) * ((y + z) * (z + x))) * ((x + y) * cA * cB * ((x + y) * cA * cB)) =
      ((z + x) * (x + y) * ((x + y) * (y + z)) * ((y + z) * (z + x))) * ((x + y + z) * sC * ((x + y + z) * sC)) := by
  linear_combination ((x + y) ^ 2 * ((y + z) * (z + x)) * ((x + y) * (y + z) * (cB * cB))) * hcA +
    ((x + y) ^ 2 * ((y + z) * (z + x)) * ((x + y + z) * x)) * hcB -
    ((x + y + z) ^ 2 * ((z + x) * (x + y)) * ((x + y) * (y + z))) * hsC

theorem prod4_ring (hsA : (z + x) * (x + y) * (sA * sA) = y * z) (hsB : (x + y) * (y + z) * (sB * sB) = z * x)
    (hsC : (y + z) * (z + x) * (sC * sC) = x * y) :
    ((z + x) * (x + y) * ((x + y) * (y + z)) * ((y + z) * (z + x))) * ((x + y) * sA * sB * ((x + y) * sA * sB)) =
      ((z + x) * (x + y) * ((x + y) * (y + z)) * ((y + z) * (z + x))) * (z * sC * (z * sC)) := by
  linear_combination ((x + y) ^ 2 * ((y + z) * (z + x)) * ((x + y) * (y + z) * (sB * sB))) * hsA +
    ((x + y) ^ 2 * ((y + z) * (z + x)) * (y * z)) * hsB - (z ^ 2 * ((z + x) * (x + y)) * ((x + y) * (y + z))) * hsC

theorem area_ring (hs : (z + x) * (x + y) * (sA * sA) = y * z) (hc : (z + x) * (x + y) * (cA * cA) = (x + y + z) * x)
    (hK : K * K = (x + y + z) * x * y * z) :
    (z + x) * (x + y) * sA * cA * ((z + x) * (x + y) * sA * cA) = K * K := by
  linear_combination ((z + x) * (x + y) * (cA * cA)) * hs + (y * z) * hc - hK

theorem cot_ring (hs : (z + x) * (x + y) * (sA * sA) = y * z) (hc : (z + x) * (x + y) * (cA * cA) = (x + y + z) * x)
    (hK : K * K = (x + y + z) * x * y * z) (hr : r * (x + y + z) = K) :
    ((z + x) * (x + y) * ((x + y + z) * (x + y + z))) * (r * cA * (r * cA)) =
      ((z + x) * (x + y) * ((x + y + z) * (x + y + z))) * (x * sA * (x * sA)) := by
  linear_combination ((x + y) * (z + x) * (cA * cA) * (r * (x + y + z) + K)) * hr + ((x + y + z) * x) * hK +
    (K * K) * hc - ((x + y + z) * (x + y + z) * x * x) * hs

end Ring

/-! ## Positivity -/

theorem pos_add_r {x : PTm n} (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) (z : PTm n) : Γ ⊢[PRAAx] z + x ≐ succ (pred (z + x)) :=
  AnalyticNumberTheory.Primes.eq_succ_pred (y := z + pred x) ((congrAdd (.eqRefl _) hx).eqTrans (by ipra_ring))

theorem pos_add_l {x : PTm n} (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) (y : PTm n) : Γ ⊢[PRAAx] x + y ≐ succ (pred (x + y)) :=
  (congrAdd (.eqRefl _) (.eqRefl _) : Γ ⊢[PRAAx] x + y ≐ x + y).eqTrans
    ((add_comm _ _).eqTrans ((pos_add_r hx y).eqTrans (congrSucc (congrPred (add_comm _ _)))))

/-! ## The positive roots -/

/-- `lem:positive-root`: nonnegative square roots are unique. -/
theorem pos_root {u v : PTm n} (h : Γ ⊢[PRAAx] u * u ≐ v * v) : Γ ⊢[PRAAx] u ≐ v := sq_inj h

section Triangle

variable {x y z sA cA sB cB sC cC : PTm n}
  (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) (hy : Γ ⊢[PRAAx] y ≐ succ (pred y)) (hz : Γ ⊢[PRAAx] z ≐ succ (pred z))

include hx in
/-- `lem:unit-equations` at `A`: `s_A² + c_A² = 1`. -/
theorem unit_A (hs : Γ ⊢[PRAAx] (z + x) * (x + y) * (sA * sA) ≐ y * z)
    (hc : Γ ⊢[PRAAx] (z + x) * (x + y) * (cA * cA) ≐ (x + y + z) * x) : Γ ⊢[PRAAx] sA * sA + cA * cA ≐ one := by
  refine mul_cancel (D := (z + x) * (x + y)) (pos_mul' (pos_add_r hx z) (pos_add_l hx y)) ?_
  have a := natEq hs; have b := natEq hc
  apply deriveNat; ipra_simps
  linear_combination unit_ring (x := 𝔞 x) (y := 𝔞 y) (z := 𝔞 z) (sA := 𝔞 sA) (cA := 𝔞 cA)
    (by linear_combination a) (by linear_combination b)

include hx hy hz

theorem D_pos : Γ ⊢[PRAAx] (z + x) * (x + y) * ((x + y) * (y + z)) * ((y + z) * (z + x)) ≐
    succ (pred ((z + x) * (x + y) * ((x + y) * (y + z)) * ((y + z) * (z + x)))) :=
  pos_mul' (pos_mul' (pos_mul' (pos_add_r hx z) (pos_add_l hx y)) (pos_mul' (pos_add_l hx y) (pos_add_l hy z)))
    (pos_mul' (pos_add_l hy z) (pos_add_r hx z))

/-- `lem:four-products`, (3.8a): `c s_A c_B = y c_C`. -/
theorem prod1 (hsA : Γ ⊢[PRAAx] (z + x) * (x + y) * (sA * sA) ≐ y * z)
    (hcB : Γ ⊢[PRAAx] (x + y) * (y + z) * (cB * cB) ≐ (x + y + z) * y)
    (hcC : Γ ⊢[PRAAx] (y + z) * (z + x) * (cC * cC) ≐ (x + y + z) * z) :
    Γ ⊢[PRAAx] (x + y) * sA * cB ≐ y * cC := by
  refine pos_root (mul_cancel (D_pos hx hy hz) ?_)
  have a := natEq hsA; have b := natEq hcB; have c := natEq hcC
  apply deriveNat; ipra_simps
  linear_combination prod1_ring (x := 𝔞 x) (y := 𝔞 y) (z := 𝔞 z) (sA := 𝔞 sA) (cB := 𝔞 cB) (cC := 𝔞 cC)
    (by linear_combination a) (by linear_combination b) (by linear_combination c)

/-- (3.8a): `c c_A s_B = x c_C`. -/
theorem prod2 (hcA : Γ ⊢[PRAAx] (z + x) * (x + y) * (cA * cA) ≐ (x + y + z) * x)
    (hsB : Γ ⊢[PRAAx] (x + y) * (y + z) * (sB * sB) ≐ z * x)
    (hcC : Γ ⊢[PRAAx] (y + z) * (z + x) * (cC * cC) ≐ (x + y + z) * z) :
    Γ ⊢[PRAAx] (x + y) * cA * sB ≐ x * cC := by
  refine pos_root (mul_cancel (D_pos hx hy hz) ?_)
  have a := natEq hcA; have b := natEq hsB; have c := natEq hcC
  apply deriveNat; ipra_simps
  linear_combination prod2_ring (x := 𝔞 x) (y := 𝔞 y) (z := 𝔞 z) (cA := 𝔞 cA) (sB := 𝔞 sB) (cC := 𝔞 cC)
    (by linear_combination a) (by linear_combination b) (by linear_combination c)

/-- (3.8b): `c c_A c_B = s s_C`. -/
theorem prod3 (hcA : Γ ⊢[PRAAx] (z + x) * (x + y) * (cA * cA) ≐ (x + y + z) * x)
    (hcB : Γ ⊢[PRAAx] (x + y) * (y + z) * (cB * cB) ≐ (x + y + z) * y)
    (hsC : Γ ⊢[PRAAx] (y + z) * (z + x) * (sC * sC) ≐ x * y) :
    Γ ⊢[PRAAx] (x + y) * cA * cB ≐ (x + y + z) * sC := by
  refine pos_root (mul_cancel (D_pos hx hy hz) ?_)
  have a := natEq hcA; have b := natEq hcB; have c := natEq hsC
  apply deriveNat; ipra_simps
  linear_combination prod3_ring (x := 𝔞 x) (y := 𝔞 y) (z := 𝔞 z) (cA := 𝔞 cA) (cB := 𝔞 cB) (sC := 𝔞 sC)
    (by linear_combination a) (by linear_combination b) (by linear_combination c)

/-- (3.8b): `c s_A s_B = z s_C`. -/
theorem prod4 (hsA : Γ ⊢[PRAAx] (z + x) * (x + y) * (sA * sA) ≐ y * z)
    (hsB : Γ ⊢[PRAAx] (x + y) * (y + z) * (sB * sB) ≐ z * x)
    (hsC : Γ ⊢[PRAAx] (y + z) * (z + x) * (sC * sC) ≐ x * y) :
    Γ ⊢[PRAAx] (x + y) * sA * sB ≐ z * sC := by
  refine pos_root (mul_cancel (D_pos hx hy hz) ?_)
  have a := natEq hsA; have b := natEq hsB; have c := natEq hsC
  apply deriveNat; ipra_simps
  linear_combination prod4_ring (x := 𝔞 x) (y := 𝔞 y) (z := 𝔞 z) (sA := 𝔞 sA) (sB := 𝔞 sB) (sC := 𝔞 sC)
    (by linear_combination a) (by linear_combination b) (by linear_combination c)

end Triangle

section Scale

variable {x y z sA cA K d r : PTm n}

/-- (3.7), (3.10): `b c s_A c_A = K` for `K² = s x y z`. -/
theorem area_A (hs : Γ ⊢[PRAAx] (z + x) * (x + y) * (sA * sA) ≐ y * z)
    (hc : Γ ⊢[PRAAx] (z + x) * (x + y) * (cA * cA) ≐ (x + y + z) * x) (hK : Γ ⊢[PRAAx] K * K ≐ (x + y + z) * x * y * z) :
    Γ ⊢[PRAAx] (z + x) * (x + y) * sA * cA ≐ K := by
  refine pos_root ?_
  have a := natEq hs; have b := natEq hc; have k := natEq hK
  apply deriveNat; ipra_simps
  linear_combination area_ring (x := 𝔞 x) (y := 𝔞 y) (z := 𝔞 z) (sA := 𝔞 sA) (cA := 𝔞 cA) (K := 𝔞 K)
    (by linear_combination a) (by linear_combination b) (by linear_combination k)

/-- (3.12): `a = 2 d s_A c_A` from `b c s_A c_A = K` and `2 K d = a b c`. -/
theorem side_A (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) (hA : Γ ⊢[PRAAx] (z + x) * (x + y) * sA * cA ≐ K)
    (hd : Γ ⊢[PRAAx] two * K * d ≐ (y + z) * (z + x) * (x + y)) :
    Γ ⊢[PRAAx] y + z ≐ two * d * sA * cA := by
  refine mul_cancel (D := (z + x) * (x + y)) (pos_mul' (pos_add_r hx z) (pos_add_l hx y)) ?_
  ipra_lc -natEq hd - 2 * 𝔞 d * natEq hA

/-- `lem:cot-basic` (`thm:cotangent-law` cleared): `r c_A = x s_A` for `r s = K`. -/
theorem cot_A (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) (hs : Γ ⊢[PRAAx] (z + x) * (x + y) * (sA * sA) ≐ y * z)
    (hc : Γ ⊢[PRAAx] (z + x) * (x + y) * (cA * cA) ≐ (x + y + z) * x) (hK : Γ ⊢[PRAAx] K * K ≐ (x + y + z) * x * y * z)
    (hr : Γ ⊢[PRAAx] r * (x + y + z) ≐ K) : Γ ⊢[PRAAx] r * cA ≐ x * sA := by
  have hS : Γ ⊢[PRAAx] x + y + z ≐ succ (pred (x + y + z)) := pos_add_l (pos_add_l hx y) z
  refine pos_root (mul_cancel (D := (z + x) * (x + y) * ((x + y + z) * (x + y + z)))
    (pos_mul' (pos_mul' (pos_add_r hx z) (pos_add_l hx y)) (pos_mul' hS hS)) ?_)
  have a := natEq hs; have b := natEq hc; have k := natEq hK; have e := natEq hr
  apply deriveNat; ipra_simps
  linear_combination cot_ring (x := 𝔞 x) (y := 𝔞 y) (z := 𝔞 z) (sA := 𝔞 sA) (cA := 𝔞 cA) (K := 𝔞 K) (r := 𝔞 r)
    (by linear_combination a) (by linear_combination b) (by linear_combination k) (by linear_combination e)

/-- `lem:geometric-halfangles`, the cosine half: with `cos A = (b² + c² − a²)/(2bc)`,
`c_A² − s_A² = cos A`, cleared as `2 b c c_A² + a² = b² + c² + 2 b c s_A²` (the sine half is `area_A`:
`2 s_A c_A = 2K/(bc) = sin A`). -/
theorem halfangle_cos {x y z sA cA : PTm n} (hs : Γ ⊢[PRAAx] (z + x) * (x + y) * (sA * sA) ≐ y * z)
    (hc : Γ ⊢[PRAAx] (z + x) * (x + y) * (cA * cA) ≐ (x + y + z) * x) :
    Γ ⊢[PRAAx] two * ((z + x) * (x + y)) * (cA * cA) + (y + z) * (y + z) ≐
      (z + x) * (z + x) + (x + y) * (x + y) + two * ((z + x) * (x + y)) * (sA * sA) := by
  ipra_lc 2 * natEq hc - 2 * natEq hs

end Scale

end LeanProofs.IPRA.Geometry.MollweideRoots
