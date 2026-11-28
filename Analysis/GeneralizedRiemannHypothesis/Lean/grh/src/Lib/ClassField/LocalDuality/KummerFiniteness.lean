import Lib.ClassField.GaloisCohomology.KummerCyclicClasses
import Lib.ClassField.GaloisCohomology.TateIndexFormula

/-!
# Index of l-th powers in a local field and finiteness of Kummer 1-cocycles

Let `L` be a local field with ring of integers `O`. `New.IsLocalGalois Γ L A` makes `Γ` the absolute
Galois group of `L`, acting on an algebraic closure `Ω` and stabilising its valuation ring `A`; then
`O = A ∩ L` is `New.valRingBelow L A`, a discrete valuation ring with finite residue field. Absolute
values `|x|` are the multiplicative valuation `A.valuation x`. This file counts the `l`-th power
classes in `Lˣ` and deduces the number of continuous 1-cocycles `Γ → Ωˣ` killed by `n`.

## Main definitions and results

* `New.cokerKerIndex_local_units`: `#(Lˣ / Lˣ ^ l) / #μ_l(L) = l · #(O / l)`.
* `New.IsLocalGalois.card_kummer_cocycles`: there are `n² · #(O / n)` continuous 1-cocycles
  `Γ → Ωˣ` killed by `n`; `New.IsLocalGalois.card_ker_natCast_Z1_unitsModule` and
  `New.IsLocalGalois.finite_ker_natCast_Z1_unitsModule` state the count and the finiteness apart.
* `New.IsLocalGalois.finite_Z1`: a finite discrete `Γ`-module has finitely many continuous
  1-cocycles.

Notions from other files:
* `New.cokerKerIndex`: `#coker / #ker` of a linear map, a rational number that is `0` if either
  group is infinite.
* `New.DiscreteModule`: a discrete `Γ`-module over `R`: an `R`-module with the discrete topology
  and a continuous `R`-linear action of the topological group `Γ`.
* `New.Z1 ρ`: the continuous 1-cocycles of the representation `ρ`; `New.unitsModule Γ` is `Ωˣ`,
  written additively, as a discrete `Γ`-module.

## Relation to the literature

Known; see `Lib.ClassField.LocalDuality.CrystallineDuality` for sources.
-/

/-!
## The index of l-th powers in the multiplicative group

It rests on a form of Hensel's lemma for l-th roots, proved first in the algebraic closure and then
descended by Galois invariance.
-/

section LocalPowerIndex

open Ideal Quotient Nat Polynomial Valuation IsLocalRing Function.Exact Module LinearMap

/-- Let `A` be a valuation subring of an algebraically closed field `Ω`, with absolute value
`|x| = A.valuation x`. If `r ≠ 0` and `|a - 1| ≤ |l| r`, then `a` has an `l`-th root `z` with
`|z - 1| ≤ r`. -/
lemma New.exists_root_near_one {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω)
    {l : ℕ} {a : Ω} {r : A.ValueGroup} (hr : r ≠ 0) (ha : A.valuation (a - 1) ≤ A.valuation l * r) :
    ∃ z : Ω, a = z ^ l ∧ A.valuation (z - 1) ≤ r := by
  by_contra! far
  have ha_ne : a ≠ 1 := by simpa using far 1
  -- The logarithmic derivative of `a - X ^ l` at `1` is `-l / (a - 1) = ∑ z, 1 / (1 - z)`, the sum
  -- over the roots. If all roots are far from `1`, every term has valuation `< r⁻¹`.
  let P : Ω [X] := C a - X ^ l
  have log_deriv : P.derivative.eval 1 / P.eval 1 = (P.roots.map fun z : Ω ↦ 1 / (1 - z)).sum :=
    (IsAlgClosed.splits P).eval_derivative_div_eval_of_ne_zero (by simp [P, sub_eq_zero, ha_ne])
  have small : P.derivative.eval 1 / P.eval 1 ∈ A.valuation.ltAddSubgroup (Units.mk0 r hr)⁻¹ := by
    rw [log_deriv]
    -- Each root `z` of `P` is far from `1`, so `|1 / (1 - z)| < r⁻¹`.
    refine AddSubgroup.multiset_sum_mem _ _ fun t ht ↦ ?_
    obtain ⟨z, hz_root, rfl⟩ := Multiset.mem_map.mp ht
    have h_far : r < A.valuation (z - 1) :=
      far z (by simpa [P, sub_eq_zero] using (mem_roots'.mp hz_root).2)
    simp [inv_strictAnti₀, map_sub_swap, pos_iff_ne_zero, h_far, hr]
  -- As `P' 1 / P 1 = -l / (a - 1)`, this says `|l| r < |a - 1|`.
  have h_lt : A.valuation (l : Ω) * r < A.valuation (a - 1) := by
    simpa [P, derivative_pow, field, ha_ne, lt_div_iff₀ (pos_iff_ne_zero.mpr hr), pos_iff,
      sub_eq_zero] using small
  exact ha.not_gt h_lt

/-- Hensel's lemma for `l`-th roots in a local field `L` with absolute Galois group `Γ`
(`New.IsLocalGalois Γ L A`), where `|x| = A.valuation x`: if `0 < r < |l|` and `|a - 1| ≤ |l| r`,
then `a = x ^ l` for some `x` in `L` with `|x - 1| ≤ r`. -/
lemma New.exists_local_root_near_one (Γ : Type*) {L Ω : Type} [Group Γ] [TopologicalSpace Γ]
    [Field L] [Field Ω] [Algebra L Ω] [MulSemiringAction Γ Ω] (A : ValuationSubring Ω)
    [hLocal : IsLocalGalois Γ L A] {l : ℕ} [NeZero l] {a : L} {r : A.ValueGroup} (hr : r ≠ 0)
    (hr_lt : r < A.valuation l) (ha : A.valuation (algebraMap L Ω a - 1) ≤ A.valuation l * r) :
    ∃ x : L, a = x ^ l ∧ A.valuation (algebraMap L Ω x - 1) ≤ r := by
  have h_alg_closed : IsAlgClosed Ω := hLocal.toIsAlgClosed
  obtain ⟨z, hz_pow, hz⟩ := exists_root_near_one A hr ha
  have val_z : A.valuation z = 1 := by
    simpa using map_eq_of_sub_lt _ ((hz.trans_lt hr_lt).trans_le (by simp))
  have hz_ne : z ≠ 0 := by simp [← A.valuation.zero_iff, val_z]
  -- `g • z / z` is an `l`-th root of unity closer to `1` than `|l|`, so it is `1`.
  have h_fixed : ∀ g : Γ, g • z = z := by
    intro g
    have h_smul : A.valuation (g • (z - 1)) ≤ r :=
      (decompGroup.val_smul (hLocal.mem_decompGroup g) _).trans_le hz
    have h_close : A.valuation (g • z / z - 1) < A.valuation l := by
      simpa [val_z, hz_ne, smul_sub, div_sub_one] using (map_sub_le _ h_smul hz).trans_lt hr_lt
    have h_ratio_pow : (g • z / z) ^ l = 1 := by
      rw [div_pow, ← smul_pow', show g • z ^ l = z ^ l by simp [← hz_pow],
        div_self (pow_ne_zero _ hz_ne)]
    exact eq_of_div_eq_one (eq_of_pow_eq_one_of_val_sub_lt h_ratio_pow (one_pow l) h_close)
  obtain ⟨x, rfl⟩ : ∃ a : L, algebraMap L Ω a = z := hLocal.isInvariant.isInvariant z h_fixed
  exact ⟨x, (algebraMap L Ω).injective (by simp [hz_pow]), hz⟩

/-- In a local field `L` with absolute Galois group `Γ` (`New.IsLocalGalois Γ L A`), the quotient of
the integers `O = New.valRingBelow L A` by a nonzero principal ideal is finite. -/
lemma New.IsLocalGalois.finite_quotient_span_singleton {Γ L Ω : Type} [Group Γ]
    [TopologicalSpace Γ] [Field L] [Field Ω] [Algebra L Ω] [MulSemiringAction Γ Ω]
    {A : ValuationSubring Ω} (hLocal : IsLocalGalois Γ L A) {x : valRingBelow L A} (hx : x ≠ 0) :
    Finite (valRingBelow L A ⧸ span {x}) := by
  have h_dvr : IsDiscreteValuationRing (valRingBelow L A) := hLocal.isDiscreteValuationRing
  have h_residue : Finite (ResidueField (valRingBelow L A)) := hLocal.finite_residue
  -- The ideal is a power of the maximal ideal, whose quotient is finite.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, span {x} = maximalIdeal (valRingBelow L A) ^ k :=
    exists_maximalIdeal_pow_eq_of_principal _ inferInstance (span {x})
      (span_singleton_eq_bot.ne.mpr hx)
  exact finite_quotient_iff.mpr ⟨k, hk.ge⟩

/-- Let `A` be a valuation subring of `Ω` and `L → Ω` a field embedding. An `l`-th root of unity
`u` in `L` with `|u - 1| < |l|` (for the valuation of `A`) is `1`. -/
lemma New.eq_one_of_pow_eq_one_of_valuation_sub_lt {L Ω : Type} [Field L] [Field Ω] [Algebra L Ω]
    {A : ValuationSubring Ω} {l : ℕ} {u : L} (h_pow : u ^ l = 1)
    (h_close : A.valuation (algebraMap L Ω u - 1) < A.valuation l) : u = 1 := by
  simpa using eq_of_pow_eq_one_of_val_sub_lt (x := algebraMap L Ω u)
    (by rw [← map_pow, h_pow, map_one]) (one_pow l) h_close

/-- The order at the maximal ideal as an additive map. Let `L` be a local field
(`New.IsLocalGalois Γ L A`) with absolute value `|x| = A.valuation x`, `π` a uniformiser and `Y` an
additive group isomorphic to `Lˣ` (by `y`). Then some surjective `f : Y → ℤ` has
`|y a| = |π| ^ n` exactly when `f a = n`. -/
lemma New.IsLocalGalois.exists_surjective_ord {Γ L Ω : Type} [Group Γ] [TopologicalSpace Γ]
    [Field L] [Field Ω] [Algebra L Ω] [MulSemiringAction Γ Ω] {A : ValuationSubring Ω}
    (hLocal : IsLocalGalois Γ L A) {π : Lˣ} (hπ : IsUniformiser A π.val) {Y : Type} [AddCommGroup Y]
    (y : Y ≃+ Additive Lˣ) :
    ∃ f : Y →+ ℤ, Function.Surjective f ∧ ∀ (a : Y) (n : ℤ),
      A.valuation.comap (algebraMap L Ω) (y a).toMul = A.valuation.comap (algebraMap L Ω) π ^ n ↔
        f a = n := by
  set w : Valuation L A.ValueGroup := A.valuation.comap (algebraMap L Ω)
  have h_ord_exists : ∀ a : Y, ∃ n : ℤ, w (y a).toMul = w π ^ n :=
    fun a ↦ hπ.exists_valuationVia_eq_zpow hLocal _ (y a).toMul.ne_zero
  choose ord h_ord using h_ord_exists
  have hπ_pos : 0 < w π := by simp [w, pos_iff]
  have ord_eq {a : Y} {n : ℤ} (h_val : w (y a).toMul = w π ^ n) : ord a = n :=
    zpow_right_injective₀ hπ_pos hπ.valuationVia_lt_one.ne ((h_ord a).symm.trans h_val)
  have ord_add (a b : Y) : ord (a + b) = ord a + ord b :=
    ord_eq <| by
      rw [zpow_add₀ hπ_pos.ne', ← h_ord, ← h_ord]
      simp [w]
  refine ⟨AddMonoidHom.mk' ord ord_add, fun n ↦ ?_, fun a n ↦ ⟨ord_eq, ?_⟩⟩
  · -- `f` is onto: `n` is the order of `π ^ n`.
    exact ⟨y.symm (n • .ofMul π), ord_eq (by simp)⟩
  · rintro rfl
    exact h_ord a

/-- The index of `l`-th powers in a field `L`, where `Γ = Gal(Ω/L)` with `Ω` algebraically closed of
characteristic 0 and `O = New.valRingBelow L A` a discrete valuation ring with finite residue field
(`New.IsLocalGalois Γ L A`). Let `l ≠ 0` and let `Y` be an additive group isomorphic to `Lˣ` (by
`y`). For multiplication by `l` on `Y`, the index `#(Y / l Y) / #Y[l]` (a) is not `0`, that is, both
groups are finite; (b) equals `l · #(O / l O)`. -/
lemma New.cokerKerIndex_local_units {Γ L Ω : Type} [Group Γ] [TopologicalSpace Γ] [Field L]
    [Field Ω] [Algebra L Ω] [MulSemiringAction Γ Ω] {A : ValuationSubring Ω}
    (hLocal : IsLocalGalois Γ L A) (l : ℕ) [NeZero l] {Y : Type} [AddCommGroup Y]
    (y : Y ≃+ Additive Lˣ) :
    -- (a) both groups are finite
    cokerKerIndex (l : End ℤ Y) ≠ 0 ∧
    -- (b) the value of the index
    cokerKerIndex (l : End ℤ Y) =
      l * Nat.card (valRingBelow L A ⧸ span {(l : valRingBelow L A)}) := by
  -- The index is multiplicative in `1 → Oˣ → Lˣ → ℤ → 0`, it is `l` on `ℤ`, and `Oˣ` may be
  -- replaced by the subgroup `V = 1 + l π O` of finite index. On `V` the `l`-th power map is
  -- injective, and `a ↦ (a - 1) / (l π)` identifies its cokernel with `O / l`.
  obtain ⟨π, hπ⟩ := hLocal.exists_isUniformiser
  -- The fields of `hLocal` (discrete valuation ring, finite residue field, …) as local instances.
  have h_fields := hLocal
  obtain ⟨⟩ := h_fields
  have h_char : CharZero L := (algebraMap L Ω).charZero
  -- `w` is the absolute value of `L`.
  set w : Valuation L A.ValueGroup := A.valuation.comap (algebraMap L Ω)
  have h_finite_l : Finite (valRingBelow L A ⧸ span {(l : valRingBelow L A)}) :=
    hLocal.finite_quotient_span_singleton (by simpa using NeZero.ne l)
  have lπ_lt : w (l * π) < A.valuation l := by simp [w, hπ.valuationVia_lt_one, pos_iff, NeZero.ne]
  have div_mem {x : L} : x / (l * π) ∈ valRingBelow L A ↔ w x ≤ w (l * π) := by
    simp [div_le_one₀, w, pos_iff, NeZero.ne]
  -- The order `f : Y → ℤ`, whose kernel is the unit group.
  obtain ⟨f₀, f_surj, h_ord⟩ := hLocal.exists_surjective_ord hπ y
  let f := f₀.toIntLinearMap
  have val_ker (a : f.ker) : w (y a).toMul = 1 := by
    simpa [w] using (h_ord a 0).mpr a.property
  -- `V` is the subgroup `1 + l π O` of the unit group.
  let V : Submodule ℤ f.ker :=
    (AddSubgroup.ofSub {a : f.ker | ((y a).toMul.val - 1) / (l * π) ∈ valRingBelow L A}
      ⟨0, by simp⟩ fun a ha b hb ↦ by
        -- As `|b| = 1`, `a / b - 1` has the absolute value of `(a - 1) - (b - 1)`.
        simpa [val_ker, div_mem, ← division_def, ← sub_div, div_sub_one] using
          sub_mem ha.out hb.out).toIntSubmodule
  -- The element `1 + x` of `V`, for `x ∈ l π O`.
  let oneAdd (x : L) (hx : w x ≤ w (l * π)) : V :=
    have h_val : w (1 + x) = 1 := w.map_one_add_of_lt ((hx.trans_lt lπ_lt).trans_le (by simp))
    have h_ne : 1 + x ≠ 0 := fun h_zero ↦ by simp [h_zero] at h_val
    have h_ker : f (y.symm (.ofMul (.mk0 (1 + x) h_ne))) = 0 :=
      (h_ord _ 0).mp (by simpa [w] using h_val)
    ⟨⟨y.symm (.ofMul (.mk0 (1 + x) h_ne)), h_ker⟩, div_mem.mpr (by simp_all)⟩
  -- Reduction modulo `l π` embeds `Oˣ / V` into the finite ring `O / l π`.
  have h_finite_index : Finite (f.ker ⧸ V) := by
    refine (hLocal.finite_quotient_span_singleton (x := l * ⟨π, hπ.valuationVia_lt_one.le⟩)
      (by simpa [Subtype.ext_iff] using NeZero.ne l)).of_injective
      (fun a ↦ mk _ ⟨(y a.out).toMul, (val_ker a.out).le⟩) fun a b hab ↦ ?_
    -- Equal residues mod `l π` of representatives put their quotient in `V`.
    have h_quot : w (((y (a.out - b.out : f.ker)).toMul : L) - 1) ≤ w (l * π) := by
      simpa [mk_span_eq_iff_dvd_sub, dvd_iff_valuationVia_le, val_ker, w, div_sub_one,
        valuationVia] using hab
    exact out_equiv_out.mp (V.quotientRel_def.mpr (div_mem.mpr h_quot))
  -- An `l`-th root of unity closer to `1` than `|l|` is `1`.
  have ker_pow : LinearMap.ker (l : End ℤ V) = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr fun a ha ↦ ?_
    have h_pow : (y a).toMul.val ^ l = 1 := by
      simpa using congrArg (fun v : V ↦ ((y v).toMul : L)) ha
    have h_close : A.valuation (algebraMap L Ω (y a).toMul - 1) < A.valuation l := by
      simpa [w] using (div_mem.mp a.property).trans_lt lπ_lt
    simpa using eq_one_of_pow_eq_one_of_valuation_sub_lt h_pow h_close
  -- `red a` is the class of `(a - 1) / (l π)` in `O / l`; it is additive by `h_defect`.
  have h_defect (s t : L) : (s * t - 1) / (l * π) - ((s - 1) / (l * π) + (t - 1) / (l * π)) =
      l * ((s - 1) / (l * π) * ((t - 1) / (l * π)) * π) := by field
  let red : V →ₗ[ℤ] valRingBelow L A ⧸ span {(l : valRingBelow L A)} :=
    (AddMonoidHom.mk' (fun a : V ↦ mk (span {(l : valRingBelow L A)}) ⟨_, a.property⟩) fun a b ↦ by
      refine mk_span_eq_iff_dvd_sub.mpr
        ⟨⟨_, a.property⟩ * ⟨_, b.property⟩ * ⟨π, hπ.valuationVia_lt_one.le⟩, Subtype.ext ?_⟩
      simpa using h_defect _ _).toIntLinearMap
  have red_surj : Function.Surjective red := by
    refine Quot.ind fun x ↦ ?_
    -- `x` is the image of `1 + x l π`.
    have h_le : w ((x : L) * (l * π)) ≤ w (l * π) := div_mem.mp (by simp [NeZero.ne])
    refine ⟨oneAdd ((x : L) * (l * π)) h_le, congrArg (Ideal.Quotient.mk _) (Subtype.ext ?_)⟩
    simp [oneAdd, NeZero.ne]
  have red_exact : Function.Exact (l : End ℤ V) red := by
    refine .of_comp_of_mem_range ?_ fun a ha ↦ ?_
    · ext
      simpa using mul_eq_zero_of_left (mk_singleton_self _) _
    · -- If `l ∣ (a - 1) / (l π)`, Hensel's lemma gives an `l`-th root of `a` in `V`.
      -- `ha`: `l` divides `(a - 1) / (l π)` in `O`, that is, `|(a - 1) / (l π)| ≤ |l|`.
      have h_near :
          A.valuation (algebraMap L Ω (y a).toMul.val - 1) ≤ A.valuation l * w (l * π) := by
        simpa [w, div_le_iff₀, NeZero.ne, valuationVia, pos_iff] using
          dvd_iff_valuationVia_le.mp ((eq_zero_iff_dvd (l : valRingBelow L A) _).mp ha)
      obtain ⟨x, hx_pow, hx⟩ :=
        exists_local_root_near_one Γ A (by simp [NeZero.ne]) lπ_lt h_near
      refine ⟨oneAdd (x - 1) (by simpa [w] using hx), Subtype.ext (Subtype.ext (y.injective ?_))⟩
      ext
      simp [oneAdd, hx_pow]
  -- Pass from `f.ker` to `V` (the inclusion has finite kernel and cokernel), and read off the
  -- kernel and the cokernel on `V`.
  have idx_units :
      cokerKerIndex (l : End ℤ f.ker) =
        Nat.card (valRingBelow L A ⧸ span {(l : valRingBelow L A)}) := by
    rw [← cokerKerIndex_natCast_eq_of_ne_zero V.subtype (by simp [ne_of_gt, cokerKerIndex]),
      cokerKerIndex, ker_pow, card_congr (red_exact.linearEquivOfSurjective red_surj).toEquiv]
    simp
  -- Split off `ℤ`, where the index is `l`.
  rw [cokerKerIndex_mul_of_exact _ f (by simp) f.exact_subtype_ker_map f_surj
      (by simp [idx_units, ne_of_gt]),
    idx_units, cokerKerIndex_eq_pow_finrank.right]
  simp [mul_comm, NeZero.ne]

end LocalPowerIndex

/-!
## Kummer count and finiteness of continuous 1-cocycles

`New.DiscreteUnits` is Ωˣ written additively, `New.unitsModule` the same as a discrete Γ-module, and
`New.Z1` the module of continuous 1-cocycles.
-/

section LocalFiniteness

open Nat Function HasEnoughRootsOfUnity NeZero LinearMap CommGroup Ideal

namespace New.IsLocalGalois

variable {Γ k Ω : Type} [Group Γ] [TopologicalSpace Γ] [Field k] [Field Ω] [Algebra k Ω]
  [MulSemiringAction Γ Ω] {A : ValuationSubring Ω}

/-- Kummer theory. Assume `New.IsLocalGalois Γ k A`: `Ω` is algebraically closed of characteristic
0, `Γ` is the Galois group of `Ω` over `k` and stabilises the valuation subring `A`, and
`O = New.valRingBelow k A = A ∩ k` is a discrete valuation ring with finite residue field (`k` need
not be complete). For `n ≠ 0`, let `c` be the number of continuous 1-cocycles `Γ → Ωˣ` killed by `n`
(those with values in the `n`-th roots of unity). Then (a) `c > 0`, which says that the group is
finite, since `Nat.card` of an infinite type is `0`; (b) `c = n² · #(O / n O)`.

It is proved from Hilbert 90, the multiplicativity of `New.cokerKerIndex` along
`1 → kˣ → Ωˣ → Z¹ → 1`, and `New.cokerKerIndex_local_units` on `kˣ`, not from Tate's local Euler
characteristic formula; it is a variant of Kummer theory; it counts 1-cocycles rather than
cohomology classes with values in the n-th roots of unity. -/
lemma card_kummer_cocycles [hLocal : IsLocalGalois Γ k A] (n : ℕ) [NeZero n] :
    let c := Nat.card (n : Module.End ℤ (Z1 (unitsModule Γ).ρ)).ker
    -- (a)
    0 < c ∧
    -- (b)
    c = n ^ 2 * Nat.card (valRingBelow k A ⧸ span {(n : valRingBelow k A)}) := by
  -- By Hilbert 90 the sequence `1 → kˣ → Ωˣ → Z¹ → 1` is exact, and the index `#coker / #ker` of
  -- multiplication by `n` is multiplicative in it. On `kˣ`, the group `K` of invariants of `Ωˣ`,
  -- it is `n · #(O / n)`.
  have h_surj : Surjective (unitsModule Γ).coboundary :=
    fun f ↦ (hilbert90_unitsRep f).imp (by aesop)
  let K : Submodule ℤ (DiscreteUnits Ω) := (unitsRep (Γ := Γ) (Ω := Ω)).invariants
  obtain ⟨h_ne, h_units⟩ : cokerKerIndex (n : Module.End ℤ K) ≠ 0 ∧
      cokerKerIndex (n : Module.End ℤ K) =
        n * Nat.card (valRingBelow k A ⧸ span {(n : valRingBelow k A)}) :=
    cokerKerIndex_local_units hLocal n
      (AddEquiv.ofBijective _ (DiscreteUnits.ofBase_bijective Γ)).symm
  -- The invariants are the kernel of the coboundary map `x ↦ (g ↦ g • x - x)`.
  have h_exact : Exact K.subtype (unitsModule Γ).coboundary := by
    simp [K, Exact, funext_iff, Subtype.ext_iff, sub_eq_zero]
  have h_mul :
      cokerKerIndex (n : Module.End ℤ (DiscreteUnits Ω)) =
        cokerKerIndex (n : Module.End ℤ K) *
          cokerKerIndex (n : Module.End ℤ (Z1 (unitsModule Γ).ρ)) :=
    cokerKerIndex_mul_of_exact K.subtype _ K.subtype_injective h_exact h_surj h_ne
  -- `Ωˣ` is divisible, hence so is its quotient `Z¹`; and `Ωˣ` has `n` elements killed by `n`.
  have h_div : Surjective fun x : DiscreteUnits Ω ↦ n • x := fun x ↦ x.exists_nsmul out
  have h_div' : Surjective fun f : Z1 (unitsModule Γ).ρ ↦ n • f :=
    .of_comp (by simpa [comp_def] using h_surj.comp h_div)
  -- `erw`: the `n`-torsion of `DiscreteUnits Ω` is `rootsOfUnity n Ω` only after unfolding.
  erw [h_units, cokerKerIndex, cokerKerIndex, range_eq_top.mpr h_div, range_eq_top.mpr h_div',
    natCard_rootsOfUnity] at h_mul
  -- What is left is an equation in `ℚ` for `c`, the number of cocycles killed by `n`.
  replace h_mul : (1 : ℚ) / n = n * Nat.card (valRingBelow k A ⧸ span {(n : valRingBelow k A)}) *
      (1 / Nat.card (n : Module.End ℤ (Z1 (unitsModule Γ).ρ)).ker) := by
    simpa [Nat.card_unique] using h_mul
  qify
  grind

/-- Let `k` be a local field with absolute Galois group `Γ` (`New.IsLocalGalois Γ k A`) and let
`n ≠ 0`. The continuous 1-cocycles `Γ → Ωˣ` killed by `n` form a finite group. -/
lemma finite_ker_natCast_Z1_unitsModule [IsLocalGalois Γ k A] (n : ℕ) [NeZero n] :
    Finite (n : Module.End ℤ (Z1 (unitsModule Γ).ρ)).ker :=
  Nat.finite_of_card_ne_zero (card_kummer_cocycles n).left.ne'

/-- Assume `New.IsLocalGalois Γ k A`: `Ω` is algebraically closed of characteristic 0, `Γ` is the
Galois group of `Ω` over `k` and stabilises the valuation subring `A`, and
`O = New.valRingBelow k A = A ∩ k` is a discrete valuation ring with finite residue field (`k` need
not be complete). Then for `n ≠ 0`, the number of continuous 1-cocycles `Γ → Ωˣ` killed by `n` is
`n² · #(O / n O)`. -/
lemma card_ker_natCast_Z1_unitsModule [IsLocalGalois Γ k A] (n : ℕ) [NeZero n] :
    Nat.card (n : Module.End ℤ (Z1 (unitsModule Γ).ρ)).ker =
      n ^ 2 * Nat.card (valRingBelow k A ⧸ span {(n : valRingBelow k A)}) :=
  (card_kummer_cocycles n).right

/-- If `k` is a local field with absolute Galois group `Γ` (`New.IsLocalGalois Γ k A`), then for
every finite discrete `Γ`-module `M` over a commutative ring `R`, the module `Z¹(Γ, M)` of
continuous 1-cocycles is finite.

A case of the finiteness of Galois cohomology of a local field: degree one, in characteristic 0,
stated for continuous 1-cocycles of a finite module rather than for H¹. -/
lemma finite_Z1 [IsLocalGalois Γ k A] ⦃R : Type⦄ [CommRing R] (M : DiscreteModule R Γ)
    [Finite M] : Finite (Z1 M.ρ) := by
  -- Let `U` be an open subgroup acting trivially on `Hom(M, Ωˣ)`. A cocycle `z` is determined by
  -- its values on representatives of `Γ / U` and by the cocycles `f ∘ z` of `U` in `Ωˣ`, for `f`
  -- in `Hom(M, Ωˣ)`. These are killed by `#M`, so Kummer theory over the fixed field of `U`
  -- leaves finitely many of them.
  obtain ⟨⟨U, hU_normal⟩, hU⟩ := exists_openNormalSubgroup_apply_eq M.cartierDual.continuous
  -- On `U` every `f : M →+ DiscreteUnits Ω` is equivariant (`using!`: the action on
  -- `M.cartierDual` in `hU` gives this equation only after unfolding).
  have h_equiv (f : M →+ DiscreteUnits Ω) (u : U.1) (x : M) :
      f (M.ρ u x) = unitsRep u.val (f x) := by
    simpa using! congr($(hU _ u.property f) (M.ρ u x)).symm
  -- Over the fixed field of `U` the cocycles killed by `#M` form a finite group.
  obtain ⟨h_card_pos, -⟩ := (of_finite U).isLocalGalois.card_kummer_cocycles (.card M)
  have hz_mul (z : Z1 M.ρ) (g h : Γ) : z.val (g * h) = z.val g + M.ρ g (z.val h) :=
    z.property.right g h
  -- `e` numbers the cocycles of `U` killed by `#M`; `res z f` is the number of `f ∘ z`
  -- (`using!`: the cocycle identity of `f ∘ z` comes from that of `z` only after unfolding).
  have e := equivFinOfCardPos h_card_pos.ne'
  let res (z : Z1 M.ρ) (f : M →+ DiscreteUnits Ω) :=
    e ⟨⟨fun u ↦ f (z.val u),
      continuous_of_discreteTopology.comp (z.property.left.comp continuous_subtype_val),
      fun g g' ↦ by simpa [hz_mul z] using! h_equiv f g _⟩,
      by simp [Subtype.ext_iff, funext_iff, ← map_nsmul]⟩
  refine .of_injective (fun z ↦ (fun q : Γ ⧸ U.1 ↦ z.val q.out, res z)) fun y z hyz ↦ ?_
  have h_out_eq : (fun q : Γ ⧸ U.1 ↦ y.val q.out) = fun q ↦ z.val q.out := congrArg Prod.fst hyz
  have h_res_eq : res y = res z := congrArg Prod.snd hyz
  ext g
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g
  -- Characters with values in `Ωˣ` separate the points of `M`, so `y` and `z` agree on `U`.
  have h_res : y.val u = z.val u := by
    refine (CommGroup.forall_apply_eq_apply_iff (Multiplicative M) (M := Ω)).mp fun f ↦ ?_
    exact congrArg (fun c ↦ c.val.val u) (e.injective (congrFun h_res_eq f.toAdditiveRight))
  -- On the representative `g * u` of the class of `g`, the two cocycles agree.
  have h_rep : y.val (g : Γ ⧸ U.1).out = z.val (g : Γ ⧸ U.1).out := congrFun h_out_eq g
  simpa [hz_mul y, hz_mul z, hu, h_res] using h_rep

end New.IsLocalGalois

end LocalFiniteness
