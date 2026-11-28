import Mathlib.LinearAlgebra.Projectivization.Basic
import Lib.Weil.Construction.FiniteMultiplier
import Lib.Weil.Unramified.HeckeGL

/-!
# Neighbours of the standard lattice

Let E be a CM field with Weil data (`WeilData E`, used here for a primitive 5040th root of unity,
hence √-1, and an element of trace 1), so that every finite place of its real subfield is split or
inert; let L = Ô^n be the standard lattice (`New.stdLattice`) with the form ⟨x, z⟩ = x* z, and w a
finite place of E with uniformiser ϖ and residue field k_w of order q_w. A vector x that is
supported at w, lies outside L, and has ϖx ∈ L and ⟨x, x⟩ integral defines a neighbour L₁ = L₀ + Ôx
of L, where L₀ = {z ∈ L : ⟨x, z⟩ integral}. A quasi-reflection ρ supported on w and its conjugate
maps L₁ into L. The same ρ serves all x with the same line of ϖx in k_w^n and the same residue of
ϖ⟨b, cx − b⟩, where b is a fixed such vector with this line and c a unit with cx − b ∈ L; these
residues number at most √q_w, and at most one if w is split. A lattice γL ≠ L, for γ unitary, holds
such a vector x at some place w, and passing from γ to ργ divides the index [L : L ∩ γ⁻¹L] = [γL : L
∩ γL] by at least q_w. So a step from L to L₁ towards γL is read as a step from γL to ργL towards L.
This file treats one step; the steps are summed in `Lib.SiegelWeil.UnramifiedSeries.RallisSeries`.

If w is split, L₁ is L enlarged by a line at w and cut down to a hyperplane at w̄. So the steps at w
and at w̄ go up by a line and down by a hyperplane at w. If w is inert, the line of ϖx determines L₀
and its dual L + Ôx, and the residues index the isotropic lines other than L/L₀ in the hermitian
plane (L + Ôx)/L₀.

## Main definitions and results

* `New.SiegelWeil.IsNeighbourVector`, `New.SiegelWeil.MapsNeighbour`: the vector x, and the relation
  ρL₁ ⊆ L.
* `New.SiegelWeil.neighbourResidues`: the residue classes that tell apart the neighbours with the
  same line; `New.SiegelWeil.card_neighbourResidues_le_one` and
  `New.SiegelWeil.card_neighbourResidues_sq_le` bound their number.
* `New.SiegelWeil.exists_family_mapsNeighbour`: a family of ρ, indexed by lines and residue classes,
  serves all x.
* `New.SiegelWeil.exists_isNeighbourVector_mulVec`: a lattice γL ≠ L holds such a vector.
* `New.SiegelWeil.q_mul_norm_finMultiplier_mul_sq_le`: one step lowers the index.

Notions from other files:
* `New.stdLattice E n`: the standard lattice Ô^n, where `Ô E` is the ring of integral finite adeles
  in the finite adele ring `𝔸f E`; `singleAdele w a` is the finite adele with component a at w and 0
  elsewhere, so `singleAdele w c • x` is the multiple c x at w.
* `New.finMultiplier γ`: its squared absolute value is the index [L : L ∩ γ⁻¹L].

## Relation to the literature

Known result: Kneser's neighbours. Here only the standard lattice over the integral finite adeles
and its translates by unitary elements are treated; split and inert places are treated by the same
step, taken at w or at its conjugate. Source: M. Greenberg, J. Voight, Lattice methods for algebraic
modular forms on classical groups (2014), section 5.
-/

namespace New.SiegelWeil

open NumberField Matrix WithZero Valued IsLocalRing

section NeighbourVector

variable {E n : Type*} [Field E] [NumberField E] {w : FinPlace E}

/-! ### Integral finite adeles and products at one place -/

/-- A finite adele that vanishes away from `w` and is integral at `w` is integral. -/
lemma mem_Ô_of_eq_zero_of_ne {s : 𝔸f E} (h_supp : ∀ u : FinPlace E, u ≠ w → s u = 0)
    (h_le : v (s w) ≤ 1) : s ∈ Ô E := by
  refine mem_Ô.2 fun u ↦ ?_
  rcases eq_or_ne u w with rfl | hu <;> simp [*]

lemma singleAdele_mem_Ô {a : LocField w} (ha : v a ≤ 1) : singleAdele w a ∈ Ô E :=
  mem_Ô_of_eq_zero_of_ne (fun _ hu ↦ singleAdele_of_ne hu a) (by rwa [singleAdele_same])

/-- Multiplication by the idempotent at `w` keeps the component at `w` and deletes the others. -/
lemma singleAdele_one_mul (s : 𝔸f E) : singleAdele w 1 * s = singleAdele w (s w) := by
  ext1 u
  rcases eq_or_ne u w with rfl | hu <;> simp [singleAdele_of_ne, *]

/-- The standard lattice contains the vectors with one integral coordinate and all others zero. -/
lemma single_mem_stdLattice [Fintype n] [DecidableEq n] {a : 𝔸f E} (ha : a ∈ Ô E) (k : n) :
    Pi.single k a ∈ stdLattice E n := by
  intro j
  rcases eq_or_ne j k with rfl | hj <;> simp [*]

/-- The component at `u` of the adelic product `x* z = ∑ j, x̄ j * z j`, computed in the local field
at `u`. -/
lemma star_dotProduct_apply [IsCMField E] [Fintype n] (x z : n → 𝔸f E) (u : FinPlace E) :
    (star x ⬝ᵥ z) u = ∑ j : n, star (x j) u * z j u :=
  map_sum (evalAt u) (fun j : n ↦ star (x j) * z j) Finset.univ

/-! ### Neighbour vectors and their residues -/

/-- The vector `x` defines a neighbour at `w` of the standard lattice `L`: it is supported at
`w`, `ϖ x ∈ L` and `x ∉ L` for a uniformiser `ϖ` at `w`, and its norm `x* x` is integral. -/
structure IsNeighbourVector [IsCMField E] [Fintype n] (w : FinPlace E) (x : n → 𝔸f E) : Prop where
  /-- The components away from `w` vanish. -/
  eq_zero_of_ne (j : n) : ∀ u : FinPlace E, u ≠ w → x j u = 0
  /-- The coordinates have poles of order at most one at `w`. -/
  v_le (j : n) : v (x j w) ≤ exp 1
  /-- Some coordinate has a pole at `w`. -/
  exists_v_eq : ∃ k : n, v (x k w) = exp 1
  /-- The norm is integral. -/
  norm_mem : star x ⬝ᵥ x ∈ Ô E

/-- The unitary element `ρ` maps the neighbour `L₀ + Ô x` into the standard lattice `L`, where
`L₀` is the lattice of the `z ∈ L` with `x* z` integral. -/
structure MapsNeighbour [IsCMField E] [Fintype n] [DecidableEq n] (ρ : Gf E n) (x : n → 𝔸f E) :
    Prop where
  /-- `ρ` maps `L₀` into `L`. -/
  mulVec_mem_of_dot_mem :
    ∀ z ∈ stdLattice E n, star x ⬝ᵥ z ∈ Ô E → ρ.val.val *ᵥ z ∈ stdLattice E n
  /-- `ρ` maps `x` into `L`. -/
  mulVec_mem : ρ.val.val *ᵥ x ∈ stdLattice E n

/-- The residue class of `ϖ s` at `w`, for the chosen uniformiser `ϖ` (and `0` if `ϖ s` is not
integral). -/
noncomputable def polarResidue (s : LocField w) : ResField w :=
  residueOrZero ((uniformizer w).val * s)

/-- The residue classes of `ϖ s` for the finite adeles `s` that are supported at `w`, have a pole
of order at most one and have integral trace `s + s̄`. They tell apart the neighbours that belong
to the same line: for `w` inert, a neighbour vector `b` and `a ∈ L`, the norm of `b + a` is integral
exactly when `s = b* a` has integral trace. -/
def neighbourResidues [IsCMField E] (w : FinPlace E) : Set (ResField w) :=
  {r : ResField w | ∃ s : 𝔸f E, (∀ u : FinPlace E, u ≠ w → s u = 0) ∧ v (s w) ≤ exp 1 ∧
    s + star s ∈ Ô E ∧ r = polarResidue (s w)}

lemma uniformizer_mul_mem {s : LocField w} (hs : v s ≤ exp 1) :
    (uniformizer w).val * s ∈ LocInt w := by
  rwa [mem_LocInt, map_mul, v_uniformizer, WithZero.exp_neg, inv_mul_le_one₀ exp_pos]

/-- If `s` has a pole of order at most one, its polar residue is the residue of the local integer
`ϖ s`. -/
lemma polarResidue_eq_residue {s : LocField w} (hs : v s ≤ exp 1) :
    polarResidue s = residue (LocInt w) ⟨(uniformizer w).val * s, uniformizer_mul_mem hs⟩ :=
  residueOrZero_coe (⟨(uniformizer w).val * s, uniformizer_mul_mem hs⟩ : LocInt w)

/-- An element with a pole of order at most one is integral if and only if its polar residue, the
residue class of `ϖ s`, vanishes. -/
lemma polarResidue_eq_zero_iff {s : LocField w} (hs : v s ≤ exp 1) :
    polarResidue s = 0 ↔ v s ≤ 1 := by
  rw [polarResidue, residueOrZero_eq_zero, map_mul, v_uniformizer, WithZero.exp_neg, Ne,
    inv_mul_eq_one₀ exp_ne_zero]
  refine ⟨fun h_ne ↦ ?_, fun h_le ↦ (h_le.trans_lt (by decide : (1 : ℤᵐ⁰) < exp 1)).ne'⟩
  have h_lt : v s < 1 * exp 1 := by simpa using hs.lt_of_ne' h_ne
  exact (lt_mul_exp_iff_le one_ne_zero).1 h_lt

/-- If `s` and `s'` have poles of order at most one, so does `s + c s'` for a local integer `c`. -/
lemma v_add_mul_le {s s' : LocField w} (hs : v s ≤ exp 1) (hs' : v s' ≤ exp 1) (c : LocInt w) :
    v (s + c * s') ≤ exp 1 :=
  v.map_add_le hs (by simpa using mul_le_mul' (mem_LocInt.1 c.prop) hs')

/-- The residue of a local integer vanishes if and only if it is not a unit. -/
lemma residue_eq_zero_iff_v_ne_one (a : LocInt w) :
    residue (LocInt w) a = 0 ↔ v (a : LocField w) ≠ 1 := by
  rw [← residueOrZero_coe, residueOrZero_eq_zero]

/-- On elements with a pole of order at most one, the polar residue is linear over the local
integers. -/
lemma polarResidue_add_mul {s s' : LocField w} (hs : v s ≤ exp 1) (hs' : v s' ≤ exp 1)
    (c : LocInt w) : polarResidue (s + (c : LocField w) * s') =
      polarResidue s + residue (LocInt w) c * polarResidue s' := by
  rw [polarResidue_eq_residue hs, polarResidue_eq_residue hs',
    polarResidue_eq_residue (v_add_mul_le hs hs' c), ← map_mul, ← map_add]
  exact congrArg _ (Subtype.ext (by simp [mul_add, mul_left_comm]))

/-- For `s`, `s'` with poles of order at most one, the polar residue of `s` is `c` times that of
`s'` if and only if `s - c s'` is integral. -/
lemma polarResidue_eq_mul_iff {s s' : LocField w} (hs : v s ≤ exp 1) (hs' : v s' ≤ exp 1)
    (c : LocInt w) :
    polarResidue s = residue (LocInt w) c * polarResidue s' ↔ v (s - c * s') ≤ 1 := by
  have h_sub : s - c * s' = s + (-c : LocInt w) * s' := by simp [sub_eq_add_neg]
  rw [h_sub, ← polarResidue_eq_zero_iff (v_add_mul_le hs hs' (-c)), polarResidue_add_mul hs hs',
    map_neg, neg_mul, add_neg_eq_zero]

/-- Two elements with poles of order at most one have the same polar residue if and only if their
difference is integral. -/
lemma polarResidue_eq_iff {s s' : LocField w} (hs : v s ≤ exp 1) (hs' : v s' ≤ exp 1) :
    polarResidue s = polarResidue s' ↔ v (s - s') ≤ 1 := by
  simpa using polarResidue_eq_mul_iff hs hs' 1

variable [IsCMField E]

/-- At a split place `w` (one that differs from its conjugate) there is at most one class in
`neighbourResidues w`, namely `0`: an integral trace `s + s̄` of an adele supported at `w` makes
`s` integral. -/
lemma card_neighbourResidues_le_one (hw : w.IsSplit) : Nat.card (neighbourResidues w) ≤ 1 := by
  have h_zero : ∀ r ∈ neighbourResidues w, r = 0 := by
    rintro _ ⟨s, h_supp, h_le, h_trace, rfl⟩
    -- As `w` is split, `star w ≠ w`, so `s̄` vanishes at `w`.
    have h_int : v (s w) ≤ 1 := by simpa [h_supp (star w) hw] using mem_Ô.1 h_trace w
    exact (polarResidue_eq_zero_iff h_le).2 h_int
  exact Finite.card_le_one_iff_subsingleton.2 (Set.subsingleton_of_forall_eq 0 h_zero).coe_sort

/-- If `y` is integral, `y - ȳ` has an integral inverse `d`, and `s + y t` and the traces of `s` and
`t` are integral, then `t` is integral. -/
lemma mem_Ô_of_add_mul_mem {d y s t : 𝔸f E} (hd : d ∈ Ô E) (hy : y ∈ Ô E)
    (h_inv : d * (y - star y) = 1) (hs : s + star s ∈ Ô E) (ht : t + star t ∈ Ô E)
    (h_mem : s + y * t ∈ Ô E) : t ∈ Ô E := by
  have h_eq : t = d * (s + y * t + star (s + y * t) - (s + star s) - star y * (t + star t)) := by
    simp only [star_add, star_mul]
    linear_combination -t * h_inv
  rw [h_eq]
  exact mul_mem hd (sub_mem (sub_mem (add_mem h_mem (star_mem_Ô h_mem)) hs)
    (mul_mem (star_mem_Ô hy) ht))

/-- Let `y` be integral with `y - ȳ` inverted by an integral `d`, and let `s`, `s'`, `t`, `t'`
be supported at `w`, with poles of order at most one and integral traces. If `s + y t` and
`s' + y t'` have the same polar residue at `w` (residue of `ϖ` times the component at `w`), then so
do `t` and `t'`. -/
lemma polarResidue_eq_of_add_mul_eq {d y s s' t t' : 𝔸f E} (hd : d ∈ Ô E) (hy : y ∈ Ô E)
    (h_inv : d * (y - star y) = 1) (hs_supp : ∀ u : FinPlace E, u ≠ w → s u = 0)
    (hs'_supp : ∀ u : FinPlace E, u ≠ w → s' u = 0) (ht_supp : ∀ u : FinPlace E, u ≠ w → t u = 0)
    (ht'_supp : ∀ u : FinPlace E, u ≠ w → t' u = 0) (hs_le : v (s w) ≤ exp 1)
    (hs'_le : v (s' w) ≤ exp 1) (ht_le : v (t w) ≤ exp 1) (ht'_le : v (t' w) ≤ exp 1)
    (hs_trace : s + star s ∈ Ô E) (hs'_trace : s' + star s' ∈ Ô E)
    (ht_trace : t + star t ∈ Ô E) (ht'_trace : t' + star t' ∈ Ô E)
    (h_res : polarResidue (s w + y w * t w) = polarResidue (s' w + y w * t' w)) :
    polarResidue (t w) = polarResidue (t' w) := by
  let Y : LocInt w := ⟨y w, mem_Ô.1 hy w⟩
  have h_int : v (s w + y w * t w - (s' w + y w * t' w)) ≤ 1 :=
    (polarResidue_eq_iff (v_add_mul_le hs_le ht_le Y) (v_add_mul_le hs'_le ht'_le Y)).1 h_res
  have h_mem : s - s' + y * (t - t') ∈ Ô E := mem_Ô_of_eq_zero_of_ne (w := w)
    (fun u hu ↦ by simp [hs_supp, hs'_supp, ht_supp, ht'_supp, hu])
    (by simpa [mul_sub, add_sub_add_comm] using h_int)
  have ht_sub : t - t' ∈ Ô E := mem_Ô_of_add_mul_mem hd hy h_inv
    (by simpa [add_sub_add_comm] using sub_mem hs_trace hs'_trace)
    (by simpa [add_sub_add_comm] using sub_mem ht_trace ht'_trace) h_mem
  exact (polarResidue_eq_iff ht_le ht'_le).2 (mem_Ô.1 ht_sub w)

/-- Let `E` contain a primitive 5040th root of unity (`HasPrimitiveRoot5040`). Then the number of
classes in `neighbourResidues w` (the residues of `ϖ s` for `s` supported at `w` with a pole of
order at most one and integral trace) is at most the square root of the order `q_w` of the residue
field at `w`. -/
lemma card_neighbourResidues_sq_le [HasPrimitiveRoot5040 E] :
    Nat.card (neighbourResidues w) ^ 2 ≤ w.q := by
  -- For an integer `y` with `y - ȳ` a unit, the map `(r, r') ↦ r + y r'` is injective on pairs of
  -- classes in `neighbourResidues w`.
  obtain ⟨y, hy⟩ : ∃ y : 𝓞 E, IsUnit (y - star y) := HasPrimitiveRoot5040.exists_isUnit_sub_star
  obtain ⟨d, hd⟩ := hy.exists_left_inv
  let ι (a : 𝓞 E) : 𝔸f E := algebraMap E (𝔸f E) a
  have h_int (a : 𝓞 E) : ι a ∈ Ô E := algebraMap_mem_Ô.2 a.prop
  have h_inv : ι d * (ι y - star (ι y)) = 1 := by simpa [ι] using congrArg ι hd
  let Y : LocInt w := ⟨ι y w, mem_Ô.1 (h_int y) w⟩
  have h_lift (r : neighbourResidues w) : ∃ s : 𝔸f E, (∀ u : FinPlace E, u ≠ w → s u = 0) ∧
      v (s w) ≤ exp 1 ∧ s + star s ∈ Ô E ∧ r = polarResidue (s w) := r.prop
  choose s hs_supp hs_le hs_trace hs_res using h_lift
  rw [sq, ← Nat.card_prod, ← card_ResField]
  refine Nat.card_le_card_of_injective (fun p : neighbourResidues w × neighbourResidues w ↦
    (p.1 : ResField w) + residue (LocInt w) Y * (p.2 : ResField w)) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ h_eq
  have h_res : polarResidue (s a w + (Y : LocField w) * s b w) =
      polarResidue (s a' w + (Y : LocField w) * s b' w) := by
    simpa only [polarResidue_add_mul (hs_le _) (hs_le _), ← hs_res] using h_eq
  have hb : (b : ResField w) = b' := by
    rw [hs_res b, hs_res b']
    exact polarResidue_eq_of_add_mul_eq (h_int d) (h_int y) h_inv (hs_supp a) (hs_supp a')
      (hs_supp b) (hs_supp b') (hs_le a) (hs_le a') (hs_le b) (hs_le b') (hs_trace a)
      (hs_trace a') (hs_trace b) (hs_trace b') h_res
  have ha : (a : ResField w) = a' := by simpa [hb] using h_eq
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)

/-! ### The line of a neighbour vector -/

variable [Fintype n] {x b : n → 𝔸f E}

/-- The reduction of `ϖ x` modulo `w`, whose coordinates are the polar residues of those of `x`,
is not zero, for a neighbour vector `x`. -/
lemma IsNeighbourVector.polarResidue_ne_zero (hx : IsNeighbourVector w x) :
    (fun j : n ↦ polarResidue (x j w)) ≠ 0 := by
  obtain ⟨k, hk⟩ := hx.exists_v_eq
  refine Function.ne_iff.2 ⟨k, ?_⟩
  simp [polarResidue_eq_zero_iff (hx.v_le k), hk, ← exp_zero]

/-- The line spanned by the reduction of `ϖ x` modulo `w`, for a neighbour vector `x`. -/
noncomputable def IsNeighbourVector.line (hx : IsNeighbourVector w x) :
    Projectivization (ResField w) (n → ResField w) :=
  Projectivization.mk (ResField w) (fun j : n ↦ polarResidue (x j w)) hx.polarResidue_ne_zero

/-- A multiple of a neighbour vector by a local unit is a neighbour vector. -/
lemma IsNeighbourVector.smul (hx : IsNeighbourVector w x) {c : LocField w} (hc : v c = 1) :
    IsNeighbourVector w (singleAdele w c • x) where
  eq_zero_of_ne j u hu := by simp [hx.eq_zero_of_ne j u hu]
  v_le j := by simpa [hc] using hx.v_le j
  exists_v_eq := by simpa [hc] using hx.exists_v_eq
  norm_mem := by
    have hc_mem : singleAdele w c ∈ Ô E := singleAdele_mem_Ô hc.le
    simpa using mul_mem hc_mem (mul_mem (star_mem_Ô hc_mem) hx.norm_mem)

/-- Two neighbour vectors with the same line differ, after scaling by a local unit, by a vector of
the standard lattice. -/
lemma IsNeighbourVector.exists_smul_sub_mem (hb : IsNeighbourVector w b)
    (hx : IsNeighbourVector w x) (h_line : hb.line = hx.line) :
    ∃ c : LocField w, v c = 1 ∧ singleAdele w c • x - b ∈ stdLattice E n := by
  obtain ⟨a, ha⟩ : ∃ a : (ResField w)ˣ,
      a • (fun j : n ↦ polarResidue (x j w)) = fun j : n ↦ polarResidue (b j w) :=
    (Projectivization.mk_eq_mk_iff ..).1 h_line
  obtain ⟨c, hc⟩ : ∃ c : LocInt w, residue (LocInt w) c = a := residue_surjective _
  have hc_val : v (c : LocField w) = 1 :=
    by_contra fun h_ne ↦ hc.trans_ne a.ne_zero ((residue_eq_zero_iff_v_ne_one c).2 h_ne)
  refine ⟨c, hc_val, fun j ↦ mem_Ô_of_eq_zero_of_ne (w := w)
    (fun u hu ↦ by simp [hx.eq_zero_of_ne j u hu, hb.eq_zero_of_ne j u hu]) ?_⟩
  have h_res : polarResidue (b j w) = residue (LocInt w) c * polarResidue (x j w) := by
    simpa [hc, Units.smul_def] using (congrFun ha j).symm
  simpa [Valuation.map_sub_swap v (b j w)] using
    (polarResidue_eq_mul_iff (hb.v_le j) (hx.v_le j) c).1 h_res

/-- For neighbour vectors `b` and `x` at `w`, the product `⟨b, x - b⟩` vanishes away from `w`. -/
lemma IsNeighbourVector.star_dotProduct_sub_eq_zero_of_ne (hb : IsNeighbourVector w b)
    (hx : IsNeighbourVector w x) (u : FinPlace E) (hu : u ≠ w) : (star b ⬝ᵥ (x - b)) u = 0 := by
  simp [star_dotProduct_apply, hx.eq_zero_of_ne _ u hu, hb.eq_zero_of_ne _ u hu]

/-- For a neighbour vector `b` at `w` and a vector `z` of the standard lattice, the product
`b* z = star b ⬝ᵥ z` has a pole of order at most one at `w`. -/
lemma IsNeighbourVector.v_star_dotProduct_le (hb : IsNeighbourVector w b) {z : n → 𝔸f E}
    (hz : z ∈ stdLattice E n) : v ((star b ⬝ᵥ z) w) ≤ exp 1 := by
  rw [star_dotProduct_apply]
  refine v.map_sum_le fun j _ ↦ ?_
  grw [map_mul, v_star_apply, mem_Ô.1 (hz j) w, mul_one]
  rcases eq_or_ne (star w) w with hw | hw
  · rw [hw]
    exact hb.v_le j
  · simp [hb.eq_zero_of_ne j _ hw]

/-- If `a x` and `a' x` are congruent modulo the standard lattice, for a neighbour vector `x` and
local integers `a` and `a'`, then `a` and `a'` have the same residue. -/
lemma IsNeighbourVector.residue_eq_of_smul_mem (hx : IsNeighbourVector w x) {a a' : LocInt w}
    (h_mem : (-singleAdele w (a : LocField w) + singleAdele w (a' : LocField w)) • x ∈
      stdLattice E n) : residue (LocInt w) a = residue (LocInt w) a' := by
  obtain ⟨k, hk⟩ := hx.exists_v_eq
  set d : LocInt w := -a + a' with hd
  have h_le : v (d : LocField w) * exp 1 ≤ 1 := by simpa [hk, hd] using mem_Ô.1 (h_mem k) w
  have h_ne : v (d : LocField w) ≠ 1 := fun h_one ↦ by simp +decide [h_one] at h_le
  simpa [hd, neg_add_eq_zero] using (residue_eq_zero_iff_v_ne_one d).2 h_ne

/-! ### A quasi-reflection maps the neighbour into the standard lattice -/

/-- Let the coordinate `x k` of a neighbour vector have a pole at `w`, and let `t` be integral and,
away from `w`, inverse to an integral `t'`. Then `x k + t` has an integral inverse `c`, and `c x`
lies in the standard lattice. -/
lemma IsNeighbourVector.exists_mul_add_eq_one (hx : IsNeighbourVector w x) {k : n}
    (hk : v (x k w) = exp 1) {t t' : 𝔸f E} (ht : t ∈ Ô E) (ht' : t' ∈ Ô E)
    (h_inv : ∀ u : FinPlace E, u ≠ w → t' u * t u = 1) :
    ∃ c ∈ Ô E, c * (x k + t) = 1 ∧ c • x ∈ stdLattice E n := by
  have h_lt : v (t w) < v (x k w) := ((mem_Ô.1 ht w).trans_lt (by decide)).trans_eq hk.symm
  have h_val : v (x k w + t w) = exp 1 := (v.map_add_eq_of_lt_left h_lt).trans hk
  have h_ne : x k w + t w ≠ 0 := v.ne_zero_iff.1 (h_val.trans_ne exp_ne_zero)
  have h_inv_le : v (x k w + t w)⁻¹ ≤ 1 := by simp +decide [h_val]
  -- The inverse is `1 / (x k + t)` at `w` and `t'` at the other places.
  set c : 𝔸f E := singleAdele w (x k w + t w)⁻¹ + (1 - singleAdele w 1) * t' with hc
  have hc_apply : c w = (x k w + t w)⁻¹ := by simp [hc]
  have hc_mem : c ∈ Ô E := add_mem (singleAdele_mem_Ô h_inv_le)
    (mul_mem (sub_mem (one_mem _) (singleAdele_mem_Ô (by simp))) ht')
  refine ⟨c, hc_mem, ?_, fun j ↦ mem_Ô_of_eq_zero_of_ne (w := w)
    (fun u hu ↦ by simp [hx.eq_zero_of_ne j u hu]) ?_⟩
  · ext1 u
    rcases eq_or_ne u w with rfl | hu
    · simp [hc_apply, h_ne]
    · simpa [hc, singleAdele_of_ne hu, hx.eq_zero_of_ne k u hu] using h_inv u hu
  · have h_le : v ((x k w + t w)⁻¹ * x j w) ≤ 1 := by
      rw [map_mul, map_inv₀, h_val, inv_mul_le_one₀ exp_pos]
      exact hx.v_le j
    simpa [hc_apply] using h_le

end NeighbourVector

section Reflection

section

variable {E n : Type*} [Field E] [NumberField E] [IsCMField E] [Fintype n] [DecidableEq n]

/-- Let `u` be a vector that vanishes away from a set `S` of places and its conjugate, and let `c`
satisfy `c + c̄ = c̄ c ⟨u, u⟩`. Then the quasi-reflection `z ↦ z - c ⟨u, z⟩ u` is a unitary element
`ρ` supported on `S` and its conjugate, that is, its components at all other places are `1`. -/
lemma exists_quasiReflection {S : Set (FinPlace E)} {u : n → 𝔸f E} {c : 𝔸f E}
    (h_supp : ∀ a : FinPlace E, a ∉ S → star a ∉ S → ∀ i : n, u i a = 0)
    (h_trace : c + star c = star c * c * (star u ⬝ᵥ u)) :
    ∃ ρ ∈ Gf.supportedOn n S,
      ∀ z : n → 𝔸f E, (ρ : Matrix n n (𝔸f E)) *ᵥ z = z - (c * (star u ⬝ᵥ z)) • u := by
  -- The matrix `R = 1 - c P` with `P = u u*` is unitary for the standard form (whose matrix is
  -- `1`), as `P² = ⟨u, u⟩ P`.
  set P : Matrix n n (𝔸f E) := vecMulVec u (star u) with hP
  have hP_star : Pᴴ = P := by rw [hP, conjTranspose_vecMulVec, star_star]
  have hP_sq : P * P = (star u ⬝ᵥ u) • P := by simp [hP, vecMulVec_mul_vecMulVec, vecMulVec_smul]
  have h_unitary : (1 - c • P)ᴴ * 1 * (1 - c • P) = 1 := calc
    (1 - c • P)ᴴ * 1 * (1 - c • P) = 1 - (c + star c) • P + (star c * c) • (P * P) := by
      simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hP_star, mul_one,
        sub_mul, mul_sub, one_mul, smul_mul_smul_comm, add_smul]
      abel
    _ = 1 := by rw [hP_sq, smul_smul, ← h_trace, sub_add_cancel]
  refine ⟨U.of isUnit_one _ h_unitary,
    Gf.mem_supportedOn.2 fun a ha ha' ↦ Units.ext (Matrix.ext fun i j ↦ ?_), fun z ↦ ?_⟩
  · change (1 - c • P) i j a = (1 : Matrix n n (LocField a)) i j
    rcases eq_or_ne i j with rfl | hij <;> simp [vecMulVec_apply, h_supp a ha ha', *]
  · change (1 - c • P) *ᵥ z = _
    rw [hP, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul]

end

variable {E n : Type*} [Field E] [CMType E] {w : FinPlace E} [Fintype n] {x b : n → 𝔸f E}
  [DecidableEq n] {ρ γ : Gf E n}

/-- An integral, self-conjugate finite adele `N` supported at `w` is the trace of an integral `t`
that has an integral inverse away from `w`. The Weil data (instance `WeilData E`) supply the
primitive 5040th root of unity, hence `√-1`, and an element of trace `1`. -/
lemma exists_add_star_eq [WeilData E] {N : 𝔸f E} (hN : N ∈ Ô E) (h_star : star N = N)
    (h_supp : ∀ u : FinPlace E, u ≠ w → N u = 0) :
    ∃ t ∈ Ô E, t + star t = N ∧ ∃ t' ∈ Ô E, ∀ u : FinPlace E, u ≠ w → t' u * t u = 1 := by
  -- Take `t = c₀ N + i`, where `c₀` has trace `1`, `i² = -1` and `ī = -i`.
  obtain ⟨i, hi_sq, hi_star⟩ : ∃ i : 𝓞 E, i * i = -1 ∧ star i = -i :=
    HasPrimitiveRoot5040.exists_mul_self_eq_neg_one
  set I : 𝔸f E := algebraMap E (𝔸f E) i with hI
  have hI_mem : I ∈ Ô E := algebraMap_mem_Ô.2 i.prop
  have hI_sq : -I * I = 1 := by
    simpa [hI] using congrArg (fun a : 𝓞 E ↦ -algebraMap E (𝔸f E) a) hi_sq
  have hI_star : star I = -I := by
    simpa [hI] using congrArg (fun a : 𝓞 E ↦ algebraMap E (𝔸f E) a) hi_star
  refine ⟨stdLattice.traceOneAdele * N + I,
    add_mem (mul_mem stdLattice.traceOneAdele_mem hN) hI_mem, ?_, -I, neg_mem hI_mem,
    fun u hu ↦ by simpa [h_supp u hu] using congr_arg (fun a : 𝔸f E ↦ a u) hI_sq⟩
  rw [star_add, star_mul, h_star, hI_star]
  linear_combination N * stdLattice.traceOneAdele_add_star (E := E)

/-- For a neighbour vector `x` at the finite place `w` (supported at `w`, with `ϖ x ∈ L`, `x ∉ L`
and `⟨x, x⟩` integral), some unitary element `ρ` supported on `w` and its conjugate maps the
neighbour `L₀ + Ô x` into the standard lattice `L` (`MapsNeighbour`). Here `L₀` is the set of
`z ∈ L` with `⟨x, z⟩` integral. The standing data `[WeilData E]` include a primitive 5040th root of
unity in the CM field `E`, so `E/E⁺` is unramified at the finite places. -/
lemma IsNeighbourVector.exists_mapsNeighbour [WeilData E] (hx : IsNeighbourVector w x) :
    ∃ ρ ∈ Gf.supportedOn n {w}, MapsNeighbour ρ x := by
  -- Let `x k` have a pole and let `y ∈ L` be the vector with `⟨y, z⟩ = z k` at `w` and `0`
  -- elsewhere. Reflect in `x + y` with the scalar `c = (x k + t)⁻¹`, where `t` has trace
  -- `⟨x, x⟩ + ⟨y, y⟩`.
  obtain ⟨k, hk⟩ : ∃ k : n, v (x k w) = exp 1 := hx.exists_v_eq
  set y : n → 𝔸f E := Pi.single k (star (singleAdele w 1)) with hy
  have hy_mem : y ∈ stdLattice E n :=
    single_mem_stdLattice (star_mem_Ô (singleAdele_mem_Ô (map_one v).le)) k
  have hy_dot (z : n → 𝔸f E) : star y ⬝ᵥ z = singleAdele w (z k w) := by
    rw [← singleAdele_one_mul, hy, Pi.star_single, star_star, single_dotProduct]
  have hyx : star y ⬝ᵥ x = x k := by
    rw [hy_dot]
    ext u
    rcases eq_or_ne u w with rfl | hu <;> simp [hx.eq_zero_of_ne k u, *]
  have h_real : star (star x ⬝ᵥ x + star y ⬝ᵥ y) = star x ⬝ᵥ x + star y ⬝ᵥ y := by
    rw [star_add, ← star_dotProduct, ← star_dotProduct]
  have h_supp (u : FinPlace E) (hu : u ≠ w) : (star x ⬝ᵥ x + star y ⬝ᵥ y) u = 0 := by
    simp [hy_dot, star_dotProduct_apply x, hu, hx.eq_zero_of_ne _ u hu]
  obtain ⟨t, ht, ht_trace, t', ht', h_inv⟩ :
      ∃ t ∈ Ô E, t + star t = star x ⬝ᵥ x + star y ⬝ᵥ y ∧
        ∃ t' ∈ Ô E, ∀ u : FinPlace E, u ≠ w → t' u * t u = 1 :=
    exists_add_star_eq (add_mem hx.norm_mem (stdLattice.star_dotProduct_mem hy_mem hy_mem)) h_real
      h_supp
  obtain ⟨c, hc, hc_mul, hcx⟩ : ∃ c ∈ Ô E, c * (x k + t) = 1 ∧ c • x ∈ stdLattice E n :=
    hx.exists_mul_add_eq_one hk ht ht' h_inv
  have h_dot : star (x + y) ⬝ᵥ x = star x ⬝ᵥ x + x k := by rw [star_add, add_dotProduct, hyx]
  have hc_trace : c + star c = star c * c * (star (x + y) ⬝ᵥ (x + y)) := by
    have hc_star : star (x k + t) * star c = 1 := by rw [← star_mul, hc_mul, star_one]
    have h_norm : star (x + y) ⬝ᵥ (x + y) = x k + t + star (x k + t) := by
      rw [dotProduct_add, h_dot, star_add x, add_dotProduct, star_dotProduct x y, hyx, star_add]
      linear_combination -ht_trace
    rw [h_norm]
    linear_combination -star c * hc_mul - c * hc_star
  have h_zero (a : FinPlace E) (ha : a ∉ ({w} : Set (FinPlace E)))
      (ha' : star a ∉ ({w} : Set (FinPlace E))) (i : n) : (x + y) i a = 0 := by
    rcases eq_or_ne i k with rfl | hi
    · simp [hy, hx.eq_zero_of_ne i a ha, singleAdele_of_ne ha']
    · simp [hy, hx.eq_zero_of_ne i a ha, hi]
  obtain ⟨ρ, hρ_supp, hρ⟩ : ∃ ρ ∈ Gf.supportedOn n {w},
      ∀ z : n → 𝔸f E, (ρ : Matrix n n (𝔸f E)) *ᵥ z = z - (c * (star (x + y) ⬝ᵥ z)) • (x + y) :=
    exists_quasiReflection h_zero hc_trace
  refine ⟨ρ, hρ_supp, fun z hz hxz ↦ ?_, ?_⟩
  · set s : 𝔸f E := star (x + y) ⬝ᵥ z with hs
    have hs_mem : s ∈ Ô E := by
      rw [hs, star_add, add_dotProduct]
      exact add_mem hxz (stdLattice.star_dotProduct_mem hz hy_mem)
    have h_eq : z - (c * s) • (x + y) = z - (s • c • x + (s * c) • y) := by
      rw [smul_add, mul_comm c s, mul_smul s c x]
    rw [hρ, ← hs, h_eq]
    exact sub_mem hz (add_mem (stdLattice.smul_mem_stdLattice hs_mem hcx)
      (stdLattice.smul_mem_stdLattice (mul_mem hs_mem hc) hy_mem))
  · have h_eq : x - (c * (star x ⬝ᵥ x + x k)) • (x + y) =
        (t - star x ⬝ᵥ x) • c • x - (c * (star x ⬝ᵥ x) + (c • x) k) • y := by
      ext1 j
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      linear_combination -x j * hc_mul
    rw [hρ, h_dot, h_eq]
    exact sub_mem (stdLattice.smul_mem_stdLattice (sub_mem ht hx.norm_mem) hcx)
      (stdLattice.smul_mem_stdLattice (add_mem (mul_mem hc hx.norm_mem) (hcx k)) hy_mem)

/-! ### A finite family that serves all neighbours -/

/-- Let `x` be a neighbour vector at the finite place `w` and `c` a local unit. If `ρ` maps the
neighbour of `c x` into the standard lattice, then it does the same for the neighbour of `x`. -/
lemma MapsNeighbour.of_smul (hx : IsNeighbourVector w x) {c : LocField w} (hc : v c = 1)
    (hρ : MapsNeighbour ρ (singleAdele w c • x)) : MapsNeighbour ρ x where
  mulVec_mem_of_dot_mem z hz hxz := by
    refine hρ.mulVec_mem_of_dot_mem z hz ?_
    rw [star_smul, smul_dotProduct]
    exact mul_mem (star_mem_Ô (singleAdele_mem_Ô hc.le)) hxz
  mulVec_mem := by
    have h_eq : x = singleAdele w c⁻¹ • singleAdele w c • x := by
      have hc_ne : c ≠ 0 := v.ne_zero_iff.1 (by simp [hc])
      ext j u
      rcases eq_or_ne u w with rfl | hu <;> simp [hx.eq_zero_of_ne j u, *]
    rw [h_eq, mulVec_smul]
    exact stdLattice.smul_mem_stdLattice (singleAdele_mem_Ô (by simp [hc])) hρ.mulVec_mem

omit [DecidableEq n] in
/-- If two neighbour vectors `b` and `x` at the finite place `w` differ by a vector of the standard
lattice, then the polar residue of `s = ⟨b, x - b⟩`, the residue of `ϖ s` at `w`, lies in the set
`neighbourResidues w` of such residues for `s` supported at `w` with a pole of order at
most one and with integral trace. -/
lemma IsNeighbourVector.polarResidue_dot_sub_mem (hb : IsNeighbourVector w b)
    (hx : IsNeighbourVector w x) (h_sub : x - b ∈ stdLattice E n) :
    polarResidue ((star b ⬝ᵥ (x - b)) w) ∈ neighbourResidues w := by
  refine ⟨_, hb.star_dotProduct_sub_eq_zero_of_ne hx, hb.v_star_dotProduct_le h_sub, ?_, rfl⟩
  have h_trace : star b ⬝ᵥ (x - b) + star (star b ⬝ᵥ (x - b)) =
      star x ⬝ᵥ x - star b ⬝ᵥ b - star (x - b) ⬝ᵥ (x - b) := by
    simp only [← star_dotProduct, star_sub, sub_dotProduct, dotProduct_sub]
    ring
  rw [h_trace]
  exact sub_mem (sub_mem hx.norm_mem hb.norm_mem) (stdLattice.star_dotProduct_mem h_sub h_sub)

/-- Let the neighbour vectors `x₁` and `x₂` at the finite place `w` be congruent to the neighbour
vector `b` modulo the standard lattice. If `⟨b, x₁ - b⟩` and `⟨b, x₂ - b⟩` have the same polar
residue (the residue of `ϖ` times the component at `w`) and `ρ` maps the neighbour of `x₁` into the
lattice, then it does the same for the neighbour of `x₂`. -/
lemma MapsNeighbour.of_polarResidue_eq {x₁ x₂ : n → 𝔸f E} (hb : IsNeighbourVector w b)
    (hx₁ : IsNeighbourVector w x₁) (hx₂ : IsNeighbourVector w x₂)
    (h_sub₁ : x₁ - b ∈ stdLattice E n) (h_sub₂ : x₂ - b ∈ stdLattice E n)
    (h_res : polarResidue ((star b ⬝ᵥ (x₂ - b)) w) = polarResidue ((star b ⬝ᵥ (x₁ - b)) w))
    (hρ : MapsNeighbour ρ x₁) : MapsNeighbour ρ x₂ := by
  have h_sub : x₂ - x₁ ∈ stdLattice E n := by simpa using sub_mem h_sub₂ h_sub₁
  have hb_dot : star b ⬝ᵥ (x₂ - x₁) ∈ Ô E := by
    rw [← sub_sub_sub_cancel_right x₂ x₁ b, dotProduct_sub]
    exact mem_Ô_of_eq_zero_of_ne (w := w)
      (fun u hu ↦ by
        rw [finAdele_sub_apply, hb.star_dotProduct_sub_eq_zero_of_ne hx₁ u hu,
          hb.star_dotProduct_sub_eq_zero_of_ne hx₂ u hu, sub_zero])
      ((polarResidue_eq_iff (hb.v_star_dotProduct_le h_sub₂) (hb.v_star_dotProduct_le h_sub₁)).1
        h_res)
  have hx₁_dot : star x₁ ⬝ᵥ (x₂ - x₁) ∈ Ô E := by
    have h_eq : star x₁ ⬝ᵥ (x₂ - x₁) = star b ⬝ᵥ (x₂ - x₁) + star (x₁ - b) ⬝ᵥ (x₂ - x₁) := by
      rw [← add_dotProduct, ← star_add, add_sub_cancel]
    rw [h_eq]
    exact add_mem hb_dot (stdLattice.star_dotProduct_mem h_sub h_sub₁)
  refine ⟨fun z hz hxz ↦ hρ.mulVec_mem_of_dot_mem z hz ?_, ?_⟩
  · have h_eq : star x₁ ⬝ᵥ z = star x₂ ⬝ᵥ z - star (x₂ - x₁) ⬝ᵥ z := by
      rw [← sub_dotProduct, ← star_sub, sub_sub_cancel]
    rw [h_eq]
    exact sub_mem hxz (stdLattice.star_dotProduct_mem hz h_sub)
  · rw [← add_sub_cancel x₁ x₂, mulVec_add]
    exact add_mem hρ.mulVec_mem (hρ.mulVec_mem_of_dot_mem _ h_sub hx₁_dot)

/-- There is a family of unitary elements supported on the finite place `w` and its conjugate,
indexed by pairs of a line in `k_w^n` (`k_w` is the residue field at `w`) and a class in
`neighbourResidues w` (the residues of `ϖ s` for `s` supported at `w` with a pole of order at most
one and integral trace). For every neighbour vector `x` at `w`, some member of the family maps the
neighbour `L₀ + Ô x` into the standard lattice `L`. Here a neighbour vector is supported at `w`, has
`ϖ x ∈ L` and `x ∉ L` for a uniformiser `ϖ`, and has integral norm `x* x`, and `L₀` is the set of
`z ∈ L` with `⟨x, z⟩` integral. -/
theorem exists_family_mapsNeighbour [WeilData E] (w : FinPlace E) :
    ∃ ρ : Projectivization (ResField w) (n → ResField w) × neighbourResidues w → Gf E n,
      (∀ p : Projectivization (ResField w) (n → ResField w) × neighbourResidues w,
        ρ p ∈ Gf.supportedOn n {w}) ∧
      ∀ x : n → 𝔸f E, IsNeighbourVector w x →
        ∃ p : Projectivization (ResField w) (n → ResField w) × neighbourResidues w,
          MapsNeighbour (ρ p) x := by
  -- Choose a base vector `b ℓ` on each line `ℓ` that occurs, and then one quasi-reflection for
  -- all `x ≡ b ℓ` with a given polar residue of `⟨b ℓ, x - b ℓ⟩`.
  have h_base (ℓ : Projectivization (ResField w) (n → ResField w)) :
      ∃ b : n → 𝔸f E, ∀ (x : n → 𝔸f E) (hx : IsNeighbourVector w x), hx.line = ℓ →
        ∃ hb : IsNeighbourVector w b, hb.line = ℓ := by
    by_cases h_ex : ∃ (b : n → 𝔸f E) (hb : IsNeighbourVector w b), hb.line = ℓ
    · exact h_ex.imp fun b hb_line _ _ _ ↦ hb_line
    · exact ⟨0, fun x hx h_line ↦ absurd ⟨x, hx, h_line⟩ h_ex⟩
  choose b hb_base using h_base
  have h_refl (p : Projectivization (ResField w) (n → ResField w) × neighbourResidues w) :
      ∃ ρ ∈ Gf.supportedOn n {w}, IsNeighbourVector w (b p.1) →
        ∀ x : n → 𝔸f E, IsNeighbourVector w x → x - b p.1 ∈ stdLattice E n →
          polarResidue ((star (b p.1) ⬝ᵥ (x - b p.1)) w) = p.2 → MapsNeighbour ρ x := by
    by_cases h_ex : ∃ x : n → 𝔸f E, IsNeighbourVector w x ∧ x - b p.1 ∈ stdLattice E n ∧
      polarResidue ((star (b p.1) ⬝ᵥ (x - b p.1)) w) = p.2
    · obtain ⟨x₁, hx₁, h_sub₁, h_res₁⟩ := h_ex
      -- The quasi-reflection of one such `x₁` serves all others.
      obtain ⟨ρ, hρ_supp, hρ⟩ := hx₁.exists_mapsNeighbour
      exact ⟨ρ, hρ_supp, fun hb x₂ hx₂ h_sub₂ h_res₂ ↦
        hρ.of_polarResidue_eq hb hx₁ hx₂ h_sub₁ h_sub₂ (h_res₂.trans h_res₁.symm)⟩
    · exact ⟨1, one_mem _, fun _ x hx h_sub h_res ↦ absurd ⟨x, hx, h_sub, h_res⟩ h_ex⟩
  choose ρ hρ_supp hρ using h_refl
  refine ⟨ρ, hρ_supp, fun x hx ↦ ?_⟩
  obtain ⟨hb, h_line⟩ := hb_base hx.line x hx rfl
  obtain ⟨c, hc, h_sub⟩ := hb.exists_smul_sub_mem hx h_line
  set x' : n → 𝔸f E := singleAdele w c • x
  have hx' : IsNeighbourVector w x' := hx.smul hc
  let p : Projectivization (ResField w) (n → ResField w) × neighbourResidues w :=
    (hx.line, ⟨polarResidue ((star (b hx.line) ⬝ᵥ (x' - b hx.line)) w),
      hb.polarResidue_dot_sub_mem hx' h_sub⟩)
  exact ⟨p, (hρ p hb x' hx' h_sub rfl).of_smul hx hc⟩

/-! ### One step towards the standard lattice -/

/-- If the unitary element `γ` does not stabilise the standard lattice `L` (that is, lies outside
`stdLevel`), then at some finite place `w` where `γ` has a nontrivial component, `γ L` holds a
neighbour vector: a vector supported at `w`, outside `L`, in `L` after multiplication by a
uniformiser, and with integral norm. -/
theorem exists_isNeighbourVector_mulVec (hγ : γ ∉ stdLevel E n) :
    ∃ w : FinPlace E, γ.atPlace w ≠ 1 ∧
      ∃ z ∈ stdLattice E n, IsNeighbourVector w ((γ : Matrix n n (𝔸f E)) *ᵥ z) := by
  -- Take a column `j` with a pole at `w` and scale it so that its largest pole has order one.
  obtain ⟨i, j, w, h_pole⟩ : ∃ (i j : n) (w : FinPlace E),
      1 < v ((γ : Matrix n n (𝔸f E)) i j w) := by simpa [mem_stdLevel, mem_Ô] using hγ
  set g : n → LocField w := fun a ↦ (γ : Matrix n n (𝔸f E)) a j w with hg
  obtain ⟨k, -, hk⟩ :=
    Finset.exists_max_image Finset.univ (fun a : n ↦ v (g a)) ⟨i, Finset.mem_univ i⟩
  have hk_pole : 1 < v (g k) := h_pole.trans_le (hk i (Finset.mem_univ i))
  set s : LocField w := (uniformizer w).val⁻¹ * (g k)⁻¹ with hs
  have hs_le : v s ≤ 1 := by
    rw [hs, v_uniformizer_inv_mul_le_one_iff, map_inv₀]
    exact inv_lt_one_of_one_lt₀ hk_pole
  set z : n → 𝔸f E := Pi.single j (singleAdele w s) with hz_def
  have hz : z ∈ stdLattice E n := single_mem_stdLattice (singleAdele_mem_Ô hs_le) j
  have h_val (a : n) :
      v (((γ : Matrix n n (𝔸f E)) *ᵥ z) a w) = exp 1 * (v (g a) * (v (g k))⁻¹) := by
    have h_apply : ((γ : Matrix n n (𝔸f E)) *ᵥ z) a w = g a * s := by simp [hz_def, hg]
    rw [h_apply, hs, map_mul, map_mul, map_inv₀, map_inv₀, v_uniformizer, WithZero.exp_neg, inv_inv,
      mul_left_comm]
  have h_atPlace : γ.atPlace w ≠ 1 := fun h_one ↦ by
    have h_apply : (γ : Matrix n n (𝔸f E)) i j w = (1 : Matrix n n (LocField w)) i j :=
      congr_arg (fun g : GL n (LocField w) ↦ g.val i j) h_one
    rcases eq_or_ne i j with rfl | hij <;> simp [*] at h_pole
  refine ⟨w, h_atPlace, z, hz,
    { eq_zero_of_ne := fun a u hu ↦ by simp [hz_def, hu]
      v_le := fun a ↦ (h_val a).trans_le
        (mul_le_of_le_one_right' (mul_inv_le_one_of_le₀ (hk a (Finset.mem_univ a)) zero_le))
      exists_v_eq := ⟨k, by rw [h_val, mul_inv_cancel₀ (zero_lt_one.trans hk_pole).ne', mul_one]⟩
      norm_mem := by
        rw [stdLattice.star_mulVec_dotProduct_mulVec]
        exact stdLattice.star_dotProduct_mem hz hz }⟩

/-- One step lowers the index. For `ρ`, `γ` in the finite adelic unitary group over the CM field `E`
with Weil data, let `z` be in the standard lattice `L` and let `γ z` be a neighbour vector at the
finite place `w`: it is supported at `w`, `ϖ (γ z) ∈ L` and `γ z ∉ L` for a uniformiser `ϖ` at `w`,
and its norm is integral. If `ρ` maps its neighbour `L₀ + Ô (γ z)` into `L`, where `L₀` is the set
of `y ∈ L` with `(γ z)* y` integral, then `q_w |Δ(ρ γ)|² ≤ |Δ(γ)|²`, where `q_w` is the order of the
residue field at `w` and `|Δ(g)|²` (`Δ` is `finMultiplier`) is the index of `L ∩ g⁻¹ L` in `L`. -/
theorem q_mul_norm_finMultiplier_mul_sq_le [WeilData E] {z : n → 𝔸f E} (hz : z ∈ stdLattice E n)
    (h_vec : IsNeighbourVector w ((γ : Matrix n n (𝔸f E)) *ᵥ z))
    (hρ : MapsNeighbour ρ ((γ : Matrix n n (𝔸f E)) *ᵥ z)) :
    w.q * ‖finMultiplier (ρ * γ)‖ ^ 2 ≤ ‖finMultiplier γ‖ ^ 2 := by
  -- With `H = L ∩ γ⁻¹ L` and `K = L ∩ (ρ γ)⁻¹ L` we have `H ≤ K`, and the multiples of `z` give
  -- `q_w` different classes in `K / H`.
  set H : AddSubgroup (n → 𝔸f E) :=
    (stdLattice E n).comap ((γ : Matrix n n (𝔸f E)).mulVecLin : (n → 𝔸f E) →+ (n → 𝔸f E)) ⊓
      stdLattice E n
  set K : AddSubgroup (n → 𝔸f E) :=
    (stdLattice E n).comap (((ρ * γ : Gf E n) : Matrix n n (𝔸f E)).mulVecLin :
      (n → 𝔸f E) →+ (n → 𝔸f E)) ⊓ stdLattice E n
  have hH_index : ‖finMultiplier γ‖ ^ 2 = H.relIndex (stdLattice E n) := by
    rw [norm_finMultiplier_sq, AddSubgroup.inf_relIndex_right]
  have hK_index : ‖finMultiplier (ρ * γ)‖ ^ 2 = K.relIndex (stdLattice E n) := by
    rw [norm_finMultiplier_sq, AddSubgroup.inf_relIndex_right]
  have mem_K {a : n → 𝔸f E} : a ∈ K ↔
      (ρ : Matrix n n (𝔸f E)) *ᵥ (γ : Matrix n n (𝔸f E)) *ᵥ a ∈ stdLattice E n ∧
        a ∈ stdLattice E n := by
    rw [mulVec_mulVec]
    rfl
  have h_le : H ≤ K := fun a ⟨hγa, ha⟩ ↦ mem_K.2 ⟨hρ.mulVec_mem_of_dot_mem _ hγa
    (by simpa [stdLattice.star_mulVec_dotProduct_mulVec] using stdLattice.star_dotProduct_mem ha
          hz), ha⟩
  have h_tower : H.relIndex K * K.relIndex (stdLattice E n) = H.relIndex (stdLattice E n) :=
    AddSubgroup.relIndex_mul_relIndex H K _ h_le inf_le_right
  have h_finite : Finite (K ⧸ H.addSubgroupOf K) := by
    refine Nat.finite_of_card_ne_zero (left_ne_zero_of_mul (h_tower.trans_ne ?_))
    simpa [← Nat.cast_ne_zero (R := ℝ), ← hH_index] using finMultiplier_ne_zero γ
  obtain ⟨σ, hσ⟩ := (IsLocalRing.residue_surjective (R := LocInt w)).hasRightInverse
  have h_mem (a : ResField w) : singleAdele w (σ a : LocField w) • z ∈ K := by
    refine mem_K.2 ⟨?_, stdLattice.smul_mem_stdLattice (singleAdele_mem_Ô (σ a).prop) hz⟩
    rw [mulVec_smul, mulVec_smul]
    exact stdLattice.smul_mem_stdLattice (singleAdele_mem_Ô (σ a).prop) hρ.mulVec_mem
  let classOf (a : ResField w) : K ⧸ H.addSubgroupOf K :=
    (⟨singleAdele w (σ a : LocField w) • z, h_mem a⟩ : K)
  have h_inj : Function.Injective classOf := by
    intro a a' h_eq
    obtain ⟨h_diff, -⟩ : -(singleAdele w (σ a : LocField w) • z) +
        singleAdele w (σ a' : LocField w) • z ∈ H :=
      AddSubgroup.mem_addSubgroupOf.1 (QuotientAddGroup.eq.1 h_eq)
    have h_smul : (-singleAdele w (σ a : LocField w) + singleAdele w (σ a' : LocField w)) •
        ((γ : Matrix n n (𝔸f E)) *ᵥ z) ∈ stdLattice E n := by
      simpa [add_smul, mulVec_add, mulVec_smul, mulVec_neg] using h_diff
    exact (hσ a).symm.trans ((h_vec.residue_eq_of_smul_mem h_smul).trans (hσ a'))
  have h_card : w.q ≤ H.relIndex K :=
    (card_ResField w).ge.trans (Nat.card_le_card_of_injective classOf h_inj)
  rw [hH_index, hK_index, ← h_tower, Nat.cast_mul]
  gcongr
end Reflection

end New.SiegelWeil
