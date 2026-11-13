import DiophantineConsistency.Z10.Z10Regs
import DiophantineConsistency.ZRows.PellNegBase
import DiophantineConsistency.ZRows.LinearInterpolation

/-! # Ten-integer package 106: full residue-class interpolation

Completeness step C8 of the route (`BASELINE_PROOF.md` §3). Fix the main Lucas data
`A = 2(a + 2)`, an odd index `B`, `C = ψ_a(B)` and `d = 2 χ_a(B)`, so `D = d²`. For every
`z > 0` the theorem `interp` gives `ξ > 0` with `z ∣ ξ` such that **every** residue class
modulo `ξ` contains a `y` making `a1 = D F I` a square, for the register formulas
`E0 = C² ξ`, `E = D E0`, `F = 4(A² − 4) E0 E + 1`, `G = (A/2 − 1)(F − 1) − 1`, `Ω = 16 E`,
`H = C + F (B − C + Ω y)`, `I = (G² − 1) H² + 1` (`a1Of`, equal to the register `a1` by
`regs_a1`).

The construction, all of it explicit:

* the strong index (`ZRowsPellValuation.strong_index`) gives `n₀ = g w` with
  `8 C² χ_a(B) z ∣ u = ψ_a(n₀)`, `g ∣ u` and `w` coprime to `u`; put `ξ = u / (8 C² χ_a(B))`,
  `r₀ = χ_a(n₀)`. Then `F = r₀²`, `Ω = 8 χ_a(B) u` and `F − 1 = Ω ξ Δ C²`;
* the second base is `G = (a + 1) Δ u² − 1` (Lean base `gb = G − 2`): `G ≡ −1 (mod Ω ξ)`
  and `G ≡ −A/2 (mod F)`;
* for the target class `c`, take `L = w r₀ L₁` with `L₁ ≡ α r₀ c (mod ξ)` (`α w ≡ 1`,
  `r₀² ≡ 1`), and the odd index `j = B + Ω L`, `H₀ = ψ_gb(j)`. Then
  `H₀ ≡ j (mod Ω ξ)` (`ZRowsPellNegBase.alt_odd`), `H₀ ≡ ψ_a(j) (mod F)`
  (`ZRowsPellNegBase.nb_odd`) and `ψ_a(j) ≡ C (mod F)` (`square_period`, since
  `4 n₀ r₀ ∣ Ω L`);
* `y = (H₀ − C − (B − C) F) / (Ω F)` is explicit (`H_core`), `y ≡ L ≡ c (mod ξ)`
  (`class_core`, `L_core`), `H = H₀`, and `I = χ_gb(j)²`, `D F I = (d r₀ χ_gb(j))²`.

The ring certificates were checked offline (sympy) before compilation.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Z10Interp

/-! ## The register formulas and the ring identities -/

section Ring
variable {𝔸 : Type*} [CommRing 𝔸]

def Dof (h C : 𝔸) : 𝔸 := (2 * h * (2 * h) - 4) * (C * C) + 4
def Fof (h C xi : 𝔸) : 𝔸 :=
  4 * (2 * h * (2 * h) - 4) * ((C * C * xi) * (Dof h C * (C * C * xi))) + 1
def Gof (h C xi : 𝔸) : 𝔸 := (h - 1) * (Fof h C xi - 1) - 1
def Omof (h C xi : 𝔸) : 𝔸 := 16 * (Dof h C * (C * C * xi))
def Hof (h B C xi y : 𝔸) : 𝔸 := C + Fof h C xi * (B - C + Omof h C xi * y)
def Iof (h B C xi y : 𝔸) : 𝔸 :=
  (Gof h C xi * Gof h C xi - 1) * (Hof h B C xi y * Hof h B C xi y) + 1
/-- The radicand `a1 = D F I` as a function of `halfA, B1, C, xi, y`. -/
def a1Of (h B C xi y : 𝔸) : 𝔸 := Dof h C * Fof h C xi * Iof h B C xi y

theorem regs_a1 (p : Fin 4 → 𝔸) (x : Fin 10 → 𝔸) :
    (Z10Regs.regs p x).a1 = a1Of (Z10Regs.regs p x).halfA (Z10Regs.regs p x).B1
      (Z10Regs.regs p x).C (Z10Regs.regs p x).xi (x 7) := rfl

/-- The second Pell ordinate meets the linear form at the explicit `y`. -/
theorem H_core {C B F Om xi t H0 J L e p0 y : 𝔸}
    (hy : y = L + xi * e - (B - C) * t - t * (p0 - (B - C)))
    (hp0 : H0 - C = F * p0) (he : H0 - J = Om * xi * e) (hj : J = B + Om * L)
    (hFt : F = 1 + Om * t) : C + F * (B - C + Om * y) = H0 := by
  subst hy
  linear_combination Om * t * hp0 - F * (he + hj) + (H0 - C) * hFt

/-- The explicit `y` lies in the class of `L`. -/
theorem class_core {C B xi d L e p0 y : 𝔸}
    (hy : y = L + xi * e - (B - C) * (xi * d) - (xi * d) * (p0 - (B - C))) :
    y - L = xi * (e - d * p0) := by
  subst hy; ring

/-- `L = w r₀ L₁` lies in the target class `c`. -/
theorem L_core {w r0 L1 c α β κ xi u C xa δ : 𝔸} (hL1 : L1 - α * r0 * c = xi * κ)
    (hcop : w * α + u * β = 1) (hn0 : r0 * r0 = 1 + δ * u * u)
    (hu : u = 8 * C * C * xa * xi) :
    w * r0 * L1 - c =
      xi * (w * r0 * κ + c * (w * α * (8 * xa * u) * δ * (C * C) - 8 * C * C * xa * β)) := by
  linear_combination (w * r0) * hL1 + (c * r0 * r0 - 8 * c * C * C * xa * xi * u * δ) * hcop +
    (c - β * c * u) * hn0 + (δ * c * u - β * c - δ * β * c * u * u) * hu

end Ring

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ArithmeticPellRecurrence

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The interpolation theorem -/

/-- **Full residue-class interpolation** (C8). -/
theorem interp (a Bn z j0 : V) (hz : 0 < z) (hB : Bn = 2 * j0 + 1) :
    ∃ xi : V, 0 < xi ∧ z ∣ xi ∧ ∀ c : DiffRing V, ∃ y s : DiffRing V,
      (ι xi : DiffRing V) ∣ y - c ∧
        a1Of (ι a + 2) (ι Bn) (ι (ycoord Bn a)) (ι xi) y = s * s := by
  obtain ⟨Cn, hCn⟩ : ∃ Cn : V, Cn = ycoord Bn a := ⟨_, rfl⟩
  obtain ⟨xa, hxa⟩ : ∃ xa : V, xa = xcoord Bn a := ⟨_, rfl⟩
  rw [← hCn]
  have hBpos : 0 < Bn := by
    rw [hB]; exact lt_of_lt_of_le (by norm_num) (le_add_left le_rfl : (1 : V) ≤ 2 * j0 + 1)
  have hC0 : 0 < Cn := by rw [hCn]; exact lt_of_lt_of_le hBpos (time_le_y Bn a)
  have hxa0 : 0 < xa := by rw [hxa]; exact lt_of_lt_of_le (by norm_num) (one_le_x Bn a)
  have hN : 0 < 8 * Cn * Cn * xa * z :=
    mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hC0) hC0) hxa0) hz
  obtain ⟨n0, g, w, hn, ⟨m, hm⟩, hgw, ⟨ug, hug⟩, hw⟩ := ZRowsPellValuation.strong_index a _ hN
  obtain ⟨u, hu⟩ : ∃ u : V, u = ycoord n0 a := ⟨_, rfl⟩
  obtain ⟨r0, hr0⟩ : ∃ r0 : V, r0 = xcoord n0 a := ⟨_, rfl⟩
  rw [← hu] at hm hug hw
  have hu0 : 0 < u := by rw [hu]; exact lt_of_lt_of_le hn (time_le_y n0 a)
  have hm0 : 0 < m := pos_of_mul_pos_right
    (show 0 < 8 * Cn * Cn * xa * z * m by rw [← hm]; exact hu0) (Arithmetic.zero_le _)
  obtain ⟨xi, hxi⟩ : ∃ xi : V, xi = z * m := ⟨_, rfl⟩
  have hxi0 : 0 < xi := by rw [hxi]; exact mul_pos hz hm0
  have hux : u = 8 * Cn * Cn * xa * xi := by rw [hm, hxi]; ring
  refine ⟨xi, hxi0, ⟨m, hxi⟩, fun c => ?_⟩
  -- the second base `gb + 2 = (a + 1) Δ u² − 1`
  have hδ3 : 3 ≤ delta a := by
    unfold delta
    calc (3 : V) = 1 * 3 := by ring
      _ ≤ (a + 1) * (a + 3) :=
        mul_le_mul (le_add_left le_rfl) (le_add_left le_rfl) (by norm_num) (Arithmetic.zero_le _)
  have hu1 : 1 ≤ u := pos_iff_one_le.mp hu0
  have hP3 : 3 ≤ (a + 1) * (delta a * u * u) := by
    calc (3 : V) = 1 * (3 * 1 * 1) := by ring
      _ ≤ (a + 1) * (delta a * u * u) :=
        mul_le_mul (le_add_left le_rfl)
          (mul_le_mul (mul_le_mul hδ3 hu1 (by norm_num) (Arithmetic.zero_le _)) hu1
            (by norm_num) (Arithmetic.zero_le _))
          (by norm_num) (Arithmetic.zero_le _)
  obtain ⟨gb, hgbd⟩ : ∃ gb : V, gb = (a + 1) * (delta a * u * u) - 3 := ⟨_, rfl⟩
  have hgb : gb + 3 = (a + 1) * (delta a * u * u) := by rw [hgbd]; exact tsub_add_cancel_of_le hP3
  have hn0V : r0 * r0 = 1 + delta a * u * u := by
    rw [hr0, hu]; exact ArithmeticPellRecurrence.norm n0 a
  -- the target class: `L = w r₀ L₁`
  obtain ⟨α, β, hαβ⟩ := ModelBetaFunction.bez_one_iff_ring.mp hw
  obtain ⟨L1, κ, hκ⟩ := ZRowsIntersective19.exists_nat_congr xi hxi0 (α * ι r0 * c)
  -- the odd index `j = B + Ω L`
  obtain ⟨jj, hjj⟩ : ∃ jj : V, jj = j0 + 4 * xa * u * (w * r0 * L1) := ⟨_, rfl⟩
  have hj : 2 * jj + 1 = Bn + 8 * xa * u * (w * r0 * L1) := by rw [hjj, hB]; ring
  have hjk : Bn + 2 * (r0 * (2 * xa * ug * L1)) * (2 * n0) = 2 * jj + 1 := by
    rw [hj, hgw, hug]; ring
  -- `H₀ ≡ j (mod Ω ξ)`
  have hd : 8 * xa * u * xi ∣ gb + 3 := ⟨(a + 1) * (delta a * Cn * Cn), by
    rw [hgb]
    calc (a + 1) * (delta a * u * u) = (a + 1) * (delta a * u * (8 * Cn * Cn * xa * xi)) := by
          rw [← hux]
      _ = 8 * xa * u * xi * ((a + 1) * (delta a * Cn * Cn)) := by ring⟩
  have hΩ0 : 0 < 8 * xa * u * xi := mul_pos (mul_pos (mul_pos (by norm_num) hxa0) hu0) hxi0
  obtain ⟨e, he⟩ := ZRowsPellNegBase.alt_odd gb (8 * xa * u * xi) hΩ0 hd jj
  -- `H₀ ≡ ψ_a(j) (mod F)`
  have hk : r0 * r0 ∣ (gb + 2) + (a + 2) := ⟨a + 1, by
    calc gb + 2 + (a + 2) = (gb + 3) + (a + 1) := by ring
      _ = (a + 1) * (delta a * u * u) + (a + 1) := by rw [hgb]
      _ = r0 * r0 * (a + 1) := by rw [hn0V]; ring⟩
  have hr1 : 1 ≤ r0 := by rw [hr0]; exact one_le_x n0 a
  have hF0 : 0 < r0 * r0 :=
    mul_pos (lt_of_lt_of_le (by norm_num) hr1) (lt_of_lt_of_le (by norm_num) hr1)
  obtain ⟨pb, hpb⟩ := ZRowsPellNegBase.nb_odd gb a (r0 * r0) hF0 hk jj
  -- `ψ_a(j) ≡ C (mod F)`
  obtain ⟨q, hq⟩ := ZRowsLinearInterpolation.square_period a Bn n0 (2 * xa * ug * L1)
  rw [← hr0, hjk, ← hCn] at hq
  -- the ring of differences
  have Hu : (ι u : DiffRing V) = 8 * ι Cn * ι Cn * ι xa * ι xi := by
    rw [hux]; simp only [map_mul, map_ofNat]
  have Hn0 : (ι r0 : DiffRing V) * ι r0 = 1 + (ι a + 1) * (ι a + 3) * ι u * ι u := by
    have h := congrArg (ι (V := V)) hn0V
    unfold delta at h
    simpa only [map_add, map_mul, map_one, map_ofNat] using h
  have HnB : (ι xa : DiffRing V) * ι xa = 1 + (ι a + 1) * (ι a + 3) * ι Cn * ι Cn := by
    have h := ArithmeticPellRecurrence.norm Bn a
    rw [← hxa, ← hCn] at h
    unfold delta at h
    have h' := congrArg (ι (V := V)) h
    simpa only [map_add, map_mul, map_one, map_ofNat] using h'
  have Hgb : (ι gb : DiffRing V) + 3 = (ι a + 1) * ((ι a + 1) * (ι a + 3) * ι u * ι u) := by
    have h := congrArg (ι (V := V)) hgb
    unfold delta at h
    simpa only [map_add, map_mul, map_one, map_ofNat] using h
  have HnJ := ArithmeticPellRecurrence.norm (2 * jj + 1) gb
  unfold delta at HnJ
  have HnJ' := congrArg (ι (V := V)) HnJ
  simp only [map_add, map_mul, map_one, map_ofNat] at HnJ'
  have Hj : (ι (2 * jj + 1) : DiffRing V) =
      ι Bn + 8 * ι xa * ι u * (ι w * ι r0 * ι L1) := by
    rw [hj]; simp only [map_add, map_mul, map_ofNat]
  rw [map_mul, map_mul, map_mul, map_ofNat] at he
  rw [map_mul] at hpb
  have hp0 : ι (ycoord (2 * jj + 1) gb) - ι Cn = ι r0 * ι r0 * (pb + q) := by
    linear_combination hpb + hq
  -- the register formulas at the construction
  have hDv : Dof (ι a + 2) (ι Cn) = 2 * ι xa * (2 * ι xa) := by
    unfold Dof; linear_combination (-4 : DiffRing V) * HnB
  have hFv : Fof (ι a + 2) (ι Cn) (ι xi) = ι r0 * ι r0 := by
    unfold Fof; rw [hDv]
    linear_combination -Hn0 - (ι a + 1) * (ι a + 3) * (ι u + 8 * ι Cn * ι Cn * ι xa * ι xi) * Hu
  have hOm : Omof (ι a + 2) (ι Cn) (ι xi) = 8 * ι xa * ι u := by
    unfold Omof; rw [hDv]; linear_combination (-8 * ι xa) * Hu
  have hGv : Gof (ι a + 2) (ι Cn) (ι xi) = ι gb + 2 := by
    unfold Gof; rw [hFv]; linear_combination (ι a + 1) * Hn0 - Hgb
  have hFt : ι r0 * ι r0 =
      1 + 8 * ι xa * ι u * (ι xi * ((ι a + 1) * (ι a + 3) * (ι Cn * ι Cn))) := by
    linear_combination Hn0 + (ι a + 1) * (ι a + 3) * ι u * Hu
  -- the explicit `y`
  obtain ⟨y, hy⟩ : ∃ y : DiffRing V, y = ι w * ι r0 * ι L1 + ι xi * e -
      (ι Bn - ι Cn) * (ι xi * ((ι a + 1) * (ι a + 3) * (ι Cn * ι Cn))) -
      (ι xi * ((ι a + 1) * (ι a + 3) * (ι Cn * ι Cn))) * ((pb + q) - (ι Bn - ι Cn)) :=
    ⟨_, rfl⟩
  have hHv : Hof (ι a + 2) (ι Bn) (ι Cn) (ι xi) y = ι (ycoord (2 * jj + 1) gb) := by
    unfold Hof; rw [hFv, hOm]
    exact H_core hy hp0 he Hj hFt
  refine ⟨y, 2 * ι xa * ι r0 * ι (xcoord (2 * jj + 1) gb), ?_, ?_⟩
  · have hcl := class_core hy
    have hLc := L_core hκ hαβ Hn0 Hu
    have e1 : y - c = (y - ι w * ι r0 * ι L1) + (ι w * ι r0 * ι L1 - c) := by ring
    rw [e1]
    exact dvd_add ⟨_, hcl⟩ ⟨_, hLc⟩
  · unfold a1Of Iof
    rw [hDv, hFv, hGv, hHv]
    linear_combination (-(2 * ι xa * (2 * ι xa)) * (ι r0 * ι r0)) * HnJ'

#print axioms H_core
#print axioms L_core
#print axioms interp

end DiophantineConsistency.Z10Interp
