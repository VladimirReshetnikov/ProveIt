import Lib.PadicHodge.Kisin.Modules
import Lib.PadicHodge.Kisin.PeriodMatrixFrame
import Lib.PadicHodge.RadiusLemma

/-!
# The frame theorem for Kisin modules and stability under normalising Galois elements

Let `L` be a lattice datum over a Kummer chart `k`. The ring `S` of `k` has a variable `z` and the
element `E = z ^ e * unit + p`, and `k.frobE m` is `φ ^ m E`; `phiInvToBdR 0` is the map
`Ainf → BdR`. Let `h = L.jumpBound` and `τ = [ε^{1/p}] − 1`. A form is an `Ainf`-linear map
`W(C♭) ⊗ L → B_dR`. Those in `L.forms` are `Γ'`-equivariant on `1 ⊗ L`. They cut out the
`Ainf`-module `L.kisinAinf` and the Kisin module `N = L.kisinModule` over `S`. `L.ainfLattice` is
`Ainf ⊗ L`; `L.fracSpan` holds the `x` with `r • x ∈ L.ainfLattice` for some non-zero divisor `r` of
`Ainf`, and `L.frobKisinAinf l` is `φ ^ l (L.kisinAinf)`.

## Overview of this theory

A chart (`New.Lift.Chart`) is a `Λ`-algebra map `Λ⟦X⟧ → A_inf`, with `Λ = W(𝔽_{p^f})`. It sends `X`
to a non-unit Teichmüller lift `z = [ϖ^♭]`. It sends some `X^e V + p`, with `V` a unit, to a
generator `E` of `ker θ`. `S` is its image. `B⁺` (`New.Period.BPlus`) receives `A_inf` and maps to
`B_max` (`New.Period.Bmax`) and `B_dR`. Its `S`-subalgebra `S_B` (`New.Lift.Chart.bicommutant`) is
the `p`-adic closure of `S[E/p]` with `p` inverted
(`New.Lift.Chart.adjoinEDivPClosure_eq_bicommutant`). Put `μ = [ε] - 1`, with `ε` a compatible
system of `p`-power roots of unity, and `τ = φ⁻¹ μ`.

* Let `K` be the field fixed by an open subgroup `G_K` of `Gal(ℚ̄_p/ℚ_p)`. There is a Kummer chart
  (`New.Lift.KummerChart`) with `Λ` and `θ z` fixed by `G_K` and `e f = [K : ℚ_p]`
  (`New.Lift.exists_kummerChart`).
* Let `c` be a chart for `G_K` (`IsChartOf`). Let `T` be a crystalline `ℤ_p`-lattice with action
  `ρ`, whose jumps (the `k` with `New.Period.jump` nonzero) lie in `[-a, b]`. In a basis of `T`
  there are three objects. The first is `P`, invertible over `B_max`, with `ρ(g) · g P = P`. The
  second is a unit `v` with `E τ v = μ`. The third is `U` over `B⁺`, whose image in `B_max` is
  `(E τ)^a P`. This `U` satisfies the predicate `IsPeriodMatrix` with height `a + b` and Frobenius
  factor `v^a` (`New.Lift.Chart.IsChartOf.exists_isPeriodMatrixOf`).
* Take such a `U` of height `h` and factor `v`. There are `Q` and `Q'` over `A_inf`, `Z` over `S_B`
  and `B` over `S` with `Q Q' = τ^h`, `U Z = E^h Q` and `φ Q = v Q B`
  (`New.Lift.Chart.IsPeriodMatrix.exists_frame`).
* On a Kummer chart, let `h = jumpBound`. Let `N` be the `S`-module `kisinModule` and `M` its
  `A_inf`-span `kisinAinf`. Then `τ^h` maps `M` into `ainfLattice` and back, and `E^h φ N ⊆ N`. Take
  a crystalline form `λ` (`crysForms`, valued in `B_dR`). Then `E^h λ(N)` lies in the image of
  `S_B`. Suppose `d ∈ A_inf` is such that `d ∣ E^m r` in `B⁺` forces `d ∣ r`. Then `x ∈ M` lies in
  `d M` once, for one `n`, `E^n λ(x) ∈ d B⁺` for all such `λ`
  (`New.Lift.KummerChart.JumpLattice.mem_smul_kisinAinf_of_crysForms`).

This is a substitute, in the form needed here, for part of Kisin's theorem on the module of a
crystalline lattice (Kisin 2006; Bhatt–Morrow–Scholze 2018). The inclusion `E^n N ⊆ S φ N` and an
equivalence of categories are not stated.

Contents of the files. `Charts`: coordinates and an approximation lemma.
`Bicommutant`: extension to `B⁺`.
`PeriodMatrixBasis`: `U`, and `Q` with `det Q ≠ 0`. `PeriodMatrixFrame`: `p ∤ det Q`, hence the
frame. `KummerChartDeRham`: the different, and values in `B_dR`. `Modules`: `M`, `N` and the
`B_dR`-valued forms. `FrameTheorem`: `N` as the `S`-span of the columns of `τ^{-h} Q`, using
`Lib.PadicHodge.RadiusLemma`.

## Main definitions and results

* `New.Lift.KummerChart.JumpLattice.frame_theorem`: a relation `∑ c i • v i = 0` among vectors of
  `L.valueFieldPoints L.fracSpan` still holds after applying any `k.S`-linear `f : Ainf → k.S` to
  the coefficients (`New.Lift.KummerChart.JumpLattice.FrameProperties`).
* `New.Lift.KummerChart.JumpLattice.valueFieldPoints_frobKisinAinf_eq_span`: the vectors of
  `φ ^ l (L.kisinAinf)` on which all forms in `L.forms` take values in `k.valueField 0` form the
  `S`-span of `φ ^ l N`.
* `New.Lift.KummerChart.JumpLattice.smul_mem_kisinAinf`: an element `g` that conjugates `Γ'` into
  itself preserves the module `New.Lift.KummerChart.JumpLattice.kisinAinf`. The reason is that
  conjugation by `g` keeps forms `Γ'`-equivariant
  (`New.Lift.KummerChart.JumpLattice.conjForm_mem_forms`).

Notions from other files:
* `New.Lift.KummerChart.JumpLattice`: A finite free O-module with an action of Γ, crystalline over
  Γ', together with a finite set of integers for each embedding of O in `ℂ_[p]` that contains the
  jumps at that embedding. It also carries finite sets of integers indexed by `Letter`, which this
  file does not use directly.
* `New.Lift.KummerChart.JumpLattice.Ambient`: The module W(C^♭)⊗L for the lattice underlying L;
  `DiagTensor.mk 1 t` is the vector 1 ⊗ t.
* `New.Lift.KummerChart.JumpLattice.kisinAinf`: The x in A_inf[1/τ] ⊗ L with μ(φ^n x) in B_dR^+ for
  all n ≥ 1 and all μ in `L.forms`, where τ = [ε^{1/p}] − 1. The Kisin module consists of those x on
  which all forms in `L.forms` take values in the subfield `k.valueField 0` of B_dR.

## Relation to the literature

Known; see `Lib.PadicHodge.Kisin.PeriodMatrixFrame` and `Lib.PadicHodge.Kisin.Modules` for sources.
-/

/-! ## The frame theorem: spanning and bounded height -/

section FrameTheorem

namespace New.Lift.KummerChart.JumpLattice

open Period Pointwise Submodule Set FrobGroup Module FaithfulSMul Matrix Algebra MulSemiringAction
  Finset LinearMap TensorProduct algebraMap
open Chart hiding φ

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p]
  {k : KummerChart Γ} {O : Coeffs} {L : JumpLattice O}

/-- Every `ℤ_[p]`-linear map `f` from the lattice `L` to `BdR` is the restriction of some
form `μ` to the vectors `1 ⊗ t`. -/
lemma exists_functional_extend (f : Rep.of (overZp L.ρ) →ₗ[ℤ_[p]] BdR) :
    ∃ μ : L.Functional, ∀ t : Rep.of (overZp L.ρ), μ (DiagTensor.mk 1 t) = f t := by
  -- Over the field `BdR`, some linear map `Ψ` on `BdR ⊗ WittCFlat` with values in
  -- `L.Carrier →ₗ BdR` sends the non-zero vector `1` to `f`. Its restriction to `WittCFlat` is
  -- `Ainf`-linear and defines `μ`.
  have h_nontrivial : Nontrivial (BdR ⊗[Ainf] WittCFlat) :=
    nontrivial_of_algebraMap_injective_of_isDomain Ainf BdR WittCFlat
      (algebraMap_injective Ainf BdR) (algebraMap_injective Ainf WittCFlat)
  obtain ⟨Ψ, -, hΨ⟩ :=
    exists_extend_of_notMem (K := BdR) (p := ⊥) (v := (1 : BdR ⊗[Ainf] WittCFlat)) 0 one_ne_zero f
  exact ⟨AlgebraTensorModule.lift ((liftBaseChangeEquiv BdR).symm Ψ), DFunLike.congr_fun hΨ⟩

/-- Let `μ` and `μ'` be forms, `g ∈ Γ`, and let `A` be an invertible matrix over `BdR` with
`ρ(g) * g(A) = A`, where `ρ(g)` is the matrix of `g` in the basis `finBasis ℤ_[p] L.Carrier`. Then
`μ'(1 ⊗ g t) = g • μ(1 ⊗ t)` for all `t` if and only if
`basisValues μ' ᵥ* A = g • (basisValues μ ᵥ* A)`; here `basisValues` is the vector of values
of a form on the basis vectors `1 ⊗ e i`. -/
lemma equivariant_iff_basisValues {μ : L.Functional} {g : GroupOverGp.G}
    {A : Matrix (Fin (finrank ℤ_[p] L.Carrier)) (Fin (finrank ℤ_[p] L.Carrier)) BdR}
    {μ' : L.Functional} (hA : IsUnit A)
    (h_cocycle : (repMatrix L.ρ (finBasis ℤ_[p] L.Carrier) g).map (algebraMap ℤ_[p] BdR) *
      A.map (fun x : BdR ↦ toGp g • x) = A) :
    (∀ t : L.Carrier, μ' (DiagTensor.mk 1 (L.ρ g t)) = toGp g • μ (DiagTensor.mk 1 t)) ↔
      basisValues μ' ᵥ* A = toGp g • basisValues μ ᵥ* A := by
  set P := (repMatrix L.ρ (finBasis ℤ_[p] L.Carrier) g).map (algebraMap ℤ_[p] BdR)
  set gA := A.map (fun x : BdR ↦ toGp g • x)
  -- Both sides of the matrix equation are products with the invertible matrix `gA = g • A`:
  -- the left one by `h_cocycle : P * gA = A`, the right one since `g` acts by a ring map.
  have h_left : basisValues μ' ᵥ* A = basisValues μ' ᵥ* P ᵥ* gA := by rw [vecMul_vecMul, h_cocycle]
  have h_right : toGp g • basisValues μ ᵥ* A = (toGp g • basisValues μ) ᵥ* gA :=
    funext ((toRingHom (Gp p) BdR (toGp g)).map_vecMul A (basisValues μ))
  have h_unit : IsUnit gA := hA.map (toRingHom (Gp p) BdR (toGp g)).mapMatrix
  have h_entry (l : Fin (finrank ℤ_[p] L.Carrier)) :
      (basisValues μ' ᵥ* P) l = μ' (.mk 1 (L.ρ g (finBasis ℤ_[p] L.Carrier l))) := by
    simp [P, repMatrix, toMatrixAlgEquiv_apply, ← smul_def', ← commutes, ← map_smul_of_tower,
      ← map_sum, -LinearMap.map_smulₛₗ, -map_smul, vecMul, dotProduct, basisValues]
  rw [h_left, h_right, (vecMul_injective_of_isUnit h_unit).eq_iff]
  simp only [funext_iff, h_entry]
  refine ⟨fun h l ↦ h (finBasis ℤ_[p] L.Carrier l), fun h t ↦ ?_⟩
  -- The forms `conjForm μ' g` and `μ` agree on a basis, so they agree on `L.fracSpan`.
  have h_row : basisValues (conjForm μ' g) = basisValues μ := funext fun l ↦ by
    simp [h, basisValues]
  simpa [inv_smul_eq_iff] using
    apply_eq_of_mem_fracSpan (conjForm μ' g) μ h_row
      (mem_saturateBy_of_mem (mk_one_mem_ainfLattice t))

/-- The module `L.kisinAinf` lies in `L.fracSpan`: a power of `τ` is a non-zero divisor of
`Ainf`. -/
lemma kisinAinf_le_fracSpan : L.kisinAinf ≤ L.fracSpan := by
  rintro x ⟨⟨_, ⟨N, rfl⟩, hτx⟩, -⟩
  exact ⟨tau ^ N, by simp, hτx⟩

/-- The module `W(C♭) ⊗ L` has no `Ainf`-torsion. -/
instance : IsTorsionFree Ainf L.Ambient := .trans_faithfulSMul _ WittCFlat (_ ⊗ _)

/-! ### A frame of the lattice

The proof of `frame_theorem` reads everything off a frame of `L` (`Frame`): the period matrix
`(E * τ) ^ a • M` of `L`, with `a = L.jumpBound`, and the frame `Q`, `Q'`, `Z`, `Y`, `B` that
`New.Lift.Chart.IsPeriodMatrix.exists_frame` gives for it. -/

/-- The vector `∑ i, t i • (1 ⊗ e i)` of `L.ainfLattice` with coordinates `t` in the basis
`e = finBasis ℤ_[p] L.Carrier`. -/
private noncomputable def latticeVec (L : JumpLattice O) :
    (Fin (finrank ℤ_[p] L.Carrier) → Ainf) →ₗ[Ainf] L.Ambient :=
  Fintype.linearCombination Ainf (DiagTensor.mk 1 ∘ finBasis ℤ_[p] L.Carrier)

private lemma ainfLattice_eq_range_latticeVec : L.ainfLattice = (latticeVec L).range := by
  simp [ainfLattice_eq_span_basis, latticeVec]

/-- The ring map `Bmax → BdR` that applies `φ ^ m` and then maps to `BdR`. -/
private noncomputable def frobPowToBdR (m : ℕ) : Bmax →+* BdR :=
  (algebraMap Bmax BdR).comp (toRingHom FrobGal Bmax (.ofAdd m, 1))

/-- A frame of the lattice `L`, with `a = L.jumpBound`: a period matrix `U` made from an invertible
matrix `M` (`New.Lift.Chart.IsPeriodMatrixOf`), the matrices `Q`, `Q'`, `Z`, `Y`, `B` of
`New.Lift.Chart.IsPeriodMatrix.exists_frame`, and vectors `n i` such that `τ ^ a • n i` is the
vector of `L.ainfLattice` with coordinates the column `i` of `Q`. -/
private structure Frame (L : JumpLattice O) where
  /-- An invertible matrix over `Bmax` with invariant columns. -/
  M : GL (Fin (finrank ℤ_[p] L.Carrier)) Bmax
  /-- The period matrix, over `BPlus`. -/
  U : Matrix (Fin (finrank ℤ_[p] L.Carrier)) (Fin (finrank ℤ_[p] L.Carrier)) BPlus
  /-- The unit `μ / (E * τ)` of `Ainf`. -/
  v : Ainfˣ
  /-- The period matrix is made from `M` by the factor `(E * τ) ^ a`, with unit `v`. -/
  isPeriodMatrixOf : k.chart.IsPeriodMatrixOf ((overZp L.ρ).comp k.subgroup.subtype) L.jumpBound
    L.jumpBound (finBasis ℤ_[p] L.Carrier) M.val U v
  /-- The frame matrix over `Ainf` whose columns give the basis. -/
  Q : Matrix (Fin (finrank ℤ_[p] L.Carrier)) (Fin (finrank ℤ_[p] L.Carrier)) Ainf
  /-- An inverse of `Q` up to `τ ^ (a + a)`. -/
  Q' : Matrix (Fin (finrank ℤ_[p] L.Carrier)) (Fin (finrank ℤ_[p] L.Carrier)) Ainf
  /-- The matrix over `BPlus` with entries in `k.bicommutant` that carries `U` to
  `E ^ (a + a) • Q`. -/
  Z : Matrix (Fin (finrank ℤ_[p] L.Carrier)) (Fin (finrank ℤ_[p] L.Carrier)) BPlus
  /-- An inverse of `Z` up to `E ^ (a + a)`. -/
  Y : Matrix (Fin (finrank ℤ_[p] L.Carrier)) (Fin (finrank ℤ_[p] L.Carrier)) BPlus
  /-- The matrix over `S` through which the Frobenius acts on `Q`. -/
  B : Matrix (Fin (finrank ℤ_[p] L.Carrier)) (Fin (finrank ℤ_[p] L.Carrier)) k.S
  /-- `Q * Q' = τ ^ (a + a)`. -/
  Q_mul_Q' : Q * Q' = tau ^ (L.jumpBound + L.jumpBound) • 1
  /-- The entries of `Z` lie in `k.bicommutant`. -/
  Z_mem : ∀ i j : Fin (finrank ℤ_[p] L.Carrier), Z i j ∈ k.bicommutant
  /-- `U * Z = E ^ (a + a) • Q`. -/
  U_mul_Z : U * Z = k.E.val ^ (L.jumpBound + L.jumpBound) • Q.map ainfToBPlus
  /-- `Y * Z = E ^ (a + a)`. -/
  Y_mul_Z : Y * Z = k.E.val ^ (L.jumpBound + L.jumpBound) • 1
  /-- The Frobenius acts on `Q` by `φ Q = v ^ a • (Q * B)`. -/
  map_frobEnd_Q : Q.map frobEnd = v ^ L.jumpBound • (Q * B.map (↑))
  /-- The elements of `FixesThetaZ` act on `Z` through matrices over `Ainf`. -/
  exists_smul_Z : ∀ g : Gp p, k.FixesThetaZ g →
    ∃ G : Matrix (Fin (finrank ℤ_[p] L.Carrier)) (Fin (finrank ℤ_[p] L.Carrier)) Ainf,
      g • Z = Z * G.map ainfToBPlus
  /-- The vectors `τ ^ (-a) • Qᵀ i`. -/
  n : Fin (finrank ℤ_[p] L.Carrier) → L.Ambient
  /-- `τ ^ a • n i` has the coordinates of the column `i` of `Q`. -/
  tau_pow_smul_n (i : Fin (finrank ℤ_[p] L.Carrier)) : tau ^ L.jumpBound • n i = latticeVec L (Qᵀ i)

/-- Every lattice has a frame. -/
private lemma nonempty_frame : Nonempty (Frame L) := by
  -- The period matrix comes from the crystalline basis, the frame from
  -- `New.Lift.Chart.IsPeriodMatrix.exists_frame`, and `n i` from the fact that `τ ^ a` acts
  -- bijectively on `W(C♭) ⊗ L`, as `p` does not divide `τ`.
  obtain ⟨h_adm, -, -⟩ := L.inClass
  obtain ⟨M, U, v, hM⟩ := isChartOf.exists_isPeriodMatrixOf L.jumpBound L.jumpBound
    (ρ := (overZp L.ρ).comp k.subgroup.subtype) (h_adm.mono le_sup_right :)
      (finBasis ℤ_[p] L.Carrier)
    (Nat.sInf_mem exists_jump_bound)
  obtain ⟨Q, Q', Z, Y, B, hQQ', hZ, hUZ, hYZ, hφQ, hZ_gal⟩ := hM.isPeriodMatrix.exists_frame
  have h_surj (x : L.Ambient) : ∃ y : L.Ambient, tau ^ L.jumpBound • y = x := by
    simpa [← map_pow] using
      ((isUnit_algebraMap_wittCFlat_of_not_p_dvd not_p_dvd_tau).pow
        L.jumpBound).smul_bijective.surjective x
  choose n hn using fun i : Fin (finrank ℤ_[p] L.Carrier) ↦ h_surj (latticeVec L (Qᵀ i))
  exact ⟨⟨M, U, v, hM, Q, Q', Z, Y, B, hQQ', hZ, hUZ, hYZ, hφQ, hZ_gal, n, hn⟩⟩

namespace Frame

/-- The combination `F.comb m t = ∑ i, t i • φ ^ m • F.n i`. -/
private noncomputable def comb (F : Frame L) (m : ℕ) :
    (Fin (finrank ℤ_[p] L.Carrier) → Ainf) →ₗ[Ainf] L.Ambient :=
  Fintype.linearCombination Ainf ((fun x : L.Ambient ↦ φ • x)^[m] ∘ F.n)

/-- `(φ ^ m τ ^ a) • F.comb m t`, with `a = L.jumpBound`, is the vector of `L.ainfLattice` with
coordinates `φ ^ m Q * t`. -/
private lemma smul_comb_eq_latticeVec (F : Frame L) (m : ℕ)
    (t : Fin (finrank ℤ_[p] L.Carrier) → Ainf) :
    (φ ^ m • tau ^ L.jumpBound) • F.comb m t =
      latticeVec L (F.Q.map (fun r : Ainf ↦ φ ^ m • r) *ᵥ t) := by
  -- `φ ^ m` fixes the vectors `1 ⊗ e j`, so it acts on `latticeVec L v` through the coordinates.
  have h_phi_col (j : Fin (finrank ℤ_[p] L.Carrier)) : φ ^ m • latticeVec L (F.Qᵀ j) =
      latticeVec L ((F.Q.map fun r : Ainf ↦ φ ^ m • r)ᵀ j) := by
    simp [latticeVec, smul_sum, Fintype.linearCombination_apply, frobGroup_smul_smul,
      MonoidHom.map_one]
  simp [comb, smul_sum, smul_comm _ (t _), ← frobGroup_smul_smul, F.tau_pow_smul_n, ↓mulVec_eq_sum,
    -smul_pow', h_phi_col, Fintype.linearCombination_apply]

/-- `τ ^ a • ∑ i, t i • F.n i`, with `a = L.jumpBound`, is the vector of `L.ainfLattice` with
coordinates `Q * t`. -/
private lemma tau_pow_smul_sum_eq_latticeVec (F : Frame L)
    (t : Fin (finrank ℤ_[p] L.Carrier) → Ainf) :
    tau ^ L.jumpBound • ∑ i : Fin (finrank ℤ_[p] L.Carrier), t i • F.n i =
      latticeVec L (F.Q *ᵥ t) := by
  simpa [comb, Fintype.linearCombination_apply] using F.smul_comb_eq_latticeVec 0 t

/-- A form `μ` lies in `L.forms` if and only if, for any `m`, its coordinates
`basisValues μ ᵥ* φ ^ m M` in the frame are fixed by every `g ∈ Γ'`. The reason is that the
columns of `M` are invariant. -/
private lemma mem_forms_iff (F : Frame L) (m : ℕ) {μ : L.Functional} :
    μ ∈ L.forms ↔ ∀ (g : k.subgroup) (ν : Fin (finrank ℤ_[p] L.Carrier)),
      (basisValues μ ᵥ* (frobPowToBdR m).mapMatrix F.M) ν =
        (toGp g.val • basisValues μ ᵥ* (frobPowToBdR m).mapMatrix F.M) ν := by
  refine forall_comm.trans (forall_congr' fun g ↦ ?_)
  refine (equivariant_iff_basisValues (F.M.isUnit.map (frobPowToBdR m).mapMatrix) ?_).trans
    funext_iff
  -- The invariance of the columns of `M`, mapped by `frobPowToBdR m`, which commutes with `g`.
  have h_cols : (repMatrix L.ρ (finBasis ℤ_[p] L.Carrier) g.val).map (algebraMap ℤ_[p] Bmax) *
      F.M.val.map (fun x : Bmax ↦ toGp g.val • x) = F.M.val :=
    F.isPeriodMatrixOf.hasInvariantColumns g
  have h_mapped := congrArg (frobPowToBdR m).mapMatrix h_cols
  -- `using!`: the two actions of `g` on `BdR` agree only by unfolding their definitions.
  simpa [frobPowToBdR, smul_smul, ↓map_mul, @MulAction.compHom_smul_def _ _ Bmax, Function.comp_def,
    ← IsScalarTower.algebraMap_apply] using! h_mapped

/-- For a form `μ ∈ L.forms`, each coordinate `(basisValues μ ᵥ* φ ^ m M) ν` lies in `hodgeFil 0`
and in the field `valueField 0`, being fixed by `Γ'`. -/
private lemma coord_mem_hodgeFil_zero_and_mem_valueField (F : Frame L) (m : ℕ) {μ : L.Functional}
    (hμ : μ ∈ L.forms) (ν : Fin (finrank ℤ_[p] L.Carrier)) :
    (basisValues μ ᵥ* (frobPowToBdR m).mapMatrix F.M) ν ∈ hodgeFil 0 ∧
      (basisValues μ ᵥ* (frobPowToBdR m).mapMatrix F.M) ν ∈ valueField 0 :=
  mem_hodgeFil_zero_and_mem_valueField_zero_of_fixed fun g ↦ (F.mem_forms_iff m).mp hμ g ν

/-- The values of a form on `F.comb m t` in terms of the frame: with `a = L.jumpBound`,
`φ ^ m E ^ a • μ (F.comb m t)` is the product of the coordinates `basisValues μ ᵥ* φ ^ m M` with
`φ ^ m Z * t`. -/
private lemma frobE_pow_smul_apply_comb (F : Frame L) (μ : L.Functional) (m : ℕ)
    (t : Fin (finrank ℤ_[p] L.Carrier) → Ainf) :
    (k.frobE m).val ^ L.jumpBound • μ (F.comb m t) =
      basisValues μ ᵥ* (frobPowToBdR m).mapMatrix F.M ⬝ᵥ
        (↑) ∘ (F.Z.map frobEnd^[m] *ᵥ ainfToBPlus ∘ t) := by
  -- Compare `smul_comb_eq_latticeVec` with `(E * τ) ^ a • M * Z = U * Z = E ^ (a + a) • Q`, and
  -- cancel the unit `φ ^ m ((E * τ) ^ a)`.
  set a : ℕ := L.jumpBound with ha
  have h_cmp : (k.frobE m).val ^ (a + a) • μ ((φ ^ m • tau ^ a) • F.comb m t) -
        basisValues μ ⬝ᵥ (frobPowToBdR m).mapMatrix ((F.U * F.Z).map (↑)) *ᵥ t • 1 =
      (k.frobE m).val ^ (a + a) • μ (latticeVec L (F.Q.map (fun r : Ainf ↦ φ ^ m • r) *ᵥ t)) -
        basisValues μ ⬝ᵥ (frobPowToBdR m).mapMatrix
          ((k.E.val ^ (a + a) • F.Q.map ainfToBPlus).map (↑)) *ᵥ t • 1 := by
    rw [F.smul_comb_eq_latticeVec, F.U_mul_Z]
  rw [Matrix.map_mul, F.isPeriodMatrixOf.map_eq_smul, ← ha, map_mul, ← mulVec_mulVec,
    dotProduct_mulVec] at h_cmp
  apply (((isUnit_smul_of_dvd_mu 1 ⟨_, F.isPeriodMatrixOf.E_mul_tau_mul.symm⟩).pow a).map
    (frobPowToBdR m)).mul_left_cancel
  -- The normalisation unfolds the maps and the coordinates; `ring_nf` then closes the goal.
  linear_combination (norm := (
    simp [latticeVec, frobPowToBdR, smul_def', ↓map_apply, val_frobE, phi_pow_smul, mul_sum,
      ↓RingHom.mapMatrix_apply, FrobGal.smul_def, sum_mul, mul_comm (μ _),
      ← IsScalarTower.algebraMap_apply, Fintype.linearCombination_apply, mulVec, dotProduct,
      basisValues, vecMul, sub_eq_zero]
    ring_nf)) h_cmp

/-- The case `t = Pi.single i 1` of `frobE_pow_smul_apply_comb`: the value of a form on
`φ ^ m • F.n i`. -/
private lemma frobE_pow_mul_apply_smul_n (F : Frame L) (μ : L.Functional) (m : ℕ)
    (i : Fin (finrank ℤ_[p] L.Carrier)) :
    algebraMap Ainf BdR (k.frobE m).val ^ L.jumpBound * μ (φ ^ m • F.n i) =
      ∑ ν : Fin (finrank ℤ_[p] L.Carrier), (basisValues μ ᵥ* (frobPowToBdR m).mapMatrix F.M) ν *
        algebraMap BPlus BdR (frobEnd^[m] (F.Z ν i)) := by
  simpa [comb, smul_def', dotProduct, Pi.single_apply, mulVec] using
    F.frobE_pow_smul_apply_comb μ m (Pi.single i 1)

/-- The frame vectors `F.n i` lie in `L.kisinAinf`. -/
private lemma n_mem_kisinAinf (F : Frame L) (i : Fin (finrank ℤ_[p] L.Carrier)) :
    F.n i ∈ L.kisinAinf := by
  have h_lat : tau ^ L.jumpBound • F.n i ∈ L.ainfLattice := by
    simp [F.tau_pow_smul_n, ainfLattice_eq_range_latticeVec]
  refine ⟨⟨tau ^ L.jumpBound, ⟨L.jumpBound, rfl⟩, h_lat⟩, fun m μ hμ ↦ ?_⟩
  -- The factor `frobE (m + 1) ^ a` is prime to `E`, so it does not affect the filtration.
  refine (mul_mem_hodgeFil_iff_of_not_frobE_dvd (not_frobE_dvd_frobE_of_ne m.succ_pos.ne)
    L.jumpBound).1 ?_
  have h_sum : ∑ ν, (basisValues μ ᵥ* (frobPowToBdR (m + 1)).mapMatrix F.M) ν *
      algebraMap BPlus BdR (frobEnd^[m + 1] (F.Z ν i)) ∈ hodgeFil (0 + 0) :=
    sum_mem fun ν _ ↦ mul_mem_hodgeFil
      (F.coord_mem_hodgeFil_zero_and_mem_valueField (m + 1) hμ ν).left algebraMap_mem_hodgeFil_zero
  simpa [F.frobE_pow_mul_apply_smul_n, phiInvToBdR] using h_sum

/-- Each vector `φ ^ l • F.n i` lies in `L.valueFieldPoints (L.frobKisinAinf l)`: all forms in
`L.forms` take values in the field `valueField 0` on it. -/
private lemma phi_pow_smul_n_mem_valueFieldPoints (F : Frame L) (l : ℕ)
    (i : Fin (finrank ℤ_[p] L.Carrier)) :
    φ ^ l • F.n i ∈ L.valueFieldPoints (L.frobKisinAinf l) := by
  refine ⟨by simp [frobKisinAinf, F.n_mem_kisinAinf], fun μ hμ ↦ ?_⟩
  -- All terms of `frobE_pow_mul_apply_smul_n` lie in the field `valueField 0`.
  have h_frob : MapsTo frobEnd (k.bicommutant : Set BPlus) k.bicommutant :=
    fun y hy ↦ k.frobEnd_mem_bicommutant hy
  have hZ_mem (ν : Fin (finrank ℤ_[p] L.Carrier)) :
      algebraMap BPlus BdR (frobEnd^[l] (F.Z ν i)) ∈ valueField 0 := by
    have h_iter : frobEnd^[l] (F.Z ν i) ∈ k.bicommutant := h_frob.iterate l (F.Z_mem ν i)
    -- `valueField 0` contains the image of `k.bicommutant`: its generators include `b * 1`.
    exact Subfield.subset_closure (.inr ⟨(⟨_, h_iter⟩, 1), by simp [RingHom.map_one]⟩)
  have h_mem : algebraMap Ainf BdR (k.frobE l).val ^ L.jumpBound * μ (φ ^ l • F.n i) ∈
      valueField 0 := by
    rw [F.frobE_pow_mul_apply_smul_n]
    exact sum_mem fun ν _ ↦
      mul_mem (F.coord_mem_hodgeFil_zero_and_mem_valueField l hμ ν).right (hZ_mem ν)
  simpa [phiInvToBdR] using div_mem h_mem (phiInvToBdR_mem_valueField (k.frobE l ^ L.jumpBound))

/-- Crystalline forms detect the coefficients of `F.comb m t`, up to the factor
`φ ^ m E ^ (a + a)` with `a = L.jumpBound`. Let `W` be a `BPlus`-submodule of `BdR`. If
`μ (F.comb m t) ∈ W` for every crystalline form `μ`, then `φ ^ m E ^ (a + a) * t i` maps into `W`
for every `i`. -/
private lemma phiInvToBdR_frobE_pow_mul_mem_of_forall_crysForms (F : Frame L) (m : ℕ)
    (W : Submodule BPlus BdR) (t : Fin (finrank ℤ_[p] L.Carrier) → Ainf)
    (hW : ∀ μ ∈ L.crysForms, μ (F.comb m t) ∈ W) (i : Fin (finrank ℤ_[p] L.Carrier)) :
    phiInvToBdR 0 (k.frobE m ^ (L.jumpBound + L.jumpBound) * t i) ∈ W := by
  -- Test with the forms `σ ν` given by the rows of `φ ^ m M⁻¹`; their coordinates are the unit
  -- vectors. Then combine the values with row `i` of `φ ^ m Y` and use `Y * Z = E ^ (a + a)`.
  have h_ext (ν : Fin (finrank ℤ_[p] L.Carrier)) : ∃ σ : L.Functional,
      ∀ s : Rep.of (overZp L.ρ), σ (DiagTensor.mk 1 s) =
        ((algHom ℤ_[p] Bmax BdR).toLinearMap ∘ₗ
          (finBasis ℤ_[p] L.Carrier).constr ℕ (frobEnd^[m] ∘ F.M.inv ν)) s :=
    exists_functional_extend _
  choose σ hσ using h_ext
  have h_unit (ν : Fin (finrank ℤ_[p] L.Carrier)) :
      basisValues (σ ν) ᵥ* (frobPowToBdR m).mapMatrix F.M = (1 : Matrix _ _ BdR) ν := by
    funext l
    have h_inv_entry := congrArg (fun X ↦ frobPowToBdR m (X ν l)) F.M.inv_val
    -- `using!`: `algHom ℤ_[p] Bmax BdR` and `algebraMap Bmax BdR` agree only by definition.
    simpa [frobPowToBdR, FrobGal.smul_def, hσ, Matrix.mul_apply, vecMul, dotProduct, basisValues,
      Matrix.one_apply] using! h_inv_entry
  have hσ_forms (ν : Fin (finrank ℤ_[p] L.Carrier)) : σ ν ∈ L.forms := by
    simp [F.mem_forms_iff m, ↓h_unit, Matrix.one_apply]
  have hσ_mem (ν : Fin (finrank ℤ_[p] L.Carrier)) : σ ν ∈ L.crysForms :=
    ⟨hσ_forms ν, _, hσ ν⟩
  have h_sum : ∑ ν, F.Y.map frobEnd^[m] i ν • (k.frobE m).val ^ L.jumpBound • σ ν (F.comb m t) ∈
      W :=
    sum_smul_mem W (F.Y.map frobEnd^[m] i) fun ν _ ↦
      W.smul_of_tower_mem ((k.frobE m).val ^ L.jumpBound) (hW (σ ν) (hσ_mem ν))
  suffices h_eq : phiInvToBdR 0 (k.frobE m ^ (L.jumpBound + L.jumpBound) * t i) =
      ∑ ν, F.Y.map frobEnd^[m] i ν • (k.frobE m).val ^ L.jumpBound • σ ν (F.comb m t) by
    rw [h_eq]
    exact h_sum
  simpa [↓F.frobE_pow_smul_apply_comb, ↓h_unit, ↓map_mul, ← mulVec_mulVec, val_frobE,
    algebraMap_eq_diagonal, phi_pow_smul, ↓mulVec.eq_1 (F.Y.map _), smul_def', phiInvToBdR,
    dotProduct, Matrix.one_apply, ← IsScalarTower.algebraMap_apply] using
    congr(algebraMap _ BdR (((frobEnd ^ m).mapMatrix $F.Y_mul_Z.symm *ᵥ ainfToBPlus ∘ t) i))

/-- For `x ∈ L.ainfLattice` and `a = L.jumpBound`, `τ ^ a • x` is a combination `F.comb 0 t` of
the `F.n i`. -/
private lemma exists_comb_eq_tau_pow_smul_of_mem_ainfLattice (F : Frame L) {x : L.Ambient}
    (hx : x ∈ L.ainfLattice) :
    ∃ t : Fin (finrank ℤ_[p] L.Carrier) → Ainf, F.comb 0 t = tau ^ L.jumpBound • x := by
  -- With `x = Σ α i (1 ⊗ e i)`, take `t = Q' * α` and use `Q * Q' = τ ^ (a + a)`.
  obtain ⟨α, rfl⟩ := ainfLattice_eq_range_latticeVec.le hx
  refine ⟨F.Q' *ᵥ α, ?_⟩
  simpa [comb, F.Q_mul_Q', pow_add, Fintype.linearCombination_apply, mul_smul, smul_mulVec] using
    F.tau_pow_smul_sum_eq_latticeVec (F.Q' *ᵥ α)

/-- Clause (a) of `frame_theorem`: an `S`-linear map `f : Ainf → S` carries a linear relation among
vectors of `L.valueFieldPoints L.fracSpan` to the relation with coefficients `f (c i)`. -/
private lemma sum_map_smul_eq_zero_of_sum_smul_eq_zero (F : Frame L) (f : Ainf →ₗ[k.S] k.S)
    {ι : Type} [Fintype ι] (v : ι → L.Ambient) (c : ι → Ainf)
    (hv : ∀ i : ι, v i ∈ L.valueFieldPoints L.fracSpan) (hc : ∑ i : ι, c i • v i = 0) :
    ∑ i : ι, f (c i) • v i = 0 := by
  -- A non-zero multiple of the sum is `F.comb 0 t`. The crystalline forms kill it, because
  -- `sum_phiInvToBdR_map_mul_mem_of_mem_valueField` carries the relation `μ (∑ i, c i • v i) = 0`
  -- through `f`; so `t = 0`.
  choose hv_frac hv_val using hv
  obtain ⟨r, hr, h_mem⟩ := fracSpan.sum_smul_mem (fun i ↦ f (c i)) (t := univ) fun i _ ↦ hv_frac i
  obtain ⟨t, ht⟩ := F.exists_comb_eq_tau_pow_smul_of_mem_ainfLattice h_mem
  have h_kill : ∀ μ ∈ L.crysForms, μ (F.comb 0 t) ∈ (⊥ : Submodule BPlus BdR) := by
    rintro μ ⟨hμ, -⟩
    have h_rel : ∑ i, phiInvToBdR 0 (c i) * μ (v i) ∈ (⊥ : Submodule BPlus BdR) := by
      simpa [smul_def', phiInvToBdR] using congrArg μ hc
    have h_zero : ∑ i, algebraMap Ainf BdR (f (c i)).1 * μ (v i) = 0 := by
      simpa [phiInvToBdR] using
        sum_phiInvToBdR_map_mul_mem_of_mem_valueField f _ c (fun i ↦ hv_val i μ hμ) (W := ⊥) h_rel
    simp [ht, smul_def', h_zero]
  have ht_zero (i : Fin (finrank ℤ_[p] L.Carrier)) : t i = 0 := by
    simpa using F.phiInvToBdR_frobE_pow_mul_mem_of_forall_crysForms 0 ⊥ t h_kill i
  simpa [comb, nonZeroDivisors.ne_zero hr, ht_zero, smul_eq_val_smul,
    Fintype.linearCombination_apply] using
    ht.symm

/-- If `w` divides every coefficient `t i`, then `F.comb 0 t` is `w` times a combination of the
`F.n i`. -/
private lemma exists_smul_comb_eq_of_dvd (F : Frame L) (w : Ainf)
    (t : Fin (finrank ℤ_[p] L.Carrier) → Ainf) (hw : ∀ i : Fin (finrank ℤ_[p] L.Carrier), w ∣ t i) :
    ∃ u : Fin (finrank ℤ_[p] L.Carrier) → Ainf, w • F.comb 0 u = F.comb 0 t := by
  obtain ⟨u, rfl⟩ : (fun _ : Fin (finrank ℤ_[p] L.Carrier) ↦ w) ∣ t := pi_dvd_iff.mpr hw
  exact ⟨u, (map_smul (F.comb 0) w u).symm⟩

/-- Applying `φ ^ m` to `F.comb 0 t` gives the combination of the `φ ^ m • F.n i` with the
coefficients `φ ^ m • t i`. -/
private lemma comb_phi_pow_smul (F : Frame L) (m : ℕ) (t : Fin (finrank ℤ_[p] L.Carrier) → Ainf) :
    F.comb m (fun i : Fin (finrank ℤ_[p] L.Carrier) ↦ φ ^ m • t i) = φ ^ m • F.comb 0 t := by
  simp [comb, smul_iterate, smul_sum, Fintype.linearCombination_apply, frobGroup_smul_smul]

/-- The test for `τ`: if every crystalline form sends `φ ^ (m + 1) • F.comb 0 t` into `hodgeFil 1`,
for every `m`, then `τ` divides every coefficient `t i`. -/
private lemma tau_dvd_of_forall_crysForms (F : Frame L) (t : Fin (finrank ℤ_[p] L.Carrier) → Ainf)
    (ht : ∀ m : ℕ, ∀ μ ∈ L.crysForms, μ (φ ^ (m + 1) • F.comb 0 t) ∈ hodgeFil 1)
    (i : Fin (finrank ℤ_[p] L.Carrier)) : tau ∣ t i := by
  -- By `tau_dvd_of_theta_frobEnd` it suffices that `E` divides every `φ ^ (m + 1) (t i)`. The
  -- factor `frobE (m + 1) ^ (a + a)` that the coefficient test leaves is prime to `E`.
  refine tau_dvd_of_theta_frobEnd fun m ↦ ?_
  have h_forms : ∀ μ ∈ L.crysForms, μ (F.comb (m + 1) fun j ↦ φ ^ (m + 1) • t j) ∈
      (hodgeFil 1).restrictScalars BPlus := by
    simpa [F.comb_phi_pow_smul] using ht m
  have h_fil : phiInvToBdR 0 (k.frobE (m + 1) ^ (L.jumpBound + L.jumpBound) * φ ^ (m + 1) • t i) ∈
      hodgeFil 1 :=
    F.phiInvToBdR_frobE_pow_mul_mem_of_forall_crysForms (m + 1) _ _ h_forms i
  have h_dvd : (k.frobE 0 : Ainf) ∣
      k.frobE (m + 1) ^ (L.jumpBound + L.jumpBound) * φ ^ (m + 1) • t i :=
    phiInvToBdR_mem_hodgeFil_one_iff.mp h_fil
  -- At index `0`, `thetaPhiInv` is `θ`; and `θ` does not kill `frobE (m + 1)`.
  have h_theta (r : Ainf) : thetaPhiInv 0 r = theta r := by simp [thetaPhiInv]
  have h_E_ne : theta (k.frobE (m + 1)).val ≠ 0 := by
    rw [← h_theta, Ne, ← frobE_dvd_iff]
    exact not_frobE_dvd_frobE_of_ne m.succ_pos.ne
  simpa [frobE_dvd_iff, phi_pow_smul, h_theta, h_E_ne] using h_dvd

/-- Let `x ∈ L.kisinAinf`. If `τ ^ N • x` is a combination `F.comb 0 t` of the `F.n i`, then so is
`x`: the powers of `τ` are removed one at a time by the test for `τ`. -/
private lemma exists_comb_eq_of_exists_comb_eq_tau_pow_smul (F : Frame L) {x : L.Ambient}
    (hx : x ∈ L.kisinAinf) (N : ℕ) :
    (∃ t : Fin (finrank ℤ_[p] L.Carrier) → Ainf, F.comb 0 t = tau ^ N • x) →
      ∃ t : Fin (finrank ℤ_[p] L.Carrier) → Ainf, F.comb 0 t = x := by
  induction N with
  | zero => simp
  | succ N ih =>
    rintro ⟨t, ht⟩
    rw [pow_succ', mul_smul] at ht
    -- `E` divides `φ ^ (m + 1) τ`, so `τ ^ (N + 1) • x` passes the test for `τ`.
    have h_fil (m : ℕ) : ∀ μ ∈ L.crysForms, μ (φ ^ (m + 1) • F.comb 0 t) ∈ hodgeFil 1 := by
      rintro μ ⟨hμ, -⟩
      obtain ⟨-, hτx_forms⟩ := L.kisinAinf.smul_mem (tau ^ N) hx
      have h_tau : phiInvToBdR 0 (φ ^ (m + 1) • tau) ∈ hodgeFil 1 :=
        phiInvToBdR_mem_hodgeFil_one_iff.mpr (frobE_dvd_phi_pow_tau m.succ_pos)
      have h_forms : μ (φ ^ (m + 1) • tau ^ N • x) ∈ hodgeFil 0 := hτx_forms m μ hμ
      simpa [ht, smul_def', frobGroup_smul_smul, phiInvToBdR] using mul_mem_hodgeFil h_tau h_forms
    apply ih
    simpa [ht] using F.exists_smul_comb_eq_of_dvd tau t (F.tau_dvd_of_forall_crysForms t h_fil)

/-- The frame vectors `F.n i` span `L.kisinAinf` over `Ainf`. -/
private lemma span_n_eq_kisinAinf (F : Frame L) : span Ainf (Set.range F.n) = L.kisinAinf := by
  refine L.kisinAinf.span_eq_of_le (range_subset_iff.mpr F.n_mem_kisinAinf) fun x hx ↦ ?_
  -- Some `τ ^ N • x` lies in `L.ainfLattice`; then `τ ^ (a + N) • x` is a combination of the
  -- `F.n i`.
  obtain ⟨⟨_, ⟨N, rfl⟩, hτx⟩, -⟩ := Submodule.mem_inf.mp hx
  have h_comb : ∃ t : Fin (finrank ℤ_[p] L.Carrier) → Ainf,
      F.comb 0 t = tau ^ (L.jumpBound + N) • x := by
    simpa only [smul_smul, ← pow_add] using F.exists_comb_eq_tau_pow_smul_of_mem_ainfLattice hτx
  simpa [mem_span_range_iff_exists_fun, comb, Fintype.linearCombination_apply] using
    F.exists_comb_eq_of_exists_comb_eq_tau_pow_smul hx (L.jumpBound + N) h_comb

/-- The vectors `φ ^ l • F.n i` span `L.valueFieldPoints (L.frobKisinAinf l)` over `S`. -/
private lemma span_phi_pow_smul_n_eq_valueFieldPoints (F : Frame L) (l : ℕ) :
    span k.S (Set.range fun i : Fin (finrank ℤ_[p] L.Carrier) ↦ φ ^ l • F.n i) =
      L.valueFieldPoints (L.frobKisinAinf l) := by
  refine (valueFieldPoints _).span_eq_of_le
    (range_subset_iff.mpr (F.phi_pow_smul_n_mem_valueFieldPoints l)) fun x hx ↦ ?_
  -- Write `φ ^ (-l) x = ∑ i, t i • n i` and apply the `S`-linear map `k.coord₀ : Ainf → S`, which
  -- sends `1` to `1`, to the relation `-x + ∑ i, φ ^ l (t i) • φ ^ l • n i = 0`.
  obtain ⟨hx_frob, hx_val⟩ := hx
  obtain ⟨t, ht⟩ := (mem_span_range_iff_exists_fun Ainf).mp (F.span_n_eq_kisinAinf.ge hx_frob)
  have h_le : L.frobKisinAinf l ≤ L.fracSpan :=
    fun y hy ↦ by simpa using smul_mem_fracSpan (φ ^ l) (kisinAinf_le_fracSpan hy)
  -- The vector `x` and the `φ ^ l • F.n i`, indexed by `Option`.
  let w : Option (Fin (finrank ℤ_[p] L.Carrier)) → L.Ambient :=
    fun o ↦ o.elim x fun i ↦ φ ^ l • F.n i
  have hw_frac : ∀ o, w o ∈ L.valueFieldPoints L.fracSpan := by
    rintro (_ | i)
    · exact ⟨h_le hx_frob, hx_val⟩
    · exact (F.phi_pow_smul_n_mem_valueFieldPoints l i).imp_left (h_le ·)
  have h_rel : ∑ o, k.coord₀ (φ ^ l • o.elim (-1) t) • w o = 0 := by
    refine F.sum_map_smul_eq_zero_of_sum_smul_eq_zero k.coord₀ w _ hw_frac ?_
    simp [w, ← frobGroup_smul_smul, ← smul_sum, ht]
  refine (mem_span_range_iff_exists_fun k.S).mpr ⟨fun i ↦ k.coord₀ (φ ^ l • t i), ?_⟩
  simpa [w, add_eq_zero_iff_eq_neg'] using h_rel

/-- The vectors `F.n i` are linearly independent over `Ainf`: crystalline forms detect the
coefficients. -/
private lemma linearIndependent_n (F : Frame L) : LinearIndependent Ainf F.n := by
  refine Fintype.linearIndependent_iff.mpr fun t ht i ↦ ?_
  have h_kill : ∀ μ ∈ L.crysForms, μ (F.comb 0 t) ∈ (⊥ : Submodule BPlus BdR) := by
    simp [comb, ht, Fintype.linearCombination_apply]
  simpa using F.phiInvToBdR_frobE_pow_mul_mem_of_forall_crysForms 0 ⊥ t h_kill i

private lemma comb_zero_apply (F : Frame L) (t : Fin (finrank ℤ_[p] L.Carrier) → Ainf) :
    F.comb 0 t = ∑ i : Fin (finrank ℤ_[p] L.Carrier), t i • F.n i := by
  simp [comb, Fintype.linearCombination_apply]

/-- The frame vectors `F.n i` span the Kisin module over `S`. -/
private lemma span_n_eq_kisinModule (F : Frame L) : span k.S (Set.range F.n) = L.kisinModule := by
  simpa [frobKisinAinf_zero] using F.span_phi_pow_smul_n_eq_valueFieldPoints 0

/-- Clause (b) of `frame_theorem`. Let `3 e ≤ p ^ l` and `e A ≤ p ^ l δ`. Then `p ^ (4 δ)` times a
vector `x` of `L.valueFieldPoints (L.frobKisinAinf l)` lies in the `S`-span of the vectors `y`
of that module with `g • μ y - μ y ∈ hodgeFil A` for all `μ ∈ L.forms` and all `g ∈ Γ'`. -/
private lemma pow_smul_mem_span_of_mem_valueFieldPoints (F : Frame L) {l A δ : ℕ}
    (hl : 3 * k.e ≤ p ^ l) (hA : k.e * A ≤ p ^ l * δ) {x : L.Ambient}
    (hx : x ∈ L.valueFieldPoints (L.frobKisinAinf l)) :
    p ^ (4 * δ) • x ∈ span k.S
      {y ∈ L.valueFieldPoints (L.frobKisinAinf l) |
        ∀ μ ∈ L.forms, ∀ g : k.subgroup, toGp g.val • μ y - μ y ∈ hodgeFil A} := by
  -- The radius lemma writes `φ ^ l Z = frobE l ^ a • (D * V)` with `D` fixed by `Γ'`, and
  -- `p ^ (4 δ) • c` lies in the span of the `y` with `V * y` natural modulo `E ^ A`.
  simp only [← F.span_phi_pow_smul_n_eq_valueFieldPoints l, mem_span_range_iff_exists_fun] at hx ⊢
  obtain ⟨c, rfl⟩ := hx
  obtain ⟨V, D, hD, hZV, h_rad⟩ :=
    radius_lemma (fixes _) (by simpa using (exists_smul_z 1).choose_spec) F.Z_mem F.Y_mul_Z
      (F.exists_smul_Z _ (fixes _)).choose_spec hl L.jumpBound
  rw [← Fintype.linearCombination_apply, ← map_nsmul]
  refine mapsTo_span (fun y hy ↦ ?_) (h_rad A δ hA c)
  refine ⟨⟨y, rfl⟩, fun μ hμ g ↦ ?_⟩
  -- Here `V * y = r + E ^ A • w` with `r` a vector of naturals.
  choose r w hw using mem_natCongruentSet.mp hy
  let coords : Fin (finrank ℤ_[p] L.Carrier) → BdR :=
    basisValues μ ᵥ* (frobPowToBdR l).mapMatrix F.M
  have h_val : ∑ i, (y i).val • μ (φ ^ l • F.n i) =
      coords ⬝ᵥ (↑) ∘ (D *ᵥ ((fun i ↦ (r i : BPlus)) + ainfToBPlus k.E.val ^ A • w)) := by
    simpa [coords, comb, hZV, ← mulVec_mulVec,
      eq_add_of_sub_eq' (funext hw : _ = (_ : BPlus) • w), algebraMap.smul, ← smul_sum, dotProduct,
      Function.comp_def, Fintype.linearCombination_apply, smul_mulVec] using
      F.frobE_pow_smul_apply_comb μ l fun i ↦ (y i : Ainf)
  -- The part with `r` is fixed by `g`, and the part with `E ^ A • w` lies in `hodgeFil A`.
  have h_coords_fix (ν : Fin (finrank ℤ_[p] L.Carrier)) : toGp g.val • coords ν = coords ν :=
    ((F.mem_forms_iff l).mp hμ g ν).symm
  have hD_fix (ν i : Fin (finrank ℤ_[p] L.Carrier)) : toGp g.val • D ν i = D ν i := by
    simpa using congrFun₂ (hD _ (fixes g).left) ν i
  have h_err : ∑ ν, coords ν *
      (phiInvToBdR 0 (k.frobE 0) ^ (A : ℤ) * algebraMap BPlus BdR (D ν ⬝ᵥ w)) ∈
        hodgeFil (0 + (A + 0)) :=
    sum_mem fun ν _ ↦ mul_mem_hodgeFil (F.coord_mem_hodgeFil_zero_and_mem_valueField l hμ ν).left
      (mul_mem_hodgeFil (phiInvToBdR_frobE_zpow_mem_hodgeFil 0 A) algebraMap_mem_hodgeFil_zero)
  simpa [h_val, ↓mulVec_add, mul_add, frobE, smul_sum, h_coords_fix, hD_fix,
    Fintype.linearCombination_apply, smul_eq_val_smul, dotProduct, mulVec_smul, mulVec,
    ← IsScalarTower.algebraMap_apply, sum_add_distrib, phiInvToBdR] using
    sub_mem (smul_mem_hodgeFil (toGp g) h_err) h_err

/-- Clause (d) of `frame_theorem`: for a crystalline form `μ` and `y` in the Kisin module,
`E ^ a • μ y` with `a = L.jumpBound` is the image of an element of `k.bicommutant`. -/
private lemma exists_mem_bicommutant_of_mem_kisinModule (F : Frame L) {μ : L.Functional}
    (hμ_crys : μ ∈ L.crysForms) {y : L.Ambient} (hy : y ∈ L.kisinModule) :
    ∃ s ∈ k.bicommutant, k.E.val ^ L.jumpBound • μ y = algebraMap BPlus BdR s := by
  -- The coordinates of `μ` are fixed elements of `Bmax`, so they come from `k.bicommutant`.
  obtain ⟨hμ, l, hl⟩ := hμ_crys
  rw [← F.span_n_eq_kisinModule] at hy
  obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun k.S).mp hy
  have h_fixed (ν : Fin (finrank ℤ_[p] L.Carrier)) (g : k.subgroup) :
      toGp g.val • ∑ i, l (finBasis ℤ_[p] L.Carrier i) * F.M i ν =
        ∑ i, l (finBasis ℤ_[p] L.Carrier i) * F.M i ν := by
    simpa [hl, frobPowToBdR, ← map_mul, ← map_sum, basisValues, Prod.mk_one_one, vecMul,
      dotProduct] using ((F.mem_forms_iff 0).mp hμ g ν).symm
  choose b hb_mem hb using fun ν ↦
    isChartOf.exists_mem_bicommutant_of_fixed
      (b := ∑ i, l (finBasis ℤ_[p] L.Carrier i) * F.M i ν) (h_fixed ν)
  refine ⟨b ⬝ᵥ F.Z *ᵥ ainfToBPlus ∘ fun i ↦ (c i : Ainf), ?_, ?_⟩
  · simp (maxDischargeDepth := 4) [sum_mem, mul_mem, hb_mem, F.Z_mem, dotProduct, mulVec]
  · simpa [hl, frobPowToBdR, ← map_mul, ← map_sum, ← hb, F.comb_zero_apply, frobE, smul_eq_val_smul,
      dotProduct, vecMul, basisValues, Prod.mk_one_one, ← IsScalarTower.algebraMap_apply] using
      F.frobE_pow_smul_apply_comb μ 0 fun i ↦ (c i : Ainf)

/-- Clause (e) of `frame_theorem`. Suppose `d` divides `r` whenever `d` divides `E ^ m r` in
`BPlus`. If every crystalline form `μ` has `E ^ n • μ x` in `BPlus ∙ d`, then `x ∈ L.kisinAinf` lies
in `d • L.kisinAinf`. -/
private lemma mem_smul_kisinAinf_of_forall_crysForms (F : Frame L) (d : Ainf)
    (hd : ∀ {m : ℕ} {r : Ainf}, ainfToBPlus d ∣ ainfToBPlus (k.E.val ^ m * r) → d ∣ r)
    {x : L.Ambient} (hx : x ∈ L.kisinAinf) {n : ℕ}
    (h_forms : ∀ μ ∈ L.crysForms, k.E.val ^ n • μ x ∈ BPlus ∙ algebraMap Ainf BdR d) :
    x ∈ d • L.kisinAinf := by
  -- Read off the coefficients of `x` modulo `d`; the two powers of `E` are dropped by `hd`.
  obtain ⟨t, rfl⟩ := (mem_span_range_iff_exists_fun Ainf).mp (F.span_n_eq_kisinAinf.ge hx)
  have h_dvd (i : Fin (finrank ℤ_[p] L.Carrier)) : d ∣ t i := by
    have h_forms' (μ : L.Functional) (hμ : μ ∈ L.crysForms) :
        μ (F.comb 0 (k.E.val ^ n • t)) ∈ BPlus ∙ algebraMap Ainf BdR d := by
      rw [map_smul, map_smul, F.comb_zero_apply]
      exact h_forms μ hμ
    obtain ⟨y, hy⟩ := mem_span_singleton.mp
      (F.phiInvToBdR_frobE_pow_mul_mem_of_forall_crysForms 0 _ (k.E.val ^ n • t) h_forms' i)
    have h_dvd_E : ainfToBPlus d ∣
        ainfToBPlus (k.E.val ^ (L.jumpBound + L.jumpBound) * (k.E.val ^ n * t i)) := by
      refine ⟨y, algebraMap_injective BPlus BdR ?_⟩
      simpa [frobE, commutes y, smul_def', ← IsScalarTower.algebraMap_apply, phiInvToBdR] using
        hy.symm
    exact hd (map_dvd ainfToBPlus (hd h_dvd_E))
  obtain ⟨u, hu⟩ := F.exists_smul_comb_eq_of_dvd d t h_dvd
  rw [← F.comb_zero_apply t, ← hu, F.comb_zero_apply, ← F.span_n_eq_kisinAinf]
  exact smul_mem_pointwise_smul _ d _ ((mem_span_range_iff_exists_fun Ainf).mpr ⟨u, rfl⟩)

/-- Clause (f) of `frame_theorem`: `τ ^ a`, with `a = L.jumpBound`, carries `L.kisinAinf` into
`L.ainfLattice`. -/
private lemma tau_pow_smul_mem_ainfLattice_of_mem_kisinAinf (F : Frame L) {x : L.Ambient}
    (hx : x ∈ L.kisinAinf) : tau ^ L.jumpBound • x ∈ L.ainfLattice := by
  obtain ⟨t, rfl⟩ := (mem_span_range_iff_exists_fun Ainf).mp (F.span_n_eq_kisinAinf.ge hx)
  simp [F.tau_pow_smul_sum_eq_latticeVec, ainfLattice_eq_range_latticeVec]

/-- Clause (g) of `frame_theorem`: `τ ^ a`, with `a = L.jumpBound`, carries `L.ainfLattice` into
`L.kisinAinf`. -/
private lemma tau_pow_smul_mem_kisinAinf_of_mem_ainfLattice (F : Frame L) {x : L.Ambient}
    (hx : x ∈ L.ainfLattice) : tau ^ L.jumpBound • x ∈ L.kisinAinf := by
  obtain ⟨t, ht⟩ := F.exists_comb_eq_tau_pow_smul_of_mem_ainfLattice hx
  rw [← ht, ← F.span_n_eq_kisinAinf, F.comb_zero_apply]
  exact (mem_span_range_iff_exists_fun Ainf).mpr ⟨t, rfl⟩

/-- Clause (h) of `frame_theorem`: `E ^ a • φ`, with `a = L.jumpBound` and `E` the unit
`k.frobEUnit 0` of `W(C♭)`, maps the Kisin module into itself. -/
private lemma frobEUnit_pow_smul_phi_smul_mem_kisinModule (F : Frame L) {x : L.Ambient}
    (hx : x ∈ L.kisinModule) : k.frobEUnit 0 ^ L.jumpBound • φ • x ∈ L.kisinModule := by
  -- We have `φ τ = E * τ * v` and `φ Q = v ^ a • (Q * B)`; cancel `τ ^ a` and `v ^ a`.
  obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun k.S).mp (F.span_n_eq_kisinModule.ge hx)
  refine F.span_n_eq_kisinModule.le ((mem_span_range_iff_exists_fun k.S).mpr ⟨F.B *ᵥ k.φ ∘ c, ?_⟩)
  simpa [mul_comm _ F.v.val, mul_comm _ tau, phi_smul_ainf, F.map_frobEnd_Q,
    ← F.isPeriodMatrixOf.E_mul_tau_mul, ← F.tau_pow_smul_sum_eq_latticeVec, ← mulVec_mulVec,
    mul_pow, ↓frobEUnit_pow_smul, Units.smul_def, smul_sum (r := φ), Chart.φ, frobE, comb, mulVec,
    dotProduct, smul_eq_val_smul, frobGroup_smul_smul, smul_mulVec, Fintype.linearCombination_apply,
    mul_smul] using
    (F.smul_comb_eq_latticeVec 1 fun i ↦ φ • (c i : Ainf)).symm

end Frame

/-- The properties of `L.kisinAinf` and of the Kisin module `L.kisinModule` given by the frame
theorem, with `a = L.jumpBound`, `S = k.S` the ring of the Kummer chart and `E = k.E`. -/
structure FrameProperties (L : JumpLattice O) : Prop where
  /-- (a) An `S`-linear map `f : Ainf → S` carries a relation `∑ i, c i • v i = 0` among vectors of
  `L.valueFieldPoints L.fracSpan` to the relation `∑ i, f (c i) • v i = 0`. -/
  sum_map_smul_eq_zero :
    ∀ (f : Ainf →ₗ[k.S] k.S) {ι : Type} [Fintype ι] (v : ι → L.Ambient) (c : ι → Ainf),
      (∀ i : ι, v i ∈ L.valueFieldPoints L.fracSpan) →
        ∑ i : ι, c i • v i = 0 → ∑ i : ι, f (c i) • v i = 0
  /-- (b) If `3 e ≤ p ^ l` and `e A ≤ p ^ l δ`, then `p ^ (4 δ)` times a vector of
  `L.valueFieldPoints (L.frobKisinAinf l)` lies in the `S`-span of the vectors `y` of that module
  with `g • μ y - μ y ∈ hodgeFil A` for every `μ ∈ L.forms` and every `g ∈ Γ'`. -/
  pow_smul_mem_span_of_mem_valueFieldPoints :
    ∀ l A δ : ℕ, 3 * k.e ≤ p ^ l → k.e * A ≤ p ^ l * δ →
      ∀ x ∈ L.valueFieldPoints (L.frobKisinAinf l),
        p ^ (4 * δ) • x ∈ span k.S
          {y ∈ L.valueFieldPoints (L.frobKisinAinf l) |
            ∀ μ ∈ L.forms, ∀ g : k.subgroup, toGp g.val • μ y - μ y ∈ hodgeFil A}
  /-- (c) `L.kisinAinf` is the `Ainf`-span of the Kisin module. -/
  kisinAinf_eq_span_kisinModule : L.kisinAinf = span Ainf (L.kisinModule : Set L.Ambient)
  /-- (d) For a crystalline form `μ` and `y` in the Kisin module, `E ^ a • μ y` is the image of an
  element of `k.bicommutant`. -/
  exists_mem_bicommutant_pow_smul_eq :
    ∀ μ ∈ L.crysForms, ∀ y ∈ L.kisinModule,
      ∃ s ∈ k.bicommutant, k.E.val ^ L.jumpBound • μ y = algebraMap BPlus BdR s
  /-- (e) Let `d ∈ Ainf` divide `r` whenever it divides `E ^ m r` in `BPlus`. Then `x ∈ L.kisinAinf`
  lies in `d • L.kisinAinf` once, for one `n`, `E ^ n • μ x ∈ BPlus ∙ d` for every crystalline form
  `μ`. -/
  mem_smul_kisinAinf_of_forall_crysForms :
    ∀ d : Ainf, (∀ {m : ℕ} {r : Ainf}, ainfToBPlus d ∣ ainfToBPlus (k.E.val ^ m * r) → d ∣ r) →
      ∀ x ∈ L.kisinAinf, ∀ n : ℕ,
        (∀ μ ∈ L.crysForms, k.E.val ^ n • μ x ∈ BPlus ∙ algebraMap Ainf BdR d) →
          x ∈ d • L.kisinAinf
  /-- (f) `τ ^ a` carries `L.kisinAinf` into `L.ainfLattice`. -/
  tau_pow_smul_mem_ainfLattice : ∀ x ∈ L.kisinAinf, tau ^ L.jumpBound • x ∈ L.ainfLattice
  /-- (g) `τ ^ a` carries `L.ainfLattice` into `L.kisinAinf`. -/
  tau_pow_smul_mem_kisinAinf : ∀ x ∈ L.ainfLattice, tau ^ L.jumpBound • x ∈ L.kisinAinf
  /-- (h) `E ^ a • φ`, with `E` the unit `k.frobEUnit 0` of `W(C♭)`, maps the Kisin module into
  itself. -/
  frobEUnit_pow_smul_phi_smul_mem_kisinModule :
    ∀ x ∈ L.kisinModule, k.frobEUnit 0 ^ L.jumpBound • φ • x ∈ L.kisinModule
  /-- (i) Some vectors `v i`, one for each index of a basis of `L`, span the Kisin module over `S`,
  span `L.kisinAinf` over `Ainf`, and are linearly independent over `Ainf`. -/
  exists_span_eq_kisinModule_linearIndependent :
    ∃ v : Fin (finrank ℤ_[p] L.Carrier) → L.Ambient,
      span k.S (Set.range v) = L.kisinModule ∧
      span Ainf (Set.range v) = L.kisinAinf ∧
      LinearIndependent Ainf v

/-- The frame theorem for the lattice `L` over the Kummer chart `k`: `L` has the nine properties of
`FrameProperties`. This gives part of Kisin's theorem: it shows `E ^ a φ N ⊆ N` but not the
finite-height inclusion `E ^ n N ⊆ S φ N`. That theorem concerns the module attached to a
crystalline lattice, for Kummer charts. -/
theorem frame_theorem : FrameProperties L := by
  -- Every field is read off a frame `F` of `L` (`Frame`). The vectors `F.n i` span `L.kisinAinf`
  -- over `Ainf`, and the `φ ^ l • F.n i` span `L.valueFieldPoints (L.frobKisinAinf l)` over `S`;
  -- the other fields are computations in these coordinates.
  obtain ⟨F⟩ : Nonempty (Frame L) := nonempty_frame
  exact
    { sum_map_smul_eq_zero := F.sum_map_smul_eq_zero_of_sum_smul_eq_zero
      pow_smul_mem_span_of_mem_valueFieldPoints l A δ hl hA x :=
        F.pow_smul_mem_span_of_mem_valueFieldPoints hl hA
      kisinAinf_eq_span_kisinModule := by
        rw [← F.span_n_eq_kisinModule, span_span_of_tower, F.span_n_eq_kisinAinf]
      exists_mem_bicommutant_pow_smul_eq μ hμ y := F.exists_mem_bicommutant_of_mem_kisinModule hμ
      mem_smul_kisinAinf_of_forall_crysForms d hd x hx n :=
        F.mem_smul_kisinAinf_of_forall_crysForms d hd hx
      tau_pow_smul_mem_ainfLattice x := F.tau_pow_smul_mem_ainfLattice_of_mem_kisinAinf
      tau_pow_smul_mem_kisinAinf x := F.tau_pow_smul_mem_kisinAinf_of_mem_ainfLattice
      frobEUnit_pow_smul_phi_smul_mem_kisinModule x := F.frobEUnit_pow_smul_phi_smul_mem_kisinModule
      exists_span_eq_kisinModule_linearIndependent :=
        ⟨F.n, F.span_n_eq_kisinModule, F.span_n_eq_kisinAinf, F.linearIndependent_n⟩ }

/-- `kisinAinf` is the A_inf-module of those x in A_inf[1/τ] ⊗ L with μ(φ^n x) ∈ B_dR⁺ for all n ≥ 1
and all Γ'-equivariant forms μ (`forms`). It equals the A_inf-span of the Kisin module
`kisinModule`, the S-module of its elements on which all these forms take values in the field
`k.valueField 0`. This is the field `kisinAinf_eq_span_kisinModule` of `frame_theorem`. -/
lemma kisinAinf_eq_span_kisinModule : L.kisinAinf = span Ainf (L.kisinModule : Set L.Ambient) :=
  frame_theorem.kisinAinf_eq_span_kisinModule

/-- Let `μ` be a crystalline invariant form of `L` (`crysForms`: an invariant functional
W(C^♭) ⊗ L → `BdR` whose restriction to 1 ⊗ L comes from a ℤ_p-linear map L → `Bmax`), and let `y`
be a vector of the Kisin module of `L`. Let `jumpBound` be the least a such that all Hodge–Tate
jumps of `L` lie in [−a, a]. Then `E ^ jumpBound • μ y` is the image in `BdR` of an element of
`bicommutant`, the ring S_B ⊂ `BPlus` of the chart, which is the closure of S[E/p] in `BPlus` with p
inverted. -/
lemma exists_mem_bicommutant_pow_smul_eq_of_mem_kisinModule {μ : L.Functional}
    (hμ : μ ∈ L.crysForms) {y : L.Ambient} (hy : y ∈ L.kisinModule) :
    ∃ s ∈ k.bicommutant, k.E.val ^ L.jumpBound • μ y = algebraMap BPlus BdR s :=
  frame_theorem.exists_mem_bicommutant_pow_smul_eq μ hμ y hy

/-- Crystalline forms detect divisibility in `kisinAinf`. Let powers of `E` cancel from `d`: if `d`
divides `E ^ m * r` in `BPlus`, then `d` divides `r` in `Ainf`. If `x` lies in `kisinAinf` and, for
one `n`, the values `E ^ n • μ x` of all crystalline invariant forms `μ` are `BPlus`-multiples of
`d`, then `x` lies in `d • kisinAinf`. -/
lemma mem_smul_kisinAinf_of_crysForms {d : Ainf}
    (h_cancel : ∀ {m : ℕ} {r : Ainf}, ainfToBPlus d ∣ ainfToBPlus (k.E.val ^ m * r) → d ∣ r)
    {x : L.Ambient} (hx : x ∈ L.kisinAinf) {n : ℕ}
    (h_val : ∀ μ ∈ L.crysForms, k.E.val ^ n • μ x ∈ BPlus ∙ algebraMap Ainf BdR d) :
    x ∈ d • L.kisinAinf :=
  frame_theorem.mem_smul_kisinAinf_of_forall_crysForms d h_cancel x hx n h_val

/-- Multiplication by `tau ^ jumpBound` maps `kisinAinf` into `ainfLattice`. -/
lemma tau_pow_jumpBound_smul_mem_ainfLattice_of_mem_kisinAinf {x : L.Ambient}
    (hx : x ∈ L.kisinAinf) : tau ^ L.jumpBound • x ∈ L.ainfLattice :=
  frame_theorem.tau_pow_smul_mem_ainfLattice x hx

/-- Multiplication by `tau ^ jumpBound` maps `ainfLattice` into `kisinAinf`. -/
lemma tau_pow_jumpBound_smul_mem_kisinAinf_of_mem_ainfLattice {x : L.Ambient}
    (hx : x ∈ L.ainfLattice) : tau ^ L.jumpBound • x ∈ L.kisinAinf :=
  frame_theorem.tau_pow_smul_mem_kisinAinf x hx

/-- For a jump lattice `L`, there is a family `v` in W(C^♭) ⊗ L, indexed by `Fin` of the ℤ_p-rank of
`L`, that is linearly independent over `Ainf`. Its `S`-span is the Kisin module of `L`, and its
`Ainf`-span is `kisinAinf`, the A_inf-module of the x in A_inf[1/τ] ⊗ L with μ(φ^n x) ∈ B_dR^+ for
all n ≥ 1 and all invariant forms μ. -/
lemma exists_span_eq_kisinModule_linearIndependent :
    ∃ v : Fin (finrank ℤ_[p] L.Carrier) → L.Ambient,
      span k.S (Set.range v) = L.kisinModule ∧
      span Ainf (Set.range v) = L.kisinAinf ∧
      LinearIndependent Ainf v :=
  frame_theorem.exists_span_eq_kisinModule_linearIndependent

/-- For a jump lattice `L` (a finite free `O`-module with a `Γ`-action, crystalline over `Γ'`), the
vectors of `L.frobKisinAinf l`, the image of `kisinAinf` under `φ ^ l`, on which all forms in
`L.forms` take values in the field `valueField 0` ⊂ B_dR form the `S`-span of the image of the Kisin
module `L.kisinModule` under `φ ^ l`. -/
lemma valueFieldPoints_frobKisinAinf_eq_span (l : ℕ) :
    L.valueFieldPoints (L.frobKisinAinf l) =
      span k.S ((fun y : L.Ambient ↦ φ ^ l • y) '' (L.kisinModule : Set L.Ambient)) := by
  -- Both sides are spanned by the vectors `φ ^ l • F.n i` of a frame `F`, as `φ` preserves `S`.
  obtain ⟨F⟩ : Nonempty (Frame L) := nonempty_frame
  rw [← F.span_phi_pow_smul_n_eq_valueFieldPoints l, ← F.span_n_eq_kisinModule]
  refine le_antisymm (span_mono (range_subset_iff.mpr fun i ↦ ?_)) (span_le.2 ?_)
  · exact ⟨F.n i, subset_span ⟨i, rfl⟩, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun k.S).mp hy
    refine (mem_span_range_iff_exists_fun k.S).mpr ⟨fun i ↦ (k.φ ^ l) (c i), ?_⟩
    simp only [smul_sum, smul_eq_val_smul, frobGroup_smul_smul, Chart.coe_phi_pow, phi_pow_smul]

private lemma mem_kisinAinf_of_mem_kisinModule {x : L.Ambient} (hx : x ∈ L.kisinModule) :
    x ∈ L.kisinAinf :=
  hx.left

/-- Some power of `tau` multiplies a vector of `kisinAinf` into `ainfLattice`. -/
private lemma mem_saturateBy_of_mem_kisinAinf {x : L.Ambient} (hx : x ∈ L.kisinAinf) :
    x ∈ saturateBy (Submonoid.powers tau) L.ainfLattice :=
  hx.left

/-- For a jump lattice `L` (a finite free `O`-module with a `Γ`-action, crystalline over `Γ'` of the
Kummer chart `k`), the Kisin module is free over `S`. This module consists of the x in `kisinAinf`
on which all `Γ'`-equivariant forms take values in the field `valueField 0`. -/
lemma free_kisinModule : Module.Free k.S L.kisinModule := by
  -- The family `v` is linearly independent over `Ainf`, hence over `S`, and spans the module.
  obtain ⟨v, h_span_S, -, h_indep⟩ := exists_span_eq_kisinModule_linearIndependent (L := L)
  rw [← h_span_S]
  exact .of_basis (Basis.span (h_indep.restrict_scalars' k.S))

/-- After inverting `tau`, the `Ainf`-span of the Kisin module and `ainfLattice` agree: they have
the same saturation by the powers of `tau`. This is a case of the comparison over `A_inf[1/μ]` for
Breuil–Kisin–Fargues modules (Bhatt–Morrow–Scholze 2018, Lemma 4.26), before the Frobenius twist. -/
lemma saturateBy_tau_span_kisinModule :
    saturateBy (Submonoid.powers tau) (span Ainf (L.kisinModule : Set L.Ambient)) =
      saturateBy (Submonoid.powers tau) L.ainfLattice := by
  -- `tau ^ jumpBound` carries each of `kisinAinf` and `ainfLattice` into the other.
  have h_le {M N : Submodule Ainf L.Ambient} (hMN : ∀ {x}, x ∈ M → tau ^ L.jumpBound • x ∈ N) :
      saturateBy (Submonoid.powers tau) M ≤ saturateBy (Submonoid.powers tau) N := by
    rintro x ⟨r, hr, hrx⟩
    exact ⟨tau ^ L.jumpBound * r, mul_mem ⟨L.jumpBound, rfl⟩ hr, by simpa [mul_smul] using hMN hrx⟩
  rw [← kisinAinf_eq_span_kisinModule]
  exact le_antisymm (h_le tau_pow_jumpBound_smul_mem_ainfLattice_of_mem_kisinAinf)
    (h_le tau_pow_jumpBound_smul_mem_kisinAinf_of_mem_ainfLattice)

/-- In W(C^♭) ⊗ L, `kisinAinf` is the A_inf-module of those `x` in A_inf[1/τ] ⊗ L with
μ(φ^n x) ∈ B_dR⁺ for all n ≥ 1 and all μ in `L.forms`. Then `x` lies in `kisinAinf` if
and only if two conditions hold. First, some power of `tau` = [ε^{1/p}] − 1 multiplies `x` into
`ainfLattice`, the A_inf-span of the elements 1 ⊗ y with y in L. Second, for some `n` and every `μ`
in `crysForms`, `E ^ n • μ x` is the image in `BdR` of an element of `BPlus`; here `crysForms` are
the invariant forms whose restriction to 1 ⊗ L comes from a Z_p-linear map L → `Bmax`, and `E` is
`k.E`. -/
theorem mem_kisinAinf_iff_crysForms {x : L.Ambient} :
    x ∈ L.kisinAinf ↔ x ∈ saturateBy (Submonoid.powers tau) L.ainfLattice ∧
      ∃ n : ℕ, ∀ μ ∈ L.crysForms, ∃ s : BPlus, k.E.val ^ n • μ x = algebraMap BPlus BdR s := by
  -- Forwards: expand `x` in a family `v` that spans `kisinAinf` and bound the values on each `v i`.
  -- Backwards: some `tau ^ N • x` lies in `kisinAinf`, and the crystalline forms show that it is
  -- divisible by `tau ^ N` there.
  obtain ⟨v, h_span_S, h_span_A, -⟩ := exists_span_eq_kisinModule_linearIndependent (L := L)
  constructor
  · intro hx
    refine ⟨mem_saturateBy_of_mem_kisinAinf hx, L.jumpBound, fun μ hμ ↦ ?_⟩
    obtain ⟨u, rfl⟩ := (mem_span_range_iff_exists_fun Ainf).mp (h_span_A.ge hx)
    choose q _ hq using fun i : Fin (finrank ℤ_[p] L.Carrier) ↦
      exists_mem_bicommutant_pow_smul_eq_of_mem_kisinModule hμ (h_span_S.le (subset_span ⟨i, rfl⟩))
    refine ⟨∑ i, u i • q i, ?_⟩
    simp only [map_sum, map_smul, Finset.smul_sum, smul_comm _ (u _), hq, algebraMap.smul]
  rintro ⟨hx_sat, n, h_val⟩
  rw [← saturateBy_tau_span_kisinModule, ← kisinAinf_eq_span_kisinModule] at hx_sat
  obtain ⟨r, ⟨N, rfl⟩, hx_tau : tau ^ N • x ∈ L.kisinAinf⟩ := hx_sat
  have h_dvd : tau ^ N • x ∈ tau ^ N • L.kisinAinf := by
    refine mem_smul_kisinAinf_of_crysForms tau_pow_dvd_of_dvd_E_pow_mul hx_tau (n := n)
      fun μ hμ ↦ ?_
    obtain ⟨s, hs⟩ := h_val μ hμ
    refine mem_span_singleton.mpr ⟨s, ?_⟩
    rw [map_smul, smul_comm (k.E.val ^ n), hs, Algebra.smul_def, Algebra.smul_def, mul_comm]
  obtain ⟨w, hw, hw_eq⟩ := (mem_smul_pointwise_iff_exists _ (tau ^ N) L.kisinAinf).mp h_dvd
  rwa [← smul_right_injective L.Ambient (pow_ne_zero N tau_ne_zero) hw_eq]

/-- Let the vectors `v i` lie in the Kisin module of `L`, and let `u i ∈ Ainf`. Suppose that for
every `ν` in `crysForms` (the invariant A_inf-linear functionals to B_dR whose restriction to 1 ⊗ L
comes from a Z_p-linear map L → B_max), `E ^ n • ν (∑ i, u i • v i)` is the image in `BdR` of an
element of `bicommutant`, the elements of B^+ = A_max[1/p] whose multiplication commutes with every
S-linear endomorphism of B^+ preserving the image of A_max. Then every `μ` in `crysForms` vanishes
on `∑ i, (u i - k.coord₀ (u i)) • v i`, where `k.coord₀ (u i)` is the coordinate of `u i` in S for
the chosen topological basis of `Ainf` over S, i.e. the coordinate that is the identity on S. -/
lemma apply_sum_sub_coord₀_smul_eq_zero_of_mem_crysForms {μ : L.Functional} {ι : Type} [Fintype ι]
    {v : ι → L.Ambient} (hv_mem : ∀ i : ι, v i ∈ L.kisinModule) {u : ι → Ainf} {n : ℕ}
    (h_val : ∀ ν ∈ L.crysForms, ∃ s ∈ k.bicommutant,
      k.E.val ^ n • ν (∑ i : ι, u i • v i) = algebraMap BPlus BdR s)
    (hμ : μ ∈ L.crysForms) :
    μ (∑ i : ι, (u i - algebraMap k.S Ainf (k.coord₀ (u i))) • v i) = 0 := by
  -- Write `E ^ a • μ (v i)`, with `a = jumpBound`, as the image of `q i ∈ bicommutant`, and put
  -- `w i = E ^ n * q i`. In `BPlus`, `E ^ (a + n)` times the value on `∑ i, u i • v i` is
  -- `∑ i, u i * w i`, which lies in `bicommutant`. The extended coordinate at `1` fixes it and
  -- replaces each `u i` by its coordinate `c i`, so `E ^ (a + n)` kills the value on the
  -- difference.
  set a : ℕ := L.jumpBound
  set c : ι → Ainf := fun i ↦ algebraMap k.S Ainf (k.coord₀ (u i))
  choose q hq_mem hq using fun i : ι ↦
    exists_mem_bicommutant_pow_smul_eq_of_mem_kisinModule hμ (hv_mem i)
  obtain ⟨s, hs_mem, hs⟩ := h_val μ hμ
  let w : ι → BPlus := fun i ↦ ainfToBPlus (k.E.val ^ n) * q i
  have hw_mem (i : ι) : w i ∈ k.bicommutant :=
    mul_mem (ainfToBPlus_mem_bicommutant (k.E ^ n)) (hq_mem i)
  have h_value (r : ι → Ainf) : k.E.val ^ a • k.E.val ^ n • μ (∑ i, r i • v i) =
      algebraMap BPlus BdR (∑ i, ainfToBPlus (r i) * w i) := by
    simp only [map_sum, map_smul, Finset.smul_sum, smul_comm (k.E.val ^ a), a, hq]
    simp only [w, map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def, mul_left_comm]
  have h_eq : ∑ i, ainfToBPlus (u i) * w i = ainfToBPlus (k.E.val ^ a) * s := by
    apply algebraMap_injective BPlus BdR
    rw [← h_value, hs, map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]
  have h_mem : ainfToBPlus (k.E.val ^ a) * s ∈ k.bicommutant :=
    mul_mem (ainfToBPlus_mem_bicommutant (k.E ^ a)) hs_mem
  have h_coord (i : ι) :
      k.chart.extendedCoord k.oneIndex (ainfToBPlus (u i) * w i) = ainfToBPlus (c i) * w i := by
    rw [mul_comm, k.chart.extendToBPlus_mul _ (hw_mem i), k.chart.extendToBPlus_ainfToBPlus,
      LinearMap.comp_apply, Algebra.linearMap_apply, mul_comm]
  have h_fix : ∑ i, ainfToBPlus (c i) * w i = ∑ i, ainfToBPlus (u i) * w i := by
    simpa only [← h_eq, map_sum, h_coord] using k.chart.extendedCoord_oneIndex_eq_self h_mem
  have h_zero : k.E.val ^ a • k.E.val ^ n • μ (∑ i, (u i - c i) • v i) = 0 := by
    simp only [h_value, map_sub, sub_mul, Finset.sum_sub_distrib, h_fix, sub_self, map_zero]
  simpa only [smul_eq_zero, pow_ne_zero _ k.chart.E_ne_zero, false_or] using h_zero

/-- Let `x` be a vector of W(C^♭) ⊗ L, for a lattice `L` with jump sets over the Kummer chart `k`
with ring S. Then `x` lies in the Kisin module of `L` if and only if two conditions hold. First,
some power of `tau` = [ε^{1/p}] − 1 multiplies `x` into `ainfLattice`, the A_inf-span of the 1 ⊗ y
with y in L. Second, for some `n` and every `μ` in `crysForms` (the invariant A_inf-linear
functionals to B_dR whose restriction to 1 ⊗ L comes from a Z_p-linear map L → B_max), `E ^ n • μ x`
is the image in `BdR` of an element of `bicommutant`, the elements of B^+ = A_max[1/p] whose
multiplication commutes with every S-linear endomorphism of B^+ preserving the image of A_max, which
equals `adjoinEDivPClosure` by `Chart.adjoinEDivPClosure_eq_bicommutant`. -/
theorem mem_kisinModule_iff_crysForms {x : L.Ambient} :
    x ∈ L.kisinModule ↔ x ∈ saturateBy (Submonoid.powers tau) L.ainfLattice ∧
      ∃ n : ℕ, ∀ μ ∈ L.crysForms, ∃ s ∈ k.bicommutant,
        k.E.val ^ n • μ x = algebraMap BPlus BdR s := by
  -- Forwards: the values of crystalline forms on the Kisin module. Backwards: `x` lies in
  -- `kisinAinf`, so it is a combination `∑ i, u i • v i` of a family `v` that spans it. Replacing
  -- each `u i` by its coordinate at `1` changes `x` by a vector on which every crystalline form
  -- vanishes, and that vector is `0` by the divisibility test with `d = 0`.
  obtain ⟨v, h_span_S, h_span_A, -⟩ := exists_span_eq_kisinModule_linearIndependent (L := L)
  constructor
  · intro hx
    exact ⟨mem_saturateBy_of_mem_kisinAinf (mem_kisinAinf_of_mem_kisinModule hx), L.jumpBound,
      fun μ hμ ↦ exists_mem_bicommutant_pow_smul_eq_of_mem_kisinModule hμ hx⟩
  rintro ⟨hx_sat, n, h_val⟩
  have hx_A : x ∈ L.kisinAinf := by
    refine mem_kisinAinf_iff_crysForms.mpr ⟨hx_sat, n, fun μ hμ ↦ ?_⟩
    obtain ⟨s, -, hs⟩ := h_val μ hμ
    exact ⟨s, hs⟩
  obtain ⟨u, rfl⟩ := (mem_span_range_iff_exists_fun Ainf).mp (h_span_A.ge hx_A)
  have hv_mem (i : Fin (finrank ℤ_[p] L.Carrier)) : v i ∈ L.kisinModule :=
    h_span_S.le (subset_span ⟨i, rfl⟩)
  -- `d = 0` passes the hypothesis of the divisibility test, as `E ≠ 0`.
  have h_zero_cancel {m : ℕ} {r : Ainf}
      (h_dvd : ainfToBPlus (0 : Ainf) ∣ ainfToBPlus (k.E.val ^ m * r)) : (0 : Ainf) ∣ r := by
    simpa only [map_zero, zero_dvd_iff, map_eq_zero_iff _ (algebraMap_injective Ainf BPlus),
      mul_eq_zero, pow_ne_zero m k.chart.E_ne_zero, false_or] using h_dvd
  have h_diff_mem : ∑ i, (u i - algebraMap k.S Ainf (k.coord₀ (u i))) • v i ∈ L.kisinAinf :=
    sum_mem fun i _ ↦ L.kisinAinf.smul_mem _ (mem_kisinAinf_of_mem_kisinModule (hv_mem i))
  have h_diff : ∑ i, (u i - algebraMap k.S Ainf (k.coord₀ (u i))) • v i ∈
      (0 : Ainf) • L.kisinAinf := by
    refine mem_smul_kisinAinf_of_crysForms h_zero_cancel h_diff_mem (n := 0) fun μ hμ ↦ ?_
    simp only [apply_sum_sub_coord₀_smul_eq_zero_of_mem_crysForms hv_mem h_val hμ, smul_zero,
      zero_mem]
  have hx_coord : ∑ i, u i • v i = ∑ i, k.coord₀ (u i) • v i := by
    obtain ⟨y, -, hy⟩ := (mem_smul_pointwise_iff_exists _ (0 : Ainf) L.kisinAinf).mp h_diff
    simpa only [zero_smul, sub_smul, Finset.sum_sub_distrib, algebraMap_smul, sub_eq_zero]
      using hy.symm
  rw [hx_coord]
  exact sum_mem fun i _ ↦ L.kisinModule.smul_mem (k.coord₀ (u i)) (hv_mem i)

end New.Lift.KummerChart.JumpLattice

end FrameTheorem

/-! ## Galois elements normalising a subgroup -/

namespace New.Lift.KummerChart.JumpLattice

open Period Submodule FrobGroup

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p]
  {k : KummerChart Γ} {O : Coeffs} {L : JumpLattice O} {x : L.Ambient} {μ : L.Functional}

/-- For the Kummer chart `k`, let `k.bicommutant` be its ring S_B: the elements of `BPlus` whose
multiplication commutes with every `k.S`-linear map of `BPlus` keeping the image of A_max,
equivalently the closure of `S[E/p]` in `BPlus` with `p` inverted. Let `E` be the chart's element
`k.E`. If `g ∈ G_p` and `d ∈ BPlus` are such that `d` divides `g • y - y` for every `y` in
`k.bicommutant`, and `x ∈ BdR` has `E ^ m • x` equal to the image of an element of `k.bicommutant`,
then `E ^ (2 * m) • (g • x - x)` is a `BPlus`-multiple of the image of `d` in `BdR`. -/
lemma pow_smul_gal_sub_mem_span_of_dvd {g : Gp p} {d : BPlus} {m : ℕ} {x : BdR}
    (hd : ∀ {y : BPlus}, y ∈ k.bicommutant → d ∣ g • y - y)
    (hx_mem : ∃ s ∈ k.bicommutant, k.E.val ^ m • x = algebraMap BPlus BdR s) :
    k.E.val ^ (2 * m) • (g • x - x) ∈ BPlus ∙ algebraMap BPlus BdR d := by
  obtain ⟨s, hs, hx⟩ := hx_mem
  -- In `BdR` put `F = E ^ m`. As `g • E` is associate to `E`, `F = (g • F) v` for some `v`. As `g`
  -- moves elements of `bicommutant` by multiples of `d`, `g • F - F = d r` and `g • s - s = d t`.
  -- Then `F ^ 2 (g • x - x) = v (F (g • s - s) - (g • F - F) s) = v (F t - r s) d`.
  set F : BdR := algebraMap Ainf BdR (k.E.val ^ m) with hF
  set gF : BdR := algebraMap Ainf BdR ((g • k.E.val) ^ m) with hgF
  obtain ⟨v, hv⟩ : (g • k.E.val) ^ m ∣ k.E.val ^ m :=
    pow_dvd_pow_of_dvd (k.associated_smul_E g).dvd' m
  obtain ⟨r, hr⟩ :
      d ∣ g • algebraMap Ainf BPlus (k.E.val ^ m) - algebraMap Ainf BPlus (k.E.val ^ m) :=
    hd (k.ainfToBPlus_mem_bicommutant (k.E ^ m))
  obtain ⟨t, ht⟩ := hd hs
  have h_assoc : F = gF * algebraMap Ainf BdR v := by rw [hF, hgF, ← map_mul, ← hv]
  have h_x : F * x = algebraMap BPlus BdR s := by rw [hF, ← Algebra.smul_def, hx]
  have h_gx :
      gF * (g • x) = algebraMap BPlus BdR s + algebraMap BPlus BdR d * algebraMap BPlus BdR t :=
    calc gF * (g • x) = g • (F * x) := by simp [hF, hgF, smul_mul', smul_pow']
      _ = algebraMap BPlus BdR (g • s) := by rw [h_x, smul_algebraMap_eq_algebraMap_smul]
      _ = _ := by rw [eq_add_of_sub_eq' ht, map_add, map_mul]
  have h_gF : gF - F = algebraMap BPlus BdR d * algebraMap BPlus BdR r := by
    simpa [hF, hgF, ← IsScalarTower.algebraMap_apply, smul_pow'] using
      congrArg (algebraMap BPlus BdR) hr
  have h_key : F ^ 2 * (g • x - x) = algebraMap Ainf BdR v * (F * algebraMap BPlus BdR t -
      algebraMap BPlus BdR r * algebraMap BPlus BdR s) * algebraMap BPlus BdR d := by
    linear_combination (F * algebraMap Ainf BdR v) * h_gx + (F * g • x - algebraMap BPlus BdR s) *
      h_assoc - F * h_x - (algebraMap Ainf BdR v * algebraMap BPlus BdR s) * h_gF
  refine mem_span_singleton.mpr ⟨v • (k.E.val ^ m • t - r * s), ?_⟩
  simpa [hF, Algebra.smul_def, ← IsScalarTower.algebraMap_apply, pow_mul'] using h_key.symm

/-- Let `g ∈ Γ` satisfy `g Γ' g⁻¹ ⊆ Γ'`, and let `μ` be a `Γ'`-equivariant form (`forms`). Then the
conjugate `conjForm μ g`, the form `y ↦ g⁻¹ • μ (g • y)`, is `Γ'`-equivariant. -/
lemma conjForm_mem_forms {g : GroupOverGp.G} (hg : ∀ γ ∈ k.subgroup, g * γ * g⁻¹ ∈ k.subgroup)
    (hμ : μ ∈ L.forms) : conjForm μ g ∈ L.forms := by
  -- For `γ ∈ Γ'`, use the equivariance of `μ` under `g γ g⁻¹ ∈ Γ'` at the vector `g t`.
  intro t γ
  simpa [mul_smul, inv_smul_eq_iff] using hμ (L.ρ g t) ⟨g * γ * g⁻¹, hg γ γ.prop⟩

/-- Let `g ∈ Γ` satisfy `g Γ' g⁻¹ ⊆ Γ'`. Then `g`, acting through `inr`, maps the module `kisinAinf`
of `L` into itself. -/
lemma smul_mem_kisinAinf {g : GroupOverGp.G} (hg : ∀ γ ∈ k.subgroup, g * γ * g⁻¹ ∈ k.subgroup)
    (hx : x ∈ L.kisinAinf) : inr g • x ∈ L.kisinAinf := by
  obtain ⟨⟨_, ⟨N, rfl⟩, hτx⟩, h_fil⟩ := hx
  refine ⟨?_, fun n μ hμ ↦ ?_⟩
  · -- `g • τ ^ N` multiplies `g • x` into `L.ainfLattice`, and it divides `τ ^ N`.
    have h_mem : (inr g • tau ^ N) • inr g • x ∈ L.ainfLattice := by
      simpa only [frobGroup_smul_smul] using smul_mem_ainfLattice (inr g) hτx
    have h_dvd : inr g • tau ^ N ∣ tau ^ N := by simp [associated_smul_tau.pow_pow.dvd]
    exact mem_saturateBy_of_smul h_dvd ⟨N, rfl⟩ (mem_saturateBy_of_mem h_mem)
  · -- The conjugate form `conjForm μ g` is again invariant, and `g` commutes with `φ`.
    have h_conj : conjForm μ g (φ ^ (n + 1) • x) ∈ hodgeFil 0 :=
      h_fil n (conjForm μ g) (conjForm_mem_forms hg hμ)
    have h_val : μ (inr g • φ ^ (n + 1) • x) ∈ hodgeFil 0 := by
      simpa using smul_mem_hodgeFil (toGp g) h_conj
    have h_comm : φ ^ (n + 1) * inr g = inr g * φ ^ (n + 1) :=
      ((FrobGroup.commute_phi (inr g)).pow_left (n + 1)).eq
    rwa [smul_smul, h_comm, ← smul_smul]

end New.Lift.KummerChart.JumpLattice
