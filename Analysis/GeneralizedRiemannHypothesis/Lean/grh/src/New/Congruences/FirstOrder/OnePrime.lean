import Lib.Weil.Unramified.HeckeGL

/-!
# Norms, logarithms and first-order deformations of the norm

The algebra behind the family of operators at the auxiliary places. A finite group maps to a ring
`R`, and a congruence `a ≡ b` is an equality `σ a = σ b` after a ring map `σ`. The file treats the
norm `Nm` (the sum of the group elements), the coefficients of a product of first-order deformations
`Nm j + α j ∂ j` of the norms `Nm j` of the factors of a product group (the `α j` are variables
and `∂ j ∈ R`), the first entry on the stabiliser of a line in `GL_N`, and logarithms, that is,
norms weighted by a homomorphism to `ℤ/m`.

## Main definitions and results

* `New.Patching.familyCoeff`, `New.Patching.exists_empty_eq_sum_and_insert_eq_mul`: the coefficients
  of `∏ (Nm j + α j ∂ j)` and their properties.
* `New.Patching.map_top_coeff_mul_C_sub_X_mul_C_eq_zero`,
  `New.Patching.exists_map_pow_mul_family_eq_mul_norm`: this product times any multiple of
  `t - α j r` has top coefficient `≡ 0` when `Nm j t = 0` and `∂ j t ≡ Nm j r`, and suitable
  multiples of the coefficients factor through the norm.
* `New.Patching.transfer_firstEntry`: over a finite field, the transfer to `GL_N` of the first entry
  on the stabiliser of a line is the determinant.
* `New.Patching.map_cosetNorm_mul_weightedSum_mul_cosetNormInv`,
  `New.Patching.map_sub_one_mul_weightedSum_valMinAbs`,
  `New.Patching.exists_map_valMinAbs_mul_sub_one`: three congruences for logarithms.
* `New.Patching.map_valMinAbs_eq_zero_of_shift`: a map on weights that kills all differences
  `f (· - k) - f` kills the logarithm modulo `m / (2 k)`.
* `New.Patching.cosetDerivative`, `New.Patching.exists_map_nsmul_mul_sub_one_eq_sum_mul`: the
  operator `∂` built from a logarithm on a subgroup; `n ∂ (g - 1)` is congruent to a multiple of the
  norm.

Notions from other files:
* `New.LocField w`, `New.LocInt w`, `New.ResField w`: for a finite place `w` of a number field, the
  completion `E_w`, its ring of integers `O_w` and its residue field, which has `w.q` elements.
* `New.localIntGL n w`: the subgroup `GL_n(O_w)` of `GL_n(E_w)`.
-/

/-!
## Congruences, norms and the family
-/

section NormsAndFamily

open Finset Subgroup IsComplement MulAction leftTransversals ZMod

namespace New.Patching

universe u

section Congruence

variable {R S : Type*} [Ring R] [Ring S] {σ : R →+* S} {m k : ℕ}

/-- A ring map `σ` is a reduction modulo `m / k` if it kills every `x` with `k x ∈ m R`. Then a
congruence `a ≡ b` modulo `m / k` implies `σ a = σ b`; `exists_isReductionMod` gives a `σ` for which
the converse holds. -/
def IsReductionMod (σ : R →+* S) (m k : ℕ) : Prop :=
  ∀ x y : R, k • x = m • y → σ x = 0

lemma IsReductionMod.natCast_eq_zero (hσ : IsReductionMod σ m k) : (m : S) = 0 := by
  rw [← map_natCast σ]
  exact hσ m k (by rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_comm])

/-- Let `R` be an `O`-algebra that has no `k`-torsion, and let `μ ∈ O` satisfy `k μ = m`. There is a
ring map `σ` on `R` that is a reduction modulo `m / k` (it kills `x` if `k x ∈ m R`) and whose
kernel lies in `μ R`. -/
lemma exists_isReductionMod {O : Type*} {R : Type u} [CommRing O] [Ring R] [Algebra O R] {μ : O}
    (hμ : (k : O) * μ = (m : O)) (hk : IsSMulRegular R k) :
    ∃ (S : Type u) (_ : Ring S) (σ : R →+* S),
      IsReductionMod σ m k ∧ ∀ a b : R, σ a = σ b → ∃ y : R, a - b = μ • y := by
  -- Take the quotient map `R → R / μ R`.
  let I : Ideal R := Ideal.span {algebraMap O R μ}
  have mem_I (x : R) : x ∈ I ↔ ∃ y : R, x = μ • y := by
    simp only [I, Ideal.mem_span_singleton', ← Algebra.commutes, ← Algebra.smul_def, eq_comm]
  have : I.IsTwoSided := ⟨fun {x} y hx ↦ by
    obtain ⟨x', rfl⟩ : ∃ x' : R, x = μ • x' := (mem_I x).1 hx
    exact (mem_I _).2 ⟨x' * y, smul_mul_assoc μ x' y⟩⟩
  refine ⟨R ⧸ I, inferInstance, Ideal.Quotient.mk I, fun x y hxy ↦ ?_,
    fun a b hab ↦ (mem_I _).1 (Ideal.Quotient.eq.1 hab)⟩
  have k_smul : k • x = k • μ • y := by
    rw [hxy, ← Nat.cast_smul_eq_nsmul O m, ← Nat.cast_smul_eq_nsmul O k, smul_smul, hμ]
  exact Ideal.Quotient.eq_zero_iff_mem.2 ((mem_I x).2 ⟨y, hk k_smul⟩)

end Congruence

section Norms

variable {Γ R : Type*} [Group Γ] [Fintype Γ] [Ring R] (ρ : Γ →* R) {Ψ : R} {n : ℕ}

/-- The norm `∑ ρ h` is fixed by left multiplication with `ρ g`. -/
lemma mul_sum_monoidHom (g : Γ) : ρ g * ∑ h : Γ, ρ h = ∑ h : Γ, ρ h := by
  simp only [mul_sum, ← map_mul]
  exact Equiv.sum_comp (.mulLeft g) ρ

/-- The norm `∑ ρ h` is fixed by right multiplication with `ρ g`. -/
lemma sum_monoidHom_mul (g : Γ) : (∑ h : Γ, ρ h) * ρ g = ∑ h : Γ, ρ h := by
  simp only [sum_mul, ← map_mul]
  exact Equiv.sum_comp (.mulRight g) ρ

/-- If `∑ g⁻¹ Ψ g = n` and `g A = A` for all `g`, then `n A = Nm Ψ A`, where `g` stands for `ρ g`
and `Nm = ∑ g`. -/
lemma nsmul_eq_norm_mul (hΨ : ∑ g : Γ, ρ g⁻¹ * Ψ * ρ g = n) {A : R} (hA : ∀ g : Γ, ρ g * A = A) :
    n • A = (∑ g : Γ, ρ g) * Ψ * A := by
  have sum_inv : ∑ g, ρ g⁻¹ = ∑ g, ρ g := Equiv.sum_comp (.inv Γ) ρ
  calc n • A = (∑ g, ρ g⁻¹ * Ψ * ρ g) * A := by rw [hΨ, nsmul_eq_mul]
    _ = (∑ g, ρ g⁻¹) * Ψ * A := by simp only [sum_mul, mul_assoc, hA]
    _ = (∑ g, ρ g) * Ψ * A := by rw [sum_inv]

/-- If `∑ g⁻¹ Ψ g = n` and `A g = A` for all `g`, then `n A = A Ψ Nm`, where `g` stands for `ρ g`
and `Nm = ∑ g`. -/
lemma nsmul_eq_mul_norm (hΨ : ∑ g : Γ, ρ g⁻¹ * Ψ * ρ g = n) {A : R} (hA : ∀ g : Γ, A * ρ g = A) :
    n • A = A * Ψ * ∑ g : Γ, ρ g :=
  calc n • A = A * ∑ g, ρ g⁻¹ * Ψ * ρ g := by rw [hΨ, nsmul_eq_mul']
    _ = A * Ψ * ∑ g, ρ g := by simp only [mul_sum, ← mul_assoc, hA]

end Norms

section Family

variable {J R R' : Type*} [Fintype J] [DecidableEq J] [Ring R] [Ring R'] {σ : R →+* R'}
  {Γ : J → Type*} [∀ j : J, Group (Γ j)] [∀ j : J, Fintype (Γ j)]

/-- Let `ρ` map the product of the finite groups `Γ j` to the ring `R`, and let `σ : R → R'` be a
ring map. Write `g` for `ρ g`, `Nm = ∑ g`, and `a ≡ b` for `σ a = σ b`. If `∑ g⁻¹ Ψ g = n` and
`A (g - 1) ≡ 0` for all `g` in each factor `Γ j`, then `n A ≡ A Ψ Nm`. -/
lemma map_nsmul_eq_mul_norm (ρ : (∀ j : J, Γ j) →* R) {Ψ A : R} {n : ℕ}
    (hΨ : ∑ g : (j : J) → Γ j, ρ g⁻¹ * Ψ * ρ g = n)
    (hA : ∀ (j : J) (g : Γ j), σ (A * (ρ (Pi.mulSingle j g) - 1)) = 0) :
    σ (n • A) = σ (A * Ψ * ∑ g : (j : J) → Γ j, ρ g) := by
  -- The hypothesis extends to the whole group, which the factors generate.
  have invariant (g : ∀ j, Γ j) : σ A * σ (ρ g) = σ A := by
    let H : Submonoid (∀ j, Γ j) :=
      { carrier := {g | σ A * σ (ρ g) = σ A}
        mul_mem' := fun {g h} hg hh ↦ by simp_all [← mul_assoc]
        one_mem' := by simp }
    refine Submonoid.pi_mem_of_mulSingle_mem (H := H) g fun j ↦ ?_
    change σ A * σ (ρ (Pi.mulSingle j (g j))) = σ A
    rw [← map_mul, ← sub_eq_zero, ← map_sub, ← mul_sub_one, hA]
  rw [map_nsmul, map_mul, map_mul, map_sum]
  exact nsmul_eq_mul_norm (σ.toMonoidHom.comp ρ) (by simpa using congrArg σ hΨ) invariant

/-- The product `x ↦ ∏ x j` of elements `x j ∈ 𝒜 j` of pairwise commuting subrings of `R`. -/
noncomputable def commutingProd {𝒜 : J → Subring R}
    (h𝒜 : ∀ i j : J, i ≠ j → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, Commute a b) : (∀ j : J, 𝒜 j) →* R :=
  MonoidHom.noncommPiCoprod (fun j ↦ (𝒜 j).subtype.toMonoidHom)
    fun i j hij a b ↦ h𝒜 i j hij a a.property b b.property

/-- In a product of elements of pairwise commuting subrings, any one factor can be written last. -/
lemma commutingProd_update {𝒜 : J → Subring R}
    (h𝒜 : ∀ i j : J, i ≠ j → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, Commute a b) (x : ∀ j : J, 𝒜 j) (j : J)
    (a : 𝒜 j) :
    commutingProd h𝒜 (Function.update x j a) = commutingProd h𝒜 (Function.update x j 1) * a := by
  have split : Function.update x j a = Function.update x j 1 * Pi.mulSingle j a := by
    simpa [← Pi.mulSingle.eq_1] using Function.update_mul x 1 j 1 a
  rw [split, map_mul]
  simp [commutingProd]

/-- A product of sums of elements of pairwise commuting subrings expands as a sum of products:
`∏_j ∑_i x j i = ∑_f ∏_j x j (f j)`. -/
lemma commutingProd_sum {𝒜 : J → Subring R}
    (h𝒜 : ∀ i j : J, i ≠ j → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, Commute a b) {ι : J → Type*}
    [∀ j : J, Fintype (ι j)] (x : ∀ j : J, ι j → 𝒜 j) :
    commutingProd h𝒜 (fun j : J ↦ ∑ i : ι j, x j i) =
      ∑ f : (j : J) → ι j, commutingProd h𝒜 fun j : J ↦ x j (f j) := by
  -- The product is multilinear, because any one factor can be written last.
  let Φ : (∀ j : J, 𝒜 j) →* R := commutingProd h𝒜
  have last (y : ∀ j : J, 𝒜 j) (j : J) (a : 𝒜 j) :
      Φ (Function.update y j a) = Φ (Function.update y j 1) * a := commutingProd_update h𝒜 y j a
  have Φ_add (y : ∀ j : J, 𝒜 j) (j : J) (a b : 𝒜 j) : Φ (Function.update y j (a + b)) =
      Φ (Function.update y j a) + Φ (Function.update y j b) := by
    rw [last y j (a + b), last y j a, last y j b, Subring.coe_add, mul_add]
  have Φ_smul (y : ∀ j : J, 𝒜 j) (j : J) (r : ℕ) (a : 𝒜 j) :
      Φ (Function.update y j (r • a)) = r • Φ (Function.update y j a) := by
    rw [last y j (r • a), last y j a, AddSubgroupClass.coe_nsmul, mul_smul_comm]
  let M : MultilinearMap ℕ (fun j : J ↦ 𝒜 j) R := .mk' Φ Φ_add Φ_smul
  exact M.map_sum x

/-- The coefficient `∏_{j ∈ S} ∂ j ∏_{j ∉ S} Nm j` of `∏_{j ∈ S} α j` in the family
`∏ (Nm j + α j ∂ j)` in commuting variables `α j`, where `Nm j` and `∂ j = der j` lie in the `j`-th
of the pairwise commuting subrings `𝒜 j`. -/
noncomputable def familyCoeff {𝒜 : J → Subring R}
    (h𝒜 : ∀ i j : J, i ≠ j → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, Commute a b) (Nm der : ∀ j : J, 𝒜 j)
    (S : Finset J) : R :=
  commutingProd h𝒜 (S.piecewise der Nm)

/-- An element that commutes with all the subrings `𝒜 j` commutes with every product
`familyCoeff h𝒜 Nm der S = ∏_{j ∈ S} der j ∏_{j ∉ S} Nm j` of elements `der j`, `Nm j` of `𝒜 j`. -/
lemma commute_familyCoeff {𝒜 : J → Subring R}
    (h𝒜 : ∀ i j : J, i ≠ j → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, Commute a b) (Nm der : ∀ j : J, 𝒜 j)
    {t : R} (ht : ∀ j : J, ∀ a ∈ 𝒜 j, Commute t a) (S : Finset J) :
    Commute t (familyCoeff h𝒜 Nm der S) :=
  MonoidHom.commute_noncommPiCoprod _ (fun j (a : 𝒜 j) ↦ ht j a a.property) (S.piecewise der Nm)

/-- Let `𝒜 j` be pairwise commuting subrings of `R`, with elements `Nm j` and `der j`, so that
`familyCoeff h𝒜 Nm der S` is the product `∏_{j ∈ S} der j ∏_{j ∉ S} Nm j`. Let `ρ` map the product
of the finite groups `Γ j` to `R`, with `Γ j` going into `𝒜 j`. If `Nm j` is the sum of `ρ` over
`Γ j`, then the product `∏ Nm j` at `S = ∅`, in which no `der j` occurs, is the sum of `ρ` over the
whole group. -/
lemma familyCoeff_empty (ρ : (∀ j : J, Γ j) →* R) {𝒜 : J → Subring R}
    (h𝒜 : ∀ i j : J, i ≠ j → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, Commute a b)
    (hρ : ∀ (j : J) (g : Γ j), ρ (Pi.mulSingle j g) ∈ 𝒜 j) {Nm : ∀ j : J, 𝒜 j}
    (h_norm : ∀ j : J, (Nm j : R) = ∑ g : Γ j, ρ (Pi.mulSingle j g)) (der : ∀ j : J, 𝒜 j) :
    familyCoeff h𝒜 Nm der ∅ = ∑ g : (j : J) → Γ j, ρ g := by
  let r (j : J) (g : Γ j) : 𝒜 j := ⟨ρ (Pi.mulSingle j g), hρ j g⟩
  have norm_eq : Nm = fun j ↦ ∑ g : Γ j, r j g := funext fun j ↦ Subtype.ext (by simp [h_norm, r])
  have prod_single (g : ∀ j : J, Γ j) : commutingProd h𝒜 (fun j ↦ r j (g j)) = ρ g :=
    DFunLike.congr_fun (MonoidHom.noncommPiCoprodEquiv.right_inv ρ) g
  calc familyCoeff h𝒜 Nm der ∅ = commutingProd h𝒜 fun j ↦ ∑ g : Γ j, r j g := by
        rw [familyCoeff, piecewise_empty, norm_eq]
    _ = ∑ g : (j : J) → Γ j, commutingProd h𝒜 fun j ↦ r j (g j) := commutingProd_sum h𝒜 r
    _ = ∑ g : (j : J) → Γ j, ρ g := sum_congr rfl fun g _ ↦ prod_single g

/-- Let `Nm j` and `∂ j = der j` lie in the `j`-th of the pairwise commuting subrings `𝒜 j` of `R`.
Then `familyCoeff h𝒜 Nm der S` is the coefficient of `∏_{i ∈ S} α i` in the product
`∏ (Nm i + α i ∂ i)` in commuting variables `α i`. For `j ∉ S` the coefficients at `S` and at
`insert j S` differ only in the factor at `j`: they are `N' Nm j` and `N' ∂ j` for one `N'`. -/
lemma exists_familyCoeff_eq_mul {𝒜 : J → Subring R}
    (h𝒜 : ∀ i j : J, i ≠ j → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, Commute a b) (Nm der : ∀ j : J, 𝒜 j)
    {j : J} {S : Finset J} (hj : j ∉ S) :
    ∃ N' : R,
      familyCoeff h𝒜 Nm der S = N' * Nm j ∧
      familyCoeff h𝒜 Nm der (insert j S) = N' * der j := by
  refine ⟨commutingProd h𝒜 (Function.update (S.piecewise der Nm) j 1), ?_, ?_⟩
  · rw [← commutingProd_update, ← piecewise_eq_of_notMem S der Nm hj, Function.update_eq_self,
      familyCoeff]
  · rw [← commutingProd_update, familyCoeff, piecewise_insert]

/-- Let `ρ` map the product of the finite groups `Γ j` to the ring `R`. Let `𝒜 j` be pairwise
commuting subrings that contain `der j` and the image of `Γ j`. Let `Nm j` be the sum of `ρ` over
`Γ j`. There are elements `N S` that commute with every `t` commuting with all `𝒜 j`, such that
`N ∅` is the sum of `ρ` over the whole group and, for `j ∉ S`, `N S = N' * Nm j` and
`N (insert j S) = N' * der j` for some `N'`. One may take `N S` to be the coefficient of
`∏_{j ∈ S} α j` in `∏ (Nm j + α j * der j)`. -/
lemma exists_empty_eq_sum_and_insert_eq_mul (ρ : (∀ j : J, Γ j) →* R) (𝒜 : J → Subring R)
    (h𝒜 : ∀ i j : J, i ≠ j → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, Commute a b)
    (hρ : ∀ (j : J) (g : Γ j), ρ (Pi.mulSingle j g) ∈ 𝒜 j) {der : J → R}
    (h_der : ∀ j : J, der j ∈ 𝒜 j) :
    ∃ N : Finset J → R,
      (∀ t : R, (∀ j : J, ∀ a ∈ 𝒜 j, Commute t a) → ∀ S : Finset J, Commute t (N S)) ∧
      N ∅ = ∑ g : (j : J) → Γ j, ρ g ∧
      ∀ (j : J) (S : Finset J), j ∉ S → ∃ N' : R,
        N S = N' * ∑ g : Γ j, ρ (Pi.mulSingle j g) ∧ N (insert j S) = N' * der j := by
  let Nm (j : J) : 𝒜 j := ⟨∑ g : Γ j, ρ (Pi.mulSingle j g), sum_mem fun g _ ↦ hρ j g⟩
  let der' (j : J) : 𝒜 j := ⟨der j, h_der j⟩
  exact ⟨familyCoeff h𝒜 Nm der', fun t ht ↦ commute_familyCoeff h𝒜 Nm der' ht,
    familyCoeff_empty ρ h𝒜 hρ (fun j ↦ rfl) der',
    fun j S hj ↦ exists_familyCoeff_eq_mul h𝒜 Nm der' hj⟩

/-- For `j ∉ S`, the coefficient of `∏_{i ∈ S} X i` in `G (t - X j r)` is `t` times that in `G`. -/
lemma coeff_mul_C_sub_X_mul_C_of_notMem {J T : Type*} [CommRing T] (G : MvPolynomial J T)
    (t r : T) {j : J} {S : Finset J} (hj : j ∉ S) :
    (G * (.C t - .X j * .C r)).coeff (∑ i ∈ S, .single i 1) =
      t * G.coeff (∑ i ∈ S, .single i 1) := by
  classical
  simp [mul_sub, ← mul_assoc, mul_comm _ (MvPolynomial.C _), MvPolynomial.coeff_mul_X',
    Finsupp.finsetSum_apply, Finsupp.single_apply, hj]

/-- For `j ∉ S`, the coefficient of `X j ∏_{i ∈ S} X i` in `G (t - X j r)` is `t` times that in `G`
minus `r` times the coefficient of `∏_{i ∈ S} X i` in `G`. -/
lemma coeff_mul_C_sub_X_mul_C_insert {J T : Type*} [DecidableEq J] [CommRing T]
    (G : MvPolynomial J T) (t r : T) {j : J} {S : Finset J} (hj : j ∉ S) :
    (G * (.C t - .X j * .C r)).coeff (∑ i ∈ insert j S, .single i 1) =
      t * G.coeff (∑ i ∈ insert j S, .single i 1) - r * G.coeff (∑ i ∈ S, .single i 1) := by
  rw [mul_sub, mul_left_comm G, MvPolynomial.coeff_sub, sum_insert hj, MvPolynomial.coeff_X_mul]
  simp [mul_comm G]

/-- Let `σ : R → R'` be a ring map, write `a ≡ b` for `σ a = σ b` and `∂ j = der j`, and let the
commutative ring `T` map to `R` by `ac`. Let `𝒩 = ∑_S N S ∏_{i ∈ S} X i` be the polynomial over `R`
with coefficients `N S`, of degree at most one in each of the variables `X i`, which commute with
each other and with `R`. For a polynomial `P` over `T`, the coefficient of `∏_{i ∈ J} X i` in
`𝒩 P` is then the sum over `S` of `N Sᶜ` times the coefficient of `∏_{i ∈ S} X i` in `P`. Suppose
that for `j ∉ S` there is `N'` with `N S = N' Nm j` and `N (insert j S) = N' ∂ j`. If `Nm j t = 0`
and `∂ j t ≡ Nm j r`, then this coefficient is `≡ 0` for every multiple `P = G (t - X j r)`. -/
lemma map_top_coeff_mul_C_sub_X_mul_C_eq_zero {N : Finset J → R} {der : J → R} {T : Type*}
    [CommRing T] (ac : T →+* R) {Nm : J → R}
    (h_factor : ∀ (j : J) (S : Finset J), j ∉ S →
      ∃ N' : R, N S = N' * Nm j ∧ N (insert j S) = N' * der j)
    {j : J} {t r : T} (h_norm : Nm j * ac t = 0) (h_tie : σ (der j * ac t) = σ (Nm j * ac r))
    (G : MvPolynomial J T) :
    σ (∑ S : Finset J,
      N Sᶜ * ac ((G * (.C t - .X j * .C r)).coeff (∑ i ∈ S, .single i 1))) = 0 := by
  -- Pair each `S` without `j` with `insert j S`; the coefficients of `N` at the two complements
  -- differ only in the factor at `j`.
  rw [← powerset_univ, ← insert_erase (mem_univ j), sum_powerset_insert (notMem_erase j _),
    ← sum_add_distrib, map_sum]
  refine sum_eq_zero fun S hS ↦ ?_
  have hj : j ∉ S := fun h ↦ notMem_erase j _ (mem_powerset.1 hS h)
  obtain ⟨N', h_insert, h_S⟩ : ∃ N' : R, N (insert j S)ᶜ = N' * Nm j ∧ N Sᶜ = N' * der j := by
    simpa only [insert_compl_insert hj] using h_factor j (insert j S)ᶜ (by simp)
  have kill (b : T) : N' * Nm j * ac (t * b) = 0 := by
    simp [mul_assoc, ← mul_assoc (Nm j), h_norm]
  have tie (b : T) : σ (N' * der j * ac (t * b)) = σ (N' * Nm j * ac (r * b)) := by
    simpa only [map_mul, mul_assoc] using congrArg (σ N' * · * σ (ac b)) h_tie
  let b : T := G.coeff (∑ i ∈ S, .single i 1)
  let b' : T := G.coeff (∑ i ∈ insert j S, .single i 1)
  rw [map_add, coeff_mul_C_sub_X_mul_C_of_notMem G t r hj, coeff_mul_C_sub_X_mul_C_insert G t r hj,
    h_S, h_insert]
  calc σ (N' * der j * ac (t * b)) + σ (N' * Nm j * ac (t * b' - r * b))
      = σ (N' * Nm j * ac (r * b)) + σ (-(N' * Nm j * ac (r * b))) := by
        rw [tie, map_sub, mul_sub, kill, zero_sub]
    _ = 0 := by rw [map_neg, add_neg_cancel]

/-- Let `ρ` map the product of the finite groups `Γ j` to the ring `R`, and let `σ : R → R'` be a
ring map. Write `g` for `ρ g`, `Nm = ∑ g` for the norm, `Nm j` for the sum over `Γ j`,
`∂ j = der j`, and `a ≡ b` for `σ a = σ b`. Let `N S ∈ R` be indexed by the subsets `S` of `J`, with
`N ∅ = Nm`, and for `j ∉ S` let `N S = N' Nm j` and `N (insert j S) = N' ∂ j` for some `N'`, as for
the coefficients of `∏ (Nm j + α j ∂ j)` in variables `α j`. Let `∑ g⁻¹ Ψ g = n` and `δ = n² δ'`,
where `δ'` commutes with the group and with all `N S`. Suppose that each `g ∈ Γ j` has a `Z` with
`n ∂ j (g - 1) ≡ Nm j Z` and `δ' Nm Z = 0`. Then for `i ≥ #S` there is a `Y` with
`δ ^ i N S ≡ Y Nm`, and `Y = δ ^ i` if `S` is empty. -/
lemma exists_map_pow_mul_family_eq_mul_norm {ρ : (∀ j : J, Γ j) →* R} {N : Finset J → R}
    {der : J → R} {Ψ δ' : R} {n : ℕ} (hΨ : ∑ g : (j : J) → Γ j, ρ g⁻¹ * Ψ * ρ g = n)
    (hδ'ρ : ∀ g : (j : J) → Γ j, Commute δ' (ρ g)) (hδ'N : ∀ S : Finset J, Commute δ' (N S))
    (h_empty : N ∅ = ∑ g : (j : J) → Γ j, ρ g)
    (h_factor : ∀ (j : J) (S : Finset J), j ∉ S → ∃ N' : R,
      N S = N' * ∑ g : Γ j, ρ (Pi.mulSingle j g) ∧ N (insert j S) = N' * der j)
    (h_der : ∀ (j : J) (g : Γ j), ∃ Z : R,
      σ (n • (der j * (ρ (Pi.mulSingle j g) - 1))) = σ ((∑ k : Γ j, ρ (Pi.mulSingle j k)) * Z) ∧
        δ' * (∑ k : (j : J) → Γ j, ρ k) * Z = 0)
    (S : Finset J) {i : ℕ} (hi : #S ≤ i) :
    ∃ Y : R,
      σ ((n ^ 2 • δ') ^ i * N S) = σ (Y * ∑ g : (j : J) → Γ j, ρ g) ∧
      (S = ∅ → Y = (n ^ 2 • δ') ^ i) := by
  -- Induction on `S`. For nonempty `S` write `i = e + 1`; the operator `A = n δ' δ ^ e N S` has
  -- `A (g - 1) ≡ 0`, and `n A = δ ^ (e + 1) N S` factors through the norm.
  set δ : R := n ^ 2 • δ'
  have hδ'δ : Commute δ' δ := (Commute.refl δ').smul_right (n ^ 2)
  have hδ'_norm : Commute δ' (∑ g, ρ g) := .sum_right univ ρ δ' fun g _ ↦ hδ'ρ g
  induction S using Finset.strongInduction generalizing i with | _ S ih
  rcases S.eq_empty_or_nonempty with rfl | hS
  · exact ⟨δ ^ i, by rw [h_empty], fun _ ↦ rfl⟩
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, i = e + 1 := ⟨i - 1, by grind [Finset.card_pos]⟩
  set A : R := n • (δ' * δ ^ e * N S) with hA
  have invariant (j : J) (g : Γ j) : σ (A * (ρ (Pi.mulSingle j g) - 1)) = 0 := by
    by_cases hj : j ∈ S
    · -- Write `N S = N' ∂ j`, so that `N' Nm j = N (S.erase j)`, to which the induction applies.
      obtain ⟨N', h_erase, h_S⟩ : ∃ N' : R,
          N (S.erase j) = N' * ∑ k : Γ j, ρ (Pi.mulSingle j k) ∧ N S = N' * der j := by
        simpa only [insert_erase hj] using h_factor j (S.erase j) (notMem_erase j S)
      obtain ⟨Z, hZ, hZ_zero⟩ := h_der j g
      obtain ⟨Y, hY⟩ : ∃ Y : R, σ (δ ^ e * N (S.erase j)) = σ (Y * ∑ g, ρ g) :=
        (ih (S.erase j) (erase_ssubset hj) (i := e) (by grind [card_erase_of_mem])).imp
          fun Y ↦ And.left
      -- `δ'` moves to the right of `N (S.erase j)` first: `Y` need not commute with it.
      have h_move : δ' * δ ^ e * N (S.erase j) = δ ^ e * N (S.erase j) * δ' := by
        rw [mul_assoc, ((hδ'δ.pow_right e).mul_right (hδ'N _)).eq]
      calc σ (A * (ρ (Pi.mulSingle j g) - 1))
          = σ (δ' * δ ^ e * N') * σ (n • (der j * (ρ (Pi.mulSingle j g) - 1))) := by
            simp only [hA, h_S, ← map_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
        _ = σ (δ' * δ ^ e * N (S.erase j)) * σ Z := by
            simp only [hZ, h_erase, map_mul, mul_assoc]
        _ = σ (Y * (δ' * (∑ g, ρ g) * Z)) := by
            rw [h_move, map_mul, hY, ← map_mul, ← map_mul, mul_assoc Y, ← hδ'_norm.eq]
            simp only [mul_assoc]
        _ = 0 := by rw [hZ_zero, mul_zero, map_zero]
    · -- The norm at `j` is a factor of `N S`.
      obtain ⟨N', h_S⟩ : ∃ N' : R, N S = N' * ∑ k : Γ j, ρ (Pi.mulSingle j k) :=
        (h_factor j S hj).imp fun N' ↦ And.left
      have norm_inv : (∑ k : Γ j, ρ (Pi.mulSingle j k)) * ρ (Pi.mulSingle j g) =
          ∑ k : Γ j, ρ (Pi.mulSingle j k) :=
        sum_monoidHom_mul (ρ.comp (MonoidHom.mulSingle Γ j)) g
      simp only [hA, h_S, smul_mul_assoc, mul_assoc, mul_sub_one, norm_inv, sub_self, map_zero]
  have pow_mul_eq : δ ^ (e + 1) * N S = n • A := by
    rw [hA, smul_smul, ← sq, pow_succ', ← smul_mul_assoc, ← smul_mul_assoc]
  refine ⟨A * Ψ, ?_, fun h ↦ absurd h hS.ne_empty⟩
  rw [pow_mul_eq, map_nsmul_eq_mul_norm ρ hΨ invariant]

end Family

end New.Patching

end NormsAndFamily

/-!
## The first entry on the stabiliser of a line

The transfer of the first entry over a finite field; then the first entry and the determinant of
the reduction of an integral matrix, and the logarithm on the residue units.
-/

section LineStabiliserLog

open Valued Finset IsLocalRing Matrix GeneralLinearGroup SpecialLinearGroup

namespace New.Patching

section FiniteField

variable (F : Type) [Field F] (N : ℕ) [NeZero N]

/-- The stabiliser in `GL_N(F)` of the line of the first basis vector. -/
def residueLineStabilizer : Subgroup (GL (Fin N) F) := parabolic fun i : Fin N ↦ min 1 i.val

variable {F N}

/-- A matrix stabilises the line of the first basis vector if and only if its first column
vanishes below the first entry. -/
lemma mem_residueLineStabilizer {g : GL (Fin N) F} :
    g ∈ residueLineStabilizer F N ↔ ∀ i ≠ 0, g i 0 = 0 := by
  change (∀ i j : Fin N, min 1 j.val < min 1 i.val → g i j = 0) ↔ ∀ i ≠ 0, g i 0 = 0
  refine ⟨fun hg i hi ↦ hg i 0 (by grind), fun hg i j hij ↦ ?_⟩
  obtain ⟨rfl, hi⟩ : j = 0 ∧ i ≠ 0 := by grind
  exact hg i hi

/-- If `p` stabilises the line of the first basis vector, then the first column of `h p` is the
first column of `h` times the first entry of `p`. -/
lemma mul_apply_zero_of_mem_residueLineStabilizer (h : GL (Fin N) F) {p : GL (Fin N) F}
    (hp : p ∈ residueLineStabilizer F N) (i : Fin N) : (h * p) i 0 = h i 0 * p 0 0 :=
  calc (h * p) i 0 = ∑ j : Fin N, h i j * p j 0 := Matrix.mul_apply
    _ = h i 0 * p 0 0 := Fintype.sum_eq_single 0 fun j hj ↦ by
        rw [mem_residueLineStabilizer.1 hp j hj, mul_zero]

/-- The first entry `g ↦ g 0 0`, a character of the stabiliser of the line of the first basis
vector: the scalar by which `g` acts on that line. -/
noncomputable def firstEntry : residueLineStabilizer F N →* Fˣ :=
  MonoidHom.toHomUnits
    { toFun g := (g : GL (Fin N) F) 0 0
      map_one' := by simp
      map_mul' g h := mul_apply_zero_of_mem_residueLineStabilizer (g : GL (Fin N) F) h.property 0 }

lemma coe_firstEntry (g : residueLineStabilizer F N) :
    (firstEntry g : F) = (g : GL (Fin N) F) 0 0 := rfl

/-- Let `d = diagGL t` be the diagonal matrix with entries `t i`. If `h⁻¹ d h` stabilises the line
of the first basis vector, then the first column of `h` is an eigenvector of `d`, so the first entry
of `h⁻¹ d h` is `t i` whenever the `i`-th entry of that column is nonzero. -/
lemma firstEntry_conj_diagGL {t : Fin N → Fˣ} {h d : GL (Fin N) F} (hd : d = diagGL t)
    (h_mem : h⁻¹ * d * h ∈ residueLineStabilizer F N) {i : Fin N} (hi : h i 0 ≠ 0) :
    firstEntry ⟨h⁻¹ * d * h, h_mem⟩ = t i := by
  refine Units.ext (mul_left_cancel₀ hi ?_)
  calc h i 0 * firstEntry ⟨h⁻¹ * d * h, h_mem⟩ = (h * (h⁻¹ * d * h)) i 0 :=
        (mul_apply_zero_of_mem_residueLineStabilizer h h_mem i).symm
    _ = (diagGL t * h) i 0 := by rw [mul_assoc, mul_inv_cancel_left, hd]
    _ = h i 0 * t i := by simp [mul_comm]

variable [Finite F]

/-- Let `F` be a finite field, and let `firstEntry` be the character `g ↦ g 0 0` of the stabiliser
in `GL_N(F)` of the line of the first basis vector. Its transfer to `GL_N(F)` takes the value `x` at
the diagonal matrix `diag (x, 1, …, 1)`. -/
lemma transfer_firstEntry_diagGL (x : Fˣ) :
    (firstEntry (F := F) (N := N)).transfer (diagGL (Pi.mulSingle 0 x)) = x := by
  -- The transfer is a product over the orbits of `g = diag (x, 1, …, 1)` on the lines: an orbit of
  -- length `f` through the line of `v` contributes the factor by which `g ^ f` multiplies `v`. The
  -- line of the first basis vector contributes `x`; every other `v` has a nonzero entry that `g`
  -- fixes.
  let H : Subgroup (GL (Fin N) F) := residueLineStabilizer F N
  set g : GL (Fin N) F := diagGL (Pi.mulSingle 0 x) with hg
  let Ω : Type := Quotient (MulAction.orbitRel (Subgroup.zpowers g) (GL (Fin N) F ⧸ H))
  have : Fintype Ω := Fintype.ofFinite Ω
  have g_pow (f : ℕ) : g ^ f = diagGL (Pi.mulSingle 0 (x ^ f)) := by simp [hg, Pi.mulSingle_pow]
  have g_mem : g ∈ H := mem_residueLineStabilizer.2 fun i hi ↦ by simp [g, hi]
  let η₀ : GL (Fin N) F ⧸ H := ↑(1 : GL (Fin N) F)
  have eq_iff (η : GL (Fin N) F ⧸ H) : η₀ = η ↔ η.out ∈ H := by
    conv_lhs => rw [← η.out_eq', QuotientGroup.eq, inv_one, one_mul]
  have fixed (k : GL (Fin N) F) (hk : k ∈ H) : k • η₀ = η₀ := by
    simpa [η₀, QuotientGroup.eq] using hk
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    Fintype.prod_eq_single (⟦η₀⟧ : Ω)]
  · -- The orbit of `η₀` is the single point `η₀`.
    have out_eq : η₀ = (⟦η₀⟧ : Ω).out := by
      obtain ⟨k, hk⟩ :=
        Quotient.mk_out (s := MulAction.orbitRel (Subgroup.zpowers g) (GL (Fin N) F ⧸ H)) η₀
      change (k : GL (Fin N) F) • η₀ = (⟦η₀⟧ : Ω).out at hk
      rw [← hk, fixed k (Subgroup.zpowers_le.2 g_mem k.property)]
    have out_mem : (⟦η₀⟧ : Ω).out.out ∈ H := (eq_iff _).1 out_eq
    have entry_ne : (⟦η₀⟧ : Ω).out.out 0 0 ≠ 0 := (firstEntry ⟨_, out_mem⟩).ne_zero
    have period : Function.minimalPeriod (g • ·) (⟦η₀⟧ : Ω).out = 1 :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.2 (by rw [← out_eq]; exact fixed g g_mem)
    rw [firstEntry_conj_diagGL (g_pow _) _ entry_ne, period, pow_one, Pi.mulSingle_eq_same]
  · intro q hq
    have not_mem : q.out.out ∉ H := fun h ↦ hq (by rw [(eq_iff q.out).2 h, q.out_eq])
    obtain ⟨i, hi, entry_ne⟩ : ∃ i ≠ 0, q.out.out i 0 ≠ 0 := by
      simpa [H, mem_residueLineStabilizer] using not_mem
    rw [firstEntry_conj_diagGL (g_pow _) _ entry_ne, Pi.mulSingle_eq_of_ne hi]

/-- A character `τ` of `GL n F` with values in `Fˣ`, for a finite field `F`, is trivial on
transvections: `τ` sends the image of each transvection `t` to `1`. -/
lemma map_toGL_transvection_eq_one {n : Type*} [Fintype n] [DecidableEq n] (τ : GL n F →* Fˣ)
    (t : TransvectionStruct n F) : τ (toGL t.toSpecialLinearGroup) = 1 := by
  -- `c ↦ τ (transvection c)` is a homomorphism from a group of order `q` to one of order `q - 1`.
  have : Fintype F := Fintype.ofFinite F
  let ψ : F →+ Additive Fˣ :=
    .mk' (fun c ↦ .ofMul (τ (toGL (transvection t.hij c)))) (by simp [transvection_add])
  have pow_card : τ (toGL t.toSpecialLinearGroup) ^ Fintype.card F = 1 :=
    congrArg Additive.toMul (show Fintype.card F • ψ t.c = 0 by
      rw [← map_nsmul, card_nsmul_eq_zero, map_zero])
  exact Units.ext (by rw [← FiniteField.pow_card (τ (toGL t.toSpecialLinearGroup) : F),
    ← Units.val_pow_eq_pow_val, pow_card])

/-- Let `F` be a finite field, and let `firstEntry` be the character `g ↦ g 0 0` of the stabiliser
in `GL_N(F)` of the line of the first basis vector. Its transfer to `GL_N(F)` takes the value `x` at
the diagonal matrix with `x` in place `i` and `1` elsewhere. -/
lemma transfer_firstEntry_diagGL_mulSingle (i : Fin N) (x : Fˣ) :
    (firstEntry (F := F) (N := N)).transfer (diagGL (Pi.mulSingle i x)) = x := by
  -- Conjugate by the permutation matrix `s` of the transposition of `0` and `i`.
  set τ : GL (Fin N) F →* Fˣ := (firstEntry (F := F) (N := N)).transfer
  let s : GL (Fin N) F := permGL (.swap 0 i)
  have conj : diagGL (Pi.mulSingle i x) * s = s * diagGL (Pi.mulSingle 0 x) := by
    rw [diagGL_mul_permGL, Pi.mulSingle_comp_equiv, Equiv.symm_swap, Equiv.swap_apply_right]
  have τ_conj : τ (diagGL (Pi.mulSingle i x)) = τ (diagGL (Pi.mulSingle 0 x)) :=
    mul_right_cancel (b := τ s) (by rw [← map_mul, conj, map_mul, mul_comm])
  rw [τ_conj, transfer_firstEntry_diagGL]

/-- Let `F` be a finite field, and let `firstEntry` be the character `g ↦ g 0 0` of the stabiliser
in `GL_N(F)` of the line of the first basis vector, the scalar by which `g` acts on that line. Its
transfer to `GL_N(F)` is the determinant. -/
lemma transfer_firstEntry (g : GL (Fin N) F) :
    (firstEntry (F := F) (N := N)).transfer g = GeneralLinearGroup.det g := by
  -- Both sides are characters of `GL_N(F)`, and they agree on diagonal matrices and transvections.
  set τ : GL (Fin N) F →* Fˣ := (firstEntry (F := F) (N := N)).transfer
  have det_single (i : Fin N) (x : Fˣ) :
      GeneralLinearGroup.det (diagGL (Pi.mulSingle i x) : GL (Fin N) F) = x :=
    Units.ext (by simp [← Units.coe_prod])
  have τ_diag : τ.comp diagGL = GeneralLinearGroup.det.comp diagGL :=
    MonoidHom.pi_ext fun i x ↦
      (transfer_firstEntry_diagGL_mulSingle i x).trans (det_single i x).symm
  let P (M : Matrix (Fin N) (Fin N) F) : Prop :=
    ∃ g' : GL (Fin N) F, (g' : Matrix (Fin N) (Fin N) F) = M ∧ τ g' = GeneralLinearGroup.det g'
  suffices P g by simpa [P, Units.val_inj]
  refine diagonal_transvection_induction_of_det_ne_zero P _ g.det_ne_zero ?_ ?_ ?_
  · intro D hD
    have hD_ne (i : Fin N) : D i ≠ 0 := by simp_all [prod_ne_zero_iff]
    exact ⟨diagGL fun i ↦ Units.mk0 (D i) (hD_ne i), rfl, DFunLike.congr_fun τ_diag _⟩
  · exact fun t ↦ ⟨toGL t.toSpecialLinearGroup, rfl, by simp [map_toGL_transvection_eq_one]⟩
  · rintro _ _ - - ⟨g₁, rfl, h₁⟩ ⟨g₂, rfl, h₂⟩
    exact ⟨g₁ * g₂, rfl, by rw [map_mul, map_mul, h₁, h₂]⟩

/-- Let `F` be a finite field, `l` a homomorphism from `Fˣ` to a commutative group, and `firstEntry`
the character `g ↦ g 0 0` of the stabiliser in `GL_N(F)` of the line of the first basis vector. The
transfer of `l ∘ firstEntry` to `GL_N(F)` is `l ∘ det`. -/
lemma transfer_comp_firstEntry {A : Type*} [CommGroup A] (l : Fˣ →* A) :
    (l.comp (firstEntry (N := N))).transfer = l.comp GeneralLinearGroup.det := by
  -- The transfer is a product over the cosets, and `l` commutes with products.
  ext g
  rw [MonoidHom.comp_apply, ← transfer_firstEntry, MonoidHom.transfer_def _ default,
    MonoidHom.transfer_def _ default]
  simp [Subgroup.leftTransversals.diff, map_prod]

end FiniteField

section Residue

variable {E : Type} [Field E] [NumberField E] {w : FinPlace E}

open scoped Classical in
/-- The reduction of a unit of `O_w` as a unit of the residue field, and `1` for the other elements
of `E_w`. -/
noncomputable def residueUnit (x : LocField w) : (ResField w)ˣ :=
  if h : IsUnit (residueOrZero x) then h.unit else 1

/-- A unit `x` of the residue field `ResField w` that is the reduction of a local integer
`y : LocInt w` equals `residueUnit z`, where `z : LocField w` is `y` seen in `E_w`. -/
lemma eq_residueUnit {x : (ResField w)ˣ} {y : LocInt w} {z : LocField w}
    (hx : x = residue (LocInt w) y) (hy : (y : LocField w) = z) : x = residueUnit z := by
  have x_eq : (x : ResField w) = residueOrZero z := by rw [hx, ← hy, residueOrZero_coe]
  rw [residueUnit, dite_eq_left (by simp [← x_eq])]
  exact Units.ext x_eq

/-- The reduction of `g ∈ GL_N(O_w)` lies in a subgroup `H` if and only if `g` lies in the open
subgroup `residuePreimage P H hP`, for any property `P` that describes the preimage of `H`. -/
lemma reduceGL_mem_iff_mem_residuePreimage {N : ℕ} {P : GL (Fin N) (LocField w) → Prop}
    {H : Subgroup (GL (Fin N) (ResField w))}
    {hP : ∀ k : localIntGL (Fin N) w, reduceGL k ∈ H ↔ P k} {g : localIntGL (Fin N) w} :
    reduceGL g ∈ H ↔ (g : GL (Fin N) (LocField w)) ∈ residuePreimage P H hP :=
  (hP g).trans (and_iff_right g.property).symm

/-- The reduction of `g ∈ GL_N(O_w)` stabilises the line of the first basis vector if and only if
`g` lies in the parahoric subgroup with blocks of sizes `1` and `N - 1`. -/
lemma reduceGL_mem_residueLineStabilizer_iff {N : ℕ} [NeZero N] {g : localIntGL (Fin N) w} :
    reduceGL g ∈ residueLineStabilizer (ResField w) N ↔
      (g : GL (Fin N) (LocField w)) ∈ blockParahoric (min 1) := by
  unfold residueLineStabilizer blockParahoric
  exact reduceGL_mem_iff_mem_residuePreimage

/-- If the reduction of `g ∈ GL_N(O_w)` stabilises the line of the first basis vector, then its
first entry is the reduction of the first entry of `g`. -/
lemma firstEntry_reduceGL {N : ℕ} [NeZero N] {g : localIntGL (Fin N) w}
    (hg : reduceGL g ∈ residueLineStabilizer (ResField w) N) :
    firstEntry ⟨reduceGL g, hg⟩ = residueUnit ((g : GL (Fin N) (LocField w)) 0 0) :=
  eq_residueUnit rfl rfl

/-- The determinant of the reduction of `g ∈ GL_N(O_w)` is the reduction `residueUnit` of the
determinant of `g`, a unit of `O_w`. -/
lemma det_reduceGL {N : ℕ} (g : localIntGL (Fin N) w) :
    GeneralLinearGroup.det (reduceGL g) =
      residueUnit (g : GL (Fin N) (LocField w)).val.det :=
  eq_residueUnit (RingHom.map_det ..).symm (𝒪[LocField w].subtype.map_det _)

/-- If `g ∈ GL_N(O_w)` lies in the pro-`p` Iwahori subgroup (its reduction is upper triangular with
ones on the diagonal), then the reduction has determinant `1` and first entry `1`. -/
lemma det_firstEntry_reduceGL_eq_one_of_mem_proIwahori {N : ℕ} [NeZero N] {g : localIntGL (Fin N) w}
    (hg : (g : GL (Fin N) (LocField w)) ∈ proIwahori) :
    GeneralLinearGroup.det (reduceGL g) = 1 ∧
      ∀ h_mem : reduceGL g ∈ residueLineStabilizer (ResField w) N,
        firstEntry ⟨reduceGL g, h_mem⟩ = 1 := by
  have entries : ∀ i j : Fin N, j ≤ i →
      reduceGL g i j = (1 : Matrix (Fin N) (Fin N) (ResField w)) i j :=
    (reduceGL_mem_iff_mem_residuePreimage.2 hg : reduceGL g ∈ unitriangular id (ResField w))
  exact ⟨Units.ext (det_eq_one_of_unitriangular entries),
    fun _ ↦ Units.ext ((entries 0 0 le_rfl).trans (one_apply_eq 0))⟩

/-- Let `q = w.q` be the order of the residue field at `w`, let `m ∣ q - 1`, and let `z` generate
the residue units. There is a logarithm modulo `m` to the base `z`: a homomorphism from the residue
units to `ℤ/m` that sends `z` to `1`. -/
lemma exists_residue_log {m : ℕ} (hm : m ∣ w.q - 1) {z : (ResField w)ˣ}
    (hz : ∀ x : (ResField w)ˣ, x ∈ Subgroup.zpowers z) :
    ∃ ind : (ResField w)ˣ →* Multiplicative (ZMod m), ind z = .ofAdd 1 := by
  have order_z : orderOf z = w.q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hz, Nat.card_units, card_ResField]
  have order_dvd : orderOf (Multiplicative.ofAdd (1 : ZMod m)) ∣ orderOf z := by
    rwa [order_z, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  exact ⟨monoidHomOfForallMemZpowers hz order_dvd,
    monoidHomOfForallMemZpowers_apply_gen hz order_dvd⟩

end Residue

end New.Patching

end LineStabiliserLog

/-!
## Logarithms
-/

section Logarithms

open Finset Subgroup IsComplement MulAction leftTransversals ZMod

namespace New.Patching

variable {Γ R S : Type*} [Group Γ] [Fintype Γ] [Ring R] [Ring S]

/-- If `m = 0` in `S`, then only the weights modulo `m` matter: an additive map `B` on integer
weights takes weights that are congruent modulo `m` to elements with the same image under `σ`. -/
lemma map_eq_of_weights_modEq {m : ℕ} {σ : R →+* S} (hm : (m : S) = 0) {ι : Type*}
    (B : (ι → ℤ) →+ R) (f g : ι → ℤ) (h_congr : ∀ x : ι, (g x : ZMod m) = f x) :
    σ (B f) = σ (B g) := by
  choose d hd using fun x ↦ (intCast_eq_intCast_iff_dvd_sub (g x) (f x) m).1 (h_congr x)
  have h_sub : f = m • d + g := funext fun x ↦ by simp [← hd x]
  rw [h_sub, map_add, map_add, map_nsmul, map_nsmul, nsmul_eq_mul, hm, zero_mul, zero_add]

variable {m : ℕ} (ρ : Γ →* R) {σ : R →+* S}

/-- The weighted norm `∑ f (c g) ρ g` for a homomorphism `c : Γ → ℤ/m`, as an additive function of
the weight `f : ℤ/m → ℤ`. The weight `1` gives the norm; the weight `valMinAbs`, which lifts
`ℤ/m` to `ℤ`, gives the logarithm of `c`. -/
def weightedSum (c : Γ →* Multiplicative (ZMod m)) : (ZMod m → ℤ) →+ R :=
  .mk' (fun f ↦ ∑ g : Γ, f (c g).toAdd • ρ g) (by simp [add_smul, sum_add_distrib])

lemma weightedSum_apply (c : Γ →* Multiplicative (ZMod m)) (f : ZMod m → ℤ) :
    weightedSum ρ c f = ∑ g : Γ, f (c g).toAdd • ρ g := rfl

lemma weightedSum_one (c : Γ →* Multiplicative (ZMod m)) : weightedSum ρ c 1 = ∑ g : Γ, ρ g := by
  simp [weightedSum_apply]

/-- Left multiplication by `ρ g` shifts the weight of the weighted norm `∑ f (c h) ρ h` by
`c g`. -/
lemma mul_weightedSum (c : Γ →* Multiplicative (ZMod m)) (f : ZMod m → ℤ) (g : Γ) :
    ρ g * weightedSum ρ c f = weightedSum ρ c (fun x : ZMod m ↦ f (x - (c g).toAdd)) := by
  have shift (h : Γ) :
      ρ g * f (c h).toAdd • ρ h = f ((c (g * h)).toAdd - (c g).toAdd) • ρ (g * h) := by
    rw [map_mul c, map_mul ρ, toAdd_mul, add_sub_cancel_left, mul_smul_comm]
  rw [weightedSum_apply, weightedSum_apply, mul_sum]
  exact Fintype.sum_equiv (.mulLeft g) _ _ shift

/-- Right multiplication by `ρ g` shifts the weight of the weighted norm `∑ f (c h) ρ h` by
`c g`. -/
lemma weightedSum_mul (c : Γ →* Multiplicative (ZMod m)) (f : ZMod m → ℤ) (g : Γ) :
    weightedSum ρ c f * ρ g = weightedSum ρ c (fun x : ZMod m ↦ f (x - (c g).toAdd)) := by
  have shift (h : Γ) :
      f (c h).toAdd • ρ h * ρ g = f ((c (h * g)).toAdd - (c g).toAdd) • ρ (h * g) := by
    rw [map_mul c, map_mul ρ, toAdd_mul, add_sub_cancel_right, smul_mul_assoc]
  rw [weightedSum_apply, weightedSum_apply, sum_mul]
  exact Fintype.sum_equiv (.mulRight g) _ _ shift

open scoped Classical in
/-- The sum `∑ ρ h` over the fixed representatives `h` of `Γ / H`, namely the elements `η.out` that
`Quotient.out` chooses in the cosets `η`. -/
noncomputable def cosetNorm (H : Subgroup Γ) : R := ∑ η : Γ ⧸ H, ρ η.out

open scoped Classical in
/-- The sum `∑ ρ h⁻¹` over the fixed representatives `h` of `Γ / H`. A sum `∑ f p ρ p` over `H`,
times this sum, is the sum over `Γ` in which `ρ (p h⁻¹)` has the weight `f p`. -/
noncomputable def cosetNormInv (H : Subgroup Γ) : R := ∑ η : Γ ⧸ H, ρ η.out⁻¹

/-- The derivative `∂ = -(∑ ρ h) B(valMinAbs) (∑ ρ h⁻¹)` attached to an additive map `B` on weights
`ℤ/m → ℤ`, where `h` runs over the fixed representatives of `Γ / H`. For the weighted norm `B` of a
homomorphism `a : H → ℤ/m`, the middle factor is the logarithm of `a`. -/
noncomputable def cosetDerivative (H : Subgroup Γ) (B : (ZMod m → ℤ) →+ R) : R :=
  -(cosetNorm ρ H * B valMinAbs * cosetNormInv ρ H)

/-- The element `p ∈ H` with `g x = h p`, where `h` is the fixed representative of the coset
`g x H`. -/
noncomputable def cosetComponent (H : Subgroup Γ) (g x : Γ) : H :=
  ⟨(g • x : Γ ⧸ H).out⁻¹ * (g * x), QuotientGroup.eq.1 (g • x : Γ ⧸ H).out_eq⟩

variable {H : Subgroup Γ} [Fintype H]

/-- Let `ρ` be a multiplicative map from a finite group `Γ` to a ring `R`, let `H` be a subgroup,
and let `h` run over the representatives `η.out` that `Quotient.out` chooses for the cosets
`η ∈ Γ / H`, so that `cosetNorm ρ H = ∑ ρ h`. For a weight `f : H → ℤ` and `x ∈ Γ`, the product
`(∑ ρ h) (∑_{p ∈ H} f p ρ p) ρ x⁻¹` is the sum over `g ∈ Γ` of `f p ρ g` with
`p = cosetComponent H g x`, the element of `H` in the unique factorisation `g = h p x⁻¹`. -/
lemma cosetNorm_mul_sum_mul (f : H → ℤ) (x : Γ) :
    cosetNorm ρ H * (∑ p : H, f p • ρ p) * ρ x⁻¹ = ∑ g : Γ, f (cosetComponent H g x) • ρ g := by
  have component_eq (η : Γ ⧸ H) (p : H) : cosetComponent H (η.out * p * x⁻¹) x = p := by
    simp [cosetComponent]
  rw [cosetNorm, sum_mul_sum, ← sum_product', sum_mul]
  refine sum_nbij' (fun (η, p) ↦ η.out * p * x⁻¹) (fun g ↦ (↑(g * x), cosetComponent H g x))
    (by simp) (by simp) (by simp [component_eq]) (by simp [cosetComponent]) ?_
  rintro ⟨η, p⟩ -
  simp only [component_eq, map_mul, mul_smul_comm, smul_mul_assoc]

lemma cosetNorm_mul_norm : cosetNorm ρ H * ∑ p : H, ρ p = ∑ g : Γ, ρ g := by
  simpa using cosetNorm_mul_sum_mul ρ (H := H) 1 1

omit [Fintype H] in
open scoped Classical in
/-- The transfer of `a : H → A` at `g` is the product, over the fixed representatives `h` of
`Γ / H`, of the values of `a` at the components `p ∈ H` of `g h = h' p`. -/
lemma transfer_eq_prod_cosetComponent {A : Type*} [CommGroup A] (a : H →* A) (g : Γ) :
    a.transfer g = ∏ η : Γ ⧸ H, a (cosetComponent H g η.out) := by
  have default_apply (η : Γ ⧸ H) :
      ((default : H.LeftTransversal).property.leftQuotientEquiv η : Γ) = η.out :=
    leftQuotientEquiv_apply Quotient.out_eq η
  -- Compute the transfer with the transversals `g⁻¹ • default` and `default`.
  rw [a.transfer_def (g⁻¹ • default), diff]
  -- The factor at `η` comes from the representatives `(g • η).out` and `g * η.out` of `g • η`.
  congr! 3 with η
  simp [cosetComponent, smul_apply_eq_smul_apply_inv_smul, default_apply, mul_assoc]

/-- Let `ρ` map the finite group `Γ` to the ring `R`, and let `σ : R → S` be a ring map with `m = 0`
in `S`. For a homomorphism `c` to `ℤ/m` let `L c = ∑ valMinAbs (c g) ρ g` be its logarithm, the
`weightedSum` for the lift `valMinAbs : ℤ/m → ℤ`. For `a : H → ℤ/m` on a subgroup `H`, the elements
`(∑ ρ h) (L a) (∑ ρ h⁻¹)` and `L a.transfer` have the same image under `σ`, where `h` runs over the
fixed representatives of `Γ / H` and `a.transfer` is the transfer of `a` from `H` to `Γ`. -/
lemma map_cosetNorm_mul_weightedSum_mul_cosetNormInv (hm : (m : S) = 0)
    (a : H →* Multiplicative (ZMod m)) :
    σ (cosetNorm ρ H * weightedSum (ρ.comp H.subtype) a valMinAbs * cosetNormInv ρ H) =
      σ (weightedSum ρ a.transfer valMinAbs) := by
  classical
  -- The coefficient of `g` on the left is the sum over the representatives `h` of the logarithms of
  -- the components of `g h`, which is congruent modulo `m` to the logarithm of the transfer.
  let C : (Γ → ℤ) →+ R := (Fintype.linearCombination ℤ ρ).toAddMonoidHom
  let weight (η : Γ ⧸ H) (g : Γ) : ℤ := valMinAbs (a (cosetComponent H g η.out)).toAdd
  have h_term (η : Γ ⧸ H) :
      cosetNorm ρ H * weightedSum (ρ.comp H.subtype) a valMinAbs * ρ η.out⁻¹ = C (weight η) :=
    cosetNorm_mul_sum_mul ρ (fun p ↦ valMinAbs (a p).toAdd) η.out
  have h_weights (g : Γ) :
      (valMinAbs (a.transfer g).toAdd : ZMod m) = (∑ η : Γ ⧸ H, weight η) g := by
    simp [weight, transfer_eq_prod_cosetComponent, toAdd_prod]
  calc σ (cosetNorm ρ H * weightedSum (ρ.comp H.subtype) a valMinAbs * cosetNormInv ρ H)
      = σ (C (∑ η : Γ ⧸ H, weight η)) := by
        simp only [cosetNormInv, map_sum C, mul_sum, h_term]
    _ = σ (weightedSum ρ a.transfer valMinAbs) := map_eq_of_weights_modEq hm C _ _ h_weights

/-- Let `ρ` map the finite group `Γ` to the ring `R`, and let `σ : R → S` be a ring map with `m = 0`
in `S`. Let `L = ∑ valMinAbs (c g) ρ g` be the logarithm of a homomorphism `c : Γ → ℤ/m` that sends
`γ` to the generator `1`. Then `(ρ γ - 1) L` and `-∑ ρ g` have the same image under `σ`. -/
lemma map_sub_one_mul_weightedSum_valMinAbs (hm : (m : S) = 0) (c : Γ →* Multiplicative (ZMod m))
    {γ : Γ} (hγ : c γ = .ofAdd 1) :
    σ ((ρ γ - 1) * weightedSum ρ c valMinAbs) = -σ (∑ g : Γ, ρ g) := by
  calc σ ((ρ γ - 1) * weightedSum ρ c valMinAbs)
      = σ (weightedSum ρ c ((fun x : ZMod m ↦ valMinAbs (x - 1)) - valMinAbs)) := by
        rw [sub_one_mul, mul_weightedSum, ← map_sub, hγ, toAdd_ofAdd]
    _ = σ (weightedSum ρ c (-1)) := map_eq_of_weights_modEq hm _ _ _ (by simp)
    _ = -σ (∑ g : Γ, ρ g) := by rw [map_neg, map_neg, weightedSum_one]

omit [Fintype H] in
/-- Let `ρ` map the finite group `Γ` to the ring `R`, and let `σ : R → S` be a ring map with `m = 0`
in `S`. Let `a : H → ℤ/m` be a homomorphism on a subgroup `H`. Let `B` be an additive map on weights
`ℤ/m → ℤ` such that right multiplication by `ρ p` shifts the weight by `a p`, as for the weighted
norm over `H` or a fixed left multiple of it. Then `B valMinAbs * (∑ ρ h⁻¹) * (ρ g - 1)` has the
same image under `σ` as a right multiple `B 1 * Q` of the value of `B` at the constant weight `1`.
Here `valMinAbs` is the weight sending `x` to its representative in `ℤ` of least absolute value, and
`h` runs over the fixed representatives of `Γ / H`. -/
lemma exists_map_valMinAbs_mul_sub_one (hm : (m : S) = 0) (a : H →* Multiplicative (ZMod m))
    (B : (ZMod m → ℤ) →+ R)
    (hB : ∀ (f : ZMod m → ℤ) (p : H), B f * ρ p = B fun x : ZMod m ↦ f (x - (a p).toAdd)) (g : Γ) :
    ∃ Q : R, σ (B valMinAbs * cosetNormInv ρ H * (ρ g - 1)) = σ (B 1 * Q) := by
  classical
  -- Right multiplication by `g` permutes the `h⁻¹` up to factors in `H`, which shift the weight
  -- by a constant.
  let k (η : Γ ⧸ H) : ZMod m := (a (cosetComponent H g η.out)).toAdd
  have permute : cosetNormInv ρ H * ρ g =
      ∑ η : Γ ⧸ H, ρ (cosetComponent H g η.out) * ρ η.out⁻¹ := by
    have term_eq (η : Γ ⧸ H) :
        ρ (cosetComponent H g η.out) * ρ η.out⁻¹ = ρ (toPerm g η).out⁻¹ * ρ g := by
      simp [cosetComponent, mul_assoc, ← map_mul]
    rw [cosetNormInv, sum_mul]
    exact (Fintype.sum_equiv (toPerm g) _ _ term_eq).symm
  have shift (y : ZMod m) :
      σ (B fun x ↦ valMinAbs (x - y)) = σ (B valMinAbs - valMinAbs y • B 1) := by
    rw [← map_zsmul, ← map_sub]
    exact map_eq_of_weights_modEq hm B _ _ (by simp)
  have term_congr (η : Γ ⧸ H) :
      σ (B valMinAbs * (ρ (cosetComponent H g η.out) * ρ η.out⁻¹ - ρ η.out⁻¹)) =
        σ (B 1 * -(valMinAbs (k η) • ρ η.out⁻¹)) :=
    calc σ (B valMinAbs * (ρ (cosetComponent H g η.out) * ρ η.out⁻¹ - ρ η.out⁻¹))
        = (σ (B fun x ↦ valMinAbs (x - k η)) - σ (B valMinAbs)) * σ (ρ η.out⁻¹) := by
          rw [mul_sub, ← mul_assoc, hB, ← sub_mul, map_mul, map_sub]
      _ = σ (-(valMinAbs (k η) • B 1) * ρ η.out⁻¹) := by
          rw [shift, ← map_sub, sub_sub_cancel_left, map_mul]
      _ = σ (B 1 * -(valMinAbs (k η) • ρ η.out⁻¹)) := by
          rw [neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
  refine ⟨∑ η : Γ ⧸ H, -(valMinAbs (k η) • ρ η.out⁻¹), ?_⟩
  rw [mul_assoc, mul_sub_one, permute, cosetNormInv, ← sum_sub_distrib, mul_sum, mul_sum,
    map_sum, map_sum]
  exact sum_congr rfl fun η _ ↦ term_congr η

/-- Let `σ` be a reduction modulo `m / (2 k)`, that is, let it kill every `x` with `2 k x ∈ m R`.
If an additive map `C` on weights `ℤ/m → ℤ` kills every `f (· - k) - f`, then `σ` kills its value
at the weight `valMinAbs`. -/
lemma map_valMinAbs_eq_zero_of_shift {k : ℕ} (hσ : IsReductionMod σ m (2 * k))
    (C : (ZMod m → ℤ) →+ R) (hC : ∀ f : ZMod m → ℤ, C ((fun x : ZMod m ↦ f (x - k)) - f) = 0) :
    σ (C valMinAbs) = 0 := by
  -- For `f x = x (x + k)` we have `f (x - k) - f x ≡ -2 k x` modulo `m`.
  let f (x : ZMod m) : ℤ := valMinAbs x * (valMinAbs x + k)
  have f_dvd (x : ZMod m) : ∃ d : ℤ, f (x - k) - f x + 2 * k * valMinAbs x = m * d :=
    (intCast_zmod_eq_zero_iff_dvd _ m).1 (by push_cast [f, coe_valMinAbs]; ring)
  choose d hd using f_dvd
  have f_diff : (fun x ↦ f (x - k)) - f + (2 * k) • valMinAbs = m • d :=
    funext fun x ↦ by simpa using hd x
  refine hσ (C valMinAbs) (C d) ?_
  rw [← map_nsmul, ← map_nsmul, ← f_diff, map_add, hC, zero_add]

/-- Let `ρ` map the finite group `Γ` to the ring `R`, and let `σ : R → S` be a ring map with `m = 0`
in `S`. Let `a : H → ℤ/m` be a homomorphism on a subgroup `H`, let `B` be an additive map on weights
`ℤ/m → ℤ` such that right multiplication by `p ∈ H` shifts the weight by `a p`, and let
`∂ = cosetDerivative ρ H B` be `-(∑ h) B(valMinAbs) (∑ h⁻¹)`, with `h` running over the fixed
representatives of `Γ / H`. Let `H` fix `B 1` from the left, let `∑ p⁻¹ Ψ p = n` over `H`, and let
`L g = L` for all `g` and `L (B 1) = 0`. If `R` has no `#H`-torsion, then `n ∂ (g - 1) ≡ Nm Z` for
some `Z` with `L Z = 0`. -/
lemma exists_map_nsmul_mul_sub_one_eq_sum_mul (hm : (m : S) = 0) (a : H →* Multiplicative (ZMod m))
    (B : (ZMod m → ℤ) →+ R)
    (hB : ∀ (f : ZMod m → ℤ) (p : H), B f * ρ p = B fun x : ZMod m ↦ f (x - (a p).toAdd))
    (hB_fixed : ∀ p : H, ρ p * B 1 = B 1) {Ψ L : R} {n : ℕ}
    (hΨ : ∑ p : H, ρ ↑p⁻¹ * Ψ * ρ p = n) (hL : ∀ g : Γ, L * ρ g = L) (hLB : L * B 1 = 0)
    (h_regular : IsSMulRegular R (Fintype.card H)) (g : Γ) :
    ∃ Z : R,
      σ (n • (cosetDerivative ρ H B * (ρ g - 1))) = σ ((∑ k : Γ, ρ k) * Z) ∧
      L * Z = 0 := by
  obtain ⟨Q, hQ⟩ : ∃ Q : R, σ (B valMinAbs * cosetNormInv ρ H * (ρ g - 1)) = σ (B 1 * Q) :=
    exists_map_valMinAbs_mul_sub_one ρ hm a B hB g
  have nsmul_B_one : n • B 1 = (∑ p : H, ρ p) * Ψ * B 1 :=
    nsmul_eq_norm_mul (ρ.comp H.subtype) hΨ hB_fixed
  refine ⟨-(Ψ * B 1 * Q), ?_, ?_⟩
  · calc σ (n • (cosetDerivative ρ H B * (ρ g - 1)))
        = -(σ (cosetNorm ρ H) * n • σ (B valMinAbs * cosetNormInv ρ H * (ρ g - 1))) := by
          simp only [cosetDerivative, neg_mul, smul_neg, map_neg, map_nsmul, map_mul,
            mul_smul_comm, mul_assoc]
      _ = σ (-(cosetNorm ρ H * (n • B 1 * Q))) := by
          simp only [hQ, map_neg, map_nsmul, map_mul, smul_mul_assoc]
      _ = σ ((∑ g, ρ g) * -(Ψ * B 1 * Q)) := by
          simp only [nsmul_B_one, ← cosetNorm_mul_norm ρ (H := H), mul_neg, mul_assoc]
  · have L_mul_eq_zero : L * (Ψ * B 1) = 0 := h_regular.right_eq_zero_of_smul <|
      calc Fintype.card H • (L * (Ψ * B 1)) = L * ((∑ p : H, ρ p) * Ψ * B 1) := by
            simp only [sum_mul, mul_sum, ← mul_assoc, hL, sum_const, card_univ]
        _ = 0 := by rw [← nsmul_B_one, mul_smul_comm, hLB, smul_zero]
    rw [mul_neg, ← mul_assoc, L_mul_eq_zero, zero_mul, neg_zero]

end New.Patching

end Logarithms
