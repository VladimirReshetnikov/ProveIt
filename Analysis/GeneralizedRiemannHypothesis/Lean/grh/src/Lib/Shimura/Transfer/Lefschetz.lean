import Lib.General.Combinatorics
import Lib.Shimura.HeckeTower.Model
import Lib.Shimura.Transfer.MarkedPairs

/-!
# h-null Hecke elements and the Lefschetz formula as a sum over marked pairs

Translates the geometric vanishing of local terms on a tower of Kuga–Sato varieties into a vanishing
of a sum over marked pairs, which involves only the Hecke function.

* `New.Variety.IsNullHecke`: h-nullity of a Hecke element, a condition on regular elements.
* `New.Variety.OccursInWeight`: a system of eigenvalues θ occurs in weight h.
* `New.Variety.Model.isNullHecke_of_isNullFamily`: h-null on deep levels of the tower implies
  h-null.

Idea: coincidences of two maps to the base are grouped by their marked pair; each fibre has (number
of lattice solutions) · (order of the deck group) points, and the number of solutions cancels the
denominator of the local term.

Notions from other files:
* `New.Variety.GUPlus`: the monoid of similitudes `g` whose inverse has integral entries, that is,
  which enlarge the standard lattice.
* `New.Variety.heckeAlgebra`: the Hecke algebra, the subalgebra of elements ∑ a_g [g] of k[G]
  supported on `GUPlus E n` whose function ∑ a_g 1_{g·levelGU n 𝔑} is left `levelGU n 𝔑`-invariant.
* `New.Variety.levelGU`: the principal level K(𝔑), the similitudes in `GL_n(Ô E)` that are congruent
  to `1` modulo `𝔑`.
* `New.Variety.Model`: the tower of Kuga–Sato varieties over `R`, given by a list of properties.
* `New.Variety.IsNeat`: the level 𝔑 is neat: 𝔑 ≠ 0 and, whenever `x` is a signed frame with `ℓ` for
  some form (`New.Variety.IsSignedFrame`), every y in GL_n(E) with x⁻¹yx in `levelGU n 𝔑` that fixes
  ℓ under `New.Variety.ratConj` equals 1.

## Relation to the literature

Known; see `Lib.Shimura.Transfer.WeightOccurs` for sources.
-/

namespace New.Variety

open NumberField Matrix CategoryTheory Polynomial LinearMap Finset Nat ModuliPoint QuotientAddGroup

variable {E : Type} [Field E] [CMBase E] {d₀ : ℕ}
  {n : Type} [Fintype n] [DecidableEq n] [HasQuadSubfield d₀ E]
  {𝔑 : 𝓞 E} {ν : ℕ} {R : Subalgebra (𝓞 E) E} (X : Model n d₀ 𝔑 ν R)

/-- `b` is `h`-null; the condition is void if `b` is not regular. For every `α : Fin ν → 𝓞 E`:
finitely many classes of marked triples (flag `True` of `New.Variety.countTerm`) have a non-zero
term with weight 1 (this part does not depend on `α`), and the sum over the classes of the value of
`b` times the coefficient of `X ^ h` in the local term `New.Variety.localTerm` at `2 α` is 0. Only
even multipliers `2 α` are used: for them the determinant of `1 - 2 α y` on the lattice is odd,
hence non-zero. -/
def IsNullHecke (ν h : ℕ) (b : heckeAlgebra n ℂ 𝔑) : Prop :=
  IsRegularHecke b →
  ∀ α : Fin ν → 𝓞 E,
    (countTerm True b 1).support.Finite ∧
    ∑ᶠ x, countTerm True b (fun P μ ↦ (localTerm (2 * α) P μ).coeff h) x = 0

/-- θ occurs in weight h: for every linear combination p of words in the operators `tauHecke` with
p(θ) = 1, some b·p with b in the Hecke algebra is not `h`-null in the sense of
`New.Variety.IsNullHecke`. -/
def OccursInWeight (a ν : ℕ) (θ : SafePlace 𝔑 → ℕ → ℂ) (h : ℕ) : Prop :=
  ∀ (s : Finset (List (SafePlace 𝔑 × ℕ))) (c : List (SafePlace 𝔑 × ℕ) → ℂ),
    ∑ L ∈ s, c L * (L.map ↿θ).prod = 1 →
    ¬∀ b : heckeAlgebra (Fin a) ℂ 𝔑, IsNullHecke ν h (b * ∑ L ∈ s, c L • (L.map tauHecke).prod)

private lemma realVecAction_eq_toLin' (B : Matrix n n E) :
    realVecAction B = Matrix.toLin' (B.map cmEmbedding) :=
  rfl

/-- Let the rational matrix `z` be integral in the frame `x`, and let `β` be an integer of `E`. Then
`B = 1 - 2 β z` maps the lattice `frameLattice x` into itself, `det B ≠ 0`, and the index of the
lattice in its preimage under `B` is the product of the `σ (det B)` over the complex embeddings
`σ`. -/
lemma relIndex_comap_one_sub_two_smul {x : GL n (𝔸f E)} {z B : Matrix n n E}
    (hz : ∀ i k : n, (x⁻¹.val * z.map (algebraMap E (𝔸f E)) * x.val :) i k ∈ Ô E) (β : 𝓞 E)
    (hB : B = 1 - ((2 * β : 𝓞 E) : E) • z) :
    frameLattice x ≤ (frameLattice x).comap (realVecAction B).toAddMonoidHom ∧
    B.det ≠ 0 ∧
    (frameLattice x).relIndex ((frameLattice x).comap (realVecAction B).toAddMonoidHom) =
      ∏ σ : E →+* ℂ, σ B.det := by
  -- On the lattice `Λ`, `B` acts as `1 - 2 A` with `A` integral, so its real determinant is an odd
  -- integer; its complex determinant is `∏ v, Φ v (det B)`, and the index is the norm of that.
  let Λ : Submodule ℤ (RealVectors E n) := classLattice x ⊥ (.refl ℝ (RealVectors E n))
  let c : Module.Basis (Fin (Module.finrank ℤ ↥Λ)) ℤ ↥Λ := Module.finBasis ℤ Λ
  let F : (n → InfinitePlace E → ℂ) →ₗ[ℂ] n → InfinitePlace E → ℂ :=
    (realVecAction B).restrictScalars ℂ
  -- `β z` is integral in the frame `x`, so it acts on the lattice by a `ℤ`-linear map `A`.
  have hβz (i k : n) :
      (x⁻¹.val * ((β : E) • z).map (algebraMap E (𝔸f E)) * x.val :) i k ∈ Ô E := by
    -- `-algebraMap_smul` keeps `β` a scalar of `E`, where `map_smul'` pulls it out of the map.
    simpa [-algebraMap_smul, map_smul'] using mul_mem (coe_mem_Ô β) (hz i k)
  let A : Λ →ₗ[ℤ] Λ :=
    ((realVecAction ((β : E) • z)).restrictScalars ℤ).restrict fun _ ↦
      realVecAction_mem_frameLattice hβz
  let G : Λ →ₗ[ℤ] Λ := 1 + -2 • A
  have hFG (y : Λ) : F y.val = G y := by
    simp +zetaDelta [hB, mul_smul, map_ofNat, Matrix.map_sub, map_smul', sub_mulVec, smul_mulVec]
    -- What is left is `y - 2 • (β z y) = y + -(2 * (β z y))`.
    rw [sub_eq_add_neg, two_smul, two_mul]
  have h_maps (y : RealVectors E n) (hy : y ∈ Λ) : F y ∈ Λ := by
    simpa only [hFG ⟨y, hy⟩] using (G ⟨y, hy⟩).prop
  -- The real determinant of `F` is the integer `det (1 - 2 A)`, which is odd.
  have h_real : (F.restrictScalars ℝ).det = (G.toMatrix c c).det := by
    simp [det_apply', hFG, ← det_toMatrix (c.ofZLatticeBasis ℝ), toMatrix_apply]
  have h_ne : (F.restrictScalars ℝ).det ≠ 0 := by
    rw [h_real, Int.cast_ne_zero, map_add, toMatrix_one, map_smul, det_one_add_smul]
    omega
  -- The complex determinant is the product of the `Φ v (det B)` over the infinite places.
  have h_det : F.det = ∏ v : InfinitePlace E, Φ v B.det := by
    rw [det_restrictScalars, realVecAction_eq_toLin', det_toLin', ← RingHom.mapMatrix_apply,
      ← cmEmbedding.map_det]
    -- The norm on `InfinitePlace E → ℂ` is the determinant of multiplication in each coordinate.
    change LinearMap.det (LinearMap.pi fun v ↦ mul ℂ ℂ (Φ v B.det) ∘ₗ LinearMap.proj v) = _
    rw [det_pi]
    simp
  refine ⟨h_maps, fun h0 ↦ h_ne ?_, ?_⟩
  · simp [det_restrictScalars, h_det, h0]
  · -- The index is `det F * conj (det F)`; the embeddings pair off as `Φ v` and its conjugate.
    refine (relIndex_comap_eq_det_mul_conj_det h_maps (equivOfDetNeZero _ h_ne).injective).trans ?_
    simp [h_det, prod_embeddings_eq_prod_pairs, prod_mul_distrib]

/-- The class under `GL n E` of the marked triple `(x · levelGU n 𝔑, t)`: the coset of `x` and the
pair `t`. -/
noncomputable abbrev tripleClass (𝔑 : 𝓞 E) (x : GL n (𝔸f E)) (t : GL n E × n) :
    MulAction.orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n) :=
  ⟦((x : GL n (𝔸f E) ⧸ levelGU n 𝔑), t)⟧

/-- Let the reflections of `p` and `p'` be those of the marked elements `t` and `t'`. The triples of
`(p.frame, t)` and `(p'.frame, t')` have the same class if and only if some `w` conjugates `t'` to
`t` and is an isomorphism from `p'` to `p`, once the vectors of `p` are replaced by the `w P'_j`. -/
lemma triple_class_eq_iff {p p' : ModuliPoint E n ν} {t t' : GL n E × n}
    (ht : p.reflection = eigenReflection True t.fst t.snd)
    (ht' : p'.reflection = eigenReflection True t'.fst t'.snd) :
    tripleClass 𝔑 p.frame t = tripleClass 𝔑 p'.frame t' ↔
      ∃ w : GL n E,
        (w * t'.fst * w⁻¹, t'.snd) = t ∧
        p'.IsLevelIso (levelGU n 𝔑) w {p with markedPoint j := realVecAction w (p'.markedPoint
          j)} := by
  refine Quotient.eq.trans (exists_congr fun w ↦ Prod.ext_iff.trans ?_)
  change (⟦toFinGL w * p'.frame⟧ : _ ⧸ levelGU _ 𝔑) = ⟦p.frame⟧ ∧ (w * t'.fst * w⁻¹, t'.snd) = t ↔ _
  refine and_comm.trans (and_congr_right fun e ↦ (eq_comm.trans QuotientGroup.eq).trans ?_)
  -- The condition on the reflections follows from `e`; the one on the vectors is trivial.
  simp [ht', ht, ← e, mul_assoc, isLevelIso_iff, ratConj_eigenReflection]

/-- At a neat level, let the vectors of `p` run through representatives `u` of the groups `L j`
modulo the lattice of `p.frame`, and let `δ` run through the deck group. The points so obtained on
level `i` are distinct. -/
lemma Model.point_comp_deck_injective [Nonempty n] (h_neat : IsNeat n 𝔑)
    (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n)) (p : ModuliPoint E n ν)
    (L : Fin ν → AddSubgroup (RealVectors E n)) :
    Function.Injective fun u : (∀ j : Fin ν, L j ⧸ (frameLattice p.frame).addSubgroupOf (L j)) ×
      X.deckGroup i ↦
      X.point i {p with markedPoint j := (u.fst j).out} ≫ (X.deck i u.snd).asHom := by
  rintro ⟨u, δ⟩ ⟨v, ε⟩ e
  -- Both points have the same image in the base, so they are isomorphic by some `w`, and `w = 1`
  -- by neatness.
  have h_base : X.point i {p with markedPoint j := (u j).out} ≫ X.leg i ⟦1⟧ =
      X.point i {p with markedPoint j := (v j).out} ≫ X.leg i ⟦1⟧ := by
    simpa only [Category.assoc, (X.covering i).comp_eq] using congrArg (· ≫ X.leg i ⟦1⟧) e
  obtain ⟨w, hw⟩ := (X.point_eq_iff i _ _).mp h_base
  obtain rfl : w = 1 := h_neat.eq_one_of_mem_levelGU p.isSignedFrame hw.mem_level hw.reflection_eq
  obtain rfl : u = v := by
    funext j
    have h_diff : ((u j).out - (v j).out).val ∈ frameLattice p.frame := by
      simpa using hw.sub_mem_lattice j
    exact Quotient.out_equiv_out.mp (Quotient.exact (eq_iff_sub_mem.mpr h_diff))
  -- The deck group acts freely.
  let y : specOver R ℂ ⟶ X.cover i := X.point i {p with markedPoint j := (u j).out}
  have h_deck : y ≫ X.leg i ⟦1⟧ = (y ≫ (X.deck i ε).asHom) ≫ X.leg i ⟦1⟧ := by
    rw [Category.assoc, (X.covering i).comp_eq]
  -- `δ` and `ε` move `y` to the same point over the base, so they agree.
  exact Prod.ext rfl (((X.covering i).torsor ℂ _ _ (congrArg (·.left) h_deck)).unique
    (congrArg (·.left) e) rfl)

/-- The group of vectors `P` with `(1 - 2 β z) P` in the lattice `frameLattice x`: the solutions of
`P ≡ 2 β z P` modulo the lattice of `x`. -/
private noncomputable def solutionLattice (x : GL n (𝔸f E)) (z : GL n E) (β : 𝓞 E) :
    AddSubgroup (RealVectors E n) :=
  (frameLattice x).comap
    (realVecAction (1 - ((2 * β : 𝓞 E) : E) • (z : Matrix n n E))).toAddMonoidHom

/-- The solutions of `P ≡ 2 β z P` modulo the lattice of `x`. -/
private abbrev SolutionQuotient (x : GL n (𝔸f E)) (z : GL n E) (β : 𝓞 E) : Type :=
  solutionLattice x z β ⧸ (frameLattice x).addSubgroupOf (solutionLattice x z β)

/-- If the Hecke function of `b` is non-zero at `invAutInFrame z x` and `β` is an integer of `E`,
then the lattice of `x` lies in `solutionLattice x z β`, `det (1 - 2 β z) ≠ 0`, and the number of
solutions modulo the lattice is the product of the `σ (det (1 - 2 β z))` over the complex
embeddings `σ`. -/
private lemma frameLattice_le_solutionLattice_and_card {b : heckeAlgebra n ℂ 𝔑} {x : GL n (𝔸f E)}
    {z : GL n E} (hz : heckeCosetFn b (invAutInFrame z x) ≠ 0) (β : 𝓞 E) :
    frameLattice x ≤ solutionLattice x z β ∧
    (1 - ((2 * β : 𝓞 E) : E) • (z : Matrix n n E)).det ≠ 0 ∧
    Nat.card (SolutionQuotient x z β) =
      ∏ σ : E →+* ℂ, σ (1 - ((2 * β : 𝓞 E) : E) • (z : Matrix n n E)).det := by
  -- `invAutInFrame z x = x⁻¹ z⁻¹ x` lies in `GUPlus E n`, so its inverse `x⁻¹ z x` is integral.
  have h_int (k l : n) :
      (x⁻¹.val * (z : Matrix n n E).map (algebraMap E (𝔸f E)) * x.val :) k l ∈ Ô E := by
    simpa [mul_assoc] using (heckeAlgebra.mem_GUPlus_of_ne_zero hz).2 k l
  exact relIndex_comap_one_sub_two_smul h_int β rfl

/-- The pair `t = (z, μ)` is fixed at the point `p` for the Hecke element `b` and the multipliers
`2 α`: the Hecke function of `b` is non-zero at `invAutInFrame z p.frame`, the reflection of `p` is
the reflection of `z` marked by `μ`, and every vector `p.markedPoint j` lies in
`solutionLattice p.frame z (α j)`. -/
private structure IsFixedPair (b : heckeAlgebra n ℂ 𝔑) (α : Fin ν → 𝓞 E) (p : ModuliPoint E n ν)
    (t : GL n E × n) : Prop where
  /-- The Hecke function of `b` is non-zero at `invAutInFrame t.fst p.frame`. -/
  heckeCosetFn_ne_zero : heckeCosetFn b (invAutInFrame t.fst p.frame) ≠ 0
  /-- The reflection of `p` is the reflection of `t.fst` marked by `t.snd`. -/
  reflection_eq : p.reflection = markedReflection t.fst t.snd
  /-- Every vector of `p` is a solution of `P ≡ 2 α_j t.fst P` modulo the lattice. -/
  mem_solutionLattice (j : Fin ν) : p.markedPoint j ∈ solutionLattice p.frame t.fst (α j)

/-- An isomorphism `z` from `p` to `p'` carries a fixed pair `t` of `p` to the fixed pair
`(z t.fst z⁻¹, t.snd)` of `p'`. -/
private lemma IsFixedPair.conj {b : heckeAlgebra n ℂ 𝔑} {α : Fin ν → 𝓞 E}
    {p p' : ModuliPoint E n ν} {z : GL n E} {t : GL n E × n}
    (hz : p.IsLevelIso (levelGU n 𝔑) z p') (ht : IsFixedPair b α p t) :
    IsFixedPair b α p' (z * t.fst * z⁻¹, t.snd) := by
  have h_ne : heckeCosetFn b (invAutInFrame (z * t.fst * z⁻¹) p'.frame) ≠ 0 := by
    rw [← heckeAlgebra.heckeCosetFn_conj hz.mem_level]
    simpa [mul_assoc] using ht.heckeCosetFn_ne_zero
  have h_refl : p'.reflection = markedReflection (z * t.fst * z⁻¹) t.snd := by
    simp [← hz.reflection_eq, ht.reflection_eq, ratConj_eigenReflection]
  refine ⟨h_ne, h_refl, fun j ↦ ?_⟩
  -- `z` maps solutions for `p` to solutions for `p'`, and `z P_j ≡ P'_j` modulo the lattice.
  -- The level group lies in `congruenceGL`, whose elements have integral matrices.
  obtain ⟨-, h_intGL, -⟩ := hz.mem_level
  have h_image : realVecAction z (p.markedPoint j) ∈ solutionLattice p'.frame (z * t.fst * z⁻¹)
    (α j) := by
    simpa [solutionLattice, mul_sub, sub_mul, mul_assoc, Matrix.map_sub, map_smul'] using
      realVecAction_mem_frameLattice h_intGL.isIntMatrix (ht.mem_solutionLattice j)
  have h_le : frameLattice p'.frame ≤ solutionLattice p'.frame (z * t.fst * z⁻¹) (α j) :=
    (frameLattice_le_solutionLattice_and_card h_ne (α j)).left
  simpa using sub_mem h_image (h_le (hz.sub_mem_lattice j))

/-- At a neat level and for a regular `b`, let `invAutInFrame z p.frame` (that is,
`p.frame⁻¹ z⁻¹ p.frame`) lie in the coset `γ`, at which the Hecke function of `b` is non-zero, and
let `z` fix the reflection of `p` and make the vectors of `p` solutions. Then exactly one pair `t`
is fixed at `p` with `invAutInFrame t.fst p.frame` in `γ`: `t.fst` is `z` by neatness, and the mark
`t.snd` is unique by regularity. -/
private lemma existsUnique_isFixedPair (h_neat : IsNeat n 𝔑) {b : heckeAlgebra n ℂ 𝔑}
    (h_reg : IsRegularHecke b) (α : Fin ν → 𝓞 E) {p : ModuliPoint E n ν}
    {γ : GL n (𝔸f E) ⧸ levelGU n 𝔑} (hγ : heckeCosetFn b γ ≠ 0) {z : GL n E}
    (hzγ : (invAutInFrame z p.frame : GL n (𝔸f E) ⧸ levelGU n 𝔑) = γ)
    (hzℓ : ratConj z p.reflection = p.reflection)
    (hzP : ∀ j : Fin ν, p.markedPoint j ∈ solutionLattice p.frame z (α j)) :
    ∃! t : GL n E × n,
      IsFixedPair b α p t ∧ (invAutInFrame t.fst p.frame : GL n (𝔸f E) ⧸ levelGU n 𝔑) = γ := by
  have h_ne : heckeCosetFn b (invAutInFrame z p.frame) ≠ 0 := by rwa [hzγ]
  -- By regularity, the reflection of `p` is the reflection of `z` marked by exactly one `μ`.
  obtain ⟨μ, hμ⟩ : ∃ μ : n, ∀ j : n, p.reflection = markedReflection z j ↔ μ = j := by
    obtain ⟨μ, -, hμ⟩ := (isReflection_markedReflection_and_exists_eq_iff (h_reg h_ne)).right _
      p.isReflection hzℓ
    exact ⟨μ, hμ⟩
  refine ⟨(z, μ), ⟨⟨h_ne, (hμ μ).mpr rfl, hzP⟩, hzγ⟩, ?_⟩
  rintro ⟨z', μ'⟩ ⟨ht, htγ⟩
  -- `z * z'⁻¹` fixes the frame modulo the level and the reflection, so it is `1` by neatness.
  have h_mem_level : p.frame⁻¹ * toFinGL (z * z'⁻¹) * p.frame ∈ levelGU n 𝔑 := by
    simpa [← htγ, QuotientGroup.eq, mul_assoc] using hzγ
  have h_fix : ratConj (z * z'⁻¹) p.reflection = p.reflection := by
    simpa [ht.reflection_eq, ratConj_eigenReflection, mul_assoc] using hzℓ
  obtain rfl : z = z' :=
    mul_inv_eq_one.mp (h_neat.eq_one_of_mem_levelGU p.isSignedFrame h_mem_level h_fix)
  exact Prod.ext rfl ((hμ μ').mp ht.reflection_eq).symm

/-- At a fixed pair `t` of `p`, the value at `1` of the local term at `2 α` is the number of
solutions modulo the lattice: the Lagrange factor of `localTerm` is `1` at `1`, and the other
factors multiply to `∏ j, ∏ σ, σ (det (1 - 2 α_j t.fst))`. -/
private lemma eval_one_localTerm {b : heckeAlgebra n ℂ 𝔑} {α : Fin ν → 𝓞 E}
    {p : ModuliPoint E n ν} {t : GL n E × n} (ht : IsFixedPair b α p t) :
    (localTerm (2 * α) (t.fst : Matrix n n E).charpoly t.snd).eval 1 =
      Nat.card (∀ j : Fin ν, SolutionQuotient p.frame t.fst (α j)) := by
  simp [frameLattice_le_solutionLattice_and_card ht.heckeCosetFn_ne_zero, lieRoots, apply_ite,
    RingHom.map_det, localTerm,
    (numberedRoots _ _).injective, eval_prod, eval_multiset_prod, Nat.card_pi, Matrix.map_sub,
    map_smul', det_one_sub_smul_eq_prod_roots, charpoly_map]

/-- For `γ` with representative in `GUPlus E n`, the point `p · (γ, 2 α)` is isomorphic to `p` by
`z` exactly when `invAutInFrame z p.frame` lies in the coset `γ`, `z` fixes the reflection of `p`,
and the vectors of `p` are solutions of `P ≡ 2 α_j z P` modulo the lattice. -/
private lemma isLevelIso_act_iff {γ : GL n (𝔸f E) ⧸ levelGU n 𝔑} (hγ : γ.out ∈ GUPlus E n)
    (α : Fin ν → 𝓞 E) {p : ModuliPoint E n ν} (z : GL n E) :
    (act p ⟨γ.out, hγ⟩ (2 * α)).IsLevelIso (levelGU n 𝔑) z p ↔
      (invAutInFrame z p.frame : GL n (𝔸f E) ⧸ levelGU n 𝔑) = γ ∧
      ratConj z p.reflection = p.reflection ∧
      ∀ j : Fin ν, p.markedPoint j ∈ solutionLattice p.frame z (α j) := by
  simp [solutionLattice, act, sub_mem_comm_iff,
    Quotient.mk_eq_iff_out.trans QuotientGroup.leftRel_apply, isLevelIso_iff, mul_assoc,
    Matrix.map_sub, map_smul', sub_mulVec, smul_mulVec]

/-- At a fixed pair `t` of `p`, the local term at `2 α` does not vanish at `1`. -/
private lemma eval_one_localTerm_ne_zero {b : heckeAlgebra n ℂ 𝔑} {α : Fin ν → 𝓞 E}
    {p : ModuliPoint E n ν} {t : GL n E × n} (ht : IsFixedPair b α p t) :
    (localTerm (2 * α) (t.fst : Matrix n n E).charpoly t.snd).eval 1 ≠ 0 := by
  have h_det (j : Fin ν) : (1 - ((2 * α j : 𝓞 E) : E) • (t.fst : Matrix n n E)).det ≠ 0 :=
    (frameLattice_le_solutionLattice_and_card ht.heckeCosetFn_ne_zero (α j)).right.left
  simpa [eval_one_localTerm ht, frameLattice_le_solutionLattice_and_card ht.heckeCosetFn_ne_zero,
    Nat.card_pi, prod_ne_zero_iff] using h_det

/-- At a fixed pair `t` of `p`, the frame of `p` is signed for the reflection of `t.fst` marked by
`t.snd`. -/
private lemma IsFixedPair.isSignedFrame {b : heckeAlgebra n ℂ 𝔑} {α : Fin ν → 𝓞 E}
    {p : ModuliPoint E n ν} {t : GL n E × n} (ht : IsFixedPair b α p t) :
    IsSignedFrame p.frame (markedReflection t.fst t.snd) := by
  simpa only [← ht.reflection_eq] using p.isSignedFrame

open scoped Classical in
/-- A class `c` of marked triples whose term for `b` is non-zero is the class of a fixed pair: the
pair of `c` at the point with the frame of `c`, the reflection of the pair, and the vectors `0`. -/
private lemma exists_isFixedPair_of_countTerm_ne_zero {b : heckeAlgebra n ℂ 𝔑}
    (h_reg : IsRegularHecke b) (α : Fin ν → 𝓞 E) {ω : E[X] → n → ℂ}
    {c : MulAction.orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n)}
    (hc : countTerm True b ω c ≠ 0) :
    ∃ p : ModuliPoint E n ν, IsFixedPair b α p c.out.snd ∧
      tripleClass 𝔑 p.frame c.out.snd = c := by
  obtain ⟨h_sig, h_term⟩ := ite_ne_right_iff.mp hc
  have h_ne := left_ne_zero_of_mul h_term
  let p : ModuliPoint E n ν := ⟨_, _, 0, h_sig,
    (isReflection_markedReflection_and_exists_eq_iff (h_reg h_ne)).left _⟩
  refine ⟨p, ⟨h_ne, rfl, fun j ↦ zero_mem _⟩, ?_⟩
  -- `simp` unfolds `p` and the coset of `c.out.fst.out`; what is left is `⟦c.out⟧ = c`.
  simp [p, tripleClass]
  exact c.out_eq

/-- Moving a point of level `i` by a deck transformation does not change its image under
`X.leg i ⟦1⟧`. -/
private lemma Model.comp_leg_eq_of_comp_deck_eq {i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n)}
    {p : ModuliPoint E n ν} {y : specOver R ℂ ⟶ X.cover i} {δ : X.deckGroup i}
    (e : X.point i p ≫ (X.deck i δ).asHom = y) :
    X.point i p ≫ X.leg i ⟦1⟧ = y ≫ X.leg i ⟦1⟧ := by
  rw [← e, Category.assoc, (X.covering i).comp_eq]

/-- Let `t` be a fixed pair of `p` and `t'` one of `p'`, with the same class of triples. Then the
point of `p'` on level `i` is the point of `p` with its vectors replaced by solutions `u`, moved
by a deck transformation `δ`. -/
private lemma Model.point_mem_range_of_class_eq (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n))
    {b : heckeAlgebra n ℂ 𝔑} {α : Fin ν → 𝓞 E} {p p' : ModuliPoint E n ν} {t t' : GL n E × n}
    (ht : IsFixedPair b α p t) (ht' : IsFixedPair b α p' t')
    (h_cl : tripleClass 𝔑 p'.frame t' = tripleClass 𝔑 p.frame t) :
    X.point i p' ∈ Set.range fun u : (∀ j : Fin ν, SolutionQuotient p.frame t.fst (α j)) ×
      X.deckGroup i ↦
      X.point i {p with markedPoint j := (u.fst j).out} ≫ (X.deck i u.snd).asHom := by
  -- `w` moves the vectors of `p'` to solutions, and `X.deckGroup i` is transitive on the fibres.
  obtain ⟨w, e, hw⟩ := (triple_class_eq_iff ht.reflection_eq ht'.reflection_eq).mp h_cl.symm
  have h_sol (j : Fin ν) : realVecAction w (p'.markedPoint j) ∈ solutionLattice p.frame t.fst
    (α j) := by
    rw [← e]
    exact (ht'.conj hw).mem_solutionLattice j
  let u (j : Fin ν) : SolutionQuotient p.frame t.fst (α j) := ⟦⟨_, h_sol j⟩⟧
  have h_rel : p'.IsLevelIso (levelGU n 𝔑) w {p with markedPoint j := (u j).out} :=
    ⟨hw.mem_level, hw.reflection_eq, fun j ↦ (eq_iff_sub_mem.mp (u j).out_eq.symm :)⟩
  have h_base : X.point i {p with markedPoint j := (u j).out} ≫ X.leg i ⟦1⟧ = X.point i p' ≫ X.leg i
    ⟦1⟧ :=
    ((X.point_eq_iff i _ _).mpr ⟨w, h_rel⟩).symm
  obtain ⟨δ, hδ, -⟩ := (X.covering i).torsor ℂ _ _ (congrArg (·.left) h_base)
  exact ⟨(u, δ), Over.OverMorphism.ext hδ⟩

/-- Let `t` be a fixed pair of `p`. If the point of `p'` on level `i` is the point of `p` with its
vectors replaced by solutions, moved by a deck transformation, then some fixed pair `t'` of `p'`
has the class of triples of `t`. -/
private lemma Model.exists_isFixedPair_of_point_eq
    (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n))
    {b : heckeAlgebra n ℂ 𝔑} {α : Fin ν → 𝓞 E} {p p' : ModuliPoint E n ν} {t : GL n E × n}
    (ht : IsFixedPair b α p t) (u : (∀ j : Fin ν, SolutionQuotient p.frame t.fst (α j)) ×
      X.deckGroup i)
    (hu : X.point i {p with markedPoint j := (u.fst j).out} ≫ (X.deck i u.snd).asHom = X.point i
      p') :
    ∃ t' : GL n E × n, IsFixedPair b α p' t' ∧ tripleClass 𝔑 p'.frame t' = tripleClass 𝔑 p.frame
      t := by
  -- An isomorphism `w` from the moved point to `p'` carries `t` to a fixed pair of `p'`.
  obtain ⟨w, hw⟩ := (X.point_eq_iff i _ _).mp (X.comp_leg_eq_of_comp_deck_eq hu)
  have h_fixed_u : IsFixedPair b α {p with markedPoint j := (u.fst j).out} t :=
    ⟨ht.heckeCosetFn_ne_zero, ht.reflection_eq, fun j ↦ (u.fst j).out.prop⟩
  exact ⟨_, h_fixed_u.conj hw, (triple_class_eq_iff (h_fixed_u.conj hw).reflection_eq
    ht.reflection_eq).mpr ⟨w, rfl, hw.mem_level, hw.reflection_eq, by simp⟩⟩

/-- At a neat level, two fixed pairs of the same point with the same class of triples are equal:
the isomorphism between them given by the class is `1`. -/
private lemma eq_of_isFixedPair_of_class_eq (h_neat : IsNeat n 𝔑) {b : heckeAlgebra n ℂ 𝔑}
    {α : Fin ν → 𝓞 E} {p : ModuliPoint E n ν} {t t' : GL n E × n} (ht : IsFixedPair b α p t)
    (ht' : IsFixedPair b α p t') (h_cl : tripleClass 𝔑 p.frame t = tripleClass 𝔑 p.frame t') :
    t' = t := by
  obtain ⟨w, e, hw⟩ := (triple_class_eq_iff ht.reflection_eq ht'.reflection_eq).mp h_cl
  obtain rfl : w = 1 := h_neat.eq_one_of_mem_levelGU p.isSignedFrame hw.mem_level hw.reflection_eq
  simpa using e

/-- At a fixed pair `t` of `p`, `t.fst` fixes the reflection of `p`. -/
private lemma IsFixedPair.ratConj_reflection_eq {b : heckeAlgebra n ℂ 𝔑} {α : Fin ν → 𝓞 E}
    {p : ModuliPoint E n ν} {t : GL n E × n} (ht : IsFixedPair b α p t) :
    ratConj t.fst p.reflection = p.reflection := by
  simp [ht.reflection_eq, ratConj_eigenReflection]

/-- Let `t` be a fixed pair of `p` with `invAutInFrame t.fst p.frame` in the coset `γ`, whose
representative `γ.out` lies in `GUPlus E n` and in `X.legIndices i`. Then at the point of `p` on
level `i`, the local term at `2 α` is a tangent polynomial at `y = X.point i p` for `X.leg i ⟦1⟧`
and `X.leg i γ.out ≫ X.mulMap (2 α)` (`X.tangent`). -/
private lemma Model.isTangentPoly_localTerm (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n))
    {b : heckeAlgebra n ℂ 𝔑} (h_reg : IsRegularHecke b) (α : Fin ν → 𝓞 E)
    {γ : GL n (𝔸f E) ⧸ levelGU n 𝔑} (hγ : γ.out ∈ GUPlus E n) (hγ_level : γ.out ∈ X.legIndices i)
    {p : ModuliPoint E n ν} {t : GL n E × n} (ht : IsFixedPair b α p t)
    (ht_coset : (invAutInFrame t.fst p.frame : GL n (𝔸f E) ⧸ levelGU n 𝔑) = γ)
    {y : specOver R ℂ ⟶ X.cover i} (hy : X.point i p = y) :
    IsTangentPoly X.dimension ((algPoints ℂ (CommRingCat.of R)).map (X.leg i ⟦1⟧))
      ((algPoints ℂ (CommRingCat.of R)).map (X.leg i γ.out ≫ X.mulMap (2 * α)))
      ⟨y⟩ (localTerm (2 * α) (t.fst : Matrix n n E).charpoly t.snd) := by
  subst hy
  have h_iso : (act p ⟨γ.out, hγ⟩ (2 * α)).IsLevelIso (levelGU n 𝔑) t.fst p :=
    (isLevelIso_act_iff hγ α t.fst).mpr
      ⟨ht_coset, ht.ratConj_reflection_eq, ht.mem_solutionLattice⟩
  exact X.tangent i ⟨γ.out, hγ⟩ (2 * α) p t.fst t.snd hγ_level (h_reg ht.heckeCosetFn_ne_zero)
    ht.reflection_eq h_iso

/-- The fibres of the classes of coincidences. Let `q` lift the points of level `i`, `S` be a set
of pairs `⟨c, y⟩` (coset, point) as in `mem_S_iff`, and `r s` the fixed pair of `s` (`hr`,
`r_unique`). For a fixed pair `t` of `p`, the pairs in `S` with the class of `t` correspond, by
their points, to the points of `p` with solutions as vectors, moved by a deck transformation. -/
private lemma Model.bijOn_points_setOf_class_eq (h_neat : IsNeat n 𝔑)
    (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n)) {b : heckeAlgebra n ℂ 𝔑} {α : Fin ν → 𝓞 E}
    {q : (specOver R ℂ ⟶ X.cover i) → ModuliPoint E n ν}
    (hq : ∀ y : specOver R ℂ ⟶ X.cover i, X.point i (q y) = y)
    {S : Set ((_ : (heckeCosetFn b).support) × PointsIn (X.cover i) (CommAlgCat.of ℂ ℂ))}
    (mem_S_iff : ∀ (c : (heckeCosetFn b).support) (y : specOver R ℂ ⟶ X.cover i),
      ⟨c, ⟨y⟩⟩ ∈ S ↔ ∃ z : GL n E,
        invAutInFrame z (q y).frame = (c : GL n (𝔸f E) ⧸ levelGU n 𝔑) ∧
        ratConj z (q y).reflection = (q y).reflection ∧
        ∀ j : Fin ν, (q y).markedPoint j ∈ solutionLattice (q y).frame z (α j))
    {r : ((_ : (heckeCosetFn b).support) × PointsIn (X.cover i) (CommAlgCat.of ℂ ℂ)) → GL n E × n}
    (hr : ∀ s ∈ S, IsFixedPair b α (q s.snd.down) (r s) ∧
      invAutInFrame (r s).fst (q s.snd.down).frame = (s.fst : GL n (𝔸f E) ⧸ levelGU n 𝔑))
    (r_unique : ∀ s ∈ S, ∀ t : GL n E × n, IsFixedPair b α (q s.snd.down) t ∧
      invAutInFrame t.fst (q s.snd.down).frame = (s.fst : GL n (𝔸f E) ⧸ levelGU n 𝔑) → t = r s)
    {p : ModuliPoint E n ν} {t : GL n E × n} (ht : IsFixedPair b α p t) :
    {s ∈ S | tripleClass 𝔑 (q s.snd.down).frame (r s) = tripleClass 𝔑 p.frame t}.BijOn
      (fun s ↦ s.snd.down)
      (Set.range fun u : (∀ j : Fin ν, SolutionQuotient p.frame t.fst (α j)) × X.deckGroup i ↦
        X.point i {p with markedPoint j := (u.fst j).out} ≫ (X.deck i u.snd).asHom) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Into the range (`Model.point_mem_range_of_class_eq`).
    rintro s ⟨hs, h_cl⟩
    have h_mem := X.point_mem_range_of_class_eq i ht (hr s hs).left h_cl
    rwa [hq s.snd.down] at h_mem
  · -- Injective: by neatness the point determines the pair, and the pair determines the coset.
    rintro ⟨c, ⟨y⟩⟩ ⟨hs, h_cl⟩ ⟨c', ⟨y'⟩⟩ ⟨hs', h_cl'⟩ h_points
    obtain rfl : y = y' := h_points
    have h_pair : r ⟨c, ⟨y⟩⟩ = r ⟨c', ⟨y⟩⟩ :=
      eq_of_isFixedPair_of_class_eq h_neat (hr _ hs').left (hr _ hs).left (h_cl'.trans h_cl.symm)
    have h_coset := (hr _ hs).right
    rw [h_pair] at h_coset
    rw [show c = c' from Subtype.ext (h_coset.symm.trans (hr _ hs').right)]
  · -- Onto: an isomorphism `w` with `q y` carries `t` to a pair for `q y`, which gives the coset.
    rintro y ⟨u, hu⟩
    obtain ⟨t', h_fixed, h_cl'⟩ := X.exists_isFixedPair_of_point_eq i ht u (hu.trans (hq y).symm)
    let c : (heckeCosetFn b).support :=
      ⟨_, Finsupp.mem_support_iff.mpr h_fixed.heckeCosetFn_ne_zero⟩
    have h_mem : ⟨c, ⟨y⟩⟩ ∈ S :=
      (mem_S_iff c y).mpr ⟨_, rfl, h_fixed.ratConj_reflection_eq, h_fixed.mem_solutionLattice⟩
    refine ⟨⟨c, ⟨y⟩⟩, ⟨h_mem, ?_⟩, rfl⟩
    rwa [← r_unique _ h_mem _ ⟨h_fixed, rfl⟩]

/-- The Lefschetz formula as a sum over marked pairs. Let `𝔑` be neat. If on all large levels `i`
and for all `α` the combination of the maps `X.leg i q ≫ X.mulMap α`, `q` a coset with coefficient
the value of `b` at `q`, is `h`-null in the geometric sense (`New.Variety.IsNullFamily`, dimension
`X.dimension`), then `b` is `h`-null in the sense of `New.Variety.IsNullHecke`. -/
lemma Model.isNullHecke_of_isNullFamily [Nonempty n] (h_neat : IsNeat n 𝔑)
    {b : heckeAlgebra n ℂ 𝔑} {h : ℕ}
    (h_deep : ∀ᶠ i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n) in Filter.atTop,
      ∀ α : Fin ν → 𝓞 E,
        IsNullFamily (fun q : GL n (𝔸f E) ⧸ levelGU n 𝔑 ↦ X.leg i ⟦q.out⟧ ≫ X.mulMap α)
          (heckeCosetFn b) X.dimension h) :
    IsNullHecke ν h b := by
  classical
  -- Idea: on a deep level `i`, send each coincidence of `X.leg i ⟦1⟧` and
  -- `X.leg i ⟦c.out⟧ ≫ X.mulMap (2 * α)` to a class of triples (frame, `z`, mark). The fibre over a
  -- class has (number of solutions) · `|X.deckGroup i|` elements, and the number of solutions is
  -- the denominator of the local term in `IsNullFamily`. So the sum over coincidences is, up to the
  -- factor `|X.deckGroup i|`, the sum in `IsNullHecke`.
  intro h_reg α
  have h_out_mem (c : (heckeCosetFn b).support) :
      (c : GL n (𝔸f E) ⧸ levelGU n 𝔑).out ∈ GUPlus E n :=
    heckeAlgebra.mem_GUPlus_of_ne_zero (f := b) (by aesop)
  -- Choose a deep level `i` whose set `X.legIndices i` contains the representatives `c.out`.
  obtain ⟨i, h_null, h_translate⟩ :=
    (h_deep.and (Filter.eventually_all.mpr fun c ↦ X.eventually_translate ∅ (h_out_mem c))).exists
  have h_level (c : (heckeCosetFn b).support) := (h_translate c).left
  -- `q` lifts the complex points of level `i`.
  choose q hq using X.point_surjective i
  -- `S` is the set of coincidences `⟨c, y⟩`: `c` in the support of `b`, `y` a point of level `i`.
  specialize h_null (2 * α) (X.leg i ⟦1⟧)
  extract_lets S at h_null
  -- Coincidences in terms of the uniformisation (`isLevelIso_act_iff`).
  have mem_S_iff (c : (heckeCosetFn b).support) (y : specOver R ℂ ⟶ X.cover i) :
      ⟨c, ⟨y⟩⟩ ∈ S ↔ ∃ z : GL n E, invAutInFrame z (q y).frame = (c : GL n (𝔸f E) ⧸ levelGU n 𝔑) ∧
        ratConj z (q y).reflection = (q y).reflection ∧
        ∀ j : Fin ν, (q y).markedPoint j ∈ solutionLattice (q y).frame z (α j) := by
    refine eq_comm.trans ?_
    -- `using!`: `point_leg` writes the coset as `↑g`, the sum as `⟦g⟧`; they agree by unfolding.
    simpa only [hq, h_level, ← point_leg] using!
      (X.point_eq_iff i _ (q y)).trans (exists_congr (isLevelIso_act_iff (h_out_mem c) α))
  -- A coincidence has exactly one fixed pair `(z, μ)` (`existsUnique_isFixedPair`).
  have exists_pair s (hs : s ∈ S) :
      ∃! t : GL n E × n, IsFixedPair b α (q s.snd.down) t ∧
        invAutInFrame t.fst (q s.snd.down).frame = (s.fst : GL n (𝔸f E) ⧸ levelGU n 𝔑) := by
    obtain ⟨z, hzγ, hzℓ, hzP⟩ := (mem_S_iff s.fst s.snd.down).mp hs
    exact existsUnique_isFixedPair h_neat h_reg α (Finsupp.mem_support_iff.mp s.fst.prop) hzγ hzℓ
      hzP
  choose! r hr r_unique using exists_pair
  -- So every coincidence is simple, with tangent polynomial `localTerm`
  -- (`Model.isTangentPoly_localTerm`), and `h_null` applies.
  obtain ⟨S_finite, sum_zero⟩ :=
    h_null (fun s ↦ localTerm (2 * α) ((r s).fst : Matrix n n E).charpoly (r s).snd) fun s hs ↦
      ⟨X.isTangentPoly_localTerm i h_reg α (h_out_mem s.fst) (h_level s.fst) (hr s hs).left
        (hr s hs).right (hq _), eval_one_localTerm_ne_zero (hr s hs).left⟩
  -- A class with non-zero term comes from a coincidence: take the vectors `P = 0`.
  have support_subset (ω : E[X] → n → ℂ)
      (c : MulAction.orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n))
      (hc : countTerm True b ω c ≠ 0) :
      c ∈ (fun s ↦ tripleClass 𝔑 (q s.snd.down).frame (r s)) '' S := by
    obtain ⟨p, h_fixed, h_cl_p⟩ := exists_isFixedPair_of_countTerm_ne_zero h_reg α hc
    obtain ⟨s, ⟨hs, h_cl⟩, -⟩ :=
      (X.bijOn_points_setOf_class_eq h_neat i hq mem_S_iff hr r_unique h_fixed).surjOn ⟨(0, 1), rfl⟩
    exact ⟨s, hs, h_cl.trans h_cl_p⟩
  refine ⟨(S_finite.image _).subset (support_subset _), ?_⟩
  -- Sum over the fibres (`finsum_image_eq_zero_of_fibers`): the term of a class divided by the
  -- size of its fibre is the local term of the coincidence divided by `|X.deckGroup i|`.
  have h_sum :
      ∑ᶠ c ∈ (fun s ↦ tripleClass 𝔑 (q s.snd.down).frame (r s)) '' S,
        countTerm True b (fun P μ ↦ (localTerm (2 * α) P μ).coeff h) c = 0 := by
    refine finsum_image_eq_zero_of_fibers S_finite _ sum_zero (D := Nat.card (X.deckGroup i)) fun s
      hs ↦ ?_
    obtain ⟨h_fixed, hγ⟩ := hr s hs
    have h_card :
        Nat.card {s' ∈ S | tripleClass 𝔑 (q s'.snd.down).frame (r s') =
            tripleClass 𝔑 (q s.snd.down).frame (r s)} =
          Nat.card (∀ j : Fin ν, SolutionQuotient (q s.snd.down).frame (r s).fst (α j)) *
            Nat.card (X.deckGroup i) := by
      rw [card_congr (X.bijOn_points_setOf_class_eq h_neat i hq mem_S_iff hr r_unique
        h_fixed).equiv,
        card_range_of_injective (X.point_comp_deck_injective h_neat i _
          fun j ↦ solutionLattice (q s.snd.down).frame (r s).fst (α j)),
        card_prod]
    rw [h_card, countTerm_mk, ite_eq_left h_fixed.isSignedFrame, hγ, cast_mul,
      ← eval_one_localTerm h_fixed, div_div]
  rwa [finsum_mem_def, Set.indicator_eq_self.mpr (support_subset _)] at h_sum

end New.Variety
