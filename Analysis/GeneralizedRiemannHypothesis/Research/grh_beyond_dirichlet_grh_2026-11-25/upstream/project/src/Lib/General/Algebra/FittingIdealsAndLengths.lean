import Lib.General.LinearAlgebra.HermiteForm

/-!
# Relations, relative lengths and Fitting ideals for Selmer group estimates

This file gives linear algebra for the Selmer group estimates. Conditions on a function `c : Γ → Bⁿ`
are written as relations: finitely supported matrix-valued `f` on `Γ` acting by `c ↦ ∑ γ, f γ • c γ`
(`New.relEval`). Sizes are lengths of modules in `ℕ∞`, and `addVal` is the valuation of a discrete
valuation ring, normalised to be 1 at a uniformiser. The zeroth Fitting ideal of a quotient is
controlled as relations are added.

## Main definitions and results

* `New.obeying R B`: the functions with values in `Bⁿ` killed by all relations in `R`. For
  `New.cocycleRelations ρ` these are the cocycles (`New.mem_obeying_cocycleRelations`).
* `New.relLength S T`: the length of `S / (S ⊓ T)`, with its monotonicity and additivity rules.
* `New.length_obeying_relationsOn_le`: the relations `New.relationsOn Z` of a finitely generated `Z`
  cut out a module of length at most `rank Z * length B`.
* `New.length_ker_le_addVal_det`, `New.exists_matrix_addVal_det_le_length`: lengths compared with
  valuations of determinants.
* `New.Lift.relLength_le_of_relations`: if `p ^ t L ≤ L'` and any `m + 1` elements of `L` killed by
  `p` modulo `L'` have a combination in `L'` with some coefficient `1`, the length of `L` modulo
  `L'` is at most `t m`.
* `New.Selmer.fittingIdeal.exists_addVal_le_relLength`: if `p ≠ 0`, `R` is Noetherian and
  `Φ (p • v) ∈ N` for all `v`, then for a condition `V` on the linear forms modulo `p`, some `c` of
  valuation at most the length modulo `V` of the forms that vanish on `Φ⁻¹ N` multiplies the Fitting
  ideal of an enlargement `K` of `N` into that of `N`; here `K` contains `Φ v` for every `v` killed
  by all the forms that satisfy `V`.

## Relation to the literature

Three standard properties of Fitting ideals are proved in the cases that are used, for fixed
generators: base change (Stacks Project, Tag 07ZA), the product rule for an exact sequence, and the
bound by a length.
-/

noncomputable section

/-!
## Modules cut out by matrix relations, their lengths and determinants

The classes `New.DVR` and `New.PadicIntegerRing` describe the coefficient rings: a discrete
valuation ring, and the integer ring of a finite extension of `ℚ_ℓ`.
-/

namespace New

open Matrix Module Submodule LinearMap Finsupp LinearEquiv IsDiscreteValuationRing Ideal

variable {O O' Γ n A : Type*} [CommRing O] [CommRing O'] [Fintype n] [DecidableEq n] [Ring A]
  {m M M' : Type*} [Fintype m] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
  (S T : Submodule A M) (R : Set (Γ →₀ Matrix n n O))
  (B : Type*) [AddCommGroup B] [Module O B]
  {B' : Type*} [AddCommGroup B'] [Module O B']
  {c : Γ → n → B} (φ : B →ₗ[O] B') (e : O →+* O') (Z : Submodule O (Γ → n → O))
  {S' T' : Submodule A M'} (f : M →ₗ[A] M') {a p : O}

/-- O is a discrete valuation ring (in particular a domain). -/
class DVR (O : Type*) [CommRing O] extends IsDomain O, IsDiscreteValuationRing O

/-- The quotient ring O/aO. -/
abbrev QuotSpan (a : O) : Type _ := O ⧸ Ideal.span {a}

/-- O is a discrete valuation ring of characteristic 0, finite and free over ℤ_ℓ, with finite
quotients by nonzero ideals: the integer ring of a finite extension of ℚ_ℓ. -/
class PadicIntegerRing (O : Type*) (ℓ : outParam ℕ) [Fact ℓ.Prime]
    [CommRing O] extends Algebra ℤ_[ℓ] O, DVR O, CharZero O, Free ℤ_[ℓ] O, Module.Finite ℤ_[ℓ] O,
  Ring.HasFiniteQuotients O

instance [h : Ring.HasFiniteQuotients O] [NeZero a] : Finite (QuotSpan a) :=
  h.finiteQuotient (by simp [NeZero.ne])

/-! ### Relations, the functions they kill, and lengths modulo a submodule -/

/-- Evaluation of relations. A finitely supported function `f` from `Γ` to `n × n` matrices over
`O` is sent to the `O`-linear map `c ↦ ∑ γ, f γ • c γ` from functions `Γ → Bⁿ` to `Bⁿ`. The
dependence on `f` is linear over the matrix ring. -/
@[simp]
def relEval : (Γ →₀ Matrix n n O) →ₗ[Matrix n n O] (Γ → n → B) →ₗ[O] n → B :=
  (bilinearCombination (Matrix n n O) O).flip

/-- The submodule of the functions `c : Γ → Bⁿ` killed by every relation `f` in `R`, that is, with
`∑ γ, f γ • c γ = 0` in `Bⁿ`. -/
def obeying : Submodule O (Γ → n → B) := ⨅ f ∈ R, (relEval B f).ker

/-- The matrix-valued finitely supported function obtained from f by applying the ring
homomorphism e: O → O' to every matrix entry. -/
def mapRel (f : Γ →₀ Matrix n n O) : Γ →₀ Matrix n n O' := f.mapRange e.mapMatrix (by simp)

/-- The linear relations of Z: the finitely supported matrix-valued f on Γ with Σ_γ f(γ)z(γ) = 0
in O^n for all z in Z. -/
def relationsOn : Set (Γ →₀ Matrix n n O) := {f : Γ →₀ Matrix n n O | ∀ z ∈ Z, relEval O f z = 0}

/-- The length of S/(S ∩ T) as an A-module, for submodules S, T of M. -/
def relLength : ℕ∞ := length A (S ⧸ T.submoduleOf S)

lemma relLength_ker : relLength S f.ker = length A (S.map f) := by
  rw [← f.range_domRestrict S]
  exact (f.domRestrict S).quotKerEquivRange.length_eq

lemma relLength_eq_length_map_mkQ : relLength S T = length A (S.map T.mkQ) := by
  simp [← relLength_ker]

lemma relLength_comap : relLength S (Submodule.comap f T') = relLength (S.map f) T' := by
  rw [← T'.ker_mkQ, ← f.ker_comp, relLength_ker, map_comp, relLength_ker]

/-- The length of `S` modulo an intersection is at most the sum of its lengths modulo each of the
finitely many submodules intersected. -/
lemma relLength_iInf_le (T : m → Submodule A M) :
    relLength S (⨅ i : m, T i) ≤ ∑ i : m, relLength S (T i) := by
  -- `S ⧸ ⨅ i, T i` embeds in the product of the `S ⧸ T i`.
  let π : S →ₗ[A] ∀ i : m, S ⧸ (T i).submoduleOf S := pi fun i ↦ mkQ _
  have h_ker : (⨅ i : m, T i).submoduleOf S = ker π := by
    rw [ker_pi, submoduleOf, Submodule.comap_iInf]
    exact iInf_congr fun i ↦ (ker_mkQ _).symm
  calc relLength S (⨅ i : m, T i) ≤ length A (∀ i : m, S ⧸ (T i).submoduleOf S) :=
      length_le_of_injective _ (ker_eq_bot.1 (ker_liftQ_eq_bot' _ π h_ker))
    _ = ∑ i : m, relLength S (T i) := by simp [relLength, length_pi_of_fintype]

/-- The length of `S` is the sum of its length modulo `T` and the length of `S ⊓ T`. -/
lemma relLength_add_length_inf : relLength S T + length A ↥(S ⊓ T) = length A S := by
  -- Additivity of length in `0 → S ⊓ T → S → S ⧸ T → 0`.
  have h_exact : Function.Exact (inclusion (inf_le_left : S ⊓ T ≤ S)) (T.submoduleOf S).mkQ := by
    rw [exact_iff, ker_mkQ, range_inclusion]
    simp [submoduleOf]
  rw [length_eq_add_of_exact _ _ (inclusion_injective _) (mkQ_surjective _) h_exact, add_comm,
    relLength]
@[simp]
lemma relLength_bot : relLength S ⊥ = length A S := by rw [← ker_id, relLength_ker, S.map_id]

variable {R B S T Z}

lemma smul_quot_eq_zero_of_dvd (h_dvd : a ∣ p) (b : QuotSpan a) : p • b = 0 := by
  simp [Algebra.smul_def, (Ideal.Quotient.eq_zero_iff_dvd a p).2 h_dvd]

lemma Selmer.nsmul_quot_eq_zero {ℓ M : ℕ} (h_dvd : a ∣ (ℓ : O) ^ M) :
    ∀ x : QuotSpan a, ℓ ^ M • x = 0 :=
  mod_cast smul_quot_eq_zero_of_dvd h_dvd

lemma relEval_apply (f : Γ →₀ Matrix n n O) (c : Γ → n → B) :
    relEval B f c = f.sum fun (γ : Γ) (x : Matrix n n O) ↦ x • c γ :=
  rfl

lemma mem_obeying : c ∈ obeying R B ↔ ∀ f ∈ R, relEval B f c = 0 := by simp [obeying]

/-- A linear map `φ` applied coordinatewise to `c : Γ → Bⁿ` gives a function killed by all the
relations in `R` if and only if `φ` kills each coordinate of `∑ γ, f γ • c γ` for `f ∈ R`. -/
lemma comp_mem_obeying_iff :
    (fun (g : Γ) (i : n) ↦ φ (c g i)) ∈ obeying R B' ↔
      ∀ f ∈ R, ∀ i : n, φ (relEval B f c i) = 0 := by
  simp [obeying, linearCombination, sum, funext_iff]

/-- The reduction modulo `a` of a function `z ∈ Z` is killed by all linear relations of `Z`. -/
lemma mkQ_mem_obeying_relationsOn (z : Γ → n → O) (hz : z ∈ Z) :
    (fun (g : Γ) (i : n) ↦ (Ideal.span {a}).mkQ (z g i)) ∈
      obeying (relationsOn Z) (QuotSpan a) :=
  (comp_mem_obeying_iff _).2 fun f hf i ↦ by rw [hf z hz, Pi.zero_apply, map_zero]

/-- The set of matrix-valued relations, one for each pair (g, h), expressing the cocycle
identity c(gh) = c(g) + ρ(g)c(h). -/
def cocycleRelations [Mul Γ] (ρ : Γ → Matrix n n O) : Set (Γ →₀ Matrix n n O) :=
  {f : Γ →₀ Matrix n n O | ∃ g h : Γ, f = .single (g * h) 1 - .single g 1 - .single h (ρ g)}

/-- A function `c : Γ → Bⁿ` is killed by the cocycle relations of `ρ` if and only if it satisfies
the cocycle identity `c (g * h) = c g + ρ g • c h`. -/
lemma mem_obeying_cocycleRelations [Mul Γ] {ρ : Γ → Matrix n n O} :
    c ∈ obeying (cocycleRelations ρ) B ↔ ∀ g h : Γ, c (g * h) = c g + ρ g • c h := by
  simp only [mem_obeying, cocycleRelations, Set.mem_ofPred_eq, forall_exists_index]
  refine ⟨fun h g k ↦ by simpa [sub_eq_iff_eq_add'] using h _ g k rfl, ?_⟩
  rintro h f g k rfl
  simp [h g k]

/-! ### Maps and monotonicity of relative lengths -/

/-- If a linear map `f` maps `S` into `S'` and every point of `S` mapped into `T'` lies in `T`,
then the length of `S` modulo `T` is at most that of `S'` modulo `T'`. -/
lemma relLength_le_of_mapsTo (h_maps : ∀ x ∈ S, f x ∈ S') (h_back : ∀ x ∈ S, f x ∈ T' → x ∈ T) :
    relLength S T ≤ relLength S' T' := by
  -- `S ⧸ f⁻¹ T'` surjects onto `S ⧸ T` and injects into `S' ⧸ T'`.
  let K : Submodule A S := (T'.submoduleOf S').comap (f.restrict h_maps)
  have hK : K ≤ T.submoduleOf S := fun x ↦ h_back x x.2
  calc relLength S T ≤ length A (S ⧸ K) := length_le_of_surjective _ (factor_surjective hK)
    _ ≤ relLength S' T' :=
      length_le_of_injective (mapQ K (T'.submoduleOf S') (f.restrict h_maps) le_rfl)
        (by simp [K, ← ker_eq_bot, ker_mapQ])

lemma relLength_mono {S' T' : Submodule A M} (hS : S ≤ S') (hT : T' ≤ T) :
    relLength S T ≤ relLength S' T' :=
  relLength_le_of_mapsTo .id (fun _ hx ↦ hS hx) fun _ _ hx ↦ hT hx

@[simp]
lemma relLength_eq_zero : relLength S T = 0 ↔ S ≤ T := by simp [relLength, length_quotient]

lemma length_mono (h_le : S ≤ T) : length A S ≤ length A T := by
  grw [length_submodule, length_submodule, h_le]

/-- A submodule contained in the image of `S` under a linear map has length at most that of `S`. -/
lemma length_le_of_le_map (S : Submodule A M) (h_le : T' ≤ Submodule.map f S) :
    length A T' ≤ length A S :=
  (length_mono h_le).trans (length_le_of_surjective _ (f.submoduleMap_surjective S))

variable [DVR O]

/-! ### Length bounds over a discrete valuation ring -/

/-- Let `O` be a discrete valuation ring, `n` a nonempty finite type, `B` an `O`-module and `Z` a
finitely generated `O`-module of functions `Γ → Oⁿ`. A relation on `Z` is a finitely supported
family `f` of `n × n` matrices over `O` with `∑ γ, f γ * z γ = 0` for all `z ∈ Z`. The functions
`c : Γ → Bⁿ` with `∑ γ, f γ • c γ = 0` for every such relation form a submodule of length at most
`finrank O Z * length O B`. -/
lemma length_obeying_relationsOn_le [Nonempty n] [Module.Finite O Z] :
    length O (obeying (relationsOn Z) B) ≤ finrank O Z * length O B := by
  -- Fix an index `i`, and let `φ f` be the linear form `z ↦ relEval O f z i` on `Z`. A function
  -- `c` killed by the relations of `Z` gives the map `f ↦ relEval B f c i`, which factors through
  -- the quotient by `φ.ker` and determines `c`. That quotient embeds in the dual of `Z`, so it is
  -- free of rank at most that of `Z`.
  obtain ⟨i⟩ : Nonempty n := inferInstance
  let φ : (Γ →₀ Matrix n n O) →ₗ[O] Z →ₗ[O] O :=
    (((relEval (Γ := Γ) (O := O) (n := n) O).restrictScalars O).compr₂ (proj i)).compl₂ Z.subtype
  let ev : (((Γ →₀ Matrix n n O) ⧸ φ.ker) →ₗ[O] B) →ₗ[O] Γ → n → B :=
    pi fun g ↦ pi fun j ↦ applyₗ (φ.ker.mkQ (.single g (.single i j 1)))
  have h_image : obeying (relationsOn Z) B ≤ .map ev ⊤ := fun c hc ↦ by
    let ψ : (Γ →₀ Matrix n n O) →ₗ[O] B :=
      proj i ∘ₗ ((relEval (Γ := Γ) (O := O) (n := n) B).flip c).restrictScalars O
    have h_ker : φ.ker ≤ ψ.ker := fun f hf ↦ by
      -- Row `i` of `f`, with the other rows set to zero, is a relation on `Z`.
      have h_rel : Matrix.single i i (1 : O) • f ∈ relationsOn Z := fun z hz ↦ by
        simpa [φ] using LinearMap.congr_fun hf ⟨z, hz⟩
      simpa [ψ] using mem_obeying.1 hc _ h_rel
    exact ⟨φ.ker.liftQ ψ h_ker, mem_top, by simp [ev, ψ, Matrix.single, funext_iff]⟩
  let b : Basis (Fin (finrank O φ.range)) O ((Γ →₀ Matrix n n O) ⧸ φ.ker) :=
    (finBasis O φ.range).map φ.quotKerEquivRange.symm
  calc length O (obeying (relationsOn Z) B)
    _ ≤ length O (((Γ →₀ Matrix n n O) ⧸ φ.ker) →ₗ[O] B) :=
      (length_le_of_le_map ev ⊤ h_image).trans_eq length_top
    _ = length O (Fin (finrank O φ.range) → B) := (b.constr O).length_eq.symm
    _ = finrank O φ.range * length O B := by simp
    _ ≤ finrank O Z * length O B := by grw [φ.range.finrank_le, finrank_linearMap_self]

@[simp]
lemma length_quot_span_eq_addVal : length O (QuotSpan a) = addVal O a := Ring.ord_eq_addVal a

lemma addVal_prod (f : m → O) : addVal O (∏ i : m, f i) = ∑ i : m, addVal O (f i) := by
  induction (Finset.univ : Finset m) using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => simp [ih]

/-- For a square matrix M over a discrete valuation ring O and p in O, the kernel of M acting on
(O/p)^n (the endomorphism `M • 1`) has O-length at most the valuation of det M, normalised so that a
uniformiser has valuation 1. It is a consequence of the theorem on elementary divisors. -/
lemma length_ker_le_addVal_det (M : Matrix n n O) (p : O) :
    length O (ker (M • 1 : End O (n → QuotSpan p))) ≤ addVal O M.det := by
  -- In Smith normal form `M = Q * diagonal a * P`, with `P` and `Q` invertible, the kernel lies in
  -- the image under `P⁻¹` of the product of the `a i`-torsion submodules of `O ⧸ p`, each of which
  -- is cyclic, so a quotient of `O ⧸ a i`.
  obtain ⟨Q, -, P, -, a, rfl⟩ := isValuationPair_top.smith_normal_form M
  have h_cyclic : ∀ i : n, ∃ g : QuotSpan p, torsionBy O (QuotSpan p) (a i) = O ∙ g := fun i ↦
    (IsPrincipal.of_comap _ (span {p}).mkQ_surjective _).1
  choose g hg using h_cyclic
  let ψ : (∀ i : n, QuotSpan (a i)) →ₗ[O] n → QuotSpan p :=
    P⁻¹ • piMap fun i ↦ liftQSpanSingleton _ (toSpanSingleton O _ (g i))
      (show g i ∈ torsionBy O (QuotSpan p) (a i) by simp [hg i])
  have h_ker : ker ((Q.1 * diagonal a * P.1) • 1 : End O (n → QuotSpan p)) ≤ .map ψ ⊤ :=
    fun w hw ↦ by
      -- Cancelling `Q` shows that `a i` kills the coordinate `i` of `P • w`.
      have h_coord : ∀ i : n, ∃ t : O, t • g i = (P.1 • w) i := by
        simpa [mul_smul, funext_iff, diagonal, ← mem_torsionBy_iff, Submodule.mem_span_singleton,
          hg] using hw
      choose t ht using h_coord
      exact ⟨fun i ↦ mkQ _ (t i), mem_top, ((smul_eq_iff_eq_inv_smul P).1 (funext ht).symm).symm⟩
  calc length O (ker ((Q.1 * diagonal a * P.1) • 1 : End O (n → QuotSpan p)))
    _ ≤ length O (⊤ : Submodule O (∀ i : n, QuotSpan (a i))) := length_le_of_le_map _ ⊤ h_ker
    _ = addVal O (∏ i : n, a i) := by simp [addVal_prod]
    -- `det M = det Q * (∏ i, a i) * det P`, so its valuation is no smaller than that of the
    -- product.
    _ ≤ addVal O (Q.1 * diagonal a * P.1).det := by simp [le_add_right]

/-- Let `O` be a discrete valuation ring, `B ≅ O/p` a cyclic `O`-module and `Z` an `O`-module of
functions from `Γ` to `B`. If `n i • z (q i) = 0` for all `z ∈ Z`, and only `0` vanishes at all
the finitely many points `q i`, then the length of `Z` is at most the valuation of `∏ n i`. -/
lemma OddPart.length_le_of_detecting_points {n : m → ℕ} {q : m → Γ} {Z : Submodule O (Γ → B)}
    (e : B ≃ₗ[O] QuotSpan p) (h_kill : ∀ z ∈ Z, ∀ i : m, n i • z (q i) = 0)
    (h_detect : ∀ z ∈ Z, (∀ i : m, z (q i) = 0) → z = 0) :
    length O Z ≤ addVal O (∏ i : m, n i : ℕ) := by
  classical
  -- Evaluation at the points embeds `Z` in the kernel of the diagonal matrix of the `n i`.
  let ev : (Γ → B) →ₗ[O] m → QuotSpan p := pi fun i ↦ e.toLinearMap ∘ₗ proj (q i)
  let D : Matrix m m O := diagonal fun i ↦ n i
  let W : Submodule O (m → QuotSpan p) := ker (D • 1 : End O (m → QuotSpan p))
  have h_mem (z : Γ → B) (hz : z ∈ Z) : ev z ∈ W := by
    simpa [ev, D, W, funext_iff, diagonal, Nat.cast_smul_eq_nsmul] using
      fun i ↦ congrArg e (h_kill z hz i)
  calc length O Z ≤ length O W := length_le_of_injective (ev.restrict h_mem)
        (by simpa [ev, funext_iff, disjoint_def] using h_detect)
    _ ≤ addVal O D.det := length_ker_le_addVal_det D p
    _ = addVal O (∏ i, n i : ℕ) := by simp [D]

/-- Let O be a discrete valuation ring and aO^n ⊆ L ⊆ O^n, a ≠ 0. There are a square matrix M with
rows in L and a submodule S of (O/a)^n whose annihilator in O^n is exactly L, with the valuation of
det M at most the length of S.

It is a consequence of the theorem on elementary divisors. -/
lemma exists_matrix_addVal_det_le_length (L : Submodule O (n → O)) (ha : a ≠ 0)
    (h_smul : ∀ v : n → O, a • v ∈ L) :
    ∃ M : Matrix n n O, ∃ S : Submodule O (n → QuotSpan a),
      -- (a) the rows of `M` lie in `L`
      (∀ i : n, M i ∈ L) ∧
      -- (b) `L` is the orthogonal of `S`
      (∀ v : n → O, v ∈ L ↔ ∀ w ∈ S, ∑ j : n, v j • w j = 0) ∧
      -- (c) the determinant bound
      addVal O (det M) ≤ length O S := by
  -- `L` is free of full rank, so it is the column span of a matrix `M`, and `N * M = a • 1` for
  -- some `N`. Take the matrix `Mᵀ`, and for `S` the image of `Nᵀ` on `n → O ⧸ a`.
  let g : (n → O) →ₗ[O] L := (lsmul O _ a).codRestrict L h_smul
  have hg : Function.Injective g := (lsmul_injective ha).codRestrict h_smul
  have b : (n → O) ≃ₗ[O] L :=
    ofFinrankEq _ _ (L.finrank_le.antisymm' (g.finrank_le_finrank_of_injective hg))
  obtain ⟨M, N, rfl, hNM⟩ : ∃ M N : Matrix n n O, L = M.toLin'.range ∧ N * M = a • 1 := by
    refine ⟨(L.subtype ∘ₗ b).toMatrix', (b.symm ∘ₗ g).toMatrix', by simp [LinearMap.range_comp],
      ext_iff_mulVec.2 fun v ↦ ?_⟩
    -- `g` is multiplication by `a`, with values in `L`.
    have hgb : g (b v : n → O) = a • b v := rfl
    simpa [← toLin'_apply, symm_apply_eq] using hgb
  have hN : N.det ≠ 0 := fun h_zero ↦ by simpa [h_zero, ha, eq_comm] using congrArg det hNM
  let Nt : End O (n → QuotSpan a) := Nᵀ • 1
  have h_pair (v : n → O) (x : n → QuotSpan a) :
      ∑ j, v j • Nt x j = ∑ i, (N *ᵥ v) i • x i := by
    simpa [Nt, mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul, mul_comm] using
      Finset.sum_comm
  have h_orth (v : n → O) : v ∈ M.toLin'.range ↔
      ∀ w ∈ Submodule.map Nt ⊤, ∑ j : n, v j • w j = 0 := by
    constructor
    · -- For `v = M *ᵥ t` we get `N *ᵥ v = a • t`, which pairs to zero modulo `a`.
      rintro ⟨t, rfl⟩ _ ⟨x, -, rfl⟩
      simp [h_pair, hNM, smul_mulVec, smul_quot_eq_zero_of_dvd]
    · -- Conversely `a` divides `N *ᵥ v`, say `N *ᵥ v = a • t = N *ᵥ M *ᵥ t`, and `N` is injective.
      intro hv
      have h_dvd : ∀ i : n, a ∣ (N *ᵥ v) i := fun i ↦ by
        have h_sum : ∑ j, (N *ᵥ v) j • (Pi.single i 1 : n → QuotSpan a) j = 0 :=
          (h_pair v _).symm.trans (hv _ (Submodule.mem_map_of_mem mem_top))
        simpa [← Ideal.Quotient.eq_zero_iff_dvd, Algebra.smul_def, Pi.single_apply] using h_sum
      choose t ht using h_dvd
      have h_eq : N *ᵥ (M *ᵥ t) = N *ᵥ v := by simp [funext_iff, ht, hNM, smul_mulVec]
      exact ⟨t, mulVec_injective_of_det_ne_zero hN h_eq⟩
  -- Split the length of `n → O ⧸ a` into image and kernel of `Nᵀ`, then cancel the valuation
  -- of `det N`, which is finite.
  have h_add : addVal O (det Mᵀ) + addVal O N.det ≤
      length O (Submodule.map Nt ⊤) + addVal O N.det :=
    calc addVal O (det Mᵀ) + addVal O N.det = addVal O (det (N * M)) := by simp [add_comm]
      _ = length O (⊤ : Submodule O (n → QuotSpan a)) := by simp [hNM]
      _ = relLength ⊤ Nt.ker + length O ↥(⊤ ⊓ Nt.ker) := (relLength_add_length_inf ⊤ Nt.ker).symm
      _ ≤ length O (Submodule.map Nt ⊤) + addVal O N.det := by
        grw [relLength_ker, length_mono inf_le_right, length_ker_le_addVal_det, det_transpose]
  have h_rows (i : n) : Mᵀ i ∈ M.toLin'.range := ⟨Pi.single i 1, M.mulVec_single_one i⟩
  have h_val : addVal O N.det ≠ ⊤ := mt addVal_eq_top_iff.1 hN
  exact ⟨Mᵀ, Submodule.map Nt ⊤, h_rows, h_orth, (ENat.add_le_add_iff_right h_val).1 h_add⟩

end New

/-!
## Relative lengths of p-adic integer modules

Lemmas on `New.relLength L L'`, the length of `L / (L ⊓ L')` ("the length of `L` modulo `L'`"), for
`ℤ_p`-submodules `L`, `L'`, `L''` of a module `V`, where `p` is a prime natural number (not the
`p : O` used above) and `m`, `n` are natural numbers.
-/

section RelativeLength

open Module Submodule Cardinal

namespace New.Lift

variable {p : ℕ}
  {V : Type*} [Fact p.Prime] [AddCommGroup V] [Module ℤ_[p] V]
  {L L' L'' : Submodule ℤ_[p] V} {m n : ℕ}

/-- If `L` has length at most `m` modulo `L'` and `L'` has length at most `n` modulo `L''`, then
`L` has length at most `m + n` modulo `L''`. -/
lemma relLength_trans (h_left : relLength L L' ≤ m) (h_right : relLength L' L'' ≤ n) :
    relLength L L'' ≤ ↑(m + n) :=
  -- Work modulo `L''` and filter the image of `L` by the image of `L'`.
  let π : V →ₗ[ℤ_[p]] V ⧸ L'' := L''.mkQ
  calc relLength L L'' = relLength (L.map π) (L'.map π) + length ℤ_[p] ↥(L.map π ⊓ L'.map π) := by
        rw [relLength_eq_length_map_mkQ, relLength_add_length_inf]
    _ ≤ relLength L ((L'.map π).comap π) + relLength L' L'' := by
        grw [length_mono inf_le_right, relLength_comap, relLength_eq_length_map_mkQ L']
    _ ≤ relLength L L' + relLength L' L'' := by grw [relLength_mono le_rfl (le_comap_map π L')]
    _ ≤ ↑(m + n) := by grw [h_left, h_right, Nat.cast_add]

/-- Let `T` be a submodule with `p T ≤ L'`. If any `m + 1` elements `x j` of `T` have a combination
`∑ a j • x j` in `L'` with some coefficient `a j = 1`, then `T / (T ⊓ L')` has length at
most `m`. -/
lemma relLength_le_of_prime_smul_mem {T : Submodule ℤ_[p] V}
    (h_kill : ∀ x ∈ T, (p : ℤ_[p]) • x ∈ L')
    (h_rel : ∀ x : Fin (m + 1) → T, ∃ (a : Fin (m + 1) → ℤ_[p]) (j : Fin (m + 1)),
      a j = 1 ∧ ∑ i : Fin (m + 1), a i • (x i : V) ∈ L') :
    relLength T L' ≤ m := by
  -- The quotient is a vector space over `ℤ_[p] / p`, so its length is its dimension, and any
  -- `m + 1` classes in it are linearly dependent.
  let P : Ideal ℤ_[p] := Ideal.span {(p : ℤ_[p])}
  have h_torsion : IsTorsionBy ℤ_[p] (T ⧸ L'.submoduleOf T) p :=
    (isTorsionBy_quotient_iff _ _).2 fun x ↦ h_kill x x.2
  let : Module (ℤ_[p] ⧸ P) (T ⧸ L'.submoduleOf T) := h_torsion.module
  have : P.IsMaximal := PadicInt.prime_p.isMaximal_span_singleton
  let := Ideal.Quotient.field P
  have h_dim : relLength T L' = toENat (Module.rank (ℤ_[p] ⧸ P) (T ⧸ L'.submoduleOf T)) := by
    rw [relLength, length_eq_of_surjective (R := ℤ_[p] ⧸ P) Ideal.Quotient.mk_surjective,
      length_eq_rank]
  rw [h_dim, ← not_lt, ← ENat.natCast_add_one_le_iff, ← Nat.cast_add_one, natCast_le_toENat,
    le_rank_iff]
  rintro ⟨x, h_indep⟩
  obtain ⟨y, rfl⟩ : ∃ y : Fin (m + 1) → T, (L'.submoduleOf T).mkQ ∘ y = x :=
    (mkQ_surjective _).comp_left x
  obtain ⟨a, j, haj, h_sum⟩ := h_rel y
  have h_relation : ∑ i, Ideal.Quotient.mk P (a i) • (L'.submoduleOf T).mkQ (y i) = 0 := by
    change ∑ i, (L'.submoduleOf T).mkQ (a i • y i) = 0
    rw [← map_sum, mkQ_apply, Quotient.mk_eq_zero]
    exact_mod_cast h_sum
  -- independence would force `a j = 1` to vanish modulo `p`
  have h_coeff : Ideal.Quotient.mk P (a j) = 0 :=
    Fintype.linearIndependent_iff.1 h_indep (fun i ↦ Ideal.Quotient.mk P (a i)) h_relation j
  simp [haj] at h_coeff

/-- Suppose `p ^ t L ≤ L'`, and that any `m + 1` elements `x j` of `L` with `p x j ∈ L'` have a
combination `∑ a j • x j` in `L'` with some coefficient `a j = 1`. Then `L / (L ⊓ L')` has length
at most `t m`. -/
lemma relLength_le_of_relations (t : ℕ) (h_kill : ∀ x ∈ L, p ^ t • x ∈ L')
    (h_rel : ∀ x : Fin (m + 1) → V,
      (∀ j : Fin (m + 1), x j ∈ L ∧ (p : ℤ_[p]) • x j ∈ L') →
      ∃ (a : Fin (m + 1) → ℤ_[p]) (j : Fin (m + 1)), a j = 1 ∧ ∑ i : Fin (m + 1), a i • x i ∈ L') :
    relLength L L' ≤ ↑(t * m) := by
  induction t generalizing L' with
  | zero => simpa [IsConcreteLE.le_iff] using h_kill
  | succ t ih =>
    -- Filter by `T = {x ∈ L | p • x ∈ L'}`. The hypotheses hold for `T` in place of `L'` with the
    -- exponent `t`: for the relation among the `x j` apply `h_rel` to the `p • x j`.
    let T : Submodule ℤ_[p] V := L ⊓ L'.comap (LinearMap.lsmul ℤ_[p] V p)
    have h_mem (x : V) : x ∈ T ↔ x ∈ L ∧ (p : ℤ_[p]) • x ∈ L' := Iff.rfl
    have h_top : relLength L T ≤ ↑(t * m) := by
      refine ih (fun x hx ↦ (h_mem _).2 ⟨nsmul_mem hx _, ?_⟩) fun x hx ↦ ?_
      · simpa [pow_succ', mul_smul, Nat.cast_smul_eq_nsmul] using h_kill x hx
      · obtain ⟨a, j, haj, h_sum⟩ := h_rel _ fun j ↦ (h_mem _).1 (hx j).2
        refine ⟨a, j, haj, (h_mem _).2 ⟨sum_smul_mem L a fun i _ ↦ (hx i).1, ?_⟩⟩
        simpa [Finset.smul_sum, ← mul_smul, mul_comm] using h_sum
    have h_bottom : relLength T L' ≤ m :=
      relLength_le_of_prime_smul_mem (fun x hx ↦ ((h_mem x).1 hx).2) fun x ↦
        h_rel (fun i ↦ x i) fun i ↦ (h_mem _).1 (x i).2
    simpa [add_one_mul] using relLength_trans h_top h_bottom

end New.Lift

end RelativeLength

namespace New.Selmer

/-!
## The Fitting ideal of a quotient under added relations

The zeroth Fitting ideal `New.Selmer.fittingIdeal N` of a quotient `R^ι / N`, defined by
determinants of square matrices with rows in `N`, and how it changes when `N` grows.
-/

section FittingIdeal

open Matrix Submodule Function

variable {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (N : Submodule R (ι → R))

/-- The ideal of R generated by the determinants of square matrices with all rows in N ⊆ R^ι:
the zeroth Fitting ideal of R^ι modulo N. -/
def fittingIdeal : Ideal R := Ideal.span (det '' {B : Matrix ι ι R | ∀ i : ι, B i ∈ N})

variable {N}

/-- Adding the relations `I • ⊤` to `N` changes the zeroth Fitting ideal only modulo `I`: for every
ideal `I`, the Fitting ideal of `N ⊔ I • ⊤` is contained in `fittingIdeal N ⊔ I`.

This is one inclusion of the base change property of Fitting ideals along `R → R ⧸ I`, stated
inside `R`. -/
lemma fittingIdeal.sup_smul_top_le {I : Ideal R} :
    fittingIdeal (N ⊔ I • ⊤) ≤ fittingIdeal N ⊔ I := by
  -- Write each row of `B` as `n i + m i` with `n i ∈ N` and `m i ≡ 0` modulo `I`; then
  -- `det B ≡ det n` modulo `I`.
  refine span_le.2 (Set.forall_mem_image.2 fun B hB ↦ ?_)
  choose n hn m hm h_row using fun (i : ι) ↦ mem_sup.1 (hB i)
  have h_zero (i j : ι) : Ideal.Quotient.mk I (m i j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using smul_top_le_comap_smul_top I (.proj j) (hm i))
  have h_det : det B - det (of n) ∈ I := Ideal.Quotient.eq.1 (by simp [det_apply', ← h_row, h_zero])
  exact mem_sup.2 ⟨det (of n), subset_span ⟨of n, hn, rfl⟩, _, h_det, add_sub_cancel _ _⟩

/-- If `r • v ∈ N` and each row of the square matrix `s` lies in `N` or is equal to `v`, then
`r * det s` lies in the Fitting ideal of `N`. -/
lemma mul_det_mem_fittingIdeal {r : R} {v : ι → R} (h_smul : r • v ∈ N) {s : Matrix ι ι R}
    (hs : ∀ i : ι, s i ∈ N ∨ s i = v) :
    r * det s ∈ fittingIdeal N := by
  by_cases! h_all : ∀ a : ι, s a ∈ N
  · exact Ideal.mul_mem_left _ r (subset_span ⟨s, h_all, rfl⟩)
  obtain ⟨i, hi⟩ := h_all
  have hiv : s i = v := (hs i).resolve_left hi
  by_cases h_two : ∃ j : ι, j ≠ i ∧ s j = v
  · -- Two rows are equal.
    obtain ⟨j, hj, hjv⟩ := h_two
    simp [det_zero_of_row_eq hj (hjv.trans hiv.symm)]
  · -- Multiplying row `i` by `r` puts all rows in `N`.
    refine subset_span ⟨s.updateRow i (r • s i), fun j ↦ ?_, by simp [det_updateRow_smul]⟩
    obtain rfl | hji := eq_or_ne j i
    · simpa [hiv]
    · simpa [hji] using (hs j).resolve_right fun hjv ↦ h_two ⟨j, hji, hjv⟩

/-- If `r • v ∈ N`, then `r * d` lies in `fittingIdeal N` for every `d` in the Fitting ideal of
`N ⊔ R ∙ v`. In other words, adding the vector `v` to the relations costs at most the factor `r`.

This is a case of the inclusion `Fitt(M') * Fitt(M'') ≤ Fitt(M)` for an exact sequence
`M' → M → M'' → 0`: here `M' = R / (r)` maps to `M = R^ι / N` by `1 ↦ v`. -/
lemma fittingIdeal.mul_mem_of_smul_mem {r : R} {v : ι → R} (h_smul : r • v ∈ N) :
    ∀ d ∈ fittingIdeal (N ⊔ R ∙ v), r * d ∈ fittingIdeal N := by
  -- Each row of `B` is a combination of `v` and of elements of `N`. Expand `det B` in the rows.
  refine (span_le (p := comap (.mulLeft R r) (fittingIdeal N))).2
    (Set.forall_mem_image.2 fun B hB ↦ ?_)
  change r * det B ∈ fittingIdeal N
  have h_comb (i : ι) :
      ∃ c : (ι → R) →₀ R, ↑c.support ⊆ (N : Set (ι → R)) ∪ {v} ∧ ∑ w ∈ c.support, c w • w = B i :=
    mem_span_set.1 (by simpa only [← N.sup_span] using hB i)
  choose c hc h_row using h_comb
  have h_expand :
      det B = ∑ s ∈ Fintype.piFinset fun i ↦ (c i).support, (∏ i, c i (s i)) * det (of s) := by
    -- The determinant is multilinear in the rows.
    change detRowAlternating.toMultilinearMap B = _
    rw [← funext h_row, MultilinearMap.map_sum_finset]
    exact Finset.sum_congr rfl fun s _ ↦ det_mul_column (fun i ↦ c i (s i)) s
  rw [h_expand, Finset.mul_sum]
  -- In each term, every row of `s` lies in `N` or equals `v`.
  refine sum_mem fun s hs ↦ ?_
  rw [mul_left_comm]
  exact Ideal.mul_mem_left _ _
    (mul_det_mem_fittingIdeal h_smul fun i ↦ hc i (Fintype.mem_piFinset.1 hs i))

/-- Let `I` be a finite ordered set of indices. Suppose that for each `j ∈ I`, every submodule
`K ≥ N` that contains the `v i` with `i ∈ I`, `i < j` also contains `r j • v j`. Then there is
`K ≥ N` containing all `v j`, `j ∈ I`, such that `∏ j ∈ I, r j` multiplies `fittingIdeal K` into
`fittingIdeal N`.

This is the submultiplicativity of Fitting ideals along exact sequences, in the form
`fittingIdeal.mul_mem_of_smul_mem`, iterated along the filtration by the `v j`, whose steps are
cyclic modules killed by the `r j`. -/
lemma fittingIdeal.exists_ge_mul_prod_mem {J : Type*} [LinearOrder J] {I : Finset J} {v : J → ι → R}
    (r : J → R)
    (h_step : ∀ j ∈ I, ∀ K : Submodule R (ι → R), N ≤ K → ↑I ∩ Set.Iio j ⊆ v ⁻¹' K →
      r j • v j ∈ K) :
    ∃ K : Submodule R (ι → R), N ≤ K ∧ ↑I ⊆ v ⁻¹' K ∧
      ∀ d ∈ fittingIdeal K, d * ∏ j ∈ I, r j ∈ fittingIdeal N := by
  -- Induction on `I`, adding a largest index `e`: pass from `K` to `K ⊔ R ∙ v e` by
  -- `fittingIdeal.mul_mem_of_smul_mem`.
  induction I using Finset.induction_on_max with
  | empty => exact ⟨N, le_rfl, by simp, by simp⟩
  | insert e s h_max ih =>
    obtain ⟨K, hNK, hsK, hK⟩ := ih fun j hj K hNK h_below ↦ by
      refine h_step j (Finset.mem_insert_of_mem hj) K hNK fun i hi ↦ h_below ?_
      -- The new index `e` is larger than `j`, so `i ≠ e`.
      have hje : j < e := h_max j hj
      grind
    have he : r e • v e ∈ K := h_step e (Finset.mem_insert_self e s) K hNK fun i ⟨hi, hie⟩ ↦
      hsK ((Finset.mem_insert.1 hi).resolve_left (ne_of_lt hie))
    refine ⟨K ⊔ R ∙ v e, le_sup_of_le_left hNK, ?_, fun d hd ↦ ?_⟩
    · rw [Finset.coe_insert, Set.insert_subset_iff]
      exact ⟨mem_sup_right (mem_span_singleton_self (v e)), fun i hi ↦ mem_sup_left (hsK hi)⟩
    · rw [Finset.prod_insert fun he_mem ↦ (h_max e he_mem).false, ← mul_assoc, mul_comm d]
      exact hK (r e * d) (mul_mem_of_smul_mem he d hd)

end FittingIdeal

/-!
## Linear forms modulo p and the cost of a length in the Fitting ideal

Let `O` be a discrete valuation ring, `Φ : O^n → R^ι` an `O`-linear map and `N ≤ R^ι` a submodule
with `Φ (p • O^n) ⊆ N`, `p ≠ 0`. The quotient `O^n / Φ⁻¹ N` is studied through its linear forms with
values in `O / p`.
-/

section FittingDuality

open Submodule Module IsDiscreteValuationRing

variable {O R G n ι : Type} [CommRing O] [DVR O] [CommRing R] [Algebra O R]
  (Φ : (n → O) →ₗ[O] ι → R) (z : G → n → O) (N : Submodule R (ι → R)) (p : O)

/-- The module of the functions `g ↦ Ψ (z g)` on `G`, where `Ψ : O^n → O / p` runs over the
`O`-linear maps that vanish on `Φ⁻¹ N`. The values are taken in `Unit → O / p`, vectors of
length one, as for cocycles of a representation of rank one. -/
noncomputable def formsMod : Submodule O (G → Unit → QuotSpan p) :=
  (((N.restrictScalars O).comap Φ).compatibleMaps ⊥).map
    (LinearMap.pi fun g ↦ LinearMap.applyₗ (z g))

omit [DVR O] in
variable {Φ z N p} in
/-- A function lies in `formsMod Φ z N p` if and only if it is `Ψ ∘ z` for an `O`-linear map
`Ψ : O^n → O / p` that vanishes on every `v` with `Φ v ∈ N`. -/
lemma mem_formsMod {f : G → Unit → QuotSpan p} :
    f ∈ formsMod Φ z N p ↔
      ∃ Ψ : (n → O) →ₗ[O] Unit → QuotSpan p,
        (∀ ⦃v : n → O⦄, Φ v ∈ N → Ψ v = 0) ∧ Ψ ∘ z = f :=
  Iff.rfl

omit [DVR O] in
variable {Φ p} in
/-- Enlarging `N` imposes more conditions on the forms `Ψ`, so `formsMod Φ z N p` shrinks. -/
lemma formsMod_anti {N N' : Submodule R (ι → R)} (h_le : N ≤ N') :
    formsMod Φ z N' p ≤ formsMod Φ z N p := by
  rintro f ⟨Ψ, hΨ, rfl⟩
  exact mem_formsMod.2 ⟨Ψ, fun v hv ↦ hΨ (h_le hv), rfl⟩

variable {Φ N p}

/-- Duality. Let `p ≠ 0` with `Φ (p • O^n) ⊆ N`. If every `O`-linear map `Ψ : O^n → O / p` (with
values written in `Unit → O / p`) vanishing on `Φ⁻¹ N` vanishes at `v`, then `Φ v ∈ N`. -/
lemma mem_of_forall_form_eq_zero [Fintype n] (hp : p ≠ 0) (hN : ∀ v : n → O, Φ (p • v) ∈ N)
    {v : n → O}
    (h_kill : ∀ Ψ : (n → O) →ₗ[O] Unit → QuotSpan p, (∀ ⦃u : n → O⦄, Φ u ∈ N → Ψ u = 0) → Ψ v = 0) :
    Φ v ∈ N := by
  classical
  -- `Φ⁻¹ N` is the annihilator of a module `S` of vectors modulo `p`, and each `w ∈ S` gives a
  -- linear form that vanishes on `Φ⁻¹ N`.
  obtain ⟨-, S, -, (hS : ∀ u : n → O, Φ u ∈ N ↔ ∀ w ∈ S, ∑ j : n, u j • w j = 0), -⟩ :=
    exists_matrix_addVal_det_le_length ((N.restrictScalars O).comap Φ) hp hN
  refine (hS v).2 fun w hw ↦ ?_
  let Ψ : (n → O) →ₗ[O] Unit → QuotSpan p := .pi fun _ ↦ Fintype.linearCombination O w
  have hΨ : ∀ ⦃u : n → O⦄, Φ u ∈ N → Ψ u = 0 := fun u hu ↦ by
    simpa [Ψ, funext_iff, Fintype.linearCombination_apply] using (hS u).1 hu w hw
  exact congrFun (h_kill Ψ hΨ) ()

omit [DVR O] in
/-- If `Φ (p • O^n) ⊆ N`, `p` is associated to `ϖ ^ m` and `Φ v ∉ N`, then for some `k` the vector
`Φ (ϖ ^ k • v)` is outside `N` and `Φ (ϖ ^ (k + 1) • v)` is inside. -/
lemma exists_pow_smul_notMem_and_succ_mem {ϖ : O} {m : ℕ} {v : n → O}
    (hp_pow : Associated p (ϖ ^ m)) (hN : ∀ v : n → O, Φ (p • v) ∈ N) (hvN : Φ v ∉ N) :
    ∃ k : ℕ, Φ (ϖ ^ k • v) ∉ N ∧ Φ (ϖ ^ (k + 1) • v) ∈ N := by
  obtain ⟨u, hu⟩ := hp_pow
  have h_pow : Φ (ϖ ^ m • v) ∈ N := by simpa [← hu, mul_smul] using hN ((u : O) • v)
  exact Nat.exists_not_and_succ_of_not_zero_of_exists (by simpa using hvN) ⟨m, h_pow⟩

/-- Let `O` be a discrete valuation ring, `R` an `O`-algebra, `Φ : O^n → R^ι` an `O`-linear map
with `n` finite, and `z` a family of vectors of `O^n` indexed by `G`. For `p : O` and a submodule
`N` of `R^ι`, `formsMod Φ z N p` is the module of the functions `Ψ ∘ z` on `G`, where `Ψ` runs over
the `O`-linear forms `O^n → O / p` that vanish on `Φ⁻¹ N`; values in `O / p` are written as vectors
of length one, in `Unit → QuotSpan p`.

Assume `p ≠ 0` and `Φ (p • O^n) ⊆ N ≤ N'`. Let `V` be an `O`-module of functions `G → O / p` and
`v` a vector killed by every form `Ψ` with `Ψ ∘ z ∈ V`. If `Φ (a • v)` lies in `N'` but not in `N`
for some `a : O`, then the image of `formsMod Φ z N' p` in the quotient by `V` is strictly smaller
than the image of `formsMod Φ z N p`. -/
lemma map_mkQ_formsMod_lt {O R G n ι : Type} [CommRing O] [DVR O] [CommRing R] [Algebra O R]
    {Φ : (n → O) →ₗ[O] ι → R} (z : G → n → O) {N : Submodule R (ι → R)} {p : O} [Fintype n]
    (hp : p ≠ 0) (hN : ∀ u : n → O, Φ (p • u) ∈ N)
    {N' : Submodule R (ι → R)} (h_le : N ≤ N') {V : Submodule O (G → Unit → QuotSpan p)}
    {v : n → O} (h_kill : ∀ Ψ : (n → O) →ₗ[O] Unit → QuotSpan p, Ψ ∘ z ∈ V → Ψ v = 0) {a : O}
    (h_notMem : Φ (a • v) ∉ N) (h_mem : Φ (a • v) ∈ N') :
    (formsMod Φ z N' p).map V.mkQ < (formsMod Φ z N p).map V.mkQ := by
  -- If the images agree, each `Ψ` killing `Φ⁻¹ N` agrees modulo `V` with some `Ψ'` killing
  -- `Φ⁻¹ N'`. Then `Ψ' v = Ψ v`, so `Ψ` kills `a • v`, and duality gives `Φ (a • v) ∈ N`.
  refine lt_of_le_not_ge (map_mono (formsMod_anti z h_le)) fun h_ge ↦ h_notMem ?_
  refine mem_of_forall_form_eq_zero hp hN fun Ψ hΨ ↦ ?_
  have h_form : Ψ ∘ z ∈ formsMod Φ z N p := mem_formsMod.2 ⟨Ψ, hΨ, rfl⟩
  obtain ⟨_, ⟨Ψ', hΨ', rfl⟩, h_mod⟩ : ∃ f ∈ formsMod Φ z N' p, V.mkQ f = V.mkQ (Ψ ∘ z) :=
    mem_map.1 (h_ge (mem_map_of_mem h_form))
  have h_sub : Ψ' ∘ z - Ψ ∘ z ∈ V := (Submodule.Quotient.eq V).1 h_mod
  have h_eq : Ψ' v = Ψ v := sub_eq_zero.1 (h_kill (Ψ' - Ψ) h_sub)
  calc Ψ (a • v) = Ψ' (a • v) := by rw [map_smul, map_smul, h_eq]
    _ = 0 := hΨ' h_mem

/-- Let `p ≠ 0`, `Φ (p • O^n) ⊆ N`, and let `V` be an `O`-module of functions on `G` with values in
`O / p`. There are `c : O` and `K ≥ N` such that (a) the valuation of `c` is at most the length
modulo `V` of `formsMod Φ z N p`, the functions `g ↦ Ψ (z g)` for the linear `Ψ : O^n → O / p`
that vanish on `Φ⁻¹ N`; (b) `K` contains `Φ v` whenever every linear `Ψ` with `Ψ ∘ z ∈ V` kills
`v`; (c) `c` multiplies `fittingIdeal K`, the zeroth Fitting ideal of `R^ι / K`, into
`fittingIdeal N`.

This is a relative, dual form of the bound of a Fitting ideal by length over a discrete valuation
ring, for Noetherian `R`. -/
lemma fittingIdeal.exists_addVal_le_relLength [Fintype n] (hp : p ≠ 0)
    (hN : ∀ v : n → O, Φ (p • v) ∈ N) [IsNoetherianRing R] [Fintype ι] [DecidableEq ι]
    (V : Submodule O (G → Unit → QuotSpan p)) :
    ∃ (c : O) (K : Submodule R (ι → R)), N ≤ K ∧
      -- (a)
      addVal O c ≤ relLength (formsMod Φ z N p) V ∧
      -- (b)
      (∀ ⦃v : n → O⦄, (∀ Ψ : (n → O) →ₗ[O] Unit → QuotSpan p, Ψ ∘ z ∈ V → Ψ v = 0) → Φ v ∈ K) ∧
      -- (c)
      ∀ d ∈ fittingIdeal K, c • d ∈ fittingIdeal N := by
  -- Noetherian induction on `N`. If `K = N` fails (b), enlarge `N` by one vector `x` with
  -- `ϖ • x ∈ N`, `ϖ` a uniformiser: `ϖ` takes the new Fitting ideal into the old one, and the
  -- length of `formsMod` modulo `V` drops.
  induction N using IsNoetherian.induction with | _ N ih => ?_
  by_cases! h_base : ∀ v : n → O,
    (∀ Ψ : (n → O) →ₗ[O] Unit → QuotSpan p, Ψ ∘ z ∈ V → Ψ v = 0) → Φ v ∈ N
  · exact ⟨1, N, le_rfl, by simp, h_base, by simp⟩
  obtain ⟨v, hv, hvN⟩ := h_base
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible O
  -- `p` is a power of `ϖ` up to a unit and `Φ (p • O^n) ⊆ N`, so some `Φ (ϖ ^ k • v)` is outside
  -- `N` with `Φ (ϖ ^ (k + 1) • v)` in `N`.
  obtain ⟨m, hm⟩ := associated_pow_irreducible hp hϖ
  obtain ⟨k, hk, hk_succ⟩ := exists_pow_smul_notMem_and_succ_mem hm hN hvN
  let N' : Submodule R (ι → R) := N ⊔ R ∙ Φ (ϖ ^ k • v)
  obtain ⟨c, K, hK, h_len, h_mem, h_fitting⟩ :=
    ih N' (lt_sup_iff_notMem.2 hk) fun w ↦ mem_sup_left (hN w)
  refine ⟨c * ϖ, K, le_sup_left.trans hK, ?_, h_mem, fun d hd ↦ ?_⟩
  · -- The image of `formsMod` modulo `V` is strictly smaller for `N'` than for `N`, so the length
    -- for `N` exceeds that for `N'` by at least 1, the valuation of `ϖ`.
    have h_drop : map V.mkQ (formsMod Φ z N' p) < map V.mkQ (formsMod Φ z N p) :=
      map_mkQ_formsMod_lt z hp hN le_sup_left hv hk (mem_sup_right (mem_span_singleton_self _))
    grw [addVal_mul, addVal_uniformizer hϖ, h_len]
    simpa only [relLength_eq_length_map_mkQ, length_submodule] using Order.height_add_one_le h_drop
  · have h_smul : (ϖ • 1 : R) • Φ (ϖ ^ k • v) ∈ N := by simpa [pow_succ', mul_smul] using hk_succ
    simpa [mul_smul] using mul_mem_of_smul_mem h_smul _ (h_fitting d hd)

end FittingDuality

end New.Selmer

end
