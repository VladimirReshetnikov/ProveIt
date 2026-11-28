import Lib.GaloisRep.BaseChange.CongruenceLevelMatching
import Lib.GaloisRep.BaseChange.StepMatchingPairs
import Lib.GaloisRep.BaseChange.TwistedTraceIdentity

/-!
# Base change in prime degree for definite U(n): a weak base change eigenform

Base change of algebraic modular forms on the definite unitary group along a step E'/E of prime
degree (`New.IsStep`), from the twisted trace identity `New.twisted_trace_identity`.

* `New.IsWeakBaseChange`: f' is a weak base change of f off a finite set of places.
* `New.IsLocalMatching`: matching test functions over E and E' above a finite set Z of places.
* `New.exists_isWeakBaseChange_of_matching`: an eigenform over E' that is a weak base change of f
  and has prescribed eigenvalues for the local operators.

Notions from other files that the statements use:
* `New.IsStep E' μ`: `E` contains a primitive 5040th root of unity, `E'` is a CM field, Galois of
  prime degree over `E`, with an integer of trace `1`, and `μ` is a character of the finite ideles
  of `E` with open kernel, trivial on `E^×`, such that `μ (z z̄) = 1` exactly when `z` is an element
  of `E^×` times the norm of a finite idele of `E'`.
* `Z.conjClosure` is `Z ∪ Z̄`, and `New.placesAbove E' Z` is the set of places of `E'` above it.
* `New.sphericalAt π w`: the vectors fixed by the integral elements supported at `w` and `w̄`.
  `New.HasHeckePolyAt f w hw P`: `f` is spherical at `w` and an eigenvector of each `New.heckeSplit`
  there, and `P` is built from the eigenvalues and the norm of `w`.
* `New.IsMatchingPairAbove σ μ Z K f φ`: `(f, φ)` is a matching pair of test functions for the
  twisted trace identity at the places above `Z`, at level `K`.
* `New.heckeFun ρ L F` is the Hecke operator `∑_{g ∈ G/L} F g • ρ g`, `New.levelSpace ρ L` is the
  `L`-fixed space, and `New.Weight.baseChange` is the weight pulled back to `E'`.

## Relation to the literature

Known result: Cyclic base change of prime degree for definite unitary groups (weak lift, local
matching). Here the lift goes from U(n) over E to U(n) over E' rather than to GL_n, with E'/E tame
and E containing enough roots of unity, and only existence is proved. Hecke polynomials match where
the place splits completely and an auxiliary character is trivial, tame types are kept, and class
sums are compared directly, without stabilisation. Source: J.-P. Labesse, Changement de base CM et
séries discrètes, in On the stabilization of the trace formula, 2011, Cor. 5.3, and Cohomologie,
stabilisation et changement de base, Astérisque 257, 1999; J. Arthur and L. Clozel, Simple algebras,
base change, and the advanced theory of the trace formula, Ann. Math. Studies 120, 1989; local
matching after P. Scholze, The Langlands-Kottwitz approach for some simple Shimura varieties, 2013,
Prop. 2.1 (norms inverted inside O[γ]) and J.-P. Labesse, Fonctions élémentaires et lemme
fondamental pour le changement de base stable, Duke Math. J. 61, 1990.
-/

namespace New

open NumberField Filter Module End Gf Submodule Set

variable {E E' n : Type _} [Field E] [CMType E] [Field E'] [Algebra E E'] [CMTypeOver E E']
  [Fintype n] [DecidableEq n]

/-- `f'` is a weak base change of `f` off the set `Z` of places of `E`: `Z` is finite, and for every
place `w` of `E` outside `Z ∪ Z̄` and every place `u` of `E'` above `w`,
* if `w` is unramified in the step (`New.IsStepUnramifiedAt`) and `f` is spherical at `w`, then
`f'` is spherical at `u`;
* if `w` is matched (`New.IsMatched`: `μ` is trivial on `E_w^×`, and each place above `w` has the
  norm of `w` and is moved by every `σ ≠ 1`) and split, then for every Hecke polynomial `P` of `f`
  at `w` (`New.HasHeckePolyAt`) the place `u` is split and `P` is a Hecke polynomial of `f'` at
  `u`. -/
def IsWeakBaseChange (μ : (𝔸f E)ˣ →* ℂˣ) {M M' : Type} (Z : Set (FinPlace E))
    (f : Gf E n → M → ℂ) (f' : Gf E' n → M' → ℂ) : Prop :=
  Z.Finite ∧ ∀ w : FinPlace E, w ∉ Z.conjClosure → ∀ u : FinPlace E', u.below E = w →
    (IsStepUnramifiedAt E' μ w → f ∈ sphericalAt (rightRegular ℂ (Gf E n) (M → ℂ)) w →
      f' ∈ sphericalAt (rightRegular ℂ (Gf E' n) (M' → ℂ)) u) ∧
    (IsMatched E' μ w → ∀ (hw : w.IsSplit) (P : Polynomial ℂ), HasHeckePolyAt f w hw P →
      ∃ hu : u.IsSplit, HasHeckePolyAt f' u hu P)

/-- Matching local data above a set `Z` of places of `E`, for groups `G`, `G'` mapped into the
finite adelic unitary groups over `E` and `E'` by `a`, `a'`. There are `σ ≠ 1` in `Gal(E'/E)` and
retractions `r`, `r'` (`New.IsLocalRetraction`: `a` lands in the elements supported on `Z ∪ Z̄`,
`r ∘ a = id`, and the kernel of `r` is the elements trivial on `Z`; likewise for `a'`, `r'` and the
places of `E'` above `Z`) such that
* each `F j` is bi-invariant under `L`, and each `F' j` under `L'`;
* `Z` is finite, and `L'` is stable under `σ` (through `r'`);
* the preimage of `L'` in `Gf E' n` is open, and its preimage under base change is the preimage
  of `L` in `Gf E n`;
* some level `K` between the preimage of `L'` and the integral level above `Z` has split
  `σ`-cocycles (`New.CocyclesSplit`), and for `j ∈ P` the pair `(F j ∘ r, F' j ∘ r')` matches above
  `Z` at level `K`. -/
def IsLocalMatching (μ : (𝔸f E)ˣ →* ℂˣ) (Z : Set (FinPlace E)) {G G' J : Type*} [Group G]
    [Group G'] (a : G →* Gf E n) (a' : G' →* Gf E' n) (L : Subgroup G) (L' : Subgroup G')
    (P : Set J) (F : J → G → ℂ) (F' : J → G' → ℂ) : Prop :=
  ∃ σ ≠ (1 : Gal(E'/E)), ∃ (r : Gf E n →* G) (r' : Gf E' n →* G'),
    ((∀ j : J, IsHeckeFunction L (F j) ∧ IsHeckeFunction L' (F' j)) ∧
      IsLocalRetraction a r Z ∧
      IsLocalRetraction a' r' (placesAbove E' Z) ∧
      Z.Finite ∧
      ∀ k : Gf E' n, r' (galoisGf σ k) ∈ L' ↔ r' k ∈ L') ∧
    (L'.comap r').comap baseChangeGf = L.comap r ∧
    (L'.comap r').IsOpen ∧
    ∃ K ∈ Icc (L'.comap r') (localLevel n (placesAbove E' Z)),
      CocyclesSplit (finrank E E') (idem (placesAbove E' Z)) K (galoisGf σ) ∧
      P ⊆ {j : J | IsMatchingPairAbove σ μ Z K (F j ∘ r) (F' j ∘ r')}

variable {μ : (𝔸f E)ˣ →* ℂˣ}

/-- For the empty set of places and trivial local groups, the constant functions 1 are matching
local data (`New.IsLocalMatching`). -/
lemma isLocalMatching_empty [hμ : IsStep (E := E) E' μ] :
    IsLocalMatching μ ∅ (1 : Unit →* Gf E n) (1 : Unit →* Gf E' n) ⊤ ⊤ {()} 1 1 := by
  -- Take the whole group for `K`; the idempotent of the empty set of places is `0`.
  have h_idem : idem ∅ = (0 : 𝔸f E') := by
    ext u
    simp
  obtain ⟨σ, hσ⟩ : ∃ σ : Gal(E'/E), σ ≠ 1 := hμ.exists_gal_ne_one
  -- Take some `σ ≠ 1` and the trivial retractions. The empty set is finite, and `⊤` is open and
  -- `σ`-stable, with pull-back `⊤` under base change.
  refine ⟨σ, hσ, 1, 1, ⟨?_, ?_, ?_, toFinite _, by simp⟩, by simp, isOpen_univ, ⊤, ?_, ?_, ?_⟩
  · simp [IsHeckeFunction, toFinite]
  · simp [IsLocalRetraction, trivialOn]
  · simp [IsLocalRetraction, trivialOn, placesAbove]
  · -- The level above no place is the whole group.
    exact ⟨le_top, fun g _ ↦ mem_localLevel.mpr (by simp [placesAbove])⟩
  · -- Above no place every cocycle splits, with `t = 1`.
    exact fun s _ _ ↦ ⟨1, Subgroup.mem_top 1, by simp [placesAbove, h_idem]⟩
  · -- With the idempotent `0`, the matching conditions for the constant functions `1` hold.
    simp [placesAbove, IsMatchingPair, IsNormRoot, IsRootQuotient, twistedNorm_map_eq_prod, h_idem]

/-- Let `S` be a `σ`-stable set of places of `E'`. Suppose that `K` contains the elements trivial on
`S` and that its `σ`-cocycles split on `S` (`New.CocyclesSplit`: each `s ∈ K` of twisted norm
`s · σ s ⋯ σ^{q-1} s = 1` has some `t ∈ K` that is `1` off `S` with `t⁻¹ * s * σ t = 1` on `S`), and
that `N` does the same with `S` and `Sᶜ` exchanged. Then every `s ∈ K ⊓ N` of twisted norm `1` is a
coboundary: `σ t = s⁻¹ * t` for some `t ∈ K ⊓ N`. -/
lemma exists_mem_inf_galoisGf_eq_inv_mul_of_cocyclesSplit {σ : Gal(E'/E)} {S : Set (FinPlace E')}
    {K N : Subgroup (Gf E' n)}
    {q : ℕ} (S_σ : ∀ w : FinPlace E', w.comap σ ∈ S ↔ w ∈ S) (hK : trivialOn n S ≤ K)
    (hN : trivialOn n Sᶜ ≤ N) (K_coh : CocyclesSplit q (idem S) K (galoisGf σ))
    (N_coh : CocyclesSplit q (idem Sᶜ) N (galoisGf σ)) (s : Gf E' n) (hs : s ∈ K ⊓ N)
    (hs_norm : twistedNorm (galoisGf σ) q s = 1) : ∃ t ∈ K ⊓ N, galoisGf σ t = s⁻¹ * t := by
  obtain ⟨hs_K, hs_N⟩ := Subgroup.mem_inf.mp hs
  obtain ⟨t, t_mem, t_off, ht⟩ := K_coh s hs_K hs_norm
  obtain ⟨t', t'_mem, t'_off, ht'⟩ := N_coh s hs_N hs_norm
  -- Place by place: `t` is `1` off `S` and satisfies `σ t = s⁻¹ * t` on `S`; `t'` is `1` on `S`
  -- and satisfies `σ t' = s⁻¹ * t'` off `S`. So `t * t'` solves the equation everywhere.
  have t_triv : t ∈ trivialOn n Sᶜ := by rwa [← idem_compl, idem_smul_eq_iff_mem_trivialOn] at t_off
  have t'_triv : t' ∈ trivialOn n S := by
    rwa [idem_compl, sub_sub_cancel, idem_smul_eq_iff_mem_trivialOn] at t'_off
  have ht_triv : t⁻¹ * s * galoisGf σ t ∈ trivialOn n S := idem_smul_eq_iff_mem_trivialOn.mp ht
  have ht'_triv : t'⁻¹ * s * galoisGf σ t' ∈ trivialOn n Sᶜ := idem_smul_eq_iff_mem_trivialOn.mp ht'
  -- At a place where `r⁻¹ * s * σ r` is `1`, the component of `σ r` is that of `s⁻¹ * r`.
  have galoisGf_atPlace_eq (r : Gf E' n) (w : FinPlace E')
      (hr : (r⁻¹ * s * galoisGf σ r).atPlace w = 1) :
      (galoisGf σ r).atPlace w = (s.atPlace w)⁻¹ * r.atPlace w := by
    rw [map_mul, map_mul, map_inv, mul_assoc, inv_mul_eq_one] at hr
    rw [hr, ← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨t * t', mul_mem ⟨t_mem, hN t_triv⟩ ⟨hK t'_triv, t'_mem⟩, Gf.ext fun w ↦ ?_⟩
  by_cases hw : w ∈ S
  · -- `t'` is `1` at `w` and at `w.comap σ`.
    have h_t' : atPlace w t' = 1 := mem_trivialOn.mp t'_triv w hw
    have h_σt' : atPlace w (galoisGf σ t') = 1 := by
      rw [atPlace_galoisGf σ t' rfl, mem_trivialOn.mp t'_triv _ ((S_σ w).mpr hw), map_one]
    have h_σt : atPlace w (galoisGf σ t) = (atPlace w s)⁻¹ * atPlace w t :=
      galoisGf_atPlace_eq t w (mem_trivialOn.mp ht_triv w hw)
    simp only [map_mul, map_inv, h_t', h_σt', h_σt, mul_one]
  · -- `t` is `1` at `w` and at `w.comap σ`.
    have h_t : atPlace w t = 1 := mem_trivialOn.mp t_triv w hw
    have h_σt : atPlace w (galoisGf σ t) = 1 := by
      rw [atPlace_galoisGf σ t rfl, mem_trivialOn.mp t_triv _ (fun h ↦ hw ((S_σ w).mp h)), map_one]
    have h_σt' : atPlace w (galoisGf σ t') = (atPlace w s)⁻¹ * atPlace w t' :=
      galoisGf_atPlace_eq t' w (mem_trivialOn.mp ht'_triv w hw)
    simp only [map_mul, map_inv, h_t, h_σt, h_σt', one_mul]

/-- Let `t` be a linear map with `t (π g x) = π (σ g) (t x)`, and let `u` and `u.comap σ` be split.
On a vector `x` such that `t x` is spherical at `u`, `t` carries the Hecke operator `T_j` at
`u.comap σ` (`New.heckeSplit`) to the one at `u`. -/
lemma map_heckeSplit_comap {W : Type*} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Gf E' n) W} {σ : Gal(E'/E)} {t : End ℂ W}
    (ht : ∀ (g : Gf E' n) (x : W), t (π g x) = π (galoisGf σ g) (t x)) {u : FinPlace E'}
    (hσu : (u.comap σ).IsSplit) (hu : u.IsSplit) (j : ℕ) {x : W} (hx : t x ∈ sphericalAt π u) :
    t (heckeSplit π hσu j x) = heckeSplit π hu j (t x) := by
  -- View `E'` as an extension of itself through `σ`: `u.comap σ` is the place below `u`.
  let algebra_σ : Algebra E' E' := σ.toAlgHom.toAlgebra
  refine (map_heckeSplit hσu j t fun g _hg ↦ ht g x).trans
    (heckeSplit_comp_baseChangeGf hu hσu (fun y ↦ ?_) hx fun k hk ↦ ?_)
  · -- Through `σ`, the adele `σ⁻¹ (singleAdele u y)` has component `y` at `u`.
    refine ⟨adeleMap ↑σ⁻¹ (singleAdele u y) _, ?_⟩
    have h_comp : (algebraMap E' E').comp (↑σ⁻¹ : E' →+* E') = RingHom.id E' :=
      σ.toRingEquiv.comp_symm
    have h_eval : adeleMap (algebraMap E' E') (adeleMap ↑σ⁻¹ (singleAdele u y)) u = y := by
      rw [adeleMap_adeleMap, h_comp, adeleMap_id, singleAdele_same]
    rwa [adeleMap_apply (algebraMap E' E') rfl] at h_eval
  · -- Only `u` lies above `u.comap σ` for the map `σ`, so `k = 1`.
    have only_u (v : FinPlace E') (hv_below : v.below E' = u.below E') : v = u :=
      v.ext (Ideal.comap_injective_of_surjective _ (MulAction.surjective σ)
        (congrArg (·.asIdeal) hv_below))
    have k_eq : k = 1 := eq_of_supportedOn hk (one_mem _) fun v ⟨hv_below, hv_ne⟩ ↦
      absurd (only_u v hv_below) (notMem_singleton_iff.mp hv_ne)
    simp [k_eq]

section LocalOperators

variable {G M ι : Type*} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)

/-- The `L`-fixed vectors that are generalised eigenvectors of the Hecke operator of `F i` for
the eigenvalue `θ i`, for every `i`. -/
noncomputable def heckeGenEigenspace (L : Subgroup G) (F : ι → G → ℂ) (θ : ι → ℂ) :
    Submodule ℂ M :=
  levelSpace ρ L ⊓ ⨅ i : ι, (heckeFun ρ L (F i)).maxGenEigenspace (θ i)

@[simp]
lemma mem_heckeGenEigenspace {ρ : Representation ℂ G M} {L : Subgroup G} {F : ι → G → ℂ}
    {θ : ι → ℂ} {x : M} :
    x ∈ heckeGenEigenspace ρ L F θ ↔
      x ∈ levelSpace ρ L ∧ ∀ i : ι, x ∈ (heckeFun ρ L (F i)).maxGenEigenspace (θ i) := by
  simp only [heckeGenEigenspace, Submodule.mem_inf, Submodule.mem_iInf]

/-- `T` has non-zero trace on `Y ⊓ W` for every subrepresentation `W` containing `f` such that
`Y ⊓ W` is finite-dimensional and preserved by `T`. -/
def HasNonzeroTraceAround (T : Module.End ℂ M) (Y : Submodule ℂ M) (f : M) : Prop :=
  ∀ W : Subrepresentation ρ, f ∈ W → Module.Finite ℂ ↥(Y ⊓ W.toSubmodule) →
    ∀ h_maps : ∀ x ∈ Y ⊓ W.toSubmodule, T x ∈ Y ⊓ W.toSubmodule,
      (T.restrict h_maps).trace ℂ ↥(Y ⊓ W.toSubmodule) ≠ 0

/-- `g` is fixed by `L`, and the Hecke operator of each `F i` multiplies it by `θ i`. The vector
`g` may be zero. -/
structure IsHeckeEigenvector (L : Subgroup G) (F : ι → G → ℂ) (θ : ι → ℂ) (g : M) : Prop where
  /-- `g` is fixed by `L`. -/
  mem_levelSpace : g ∈ levelSpace ρ L
  /-- The operator of `F i` multiplies `g` by `θ i`. -/
  heckeFun_apply (i : ι) : heckeFun ρ L (F i) g = θ i • g

end LocalOperators

/-- A group `G` with a map `a` to the finite adelic unitary group acts on the forms of weight `κ`
by right translation through `a`. -/
noncomputable abbrev localFormTranslation (κ : Weight E) {G : Type*} [Group G]
    (a : G →* Gf E n) : Representation ℂ G ((stdSpace E n).forms κ) :=
  ((stdSpace E n).formTranslation κ).comp a

/-- Let `w` be a place of `E` off `Z ∪ Z̄`, let `M` contain the elements trivial above `Z ∪ Z̄`, and
let the local level `m u` be the maximal compact subgroup `localIntGL n u` at each place `u` above
`w` or `w̄`. Then the integral elements supported on a set `S` of such places lie in `M` and in the
level given by `m` at the places not above `Z ∪ Z̄`. -/
lemma inf_supportedOn_le_inf_localLevel {Z : Set (FinPlace E)} {M : Subgroup (Gf E' n)}
    {m : (u : FinPlace E') → Subgroup (GL n (LocField u))}
    (hM : trivialOn n (placesAbove E' Z) ≤ M) {w : FinPlace E} (hw : w ∉ Z.conjClosure)
    (hm : ∀ u ∈ placesAbove E' {w}, m u = localIntGL n u) {S : Set (FinPlace E')}
    (hS : S ⊆ placesAbove E' {w}) :
    stdLevel E' n ⊓ supportedOn n S ≤ M ⊓ localLevel n (placesAbove E' Z)ᶜ m := by
  rintro g ⟨g_int, g_supp⟩
  have g_one (u : FinPlace E') (hu : u ∉ placesAbove E' {w}) : g.atPlace u = 1 :=
    mem_supportedOn.mp g_supp u (fun h ↦ hu (hS h))
      (fun h ↦ hu (star_mem_placesAbove.mp (hS h)))
  have h_disjoint (u : FinPlace E') (huZ : u ∈ placesAbove E' Z) : u ∉ placesAbove E' {w} := by
    intro hu_w
    have h_Z : u.below E ∈ Z ∨ star (u.below E) ∈ Z := by simpa [placesAbove] using huZ
    apply hw
    obtain rfl | rfl : u.below E = w ∨ star (u.below E) = w := by simpa [placesAbove] using hu_w
    all_goals simpa [or_comm] using h_Z
  refine ⟨hM (mem_trivialOn.mpr fun u hu ↦ g_one u (h_disjoint u hu)),
    mem_localLevel.mpr fun u _ ↦ ?_⟩
  by_cases hu : u ∈ placesAbove E' {w}
  · rw [hm u hu]
    exact mem_stdLevel_iff.mp g_int u
  · simp [g_one u hu]

/-- A non-zero function `f` is an eigenform (`New.IsEigenform`) as soon as it has a Hecke polynomial
at every split place `w` outside `S` at which the open subgroup `H` contains the maximal compact
subgroup, provided almost all places are outside `S`. -/
lemma exists_isEigenform_of_hasHeckePolyAt [HasPrimitiveRoot5040 E] {n M : Type} [Fintype n]
    [DecidableEq n] {f : Gf E n → M → ℂ} (hf : f ≠ 0) {H : Subgroup (Gf E n)} (hH : H.IsOpen)
    {S : Set (FinPlace E)} (hS : ∀ᶠ w : FinPlace E in cofinite, w ∉ S)
    (h_poly : ∀ (w : FinPlace E) (hw : w.IsSplit), w ∉ S → maxCompactAt n w ≤ H →
      ∃ P : Polynomial ℂ, HasHeckePolyAt f w hw P) :
    ∃ P : FinPlace E → Polynomial ℂ, IsEigenform f P := by
  have h_exists (w : FinPlace E) : ∃ P : Polynomial ℂ,
      ∀ hw : w.IsSplit, w ∉ S → maxCompactAt n w ≤ H → HasHeckePolyAt f w hw P := by
    by_cases hw : w.IsSplit ∧ w ∉ S ∧ maxCompactAt n w ≤ H
    · obtain ⟨h_split, h_off, h_max⟩ := hw
      exact (h_poly w h_split h_off h_max).imp fun P hP _ _ _ ↦ hP
    · exact ⟨0, fun h_split h_off h_max ↦ absurd ⟨h_split, h_off, h_max⟩ hw⟩
  choose P hP using h_exists
  have h_eventually : ∀ᶠ w : FinPlace E in cofinite,
      w.q.Prime → ∃ hw : star w ≠ w, HasHeckePolyAt f w hw (P w) := by
    filter_upwards [eventually_maxCompactAt_le hH, hS] with w h_max h_off h_prime
    exact ⟨isSplit_of_q_prime h_prime, hP w (isSplit_of_q_prime h_prime) h_off h_max⟩
  exact ⟨P, hf, h_eventually⟩

/-- Let `g` be trivial on `Z`. If its image over `E'` lies in the level `m` at the places not above
`Z`, it lies in the level `m` at all places, since its components above `Z ∪ Z̄` are `1`. -/
lemma baseChangeGf_mem_localLevel_univ {Z : Set (FinPlace E)}
    {m : (u : FinPlace E') → Subgroup (GL n (LocField u))} {g : Gf E n} (g_off : g ∈ trivialOn n Z)
    (g_level : baseChangeGf g ∈ localLevel n (placesAbove E' Z)ᶜ m) :
    baseChangeGf g ∈ localLevel n univ m := by
  refine mem_localLevel.mpr fun u _ ↦ ?_
  by_cases hu : u ∈ placesAbove E' Z
  · -- Above `Z ∪ Z̄` the image has the component of `g` at a place of `Z ∪ Z̄`, which is `1`.
    have hg_below : g.atPlace (u.below E) = 1 := by
      obtain h | h : u.below E ∈ Z ∨ star (u.below E) ∈ Z := by simpa [placesAbove] using hu
      · exact mem_trivialOn.mp g_off _ h
      · exact atPlace_star_eq_one_iff.mp (mem_trivialOn.mp g_off _ h)
    simp [atPlace_baseChangeGf, hg_below]
  · exact mem_localLevel.mp g_level u hu

/-- Let `(f₁, φ₁)`, `(f₂, φ₂)`, `(f₃, φ₃)` be matching pairs above `Z`, `X`, `Y` at levels `K`, `B`,
`C`. If the places of `E'` above `X` and above `Y` are disjoint and together are the places not
above `Z` (said with their idempotents), the products form a matching pair at all places, at level
`K ⊓ (B ⊓ C)`. -/
lemma IsMatchingPairAbove.mul_mul {σ : Gal(E'/E)} {Z X Y : Set (FinPlace E)}
    {K B C : Subgroup (Gf E' n)} {f₁ f₂ f₃ : Gf E n → ℂ} {φ₁ φ₂ φ₃ : Gf E' n → ℂ}
    (pair_Z : IsMatchingPairAbove σ μ Z K f₁ φ₁) (pair_X : IsMatchingPairAbove σ μ X B f₂ φ₂)
    (pair_Y : IsMatchingPairAbove σ μ Y C f₃ φ₃)
    (idem_mul : idem (placesAbove E' X) * idem (placesAbove E' Y) = 0)
    (idem_add : idem (placesAbove E' X) + idem (placesAbove E' Y) = 1 - idem (placesAbove E' Z)) :
    IsMatchingPair (adeleMap_star σ) (finrank E E') 1 (kerCompNorm E' μ) baseChangeGf (K ⊓ (B ⊓ C))
      (f₁ * (f₂ * f₃)) (φ₁ * (φ₂ * φ₃)) := by
  have star_idem_above (S : Set (FinPlace E)) :
      star (idem (placesAbove E' S)) = idem (placesAbove E' S) := by simp [star_idem, preimage]
  have pair_XY : IsMatchingPair (adeleMap_star σ) (finrank E E') (1 - idem (placesAbove E' Z))
      (kerCompNorm E' μ) baseChangeGf (B ⊓ C) (f₂ * f₃) (φ₂ * φ₃) := by
    rw [← idem_add]
    exact IsMatchingPair.mul pair_X pair_Y idem_mul (idem_mul_self _) (idem_mul_self _)
      (star_idem_above X) (star_idem_above Y)
  -- Split `1` as the idempotent of the places above `Z` plus its complement.
  have h_orth : idem (placesAbove E' Z) * (1 - idem (placesAbove E' Z)) = 0 := by
    simp [mul_sub, idem_mul_self]
  have h_compl_idem : (1 - idem (placesAbove E' Z)) * (1 - idem (placesAbove E' Z)) =
      1 - idem (placesAbove E' Z) := by simp [mul_sub, sub_mul, idem_mul_self]
  have h_compl_star : star (1 - idem (placesAbove E' Z)) = 1 - idem (placesAbove E' Z) := by
    simp [star_idem_above]
  rw [← add_sub_cancel (idem (placesAbove E' Z)) (1 : 𝔸f E')]
  exact IsMatchingPair.mul pair_Z pair_XY h_orth (idem_mul_self _) h_compl_idem (star_idem_above Z)
    h_compl_star

/-- A matched place (`New.IsMatched`) is unramified in the step (`New.IsStepUnramifiedAt`): some
`σ ≠ 1` moves each place above it, so it is not in the inertia group, and `μ` is trivial on
`E_w^×`. -/
lemma IsMatched.isStepUnramifiedAt [hμ : IsStep (E := E) E' μ]
    {w : FinPlace E} (hw : IsMatched E' μ w) :
    IsStepUnramifiedAt E' μ w := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Gal(E'/E), σ ≠ 1 := hμ.exists_gal_ne_one
  -- `μ` is trivial on `E_w^×`, and every `τ ≠ 1` moves each place above `w`.
  obtain ⟨μ_trivial, h_above⟩ := hw
  rintro u rfl
  obtain ⟨-, h_moved⟩ := h_above u rfl
  exact { exists_notMem_inertia := ⟨σ, notMem_inertia_of_comap_ne (h_moved σ hσ)⟩
          apply_localNorm_eq_one := fun x _hx ↦ μ_trivial (localNorm E u x) }

/-- In prime degree, let `σ ≠ 1` be in the Galois group and let `p` be a property of places of
`E'` that passes from each place `u` to `u.comap σ`. Then `p` passes from `v` to every place `u`
above the same place of `E`. -/
lemma FinPlace.induction_on_comap [IsGalois E E'] [Fact (finrank E E').Prime] {σ : Gal(E'/E)}
    (hσ : σ ≠ 1) {p : FinPlace E' → Prop} (h_comap : ∀ u : FinPlace E', p u → p (u.comap σ))
    {u v : FinPlace E'} (h_below : v.below E = u.below E) (hv : p v) : p u := by
  -- `σ` generates the Galois group, which is transitive on the places above a given place.
  obtain ⟨τ, hτ⟩ : ∃ τ : Gal(E'/E), v.comap τ = u := FinPlace.exists_gal_comap_eq h_below
  obtain ⟨i, hi⟩ : ∃ i : Fin (finrank E E'), σ ^ i.val = τ :=
    (bijective_pow_of_ne_one_of_prime_finrank hσ).surjective τ
  have h_pow (k : ℕ) : p (v.comap (σ ^ k : Gal(E'/E))) := by
    induction k with
    | zero => exact hv
    | succ k ih => exact h_comap _ ih
  rw [← hτ, ← hi]
  exact h_pow i.val

/-- Let the operators of the `F j` and the spherical operators at the places `u x` commute on the
finite-dimensional `L`-fixed vectors (`New.IsCommutingHeckeFamily`); let `f` be fixed by
`trivialOn n S ⊓ L`, with eigenvalue `ev y` for the spherical operator `op y`; and inside every
subrepresentation through `f` let the operator of `F j₀` have non-zero trace on the generalised
`θ`-eigenspace of the `F (o i)` (`New.HasNonzeroTraceAround`). Then it has non-zero trace on the
`L`-fixed joint generalised eigenspace for `θ` on the `F (o i)` and `ev` on the `op y`. -/
lemma trace_restrict_heckeFamily_ne_zero_of_hasNonzeroTraceAround {W A : Type*}
    [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (Gf E n) W} [Group A] {a : A →* Gf E n}
    {S : Set (FinPlace E)} {L : Subgroup (Gf E n)} {L₀ : Subgroup A} {J X ι Y : Type*}
    {F : J → A → ℂ} {u : X → FinPlace E} {hu : ∀ x : X, (u x).IsSplit}
    (h_family : IsCommutingHeckeFamily π S a L L₀ F hu) [Module.Finite ℂ (levelSpace π L)]
    {f : W} (hf_fixed : f ∈ levelSpace π (trivialOn n S ⊓ L)) {op : Y → X × ℕ} {ev : Y → ℂ}
    (hf_eigen : ∀ y : Y, f ∈ eigenspace (heckeSplit π (hu (op y).1) (op y).2) (ev y))
    {o : ι → J} {θ : ι → ℂ} {j₀ : J}
    (h_trace : HasNonzeroTraceAround (π.comp a) (heckeFun (π.comp a) L₀ (F j₀))
      (heckeGenEigenspace (π.comp a) L₀ (F ∘ o) θ) f)
    (h_maps : ∀ x ∈ levelSpace π L ⊓ ⨅ i : ι ⊕ Y,
        (heckeFamily π a L₀ F hu (Sum.map o op i)).maxGenEigenspace (Sum.elim θ ev i),
      heckeFamily π a L₀ F hu (.inl j₀) x ∈ levelSpace π L ⊓ ⨅ i : ι ⊕ Y,
        (heckeFamily π a L₀ F hu (Sum.map o op i)).maxGenEigenspace (Sum.elim θ ev i)) :
    LinearMap.trace ℂ _ ((heckeFamily π a L₀ F hu (.inl j₀)).restrict h_maps) ≠ 0 := by
  -- The vectors fixed by the part of `L` trivial on `S` that are generalised eigenvectors of the
  -- spherical operators form a subrepresentation `V` through `f`; the space of the conclusion
  -- is the generalised `θ`-eigenspace inside `V`.
  let V : Submodule ℂ W := levelSpace π (trivialOn n S ⊓ L) ⊓
    ⨅ y : Y, (heckeSplit π (hu (op y).1) (op y).2).maxGenEigenspace (ev y)
  have hf_mem : f ∈ V :=
    ⟨hf_fixed, (mem_iInf _).mpr fun y ↦ eigenspace_le_maxGenEigenspace (hf_eigen y)⟩
  have V_stable : ∀ (k : A), ∀ x ∈ V, π.comp a k x ∈ V := fun k x ⟨hx_fixed, hx_eigen⟩ ↦
    ⟨h_family.apply_mem k x hx_fixed, (mem_iInf _).mpr fun y ↦ mapsTo_maxGenEigenspace_of_comm
      (h_family.commute_heckeSplit k _ _) _ ((mem_iInf _).mp hx_eigen y)⟩
  have h_space : levelSpace π L ⊓ ⨅ i : ι ⊕ Y,
      (heckeFamily π a L₀ F hu (Sum.map o op i)).maxGenEigenspace (Sum.elim θ ev i) =
        heckeGenEigenspace (π.comp a) L₀ (F ∘ o) θ ⊓ V := by
    rw [h_family.levelSpace_eq, iInf_sum, inf_inf_inf_comm]
    rfl
  have h_finite : Module.Finite ℂ ↥(heckeGenEigenspace (π.comp a) L₀ (F ∘ o) θ ⊓ V) :=
    finiteDimensional_of_le ((inf_le_inf inf_le_left inf_le_left).trans h_family.levelSpace_eq.ge)
  revert h_maps
  rw [h_space]
  exact h_trace ⟨V, V_stable⟩ hf_mem h_finite

/-- A form is fixed by `K` under the translation of forms iff its underlying function is fixed by
`K` under right translation of functions. -/
private lemma mem_levelSpace_formTranslation_iff {κ : Weight E} {K : Subgroup (Gf E n)}
    {f : (stdSpace E n).forms κ} :
    f ∈ levelSpace ((stdSpace E n).formTranslation κ) K ↔
      f.val ∈ levelSpace (rightRegular ℂ (Gf E n) (WeylIndex n κ.1 → ℂ)) K := by simp
      [mem_levelSpace, Subtype.ext_iff]

/-- Let `f` be a form of weight `κ` over `E`, `g` a form of weight `κ.baseChange` over `E'`, and
`Z` a finite set of places of `E`. Suppose that for every place `w ∉ Z ∪ Z̄` at which `f` is
spherical: if `w` is unramified in the step, `g` is spherical at every place above `w`
(`h_spherical`); and if `w` is split and matched and `f` has eigenvalue `t i` for the `i`-th
spherical operator at `w`, then `g` has eigenvalue `t i` for the `i`-th spherical operator at
every split place above `w` (`h_eigen`). Then `g` is a weak base change of `f` off `Z`. -/
lemma isWeakBaseChange_of_forall_heckeSplit_eq_smul [hμ : IsStep (E := E) E' μ]
    {κ : Weight E} {f : (stdSpace E n).forms κ}
    {g : (stdSpace E' n).forms κ.baseChange} {Z : Set (FinPlace E)} (hZ : Z.Finite)
    (h_spherical : ∀ w : FinPlace E, w ∉ Z.conjClosure → IsStepUnramifiedAt E' μ w →
      f ∈ sphericalAt ((stdSpace E n).formTranslation κ) w → ∀ u : FinPlace E', u.below E = w →
        g ∈ sphericalAt ((stdSpace E' n).formTranslation κ.baseChange) u)
    (h_eigen : ∀ w : FinPlace E, w ∉ Z.conjClosure → ∀ hw : w.IsSplit, IsMatched E' μ w →
      f ∈ sphericalAt ((stdSpace E n).formTranslation κ) w → ∀ t : ℕ → ℂ,
      (∀ i : ℕ, heckeSplit ((stdSpace E n).formTranslation κ) hw i f = t i • f) →
      ∀ (u : FinPlace E') (hu : u.IsSplit), u.below E = w → ∀ i : ℕ,
        heckeSplit ((stdSpace E' n).formTranslation κ.baseChange) hu i g = t i • g) :
    IsWeakBaseChange μ Z f.val g.val := by
  refine ⟨hZ, fun w hw u hu_below ↦ ⟨fun h_unram hf ↦ ?_, fun h_matched hw_split P hP ↦ ?_⟩⟩
  · exact mem_levelSpace_formTranslation_iff.mp
      (h_spherical w hw h_unram (mem_levelSpace_formTranslation_iff.mpr hf) u hu_below)
  · obtain ⟨hf, t, rfl, ht⟩ := (hasHeckePolyAt_iff hw_split).mp hP
    -- `u` is split because `w` is, and has the same norm as `w` because `w` is matched.
    have hu_split : u.IsSplit :=
      ne_of_apply_ne (FinPlace.below E) (by rwa [below_star, hu_below])
    obtain ⟨-, h_above⟩ := id h_matched
    have h_norm : u.q = w.q := (h_above u hu_below).left
    exact ⟨hu_split, (hasHeckePolyAt_iff hu_split).mpr
      ⟨h_spherical w hw h_matched.isStepUnramifiedAt hf u hu_below, t, by rw [h_norm],
        h_eigen w hw hw_split h_matched hf t ht u hu_split hu_below⟩⟩

/-- Let `m` be a base change level below the stabiliser of the form `f` (`New.IsBaseChangeLevel`).
For a place `w` that is unramified in the step and at which `f` is spherical, each `m u` with `u`
above `w` or `w̄` is the maximal compact subgroup `localIntGL n u`. -/
private lemma IsBaseChangeLevel.eq_localIntGL_of_mem_sphericalAt {σ : Gal(E'/E)} {κ : Weight E}
    {f : (stdSpace E n).forms κ} {m : (u : FinPlace E') → Subgroup (GL n (LocField u))}
    (hm : IsBaseChangeLevel σ μ (rightStabilizer f.val) m) {w : FinPlace E}
    (hw_unram : IsStepUnramifiedAt E' μ w)
    (hf : f ∈ sphericalAt ((stdSpace E n).formTranslation κ) w) :
    ∀ u ∈ placesAbove E' {w}, m u = localIntGL n u := by
  refine hm.eq_localIntGL w hw_unram ?_
  simpa [LE.le, funext_iff] using mem_levelSpace_formTranslation_iff.mp hf

/-- Facts about a level `𝓛` over `E'` used in the proof of
`New.exists_isWeakBaseChange_of_matching`, for a form `f` over `E` and sets `Z`, `X` of places of
`E`. The level `𝓛` is `L₁` intersected with the maximal level above the split matched places of
`X` and with a subgroup `C` for the remaining places, and `𝓛 ≤ K₁ ≤ New.stdLevel E' n`; matching
pairs above `Z` have level `K`. -/
private structure IsTransferLevel (σ : Gal(E'/E)) (μ : (𝔸f E)ˣ →* ℂˣ) {κ : Weight E}
    (f : (stdSpace E n).forms κ) (Z X : Set (FinPlace E)) (K L₁ K₁ C 𝓛 : Subgroup (Gf E' n)) :
    Prop where
  /-- `K₁` consists of integral elements. -/
  le_stdLevel : K₁ ≤ stdLevel E' n
  /-- `𝓛` lies in `K₁`. -/
  le : 𝓛 ≤ K₁
  /-- `𝓛` is open. -/
  isOpen : 𝓛.IsOpen
  /-- `𝓛` is stable under `σ`. -/
  comap_galoisGf : 𝓛.comap (galoisGf σ) = 𝓛
  /-- The elements of `K₁` of twisted norm `1` are coboundaries in `K₁`. -/
  exists_coboundary (s : Gf E' n) (hs : s ∈ K₁)
    (hs_norm : twistedNorm (galoisGf σ) (finrank E E') s = 1) : ∃ t ∈ K₁, galoisGf σ t = s⁻¹ * t
  /-- `𝓛` is `L₁`, intersected with the maximal level above `X` and with `C`. -/
  eq_inf : 𝓛 = L₁ ⊓ (localLevel n (placesAbove E' X) ⊓ C)
  /-- Elements supported above `Z ∪ Z̄` lie in the maximal level above `X` and in `C`. -/
  supportedOn_le : supportedOn n (placesAbove E' Z) ≤ localLevel n (placesAbove E' X) ⊓ C
  /-- Elements supported above `X ∪ X̄` lie in `C`. -/
  supportedOn_placesAbove_le : supportedOn n (placesAbove E' X) ≤ C
  /-- The places of `X` are split. -/
  isSplit (w : FinPlace E) (hw : w ∈ X) : w.IsSplit
  /-- The places of `X` are matched. -/
  isMatched (w : FinPlace E) (hw : w ∈ X) : IsMatched E' μ w
  /-- The places of `X` lie off `Z ∪ Z̄`. -/
  notMem_conjClosure (w : FinPlace E) (hw : w ∈ X) : w ∉ Z.conjClosure
  /-- For `w ∈ X`, `𝓛` contains the integral elements supported above `w` and `w̄`. -/
  kf_inf_supportedOn_le (w : FinPlace E) (hw : w ∈ X) {S : Set (FinPlace E')}
    (hS : S ⊆ placesAbove E' {w}) : stdLevel E' n ⊓ supportedOn n S ≤ 𝓛
  /-- A product of a matching pair above `Z` of level `K`, a matching pair above `X` of maximal
  level and the indicator function of `C` is a matching pair of level `K₁`. -/
  isMatchingPair_mul {f₁ f₂ : Gf E n → ℂ} {φ₁ φ₂ : Gf E' n → ℂ}
    (h₁ : IsMatchingPairAbove σ μ Z K f₁ φ₁)
    (h₂ : IsMatchingPairAbove σ μ X (localLevel n (placesAbove E' X)) f₂ φ₂) :
    IsMatchingPair (adeleMap_star σ) (finrank E E') 1 (kerCompNorm E' μ) baseChangeGf K₁
      (f₁ * (f₂ * (indicator C 1 ∘ baseChangeGf (E' := E')))) (φ₁ * (φ₂ * indicator C 1))
  /-- `f` is fixed by the elements of `𝓛` over `E` that are trivial on `Z`. -/
  mem_levelSpace :
    f ∈ levelSpace ((stdSpace E n).formTranslation κ) (trivialOn n Z ⊓ 𝓛.comap baseChangeGf)
  /-- For a place `w` off `Z ∪ Z̄` that is unramified in the step and at which `f` is spherical,
  `𝓛` contains the integral elements supported above `w` and `w̄`. -/
  kf_inf_supportedOn_le_of_mem_sphericalAt (w : FinPlace E) (hw : w ∉ Z.conjClosure)
    (hw_unram : IsStepUnramifiedAt E' μ w)
    (hf : f ∈ sphericalAt ((stdSpace E n).formTranslation κ) w) {S : Set (FinPlace E')}
    (hS : S ⊆ placesAbove E' {w}) : stdLevel E' n ⊓ supportedOn n S ≤ 𝓛
  /-- A split matched place off `Z ∪ Z̄` at which `f` is spherical lies in `X`. -/
  mem_of_isMatched (w : FinPlace E) (hw : w ∉ Z.conjClosure) (hw_split : w.IsSplit)
    (hw_matched : IsMatched E' μ w) (hf : f ∈ sphericalAt ((stdSpace E n).formTranslation κ) w) :
    w ∈ X

/-- Let `σ ≠ 1`, let `f` be a form of weight `κ` over `E`, and let `Z` be a set of places of `E`.
Let `L₁` be an open `σ`-stable subgroup over `E'` that contains the elements trivial above
`Z ∪ Z̄`, and let `K ⊇ L₁` consist of elements integral above `Z ∪ Z̄`, with `σ`-cocycles that
split above `Z ∪ Z̄`. Then there is a level `𝓛` with the properties of `IsTransferLevel`. -/
private lemma exists_isTransferLevel [hμ : IsStep (E := E) E' μ]
    {σ : Gal(E'/E)} (hσ : σ ≠ 1) {κ : Weight E}
    (f : (stdSpace E n).forms κ) {Z : Set (FinPlace E)} {K L₁ : Subgroup (Gf E' n)}
    (h_off : trivialOn n (placesAbove E' Z) ≤ L₁) (hL₁_open : L₁.IsOpen)
    (hL₁_σ : ∀ k : Gf E' n, galoisGf σ k ∈ L₁ ↔ k ∈ L₁) (hL₁_le : L₁ ≤ K)
    (hK_le : K ≤ localLevel n (placesAbove E' Z))
    (hK_coh : CocyclesSplit (finrank E E') (idem (placesAbove E' Z)) K (galoisGf σ)) :
    ∃ (X : Set (FinPlace E)) (K₁ C 𝓛 : Subgroup (Gf E' n)),
      IsTransferLevel σ μ f Z X K L₁ K₁ C 𝓛 := by
  -- The level `𝓛` is `L₁` above `Z ∪ Z̄` and `N` elsewhere, where `N` is cut out by the local
  -- levels `m u` that `exists_isBaseChangeLevel` gives for the stabiliser of `f`. `X` is the set
  -- of split matched places off `Z ∪ Z̄` above which the `m u` are maximal, and `Y` the remaining
  -- places.
  obtain ⟨f_open, -⟩ := f.property
  obtain ⟨m, hm⟩ := exists_isBaseChangeLevel hσ f_open
  let X : Set (FinPlace E) := {w | w ∉ Z.conjClosure ∧
    (∀ u ∈ placesAbove E' {w}, m u = localIntGL n u) ∧ w.IsSplit ∧ IsMatched E' μ w}
  have X_notMem (w : FinPlace E) : w ∈ X → w ∉ Z.conjClosure :=
    fun ⟨hw_off, _hw_max, _hw_split, _hw_matched⟩ ↦ hw_off
  have X_eq_Kw (w : FinPlace E) : w ∈ X → ∀ u ∈ placesAbove E' {w}, m u = localIntGL n u :=
    fun ⟨_hw_off, hw_max, _hw_split, _hw_matched⟩ ↦ hw_max
  let N : Subgroup (Gf E' n) := localLevel n (placesAbove E' Z)ᶜ m

  obtain ⟨Y, idem_XY, on_X_le, XY_eq, idem_sum, N_eq⟩ : ∃ Y : Set (FinPlace E),
      idem (placesAbove E' X) * idem (placesAbove E' Y) = 0 ∧
      supportedOn n (placesAbove E' X) ≤ localLevel n (placesAbove E' Y) m ∧
      placesAbove E' (X ∪ Y) = (placesAbove E' Z)ᶜ ∧
      idem (placesAbove E' X) + idem (placesAbove E' Y) = 1 - idem (placesAbove E' Z) ∧
      N = localLevel n (placesAbove E' X) ⊓ localLevel n (placesAbove E' Y) m :=
    exists_remaining_places (fun w hw ↦ not_or.mp (X_notMem w hw)) fun x ↦ X_eq_Kw x x.property
  have N_level : IsMatchingLevel σ μ (X ∪ Y) N := by
    simpa [N, ← XY_eq] using hm.isMatchingLevel (X ∪ Y)
  have N_coh : CocyclesSplit (finrank E E') (idem (placesAbove E' Z)ᶜ) N (galoisGf σ) := by
    simpa [← XY_eq] using N_level.cocyclesSplit
  have Z_σ (u : FinPlace E') : u.comap σ ∈ placesAbove E' Z ↔ u ∈ placesAbove E' Z := by
    simp [placesAbove]
  refine ⟨X, K ⊓ N, localLevel n (placesAbove E' Y) m, L₁ ⊓ N,
    { le_stdLevel := ?_
      le := inf_le_inf_right N hL₁_le
      isOpen := hL₁_open.inter N_level.isOpen
      comap_galoisGf := ?_
      -- `K` has no `σ`-cohomology above `Z ∪ Z̄` and `N` none elsewhere.
      exists_coboundary := exists_mem_inf_galoisGf_eq_inv_mul_of_cocyclesSplit Z_σ
        (h_off.trans hL₁_le)
        trivialOn_le_localLevel hK_coh N_coh
      eq_inf := by rw [← N_eq]
      supportedOn_le := ?_
      supportedOn_placesAbove_le := on_X_le
      isSplit := fun _w ⟨_hw_off, _hw_max, hw_split, _hw_matched⟩ ↦ hw_split
      isMatched := fun _w ⟨_hw_off, _hw_max, _hw_split, hw_matched⟩ ↦ hw_matched
      notMem_conjClosure := X_notMem
      kf_inf_supportedOn_le := fun w hw _ hS ↦
        inf_supportedOn_le_inf_localLevel h_off (X_notMem w hw) (X_eq_Kw w hw) hS
      isMatchingPair_mul := ?_
      mem_levelSpace := ?_
      kf_inf_supportedOn_le_of_mem_sphericalAt := fun w hw hw_unram hf _ hS ↦
        inf_supportedOn_le_inf_localLevel h_off hw (hm.eq_localIntGL_of_mem_sphericalAt hw_unram hf)
          hS
      mem_of_isMatched := fun w hw hw_split hw_matched hf ↦
        ⟨hw, hm.eq_localIntGL_of_mem_sphericalAt hw_matched.isStepUnramifiedAt hf, hw_split,
          hw_matched⟩ }⟩
  · -- `K` is integral above `Z ∪ Z̄`, and `N` elsewhere.
    rintro g ⟨hg_K, hg_N⟩
    refine mem_stdLevel_iff.mpr fun u ↦ ?_
    by_cases hu : u ∈ placesAbove E' Z
    exacts [hK_le hg_K u hu, hm.le_localIntGL u (hg_N u hu)]
  · ext k
    simp [hL₁_σ, N_level.galoisGf_mem_iff]
  · rw [← N_eq]
    exact (supportedOn_le_trivialOn (by simp)).trans trivialOn_le_localLevel
  · intro f₁ f₂ φ₁ φ₂ h₁ h₂
    rw [N_eq]
    exact h₁.mul_mul h₂ (hm.isMatchingLevel Y).isMatchingPairAbove_indicator idem_XY idem_sum
  · -- An element of `𝓛` over `E` that is trivial on `Z` lies in every `m u`, so it fixes `f`.
    rw [mem_levelSpace]
    rintro ⟨g, g_off, -, g_N⟩
    have hg_stab : g ∈ rightStabilizer f.val :=
      hm.comap_le (baseChangeGf_mem_localLevel_univ g_off g_N)
    simpa [Subtype.ext_iff, funext_iff] using hg_stab

section TransferLevel

variable {σ : Gal(E'/E)} {κ : Weight E} {f : (stdSpace E n).forms κ} {Z X : Set (FinPlace E)}
  {K L₁ K₁ C 𝓛 : Subgroup (Gf E' n)}

/-- A place of `E'` above a place of `X` is split. -/
private lemma IsTransferLevel.isSplit_of_below_mem
    (h_level : IsTransferLevel σ μ f Z X K L₁ K₁ C 𝓛) {u : FinPlace E'} (hu : u.below E ∈ X) :
    u.IsSplit := by
  refine ne_of_apply_ne (FinPlace.below E) ?_
  simpa only [below_star] using h_level.isSplit (u.below E) hu

/-- At a place of `E'` above a place of `X`, `𝓛` contains the maximal compact subgroup. -/
private lemma IsTransferLevel.maxCompactAt_le_of_below_mem
    (h_level : IsTransferLevel σ μ f Z X K L₁ K₁ C 𝓛) {u : FinPlace E'} (hu : u.below E ∈ X) :
    maxCompactAt n u ≤ 𝓛 := by
  exact h_level.kf_inf_supportedOn_le (u.below E) hu (by simp [placesAbove])

/-- The elements over `E` supported at a place of `X` and its conjugate map into `C`. -/
private lemma IsTransferLevel.supportedOn_le_comap
    (h_level : IsTransferLevel σ μ f Z X K L₁ K₁ C 𝓛) {w : FinPlace E} (hw : w ∈ X) :
    supportedOn n {w} ≤ C.comap baseChangeGf := by
  exact fun g hg ↦ h_level.supportedOn_placesAbove_le
    (baseChangeGf_mem_supportedOn (supportedOn_mono (singleton_subset_iff.mpr hw) hg))

/-- The elements supported at a place of `E'` above `X` and at its conjugate lie in `C`. -/
private lemma IsTransferLevel.supportedOn_le_of_below_mem
    (h_level : IsTransferLevel σ μ f Z X K L₁ K₁ C 𝓛) {u : FinPlace E'} (hu : u.below E ∈ X) :
    supportedOn n {u} ≤ C := by
  exact (supportedOn_mono (by simp [placesAbove, hu])).trans h_level.supportedOn_placesAbove_le

/-- Let `G` be a retract at `Z` whose level `L` has preimage the pull-back of `L₁` to `E`, and let
`F j` be `L`-bi-invariant functions with commuting operators. At the pull-back of `𝓛` to `E`, the
operators of the `F j` and the spherical operators at the places of `X` form a commuting family
with a relation to functions, as in `New.exists_isHeckeFunctionRelation`. -/
private lemma IsTransferLevel.exists_isCommutingHeckeFamily_comap
    (h_level : IsTransferLevel σ μ f Z X K L₁ K₁ C 𝓛) {W G J : Type*} [AddCommGroup W]
    [Module ℂ W] (π : Representation ℂ (Gf E n) W) [Group G] {a : G →* Gf E n} {r : Gf E n →* G}
    {L : Subgroup G} {F : J → G → ℂ} (ha : IsLocalRetraction a r Z)
    (hL : L₁.comap baseChangeGf = L.comap r) (hF : ∀ j : J, IsHeckeFunction L (F j))
    (h_comm : ∀ i j : J, HeckeCommute (π.comp a) L (F i) (F j))
    (hX : ∀ x : X, x.val.IsSplit) :
    ∃ h : IsCommutingHeckeFamily π Z a (𝓛.comap baseChangeGf) L F hX,
      ∃ R : J → End ℂ (levelSpace π (𝓛.comap baseChangeGf)) → (Gf E n → ℂ) → Prop,
        IsHeckeFunctionRelation π a r (𝓛.comap baseChangeGf) L
          ((localLevel n (placesAbove E' X)).comap baseChangeGf) (C.comap baseChangeGf) F hX
          (fun i : J ⊕ X × ℕ ↦ (heckeFamily π a L F hX i).restrict (h.heckeFamily_mem i)) R := by
  have 𝓛_comap : 𝓛.comap baseChangeGf =
      L.comap r ⊓
        ((localLevel n (placesAbove E' X)).comap baseChangeGf ⊓ C.comap baseChangeGf) := by
    rw [h_level.eq_inf, Subgroup.comap_inf, Subgroup.comap_inf, hL]
  have 𝓛_comap_le : 𝓛.comap baseChangeGf ≤ stdLevel E n := fun g hg ↦
    baseChangeGf_mem_stdLevel.mp (h_level.le_stdLevel (h_level.le hg))
  have a_mem (g : G) :
      a g ∈ (localLevel n (placesAbove E' X)).comap baseChangeGf ⊓ C.comap baseChangeGf :=
    h_level.supportedOn_le (baseChangeGf_mem_supportedOn (ha.left g))
  have X_max (x : X) : maxCompactAt n x.val ≤ 𝓛.comap baseChangeGf := fun g hg ↦
    h_level.kf_inf_supportedOn_le x x.property subset_rfl
      (hg.imp baseChangeGf_mem_stdLevel.mpr baseChangeGf_mem_supportedOn)
  exact exists_isHeckeFunctionRelation a r (𝓛.comap baseChangeGf) hX ha 𝓛_comap 𝓛_comap_le a_mem hF
    h_comm (fun x ↦ h_level.notMem_conjClosure x x.property) X_max

end TransferLevel

/-- In prime degree, let `σ ≠ 1`, and let `t` preserve the `L`-fixed vectors and turn the action of
`g` into that of `σ g`. Let all places above `w` be split with `L` maximal there, and let `A u` be
the `i`-th spherical operator at `u` on the `L`-fixed vectors. If `Θ u = Θ v` whenever
`t * A u = A v * t`, then `Θ` takes the same value at all places above `w`. -/
private lemma apply_eq_of_twist_heckeSplit [IsGalois E E'] [Fact (finrank E E').Prime]
    {σ : Gal(E'/E)} (hσ : σ ≠ 1) {W : Type*} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Gf E' n) W} {L : Subgroup (Gf E' n)} {t : End ℂ W}
    (t_twist : ∀ (g : Gf E' n) (x : W), t (π g x) = π (galoisGf σ g) (t x))
    (t_mem : ∀ x ∈ levelSpace π L, t x ∈ levelSpace π L) {w : FinPlace E}
    (h_split : ∀ u : {u : FinPlace E' // u.below E = w}, u.val.IsSplit)
    (h_max : ∀ u : {u : FinPlace E' // u.below E = w}, maxCompactAt n u.val ≤ L) {i : ℕ}
    {A : {u : FinPlace E' // u.below E = w} → End ℂ (levelSpace π L)}
    (hA : ∀ (u : {u : FinPlace E' // u.below E = w}) (x : levelSpace π L),
      (A u x : W) = heckeSplit π (h_split u) i x)
    {Θ : {u : FinPlace E' // u.below E = w} → ℂ}
    (hΘ : ∀ u v : {u : FinPlace E' // u.below E = w},
      t.restrict t_mem * A u = A v * t.restrict t_mem → Θ u = Θ v)
    (u v : {u : FinPlace E' // u.below E = w}) : Θ u = Θ v := by
  -- `t` carries the spherical operator at `u'.comap σ` to the one at `u'`, so `Θ` agrees at these
  -- two places; `σ` generates the Galois group.
  have Θ_comap (u' v' : {u : FinPlace E' // u.below E = w}) (h_comap : v'.val = u'.val.comap σ) :
      Θ v' = Θ u' := by
    refine hΘ v' u' (LinearMap.ext fun x ↦ Subtype.ext ?_)
    have hx_spherical : t x ∈ sphericalAt π u'.val :=
      levelSpace_anti (h_max u') (t_mem x x.property)
    have h_carry : ∀ hv' : v'.val.IsSplit,
        t (heckeSplit π hv' i x) = heckeSplit π (h_split u') i (t x) := by
      rw [h_comap]
      exact fun hv' ↦ map_heckeSplit_comap t_twist hv' (h_split u') i hx_spherical
    calc t (A v' x) = t (heckeSplit π (h_split v') i x) := by rw [hA]
      _ = heckeSplit π (h_split u') i (t x) := h_carry (h_split v')
      _ = A u' (t.restrict t_mem x) := (hA u' (t.restrict t_mem x)).symm
  let Agree (u' : FinPlace E') : Prop := ∀ hu' : u'.below E = w, Θ ⟨u', hu'⟩ = Θ v
  have agree_comap (u' : FinPlace E') (h_agree : Agree u') : Agree (u'.comap σ) := by
    intro hσu'
    have hu' : u'.below E = w := by rwa [below_comap] at hσu'
    rw [← h_agree hu']
    exact Θ_comap ⟨u', hu'⟩ _ rfl
  exact FinPlace.induction_on_comap (p := Agree) hσ agree_comap
    (v.property.trans u.property.symm) (fun _hv ↦ rfl) u.property

/-- The eigenvector step of `New.exists_isWeakBaseChange_of_matching`, for local data as in
`New.IsLocalMatching` (`hF`: each `F j` is `L`- and each `F' j` is `L'`-bi-invariant; `h_comm`: the
operators of the `F j` commute, and so do those of the `F' j`) and a level `𝓛` as in
`IsTransferLevel`. There is a form `g ≠ 0` over `E'` fixed by `𝓛` and `L'`: a `θ`-eigenvector of the
`F' (o i)` in the image of `F' j₀`, a spherical eigenvector at split places off `Z ∪ Z̄` where `𝓛`
is maximal, and with the eigenvalues of `f` at `w` at every split place above a place `w ∈ X`. -/
private lemma exists_eigenvector_of_isTransferLevel [hμ : IsStep (E := E) E' μ]
    {σ : Gal(E'/E)} (hσ : σ ≠ 1) {κ : Weight E}
    (f : (stdSpace E n).forms κ) {Z X : Set (FinPlace E)} {K K₁ C 𝓛 : Subgroup (Gf E' n)}
    {G G' : Type*} [Group G] [Group G'] {a : G →* Gf E n} {a' : G' →* Gf E' n}
    {r : Gf E n →* G} {r' : Gf E' n →* G'} {L : Subgroup G} {L' : Subgroup G'} {ι J : Type}
    {P : Set J} {F : J → G → ℂ} {F' : J → G' → ℂ}
    (hF : ∀ j : J, IsHeckeFunction L (F j) ∧ IsHeckeFunction L' (F' j))
    (ha : IsLocalRetraction a r Z) (ha' : IsLocalRetraction a' r' (placesAbove E' Z))
    (hL : (L'.comap r').comap baseChangeGf = L.comap r)
    (hP : P ⊆ {j : J | IsMatchingPairAbove σ μ Z K (F j ∘ r) (F' j ∘ r')})
    (h_level : IsTransferLevel σ μ f Z X K (L'.comap r') K₁ C 𝓛) (o : ι → J) (θ : ι → ℂ)
    (j₀ : J) (hj₀ : j₀ ∈ P)
    (h_comm : ∀ i j : J,
      HeckeCommute (localFormTranslation κ a) L (F i) (F j) ∧
      HeckeCommute (localFormTranslation κ.baseChange a') L' (F' i) (F' j))
    (h_stable : ∀ i : ι, ∀ j ∈ P, ∃ k ∈ P,
      IsHeckeProduct (localFormTranslation κ a) L (F (o i)) (F j) (F k) ∧
      IsHeckeProduct (localFormTranslation κ.baseChange a') L' (F' (o i)) (F' j) (F' k))
    (h_trace : HasNonzeroTraceAround (localFormTranslation κ a)
      (heckeFun (localFormTranslation κ a) L (F j₀))
      (heckeGenEigenspace (localFormTranslation κ a) L (F ∘ o) θ) f) :
    ∃ g : (stdSpace E' n).forms κ.baseChange,
      g ≠ 0 ∧ g ∈ levelSpace ((stdSpace E' n).formTranslation κ.baseChange) 𝓛 ∧
      IsHeckeEigenvector (localFormTranslation κ.baseChange a') L' (F' ∘ o) θ g ∧
      g ∈ (levelSpace (localFormTranslation κ.baseChange a') L').map
        (heckeFun (localFormTranslation κ.baseChange a') L' (F' j₀)) ∧
      (∀ (u : FinPlace E') (hu : u.IsSplit), u ∉ placesAbove E' Z → maxCompactAt n u ≤ 𝓛 →
        ∃ t : ℕ → ℂ, ∀ i : ℕ,
          heckeSplit ((stdSpace E' n).formTranslation κ.baseChange) hu i g = t i • g) ∧
      ∀ w ∈ X, ∀ (hw : w.IsSplit) (t : ℕ → ℂ),
        (∀ i : ℕ, heckeSplit ((stdSpace E n).formTranslation κ) hw i f = t i • f) →
        ∀ (u : FinPlace E') (hu : u.IsSplit), u.below E = w → ∀ i : ℕ,
          heckeSplit ((stdSpace E' n).formTranslation κ.baseChange) hu i g = t i • g := by
  -- At `𝓛` and its pull-back to `E` the local and the spherical Hecke operators commute, and the
  -- twisted trace identity holds on a set `Q` of pairs of operators that is stable under matching
  -- generators. So `exists_eigenvector_of_trace_identity` gives an eigenvector `g` with the
  -- eigenvalues `θ` and those of `f`; the twist by `σ` carries the latter to every place above.
  let π : Representation ℂ (Gf E n) ((stdSpace E n).forms κ) := (stdSpace E n).formTranslation κ
  let π' : Representation ℂ (Gf E' n) ((stdSpace E' n).forms κ.baseChange) :=
    (stdSpace E' n).formTranslation κ.baseChange
  -- `X'`: the split places of `E'` not above `Z ∪ Z̄` at which `𝓛` is maximal; it contains the
  -- places above `X`.
  let X' : Type _ := {u : FinPlace E' // u.IsSplit ∧ u ∉ placesAbove E' Z ∧ maxCompactAt n u ≤ 𝓛}
  have X'_split (x : X') : x.val.IsSplit := x.property.left
  have X'_off (x : X') : x.val ∉ (placesAbove E' Z).conjClosure := by
    simpa using x.property.right.left
  have X'_max (x : X') : maxCompactAt n x.val ≤ 𝓛 := x.property.right.right
  let above (u : FinPlace E') (hu : u.below E ∈ X) : X' :=
    ⟨u, h_level.isSplit_of_below_mem hu, h_level.notMem_conjClosure (u.below E) hu,
      h_level.maxCompactAt_le_of_below_mem hu⟩
  have X_split (x : X) : x.val.IsSplit := h_level.isSplit x x.property
  -- The commuting operators over `E` and `E'`. `R k t φ` implies that `t` is the operator of the
  -- product of `F k ∘ r`, of `φ` (above `X`) and of the indicator of `C.comap baseChangeGf`.
  obtain ⟨h_fam, R, hR⟩ :=
    h_level.exists_isCommutingHeckeFamily_comap π ha hL (fun j ↦ (hF j).left)
      (fun i j ↦ (h_comm i j).left) X_split
  obtain ⟨h_fam', R', hR'⟩ :=
    exists_isHeckeFunctionRelation (π := π') a' r' 𝓛 X'_split ha' h_level.eq_inf
      (h_level.le.trans h_level.le_stdLevel) (fun g ↦ h_level.supportedOn_le (ha'.left g))
      (fun j ↦ (hF j).right) (fun i j ↦ (h_comm i j).right) X'_off X'_max
  -- `t₀` intertwines `g` with `σ g`, and `tr (T' * t₀) = z * tr T` for the operators of a matching
  -- pair.
  obtain ⟨z, z_ne, t₀, t₀_twist, t₀_stab, trace_eq⟩ :=
    twisted_trace_identity hσ κ h_level.le_stdLevel h_level.le h_level.isOpen
      h_level.comap_galoisGf h_level.exists_coboundary
  have finite_level : Module.Finite ℂ (levelSpace π (𝓛.comap baseChangeGf)) :=
    (stdSpace E n).finite_formTranslation_levelSpace κ
      (continuous_baseChangeGf.isOpen_preimage _ h_level.isOpen)
  have finite_level' : Module.Finite ℂ (levelSpace π' 𝓛) :=
    (stdSpace E' n).finite_formTranslation_levelSpace κ.baseChange h_level.isOpen
  -- Matching pairs of functions above `X`, stable under the spherical operators at `w` and at
  -- `U w`, a place above `w`.
  obtain ⟨D, hD⟩ := exists_isHeckeStableMatching (n := n) (S := X) hσ h_level.isSplit
    h_level.isMatched
  choose U hU D_stable using fun w : X ↦ hD.exists_isHeckeStableAt (E' := E') w w.property
  have U_mem (x : X) : (U x).below E ∈ X := by simpa only [hU x] using x.property
  -- The generators: the local operators of index `o i`, and those spherical operators at places
  -- of `X` of which `f` is an eigenvector. An element of `Eig` is such an operator `op y` with its
  -- eigenvalue `ev y`.
  let B : J ⊕ X × ℕ → End ℂ ((stdSpace E n).forms κ) := heckeFamily π a L F X_split
  let B' : J ⊕ X' × ℕ → End ℂ ((stdSpace E' n).forms κ.baseChange) :=
    heckeFamily π' a' L' F' X'_split
  let T (i : J ⊕ X × ℕ) : End ℂ (levelSpace π (𝓛.comap baseChangeGf)) :=
    (B i).restrict (h_fam.heckeFamily_mem i)
  let T' (i : J ⊕ X' × ℕ) : End ℂ (levelSpace π' 𝓛) := (B' i).restrict (h_fam'.heckeFamily_mem i)
  let Eig := {y : (X × ℕ) × ℂ // f ∈ eigenspace (B (.inr y.fst)) y.snd}
  let op (y : Eig) : X × ℕ := (y : (X × ℕ) × ℂ).fst
  let ev (y : Eig) : ℂ := (y : (X × ℕ) × ℂ).snd
  let gen : ι ⊕ Eig → J ⊕ X × ℕ := Sum.map o op
  let gen' : ι ⊕ Eig → J ⊕ X' × ℕ :=
    Sum.map o fun y ↦ (above (U (op y).fst) (U_mem (op y).fst), (op y).snd)
  -- `Q`: the pairs of operators that come from an index in `P` and a pair of functions in `D`. Such
  -- a pair comes from a product of matching pairs above `Z`, above `X` and the indicator of `C`.
  let Q : Set (End ℂ (levelSpace π (𝓛.comap baseChangeGf)) × End ℂ (levelSpace π' 𝓛)) :=
    {q | ∃ k ∈ P, ∃ d ∈ D, R k q.fst d.fst ∧ R' k q.snd d.snd}
  have Q_trace : ∀ q ∈ Q,
      LinearMap.trace ℂ _ (q.snd * t₀.restrict t₀_stab) = z * LinearMap.trace ℂ _ q.fst := by
    rintro q ⟨k, hk, d, hd, hq, hq'⟩
    exact trace_eq _ _ (h_level.isMatchingPair_mul (hP hk) (hD.isMatchingPairAbove d hd)) _ _
      (hR.isOperatorOf hq) (hR'.isOperatorOf hq')
  have Q_stable : ∀ q ∈ Q, ∀ i, (T (gen i), T' (gen' i)) * q ∈ Q := by
    rintro q ⟨k, hk, d, hd, hq, hq'⟩ (i | ⟨⟨⟨w, j⟩, c⟩, -⟩)
    · obtain ⟨k', hk', h_prod, h_prod'⟩ := h_stable i k hk
      exact ⟨k', hk', d, hd, hR.local_mul hq h_prod, hR'.local_mul hq' h_prod'⟩
    · -- The spherical operators act at `w ∈ X` and at `U w`, where `C` contains the supported
      -- elements.
      let u' : X' := above (U w) (U_mem w)
      exact ⟨k, hk, _, D_stable w d hd (X_split w) (X'_split u') j,
        hR.spherical_mul hq w j (h_level.supportedOn_le_comap w.property),
        hR'.spherical_mul hq' u' j (h_level.supportedOn_le_of_below_mem (U_mem w))⟩
  -- `Y`: the joint generalised eigenspace of the generators at the pulled-back level. The operator
  -- of `F j₀` preserves it and has non-zero trace on it.
  let Y : Submodule ℂ ((stdSpace E n).forms κ) := levelSpace π (𝓛.comap baseChangeGf) ⊓
    ⨅ i : ι ⊕ Eig, maxGenEigenspace (B (gen i)) (Sum.elim θ ev i)
  have Y_stable : ∀ x ∈ Y, B (.inl j₀) x ∈ Y :=
    apply_mem_inf_iInf_maxGenEigenspace_of_commute_restrict
      (fun i ↦ h_fam.heckeFamily_mem (gen i)) (h_fam.heckeFamily_mem (.inl j₀))
      (fun i ↦ h_fam.commute_restrict (.inl j₀) (gen i)) (Sum.elim θ ev)
  have h_trace_ne : LinearMap.trace ℂ Y ((B (.inl j₀)).restrict Y_stable) ≠ 0 :=
    trace_restrict_heckeFamily_ne_zero_of_hasNonzeroTraceAround h_fam h_level.mem_levelSpace
      (fun y : Eig ↦ y.property) h_trace Y_stable
  have base_mem : (T (.inl j₀), T' (.inl j₀)) ∈ Q :=
    ⟨j₀, hj₀, _, hD.indicator_mem, hR.base _, hR'.base _⟩
  -- The eigenvector lemma gives eigenvalues `Θ` that agree on operators that `t₀` intertwines
  -- (`Θ_twist`) and extend `θ` and the eigenvalues of `f` (`Θ_gen`), and `g = T' (.inl j₀) v`
  -- (`g_eq`), non-zero, with `T' i g = Θ i • g` for every `i` (`g_eig`).
  obtain ⟨Θ, g, v, Θ_twist, Θ_gen, g_eq, g_ne, g_eig⟩ :=
    exists_eigenvector_of_trace_identity (A' := T') h_fam.heckeFamily_mem h_fam.commute_restrict
      h_fam'.commute_restrict gen gen' (.inl j₀) (.inl j₀) (Sum.elim θ ev) Y_stable h_trace_ne z_ne
      base_mem Q_trace Q_stable
  have g_eig' (i : J ⊕ X' × ℕ) : B' i g.val = Θ i • g.val := congrArg Subtype.val (g_eig i)
  have fixed_of_level (x : levelSpace π' 𝓛) :
      x.val ∈ levelSpace (localFormTranslation κ.baseChange a') L' :=
    (Submodule.mem_inf.mp (h_fam'.levelSpace_eq.le x.property)).left
  have g_local (i : ι) :
      heckeFun (localFormTranslation κ.baseChange a') L' (F' (o i)) g.val = θ i • g.val :=
    (g_eig' (.inl (o i))).trans (congrArg (· • g.val) (congrFun Θ_gen (.inl i)))
  refine ⟨g.val, by simpa using g_ne, g.property, ⟨fixed_of_level g, g_local⟩,
    ⟨v.val, fixed_of_level v, congrArg Subtype.val g_eq.symm⟩, ?_, ?_⟩
  · intro u hu hu_off hu_max
    let x' : X' := ⟨u, hu, hu_off, hu_max⟩
    exact ⟨fun i ↦ Θ (.inr (x', i)), fun i ↦ g_eig' (.inr (x', i))⟩
  -- At `U x` the eigenvalues of `g` are those of `f` at `x` by construction; the twist by `σ`
  -- carries this to every place above `x`.
  intro w hw hw_split t ht u hu hu_below i
  let x : X := ⟨w, hw⟩
  let lift (u' : {u' : FinPlace E' // u'.below E = w}) : X' :=
    above u'.val (mem_of_eq_of_mem u'.property hw)
  have Θ_U : Θ (.inr (lift ⟨U x, hU x⟩, i)) = t i :=
    congrFun Θ_gen (.inr ⟨((x, i), t i), Module.End.mem_eigenspace_iff.mpr (ht i)⟩)
  have Θ_u : Θ (.inr (lift ⟨u, hu_below⟩, i)) = Θ (.inr (lift ⟨U x, hU x⟩, i)) :=
    apply_eq_of_twist_heckeSplit hσ t₀_twist t₀_stab (fun u' ↦ X'_split (lift u'))
      (fun u' ↦ X'_max (lift u')) (A := fun u' ↦ T' (.inr (lift u', i))) (fun _u' _x ↦ rfl)
      (Θ := fun u' ↦ Θ (.inr (lift u', i)))
      (fun u' v' ↦ Θ_twist (.inr (lift u', i)) (.inr (lift v', i))) ⟨u, hu_below⟩ ⟨U x, hU x⟩
  exact (g_eig' (.inr (lift ⟨u, hu_below⟩, i))).trans (by rw [Θ_u, Θ_U])

/-- Base change in prime degree for definite U(n) along the step `E'/E` (`New.IsStep`), with `E'`
containing a primitive 5040th root of unity. Let `f` be a form of weight `κ` over `E`, and `F`, `F'`
matching local data above `Z` with levels `L`, `L'` (`New.IsLocalMatching`), acting on forms by
right translation through `a` and `a'`, that is through `New.localFormTranslation`; let `o : ι → J`,
`θ : ι → ℂ`, `j₀ ∈ P`. Suppose the operators of the `F j` commute, and so do those of the `F' j`
(`h_comm`); for `j ∈ P` the operator of `F (o i)` times that of `F j` is that of some `F k` with
`k ∈ P`, the same `k` serving for `F'` (`h_stable`); and (`h_trace`) the operator of `F j₀` has
nonzero trace on `Y ⊓ W`, where `Y` is the `L`-fixed generalised eigenvectors of each `F (o i)` for
`θ i`, for every subrepresentation `W ∋ f` with `Y ⊓ W` finite-dimensional and stable. Then some
form `g` over `E'` of weight `κ.baseChange` is an eigenform with Hecke polynomials `H` (`g ≠ 0`, and
at almost all places `u` of prime norm, `u` is split and `H u` is a Hecke polynomial of `g` at `u`),
a weak base change of `f` off `Z` (`New.IsWeakBaseChange`), fixed by `L'` with eigenvalue `θ i` for
`F' (o i)`, and the image under the operator of `F' j₀` of a vector fixed by `L'`. -/
lemma exists_isWeakBaseChange_of_matching {μ : (𝔸f E)ˣ →* ℂˣ} [hμ : IsStep (E := E) E' μ]
    [HasPrimitiveRoot5040 E'] {κ : Weight E}
    (f : (stdSpace E n).forms κ) {Z : Set (FinPlace E)} {G G' : Type*} [Group G] [Group G']
    {a : G →* Gf E n} {a' : G' →* Gf E' n} {L : Subgroup G} {L' : Subgroup G'} {ι J : Type}
    {P : Set J} {F : J → G → ℂ} {F' : J → G' → ℂ}
    (h_match : IsLocalMatching μ Z a a' L L' P F F') (o : ι → J) (θ : ι → ℂ) (j₀ : J) (hj₀ : j₀ ∈ P)
    (h_comm : ∀ i j : J,
      HeckeCommute (localFormTranslation κ a) L (F i) (F j) ∧
      HeckeCommute (localFormTranslation κ.baseChange a') L' (F' i) (F' j))
    (h_stable : ∀ i : ι, ∀ j ∈ P, ∃ k ∈ P,
      IsHeckeProduct (localFormTranslation κ a) L (F (o i)) (F j) (F k) ∧
      IsHeckeProduct (localFormTranslation κ.baseChange a') L' (F' (o i)) (F' j) (F' k))
    (h_trace : HasNonzeroTraceAround (localFormTranslation κ a)
      (heckeFun (localFormTranslation κ a) L (F j₀))
      (heckeGenEigenspace (localFormTranslation κ a) L (F ∘ o) θ) f) :
    ∃ (g : (stdSpace E' n).forms κ.baseChange) (H : FinPlace E' → Polynomial ℂ),
      IsEigenform g.val H ∧
      IsWeakBaseChange μ Z f.val g.val ∧
      IsHeckeEigenvector (localFormTranslation κ.baseChange a') L' (F' ∘ o) θ g ∧
      g ∈ (levelSpace (localFormTranslation κ.baseChange a') L').map
        (heckeFun (localFormTranslation κ.baseChange a') L' (F' j₀)) := by
  -- Build the transfer level `𝓛` over `E'` (`exists_isTransferLevel`) and an eigenvector `g` at it
  -- (`exists_eigenvector_of_isTransferLevel`). Then `g` is an eigenform, and it is a weak base
  -- change of `f`: above an unramified place `w ∉ Z ∪ Z̄` at which `f` is spherical, `𝓛` is
  -- maximal, and at such a split matched `w`, `g` has the eigenvalues of `f` at every place above
  -- `w`.
  obtain ⟨σ, hσ, r, r', ⟨hF, ha, ha', hZ, L'_σ⟩, hL, L'_open, K, ⟨L'_le_K, K_le⟩, K_coh, hP⟩ :=
    h_match
  have h_off : trivialOn n (placesAbove E' Z) ≤ L'.comap r' := by
    obtain ⟨-, -, r'_ker⟩ := ha'
    rw [← r'_ker]
    exact L'.ker_le_comap r'
  obtain ⟨X, K₁, C, 𝓛, h_level⟩ := exists_isTransferLevel hσ f h_off L'_open L'_σ L'_le_K K_le K_coh
  obtain ⟨g, g_ne, g_fixed, g_local, g_image, g_eigen, g_agree⟩ :=
    exists_eigenvector_of_isTransferLevel hσ f hF ha ha' hL hP h_level o θ j₀ hj₀ h_comm h_stable
      h_trace
  have g_poly (u : FinPlace E') (hu : u.IsSplit) (hu_off : u ∉ placesAbove E' Z)
      (hu_max : maxCompactAt n u ≤ 𝓛) : ∃ P : Polynomial ℂ, HasHeckePolyAt g.val u hu P :=
    let ⟨t, ht⟩ := g_eigen u hu hu_off hu_max
    ⟨_, (hasHeckePolyAt_iff hu).mpr ⟨levelSpace_anti hu_max g_fixed, t, rfl, ht⟩⟩
  obtain ⟨H, g_eigenform⟩ :=
    exists_isEigenform_of_hasHeckePolyAt (by simpa using g_ne) h_level.isOpen
      (tendsto_place_comap_cofinite _ hZ.conjClosure.compl_mem_cofinite) g_poly
  refine ⟨g, H, g_eigenform, isWeakBaseChange_of_forall_heckeSplit_eq_smul hZ ?_ ?_, g_local,
    g_image⟩
  · intro w hw hw_unram hf u hu_below
    have hu_above : {u} ⊆ placesAbove E' {w} := by simp [placesAbove, ← hu_below]
    have hu_max : maxCompactAt n u ≤ 𝓛 :=
      h_level.kf_inf_supportedOn_le_of_mem_sphericalAt w hw hw_unram hf hu_above
    exact levelSpace_anti hu_max g_fixed
  · intro w hw hw_split hw_matched hf t ht
    exact g_agree w (h_level.mem_of_isMatched w hw hw_split hw_matched hf) hw_split t ht

end New
