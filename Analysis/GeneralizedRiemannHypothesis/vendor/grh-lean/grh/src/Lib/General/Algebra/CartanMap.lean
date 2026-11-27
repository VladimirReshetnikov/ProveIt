import Lib.ClassField.GaloisCohomology.ContinuousCocycles

/-!
# Higman's criterion, dévissage and multiplicative functions on finite modules (Cartan map)

Tools that reduce a statement about finite `l`-power-torsion discrete `G`-modules to simple cases;
they serve the inequality of local duality (`Lib.ClassField.LocalDuality.DualityInequality`) and the
cocycle counts of `Lib.ClassField.GreenbergWiles.CocycleCounts`.

* `New.DiscreteModule.IsHigmanProjective`: Higman's criterion, some additive `τ` has `∑ g τ g⁻¹ = 1`
  over `G ⧸ Q`.
* `New.DiscreteModule.FiniteKilledFixedInj`: the module is finite, killed by `n` and fixed by `Q`,
  and `ρ z - m` is injective on it.
* `New.DiscreteModule.diagonalPermModule`: the functions `Y → A` with the diagonal action of `G`.
* `New.DiscreteModule.devissage_induction`: dévissage to modules killed by `l` and fixed by a normal
  subgroup `P`.
* `New.DiscreteModule.exists_open_sylow`: an open `P ≥ U` of index prime to `l` whose elements have
  an `l`-power power in `U`.
* `New.DiscreteModule.IsMultiplicative.eq_one_of_eq_one_on_isHigmanProjective`: on the finite
  modules killed by `l` and fixed by `U` with `ρ z - 1` injective, `z` central modulo `U`, a
  function with values in `ℚ≥0` that is multiplicative in short exact sequences is `1` as soon as it
  is `1` on the modules with Higman's property.

Notions from other files:
* `New.DiscreteModule R G`: an `R`-module with the discrete topology and a continuous `R`-linear
  action `ρ` of the topological group `G`.

## Relation to the literature

Known result: The Cartan map has finite cokernel. It is stated for multiplicative functions with
nonnegative rational values on finite modules killed by a prime on which one element, central modulo
the level, fixes no nonzero vector, with projectivity read as Higman's property. It is proved using
functions on two parallel affine hyperplanes instead of Brauer characters or Artin induction.
Source: J.-P. Serre, Linear Representations of Finite Groups (1977), Thm 35; for the route by
induction from cyclic subgroups in the local Euler characteristic formula, Milne, Arithmetic Duality
Theorems, I 2.10-2.12.
-/

namespace New.DiscreteModule

open MulAction Equiv QuotientGroup Finset Finite Submonoid Function commutatorElement Subgroup
  Module.End Fintype

attribute [local instance low] Fintype.ofFinite

variable {R G : Type} [CommRing R] [Group G] [TopologicalSpace G]

/-! ### Finite modules, Higman's criterion and function modules -/

/-- Higman's criterion for the discrete `G`-module `A` relative to a subgroup `Q` of finite index:
some additive `τ : A → A` has `∑ g τ g⁻¹ = 1`, summed over the chosen representatives `g.out` of the
cosets in `G ⧸ Q`. The map `τ` is not asked to commute with `Q`. If `Q` acts trivially on `A`, the
choice of representatives does not matter, see `TrivialOn.isHigmanProjective_iff`. -/
def IsHigmanProjective (Q : Subgroup G) [Finite (G ⧸ Q)] (A : DiscreteModule R G) : Prop :=
  ∃ τ : A →+ A, ∀ a : A.V, ∑ g : G ⧸ Q, A.ρ g.out (τ (A.ρ g.out⁻¹ a)) = a

/-- The subgroup `Q` of `G` acts trivially on the discrete `G`-module `A`. -/
abbrev TrivialOn (Q : Subgroup G) (A : DiscreteModule R G) : Prop := ∀ g ∈ Q, ∀ m : A.V, A.ρ g m = m

/-- If `Q` acts trivially on `A`, the conjugate `g τ g⁻¹` of an additive map `τ` depends only on
the coset of `g` in `G ⧸ Q`. -/
lemma TrivialOn.conj_apply_eq_of_mk_eq {Q : Subgroup G} {A : DiscreteModule R G}
    (hA : A.TrivialOn Q) (τ : A →+ A) {g g' : G} (h_coset : (g : G ⧸ Q) = (g' : G ⧸ Q)) (a : A.V) :
    A.ρ g (τ (A.ρ g⁻¹ a)) = A.ρ g' (τ (A.ρ g'⁻¹ a)) := by
  obtain ⟨q, hq, rfl⟩ : ∃ q ∈ Q, g' = g * q := ⟨g⁻¹ * g', QuotientGroup.eq.1 h_coset, by simp⟩
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply, hA q hq, hA q⁻¹ (Q.inv_mem hq)]

/-- If `Q` has finite index and acts trivially on `A`, Higman's criterion may be checked with any
system `s` of representatives of the cosets in `G ⧸ Q`. -/
lemma TrivialOn.isHigmanProjective_iff {Q : Subgroup G} [Finite (G ⧸ Q)] {A : DiscreteModule R G}
    (hA : A.TrivialOn Q) (s : G ⧸ Q → G) (hs : ∀ x : G ⧸ Q, (s x : G ⧸ Q) = x) :
    A.IsHigmanProjective Q ↔
      ∃ τ : A →+ A, ∀ a : A.V, ∑ x : G ⧸ Q, A.ρ (s x) (τ (A.ρ (s x)⁻¹ a)) = a := by
  have h_term (τ : A →+ A) (a : A.V) (x : G ⧸ Q) :
      A.ρ x.out (τ (A.ρ x.out⁻¹ a)) = A.ρ (s x) (τ (A.ρ (s x)⁻¹ a)) :=
    hA.conj_apply_eq_of_mk_eq τ ((QuotientGroup.out_eq' x).trans (hs x).symm) a
  simp only [IsHigmanProjective, h_term]

/-- For a discrete `G`-module `A` and a finite set `Y` with an action of a discrete group `Δ`, the
`G × Δ`-module of functions `f : Y → A`, with `((g, δ) f) x = g (f (δ⁻¹ x))`. -/
abbrev permModule (A : DiscreteModule R G) {Δ : Type} [Group Δ] [TopologicalSpace Δ]
    [DiscreteTopology Δ] (Y : Type) [Finite Y] [MulAction Δ Y] : DiscreteModule R (G × Δ) :=
  of (V := Y → A)
    { toFun g := LinearMap.pi fun x : Y ↦ A.ρ g.1 ∘ₗ LinearMap.proj (g.2⁻¹ • x)
      map_one' := by aesop
      map_mul' := by aesop (add simp mul_smul) }

/-- The discrete `G`-module `A` is finite and killed by `n`, the subgroup `Q` acts trivially on it,
and `ρ z - m` is injective on it. -/
structure FiniteKilledFixedInj (n : ℕ) (Q : Subgroup G) (z : G) (m : ℕ) (A : DiscreteModule R G) :
    Prop where
  /-- The module is finite. -/
  finite : Finite A
  /-- The module is killed by `n`. -/
  nsmul_eq_zero : ∀ a : A, n • a = 0
  /-- The subgroup `Q` acts trivially. -/
  trivialOn : A.TrivialOn Q
  /-- The endomorphism `ρ z - m` is injective. -/
  injective : Injective ⇑(A.ρ z - m)

section FiniteKilledFixedInj
variable {n : ℕ} {Q : Subgroup G} {z : G} {m : ℕ}

/-- Being finite, killed by `n`, fixed by `Q` and with `ρ z - m` injective passes from the middle
term `B` of a short exact sequence `0 → A → B → M → 0` to `A`. -/
lemma FiniteKilledFixedInj.left_of_isShortExact {A B M : DiscreteModule R G} {ι : A.Hom B}
    {π : B.Hom M} (h_exact : IsShortExact ι π) (hB : B.FiniteKilledFixedInj n Q z m) :
    A.FiniteKilledFixedInj n Q z m := by
  -- test the properties of `A` after the injective `ι`
  obtain ⟨h_fin, h_killed, h_triv, h_inj⟩ := hB
  obtain ⟨ι_inj, -, -⟩ := h_exact
  refine ⟨of_injective ι ι_inj, fun a ↦ ι_inj ?_, fun g hg a ↦ ι_inj ?_, fun a b hab ↦ ?_⟩
  · simp [h_killed]
  · simp [ι.isIntertwining, h_triv g hg]
  · refine ι_inj (h_inj (?_ : (B.ρ z - m) (ι a) = (B.ρ z - m) (ι b)))
    simpa [ι.isIntertwining] using congrArg ι hab

/-- Being finite, killed by `n`, fixed by `Q` and with `ρ z - m` injective passes from the middle
term `B` of a short exact sequence `0 → A → B → M → 0` to `M`. -/
lemma FiniteKilledFixedInj.right_of_isShortExact {A B M : DiscreteModule R G} {ι : A.Hom B}
    {π : B.Hom M} (h_exact : IsShortExact ι π) (hB : B.FiniteKilledFixedInj n Q z m) :
    M.FiniteKilledFixedInj n Q z m := by
  -- test the properties of `M` on the image of the surjective `π`
  obtain ⟨h_fin, h_killed, h_triv, h_inj⟩ := hB
  obtain ⟨-, -, π_surj⟩ := h_exact
  have hM : Finite M := of_surjective π π_surj
  refine ⟨hM, π_surj.forall.2 fun b ↦ ?_, fun g hg ↦ π_surj.forall.2 fun b ↦ ?_,
    injective_iff_surjective.2 (π_surj.forall.2 fun b ↦ ?_)⟩
  · rw [← map_nsmul, h_killed, map_zero]
  · rw [← π.isIntertwining, h_triv g hg]
  · -- on finite modules injective means surjective, which passes from `B` to `M`
    obtain ⟨c, rfl⟩ : ∃ c : B, (B.ρ z - m) c = b := injective_iff_surjective.1 h_inj b
    exact ⟨π c, by simp [← π.isIntertwining]⟩

end FiniteKilledFixedInj

/-- Let `Q` have finite index in `G`. If `A` is killed by an integer `n` prime to the index of `Q`,
then `A` satisfies Higman's criterion relative to `Q`. -/
lemma isHigmanProjective_of_coprime_index {n : ℕ} {Q : Subgroup G} [Finite (G ⧸ Q)]
    {A : DiscreteModule R G} (h_killed : ∀ a : A, n • a = 0) (h_coprime : n.Coprime Q.index) :
    A.IsHigmanProjective Q := by
  -- with `a * n + b * [G : Q] = 1`, take `b` times the identity; `n` kills `A`
  obtain ⟨a, b, bezout⟩ : ∃ a b : ℤ, a * n + b * Q.index = 1 := h_coprime.isCoprime
  refine ⟨b • AddMonoidHom.id A, fun x ↦ ?_⟩
  have h_smul : (a * n + b * Q.index) • x = x := by rw [bezout, one_smul]
  simpa [add_smul, mul_smul, h_killed, mul_comm b, Subgroup.index] using h_smul

/-- Let `Q` have finite index in `G`, and let `A` be finite, killed by `n` and fixed by `Q`, with
`ρ z - m` injective. If `n` is prime to the index of `Q`, then `A` satisfies Higman's criterion
relative to `Q`. -/
lemma FiniteKilledFixedInj.isHigmanProjective_of_coprime {n : ℕ} {Q : Subgroup G} [Finite (G ⧸ Q)]
    {z : G} {m : ℕ} {A : DiscreteModule R G} (hA : A.FiniteKilledFixedInj n Q z m)
    (h_coprime : n.Coprime Q.index) : A.IsHigmanProjective Q :=
  isHigmanProjective_of_coprime_index hA.nsmul_eq_zero h_coprime

/-! ### Dévissage and Sylow subgroups -/

/-- Dévissage. Let `l` be prime, `n = l ^ j`, and let `p` be a property of the modules that are
finite, killed by `n`, fixed by `Q` and on which `ρ z - m` is injective. Let `P` be a normal
subgroup each of whose elements `g` has a power `g ^ l ^ i` in `Q`. If `p` holds for the modules
that are also killed by `l` and fixed by `P`, and is stable under extensions, then it always
holds. -/
@[elab_as_elim]
lemma devissage_induction {l n : ℕ} [hl : Fact l.Prime] {z : G} {m j : ℕ} (hn : l ^ j = n)
    (P Q : Subgroup G) [P.Normal]
    {p : ∀ A : DiscreteModule R G, FiniteKilledFixedInj n Q z m A → Prop}
    (h_pow : ∀ g ∈ P, ∃ i : ℕ, g ^ l ^ i ∈ Q)
    (h_base : ∀ (A : DiscreteModule R G) (hA : FiniteKilledFixedInj n Q z m A),
      FiniteKilledFixedInj l P z m A → p A hA)
    (h_ext : ∀ {A B C : DiscreteModule R G} {ι : Hom A B} {π : Hom B C}
      (h_exact : IsShortExact ι π) (hB : FiniteKilledFixedInj n Q z m B),
      p A (hB.left_of_isShortExact h_exact) → p C (hB.right_of_isShortExact h_exact) → p B hB) :
    ∀ (B : DiscreteModule R G) (hB : FiniteKilledFixedInj n Q z m B), p B hB := by
  -- Induction on the length of `B`. If `B ≠ 0`, the submodule `W` of the vectors fixed by `P` and
  -- killed by `l` is not zero; `W` is a base case, `B ⧸ W` is shorter, and `B` is their extension.
  subst hn
  refine (wellFounded_lt.onFun (f := fun B : DiscreteModule R G ↦ Module.length R B)).fix ?_
  intro B ih ⟨h_fin, h_killed, h_triv, h_inj⟩
  have h_group : IsPGroup l (Multiplicative B) := fun x ↦ ⟨j, h_killed x⟩
  obtain h_one | h_dvd := h_group.card_eq_or_dvd
  · -- The zero module is a base case.
    have : Subsingleton B := card_le_one_iff_subsingleton.1 h_one.le
    exact h_base B _ ⟨h_fin, fun _ ↦ Subsingleton.elim .., fun _ _ _ ↦ Subsingleton.elim .., h_inj⟩
  -- `P` acts through an `l`-group, as `Q` acts trivially. So `l` divides the number of fixed
  -- vectors, and by Cauchy's theorem one of them, `b`, has order `l`.
  have h_image : IsPGroup l (P.map B.ρ.toHomUnits) := by
    rintro ⟨_, g, hg, rfl⟩
    obtain ⟨i, hi⟩ := h_pow g hg
    exact ⟨i, by simp [Subtype.ext_iff, Units.ext_iff, LinearMap.ext_iff, ← map_pow, h_triv _ hi]⟩
  have h_fixed : l ∣ Nat.card (FixedPoints.addSubgroup (P.map B.ρ.toHomUnits) B) :=
    ((h_image.card_modEq_card_fixedPoints B).dvd_iff dvd_rfl).1 h_dvd
  obtain ⟨⟨b, hb_fixed⟩, hb_order⟩ := exists_prime_addOrderOf_dvd_card' l h_fixed
  rw [AddSubgroup.addOrderOf_mk] at hb_order
  let W : Submodule R B := (B.restrictTo P).H0 ⊓ (l • LinearMap.id : B →ₗ[R] B).ker
  have mem_W {x : B} : x ∈ W ↔ (∀ g : P, B.ρ g x = x) ∧ l • x = 0 := Iff.rfl
  -- `W` is stable under `G` because `P` is normal.
  have hW_stable (g : G) : W ≤ W.comap (B.ρ g) := fun x hx ↦
    mem_W.2 ⟨B.ρ.le_comap_invariants P g (mem_W.1 hx).1, by simp [← map_nsmul, (mem_W.1 hx).2]⟩
  have hW_base : (B.submodule W hW_stable).FiniteKilledFixedInj l P z m :=
    ⟨inferInstance, fun x ↦ Subtype.ext (mem_W.1 x.property).2,
      fun g hg x ↦ Subtype.ext ((mem_W.1 x.property).1 ⟨g, hg⟩),
      fun x y hxy ↦ Subtype.ext (h_inj (by simpa using Subtype.ext_iff.1 hxy))⟩
  have hb_mem : b ∈ W :=
    mem_W.2 ⟨fun g ↦ hb_fixed ⟨_, P.mem_map_of_mem _ g.property⟩, by simp [← hb_order]⟩
  have hb_ne : b ≠ 0 := fun hb ↦ hl.out.ne_one (by rw [← hb_order, hb, addOrderOf_zero])
  exact h_ext (B.isShortExact_submodule W hW_stable) _ (h_base _ _ hW_base)
    (ih _ (W.length_quotient_lt (W.ne_bot_iff.2 ⟨b, hb_mem, hb_ne⟩)) _)

/-- For a prime `l` and `U` open normal in a compact group there is an open subgroup `P ≥ U` of
index prime to `l` each of whose elements `g` has a power `g ^ l ^ k` in `U`. -/
lemma exists_open_sylow (l : ℕ) [hl : Fact l.Prime] (U : OpenNormalSubgroup G)
    [IsTopologicalGroup G] [CompactSpace G] :
    ∃ P : OpenSubgroup G,
      (U : Subgroup G) ≤ P ∧ l.Coprime P.toSubgroup.index ∧ ∀ g ∈ P, ∃ k : ℕ, g ^ l ^ k ∈ U := by
  -- `P` is the preimage in `G` of a Sylow `l`-subgroup `T` of the finite quotient `G ⧸ U`; the
  -- image of `g ∈ P` lies in that `l`-group, so it is killed by a power of `l`.
  obtain ⟨T⟩ : Nonempty (Sylow l (G ⧸ (U : Subgroup G))) := Sylow.nonempty
  let P : Subgroup G := T.toSubgroup.comap (mk' (U : Subgroup G))
  have hU_le : (U : Subgroup G) ≤ P := le_comap_mk' (U : Subgroup G) T.toSubgroup
  refine ⟨⟨P, isOpen_mono hU_le U.toOpenSubgroup.isOpen⟩, hU_le, ?_, fun g hg ↦ ?_⟩
  · simp [P, T.not_dvd_index, T.index_comap, hl.out.coprime_iff_not_dvd]
  · obtain ⟨k, hk⟩ := T.isPGroup' ⟨g, hg⟩
    exact ⟨k, (eq_one_iff _).1 (by simpa [Subtype.ext_iff] using hk)⟩

/-! ### Function modules and multiplicative functions -/

/-- Let `U` be open normal in `G`, let `S` be normal in `G ⧸ U` and let `Y` be a finite
`(G ⧸ U) ⧸ S`-set. The `G`-module of functions `f : Y → A` with the diagonal action
`(g f) y = g (f (g⁻¹ y))`, where `g` acts on `Y` through its image in `(G ⧸ U) ⧸ S`. -/
abbrev diagonalPermModule [IsTopologicalGroup G] (A : DiscreteModule R G)
    (U : OpenNormalSubgroup G) (S : Subgroup (G ⧸ (U : Subgroup G))) [S.Normal] (Y : Type)
    [Finite Y] [MulAction ((G ⧸ (U : Subgroup G)) ⧸ S) Y] : DiscreteModule R G :=
  letI : MulAction (G ⧸ (U : Subgroup G)) Y := compHom Y (mk' S)
  (A.permModule Y).restrictAlong ⟨(MonoidHom.id G).prod (mk' (U : Subgroup G)),
    Continuous.prodMk continuous_id continuous_mk⟩

/-- Let `l` be prime, `U` open normal in the compact group `G`, and suppose every commutator
`⁅z, g⁆` lies in `U`. Then `G ⧸ U` has a normal subgroup of order prime to `l` that contains the
image of some power `z ^ l ^ j`. -/
lemma exists_normal_pow_mem_not_dvd_card (l : ℕ) [hl : Fact l.Prime] (U : OpenNormalSubgroup G)
    {z : G} [IsTopologicalGroup G] [CompactSpace G] (hz_central : ∀ g : G, ⁅z, g⁆ ∈ U) :
    ∃ (S : Subgroup (G ⧸ (U : Subgroup G))) (j : ℕ),
      S.Normal ∧ (z : G ⧸ (U : Subgroup G)) ^ l ^ j ∈ S ∧ ¬l ∣ Nat.card S := by
  -- The image of `z` in `G ⧸ U` has order `l ^ j * n` with `n` prime to `l`. Its power `z ^ l ^ j`
  -- generates a central subgroup `S` of order `n`.
  obtain ⟨j, n, hn, h_order⟩ :
      ∃ j n : ℕ, ¬l ∣ n ∧ orderOf (z : G ⧸ (U : Subgroup G)) = l ^ j * n :=
    WfDvdMonoid.max_power_factor (orderOf_pos _).ne' hl.out
  let S : Subgroup (G ⧸ (U : Subgroup G)) := zpowers (z ^ l ^ j)
  have hS_card : Nat.card S = n := by
    simp [S, Fintype.card_zpowers, orderOf_pow, h_order, hl.out.pos]
  have central (g : G) : Commute (z : G ⧸ (U : Subgroup G)) g :=
    commutatorElement_eq_one_iff_commute.1 ((eq_one_iff _).2 (hz_central g))
  refine ⟨S, j, ⟨?_⟩, mem_zpowers _, by rwa [hS_card]⟩
  rintro _ ⟨i, rfl⟩ ⟨g⟩
  exact ⟨i, eq_mul_inv_of_mul_eq (((central g).pow_left _).zpow_left i)⟩

/-- Let `l` be prime and let `A` be finite, killed by `l` and fixed by `U`, with `ρ z - 1`
injective. If `S` contains the image of a power `z ^ l ^ j`, the functions `Y → A` on a finite
`(G ⧸ U) ⧸ S`-set `Y`, with the diagonal action of `G`, have the same properties. -/
lemma FiniteKilledFixedInj.diagonalPermModule [IsTopologicalGroup G] {l : ℕ} [hl : Fact l.Prime]
    {U : OpenNormalSubgroup G} {z : G} {A : DiscreteModule R G}
    (hA : A.FiniteKilledFixedInj l U z 1) {S : Subgroup (G ⧸ (U : Subgroup G))} [S.Normal] {j : ℕ}
    (hz_mem : (z : G ⧸ (U : Subgroup G)) ^ l ^ j ∈ S) (Y : Type) [Finite Y]
    [MulAction ((G ⧸ (U : Subgroup G)) ⧸ S) Y] :
    (A.diagonalPermModule U S Y).FiniteKilledFixedInj l U z 1 := by
  obtain ⟨h_fin, h_killed, h_triv, h_inj⟩ := hA
  let B : DiscreteModule R G := A.diagonalPermModule U S Y
  refine ⟨Pi.finite, fun f ↦ funext fun y ↦ h_killed (f y), fun g hg f ↦ funext fun y ↦ ?_,
    (injective_iff_map_eq_zero _).2 fun f hf ↦ funext fun y ↦ ?_⟩
  · simpa [(eq_one_iff g).2 hg] using h_triv g hg (f y)
  · -- A function fixed by `z` is fixed by `z ^ l ^ j`, which acts trivially on `Y`.
    have hf_fixed : B.ρ z f = f := by simpa [B, sub_eq_zero] using hf
    have h_fixed : B.ρ (z ^ l ^ j) f = f := by simp [Module.End.pow_apply, iterate_fixed hf_fixed]
    have h_value : (A.ρ z ^ l ^ j) (f y) = f y := by
      simpa [B, (eq_one_iff _).2 hz_mem, compHom_smul_def] using congrFun h_fixed y
    -- As `l` kills `A`, `z ^ l ^ j - 1` acts as `(z - 1) ^ l ^ j`, which is injective.
    have frobenius (x : A) : (A.ρ z ^ l ^ j) x = ((A.ρ z - 1) ^ l ^ j) x + x := by
      simpa [h_killed] using LinearMap.congr_fun
        ((Commute.one_right (A.ρ z - 1)).add_pow_prime_pow_eq hl.out j) x
    exact iterate_injective h_inj (l ^ j) (a₂ := 0) (by simpa [frobenius] using h_value)

open scoped Classical in
/-- Let the prime `l` kill `A` and not divide the order of `S`. The functions `Y → A` on a finite
`(G ⧸ U) ⧸ S`-set `Y`, with the diagonal action of `G`, satisfy Higman's criterion relative to `U`
if some `a : Y → ZMod l` has `∑ g, a (g⁻¹ • y) = 1` for every `y`, the sum running over
`(G ⧸ U) ⧸ S`. -/
lemma isHigmanProjective_diagonalPermModule [IsTopologicalGroup G] [CompactSpace G] {l : ℕ}
    [Fact l.Prime] {U : OpenNormalSubgroup G} {A : DiscreteModule R G}
    (h_killed : ∀ x : A, l • x = 0) {S : Subgroup (G ⧸ (U : Subgroup G))} [S.Normal]
    (hS_card : ¬l ∣ Nat.card S) {Y : Type} [Finite Y] [MulAction ((G ⧸ (U : Subgroup G)) ⧸ S) Y]
    (a : Y → ZMod l) (h_sum : ∀ y : Y, ∑ g : (G ⧸ (U : Subgroup G)) ⧸ S, a (g⁻¹ • y) = 1) :
    (A.diagonalPermModule U S Y).IsHigmanProjective U := by
  -- Higman's map multiplies the value at `y` by `a y / #S`. In the sum of its conjugates over
  -- `G ⧸ U` each coset of `S` occurs `#S` times, so the sum is the trace of `a`, which is `1`.
  let : Module (ZMod l) A := AddCommGroup.zmodModule h_killed
  let : MulAction (G ⧸ (U : Subgroup G)) Y := compHom Y (mk' S)
  refine ⟨.pi fun y ↦ (a y / Nat.card S) • Pi.evalAddMonoidHom (fun _ ↦ A) y,
    fun f ↦ funext fun y ↦ ?_⟩
  have h_trace : ∑ g : G ⧸ (U : Subgroup G), a (g⁻¹ • y) = Nat.card S :=
    calc _ = ∑ p : ((G ⧸ (U : Subgroup G)) ⧸ S) × S, a (p.1⁻¹ • y) :=
          S.groupEquivQuotientProdSubgroup.sum_comp fun p ↦ a (p.1⁻¹ • y)
      _ = Nat.card S := by simp [sum_prod_type_right, h_sum y]
  have h_card_ne : (Nat.card S : ZMod l) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  simp [-Nat.card_eq_fintype_card, ZMod.map_smul, ← sum_smul, ← sum_div, h_trace, h_card_ne]

variable (R) in
open scoped Classical in
/-- Let `l` be prime, `U` open normal in the compact group `G`, and suppose every commutator
`⁅z, g⁆` lies in `U`. Then there is a normal subgroup `S` of `G ⧸ U` with the following property.
Let `A` be finite, killed by `l` and fixed by `U`, with `ρ z - 1` injective, and let `Y` be a finite
`(G ⧸ U) ⧸ S`-set. Then the module of functions `Y → A` with the diagonal action of `G` has the
same properties. It satisfies Higman's criterion relative to `U` if some `a : Y → ZMod l` has
`∑ g, a (g⁻¹ • y) = 1` for every `y`, the sum running over `(G ⧸ U) ⧸ S`. -/
lemma exists_diagonalPermModule_isHigmanProjective (l : ℕ) [Fact l.Prime] (U : OpenNormalSubgroup G)
    {z : G} [IsTopologicalGroup G] [CompactSpace G] (hz_central : ∀ g : G, ⁅z, g⁆ ∈ U) :
    ∃ (S : Subgroup (G ⧸ (U : Subgroup G))) (_hS : S.Normal),
      ∀ {A : DiscreteModule R G}, A.FiniteKilledFixedInj l U z 1 →
      ∀ (Y : Type) [Finite Y] [MulAction ((G ⧸ (U : Subgroup G)) ⧸ S) Y],
        (A.diagonalPermModule U S Y).FiniteKilledFixedInj l U z 1 ∧
        ∀ a : Y → ZMod l, (∀ y : Y, ∑ g : (G ⧸ (U : Subgroup G)) ⧸ S, a (g⁻¹ • y) = 1) →
          (A.diagonalPermModule U S Y).IsHigmanProjective U := by
  obtain ⟨S, j, hS, hz_mem, hS_card⟩ := exists_normal_pow_mem_not_dvd_card l U hz_central
  exact ⟨S, hS, fun hA Y _ _ ↦ ⟨hA.diagonalPermModule hz_mem Y,
    isHigmanProjective_diagonalPermModule hA.nsmul_eq_zero hS_card⟩⟩

/-- The complement of the orbit of `y` in the `Δ`-set `Y`, as a `Δ`-set. -/
abbrev orbitCompl (Δ : Type*) {Y : Type*} [Group Δ] [MulAction Δ Y] (y : Y) : SubMulAction Δ Y :=
  (SubMulAction.mk (orbit Δ y) fun g : Δ ↦ mem_orbit_of_mem_orbit g)ᶜ

/-- Let `Δ` be a finite group and `f` a function of finite `Δ`-sets with values in `ℚ≥0` that is `1`
on empty sets and has `f Y = f (Y ∖ Δ y) * f (Δ ⧸ Stab y)` for `y` in `Y`. If `X` has a fixed point
`x` and `f (X × Δ ⧸ K) = 1` for all subgroups `K`, then `f (Δ ⧸ K) = 1` for all `K`. -/
lemma eq_one_of_prod_quotient.{u, v} (Δ : Type (max u v)) {X : Type u} [Group Δ] [Finite Δ]
    [Finite X] [MulAction Δ X] (f : ∀ (Y : Type (max u v)) [Finite Y] [MulAction Δ Y], ℚ≥0)
    (x : MulAction.fixedPoints Δ X)
    (h_empty : ∀ (Y : Type (max u v)) [Finite Y] [MulAction Δ Y], IsEmpty Y → f Y = 1)
    (h_orbit : ∀ (Y : Type (max u v)) [Finite Y] [MulAction Δ Y] (y : Y),
      f Y = f (orbitCompl Δ y) * f (Δ ⧸ stabilizer Δ y))
    (h_prod : ∀ K : Subgroup Δ, f (X × Δ ⧸ K) = 1) :
    ∀ K : Subgroup Δ, f (Δ ⧸ K) = 1 := by
  -- Induction on `K`: assume the claim for all smaller subgroups.
  refine wellFounded_lt.fix fun K ih ↦ ?_
  -- A set over `Δ ⧸ K` has orbits `Δ ⧸ K'` with `K' ≤ K`, so `f` of it is a power of `f (Δ ⧸ K)`.
  have mem_powers : ∀ (Y : Type (max u v)) [Finite Y] [MulAction Δ Y],
      (Y →[Δ] Δ ⧸ K) → f Y ∈ Submonoid.powers (f (Δ ⧸ K)) := by
    refine (measure Nat.card).wf.fix fun Y ihY _ _ p ↦ ?_
    obtain hY | ⟨⟨y₀⟩⟩ := isEmpty_or_nonempty Y
    · simp [h_empty Y hY]
    -- move `y₀` to a point `y` over the base point, whose stabilizer lies in `K`
    obtain ⟨y, hy⟩ : ∃ y : Y, p y = ⟦1⟧ :=
      (exists_smul_eq Δ (p y₀) ⟦1⟧).elim fun g hg ↦ ⟨g • y₀, (map_smul p g y₀).trans hg⟩
    have stab_le : stabilizer Δ y ≤ K := fun a ha ↦ by
      simpa [hy, QuotientGroup.eq, mem_stabilizer_iff.1 ha] using (map_smul p a y).symm
    rw [h_orbit Y y]
    refine mul_mem (ihY _ (card_subtype_lt (x := y) fun h_compl ↦ h_compl (mem_orbit_self y))
      ⟨fun y' ↦ p y', by simp⟩) ?_
    obtain h_eq | h_lt := stab_le.eq_or_lt
    · rw [h_eq]
      exact Submonoid.mem_powers _
    · simp [ih _ h_lt]
  -- The orbit of `y = (x, 1)` in `X × Δ ⧸ K` is a copy of `Δ ⧸ K`, and its complement lies over
  -- `Δ ⧸ K`. So `1 = f (Δ ⧸ K) ^ (n + 1)` for some `n`.
  let y : X × Δ ⧸ K := (x, ⟦1⟧)
  have h_stab : stabilizer Δ y = K :=
    SetLike.ext fun g ↦ by simp [y, QuotientGroup.eq, x.property g]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, f (Δ ⧸ K) ^ n = f (orbitCompl Δ y) :=
    mem_powers _ ⟨fun y' ↦ y'.val.2, by simp⟩
  have h_pow : f (Δ ⧸ K) ^ (n + 1) = 1 := by
    rw [pow_succ, hn, ← h_prod K, h_orbit (X × Δ ⧸ K) y, h_stab]
  exact (pow_eq_one_iff_of_nonneg zero_le n.succ_ne_zero).1 h_pow

/-- Let `A` be a discrete `G`-module, let `Δ` be a finite group acting on a finite set `Y`, and let
the discrete group `Γ` act through `q : Γ →* Δ`. For a `Γ`-set `X`, `A.permModule X` is the
`G × Γ`-module of functions `f : X → A` with `((g, γ) f) x = g (f (γ⁻¹ x))`. There is a short exact
sequence of these modules from the functions on the complement `C` of the orbit of `y`, to those on
`Y`, to those on the orbit `Δ ⧸ Stab y`. -/
lemma exists_isShortExact_permModule (A : DiscreteModule R G) {Γ Δ Y : Type} [Group Γ]
    [TopologicalSpace Γ] [DiscreteTopology Γ] [Group Δ] [Finite Δ] [Finite Y] [MulAction Δ Y]
    (q : Γ →* Δ) (y : Y) :
    let C : SubMulAction Δ Y := orbitCompl Δ y
    let : MulAction Γ C := compHom C q
    let : MulAction Γ Y := compHom Y q
    let : MulAction Γ (Δ ⧸ stabilizer Δ y) := compHom (Δ ⧸ stabilizer Δ y) q
    ∃ (ι : (A.permModule (Δ := Γ) C).Hom (A.permModule Y))
      (π : (A.permModule (Δ := Γ) Y).Hom (A.permModule (Δ ⧸ stabilizer Δ y))),
      IsShortExact ι π := by
  classical
  intro C _ _ _
  -- `Y` is the disjoint union of the orbit `Δ ⧸ Stab y` and `C`, so functions on `Y` split as
  -- pairs; `ι` is extension by zero and `π` is restriction to the orbit
  let e : (Δ ⧸ stabilizer Δ y) ⊕ C ≃ Y :=
    ((orbitEquivQuotientStabilizer Δ y).symm.sumCongr (.refl C)).trans
      (sumCompl fun x : Y ↦ x ∈ orbit Δ y)
  let E : (Y → A) ≃ₗ[R] (Δ ⧸ stabilizer Δ y → A) × (C → A) :=
    LinearEquiv.funCongrLeft R A e ≪≫ₗ .sumArrowLequivProdArrow _ _ R A
  let ι : (C → A) →ₗ[R] (Y → A) := E.symm ∘ₗ .inr R (Δ ⧸ stabilizer Δ y → A) (C → A)
  let π : (Y → A) →ₗ[R] (Δ ⧸ stabilizer Δ y → A) := .fst R (Δ ⧸ stabilizer Δ y → A) (C → A) ∘ₗ E
  have h_exact : Exact ι π := (E.conj_symm_exact_iff_exact _ _).2 .inr_fst
  have π_apply (v : Y → A) (d : Δ) : π v (d : Δ ⧸ stabilizer Δ y) = v (d • y) := rfl
  have ι_orbit (w : C → A) (d : Δ) : ι w (d • y) = 0 := by
    simp [← π_apply (ι w), h_exact.apply_apply_eq_zero]
  have ι_compl (w : C → A) (c : C) : ι w c = w c := show ι w (e (.inr c)) = w c by simp [ι, E]
  refine ⟨⟨ι, fun g ↦ LinearMap.ext fun w ↦ funext fun x ↦ ?_⟩,
    ⟨π, fun g ↦ LinearMap.ext fun v ↦ funext fun δ ↦ δ.inductionOn fun d ↦ ?_⟩,
    E.symm.injective.comp LinearMap.inr_injective, h_exact, Prod.fst_surjective.comp E.surjective⟩
  · -- `ι` is equivariant: check at a point `x` in the orbit of `y` or outside
    by_cases hx : x ∈ orbit Δ y
    · obtain ⟨d, rfl⟩ := hx
      simp [compHom_smul_def, smul_smul, ι_orbit]
    · lift x to C using hx
      simpa [compHom_smul_def, ι_compl] using congrArg (A.ρ g.1) (ι_compl w ((q g.2)⁻¹ • x)).symm
  · -- `π` is equivariant: check at the coset of `d`
    simp [π_apply, compHom_smul_def, mul_smul]

/-- A permutation of an abelian group killed by `n` that preserves differences is a translation, so
its `n`-th power is trivial. -/
lemma perm_pow_eq_one_of_map_sub {V : Type*} [AddCommGroup V] {n : ℕ}
    (h_killed : ∀ x : V, n • x = 0) {σ : Perm V} (hσ : ∀ x y : V, σ x - σ y = x - y) :
    σ ^ n = 1 := by
  have h_transl : σ = .addLeft (σ 0) :=
    Equiv.ext fun x ↦ by simpa [sub_eq_iff_eq_add'] using hσ x 0
  rw [h_transl]
  simp [h_killed]

/-- The sum `a ↦ ∑ g, a g` of the values of a function on a finite type. -/
def sumValuesHom (Δ M : Type) [Fintype Δ] [AddCommGroup M] : (Δ → M) →+ M :=
  .mk' (fun a : Δ → M ↦ ∑ g : Δ, a g) fun _ _ ↦ sum_add_distrib

/-- A finite group `Δ` acts on the functions `Δ → M` by `(g • a) d = a (g⁻¹ * d)`, and this keeps
the sum of the values. This is its action on the hyperplane of functions with the same sum as `e`,
moved to the functions of sum zero by letting `x` stand for `e + x`. -/
abbrev hyperplaneAction {Δ M : Type} [Group Δ] [Fintype Δ] [AddCommGroup M] (e : Δ → M) :
    MulAction Δ (sumValuesHom Δ M).ker where
  smul g x := ⟨fun d : Δ ↦ -e d + (e (g⁻¹ * d) + x.val (g⁻¹ * d)), by
    have h_sum (a : Δ → M) : ∑ d : Δ, a (g⁻¹ * d) = ∑ d : Δ, a d := sum_comp (.mulLeft g⁻¹) a
    simp [sumValuesHom, sum_add_distrib, h_sum, show ∑ d : Δ, x.val d = 0 from x.property]⟩
  one_smul x := Subtype.ext <| funext fun d ↦
    show -e d + (e (1⁻¹ * d) + x.val (1⁻¹ * d)) = x.val d by simp
  mul_smul g h x := Subtype.ext <| funext fun d ↦ by
    change -e d + (e ((g * h)⁻¹ * d) + x.val ((g * h)⁻¹ * d)) = -e d + (e (g⁻¹ * d) +
      (-e (g⁻¹ * d) + (e (h⁻¹ * (g⁻¹ * d)) + x.val (h⁻¹ * (g⁻¹ * d)))))
    simp [mul_assoc]

/-- The value at `d` of the image of `x` under `g`, for the action on the hyperplane through `e`. -/
lemma hyperplaneAction_toPerm_apply {Δ M : Type} [Group Δ] [Fintype Δ] [AddCommGroup M] (e : Δ → M)
    (g : Δ) (x : (sumValuesHom Δ M).ker) (d : Δ) :
    ((hyperplaneAction e).toPerm g x).val d = -e d + (e (g⁻¹ * d) + x.val (g⁻¹ * d)) :=
  rfl

/-- The action on the hyperplane through `e` is affine, and its linear part is the action on the
hyperplane through `0`. -/
lemma hyperplaneAction_toPerm_sub {Δ M : Type} [Group Δ] [Fintype Δ] [AddCommGroup M] (e : Δ → M)
    (g : Δ) (x y : (sumValuesHom Δ M).ker) :
    (hyperplaneAction e).toPerm g x - (hyperplaneAction e).toPerm g y =
      (hyperplaneAction 0).toPerm g (x - y) := by
  ext d
  simp only [AddSubgroupClass.coe_sub, Pi.sub_apply, hyperplaneAction_toPerm_apply, Pi.zero_apply]
  abel

/-- On the hyperplane through `e`, where `y` stands for `e + y`, the sum over `Δ` of the translates
of evaluation at `1` is constant, equal to the sum of the values of `e`. -/
lemma sum_hyperplaneAction_toPerm_apply_one {Δ M : Type} [Group Δ] [Fintype Δ] [AddCommGroup M]
    (e : Δ → M) (y : (sumValuesHom Δ M).ker) :
    ∑ g : Δ, (e 1 + ((hyperplaneAction e).toPerm g⁻¹ y).val 1) = ∑ g : Δ, e g := by
  simp only [hyperplaneAction_toPerm_apply]
  simp [sum_add_distrib, show ∑ g : Δ, y.val g = 0 from y.property]

/-- A function `φ` of the modules that are finite, killed by `n` and fixed by `Q`, with `ρ z - m`
injective, is multiplicative: `φ B = φ A * φ D` for every short exact `0 → A → B → D → 0` with `B`
of this kind. -/
def IsMultiplicative {n : ℕ} {Q : Subgroup G} {z : G} {m : ℕ}
    (φ : ∀ A : DiscreteModule R G, A.FiniteKilledFixedInj n Q z m → ℚ≥0) : Prop :=
  ∀ {A B D : DiscreteModule R G} {ι : A.Hom B} {π : B.Hom D} (h_exact : IsShortExact ι π)
    (hB : B.FiniteKilledFixedInj n Q z m),
    φ B hB = φ A (hB.left_of_isShortExact h_exact) * φ D (hB.right_of_isShortExact h_exact)

section Multiplicative
variable {l : ℕ} {U : OpenNormalSubgroup G} {z : G} [IsTopologicalGroup G] [CompactSpace G]
  {φ : ∀ A : DiscreteModule R G, A.FiniteKilledFixedInj l U z 1 → ℚ≥0}

/-- Let `φ` be a function of the modules that are finite, killed by `l` and fixed by `U`, with
`ρ z - 1` injective. If `φ` is multiplicative in short exact sequences and `1` on the modules with
Higman's property relative to `U`, then it takes the same value on isomorphic modules. -/
lemma apply_eq_of_equiv (h_mul : IsMultiplicative φ)
    (h_higman : ∀ {B : DiscreteModule R G} (hB : B.FiniteKilledFixedInj l U z 1),
      B.IsHigmanProjective U → φ B hB = 1)
    {A B : DiscreteModule R G} {hA : A.FiniteKilledFixedInj l U z 1}
    {hB : B.FiniteKilledFixedInj l U z 1} (u : A.ρ.Equiv B.ρ) : φ A hA = φ B hB := by
  -- `0 → Z → A → B → 0` is short exact for the zero module `Z`, which has Higman's property
  let Z : DiscreteModule R G := of (V := Unit) 1
  have h_exact : IsShortExact (0 : Z.Hom A) u.toIntertwiningMap :=
    ⟨injective_of_subsingleton _, fun a ↦ by simp, u.surjective⟩
  rw [h_mul h_exact hA, h_higman (hA.left_of_isShortExact h_exact) ⟨0, fun _ ↦ rfl⟩, one_mul]

/-- Let `φ` be a function of the modules that are finite, killed by the prime `l` and fixed by `U`,
with `ρ z - 1` injective, that is multiplicative in short exact sequences and `1` on the modules
with Higman's property relative to `U`. If `s t : G → H` agree modulo a normal subgroup `P` killed
by `l`, then the restrictions of an `H`-module along `s` and `t` have the same `φ`. -/
lemma apply_restrictAlong_eq_of_inv_mul_mem [Fact l.Prime] (h_mul : IsMultiplicative φ)
    (h_higman : ∀ {B : DiscreteModule R G} (hB : B.FiniteKilledFixedInj l U z 1),
      B.IsHigmanProjective U → φ B hB = 1)
    {H : Type} [Group H] [TopologicalSpace H] (P : Subgroup H) [P.Normal]
    (hP_pow : ∀ g ∈ P, g ^ l = 1) {s t : G →ₜ* H} (h_st : ∀ g : G, (t g)⁻¹ * s g ∈ P)
    (B : DiscreteModule R H) (hs : (B.restrictAlong s).FiniteKilledFixedInj l U z 1)
    (ht : (B.restrictAlong t).FiniteKilledFixedInj l U z 1) :
    φ (B.restrictAlong s) hs = φ (B.restrictAlong t) ht := by
  -- By dévissage we may assume that `P` acts trivially. With `Q = ⊥`, `z = 1` and `m = 0` only
  -- "finite and killed by `l`" is asked of `B`.
  have hB : B.FiniteKilledFixedInj l ⊥ 1 0 :=
    ⟨hs.finite, hs.nsmul_eq_zero, by simp [TrivialOn], fun x y ↦ by simp⟩
  revert hs ht
  refine devissage_induction (pow_one l) P ⊥ (fun g hg ↦ ⟨1, by simpa using hP_pow g hg⟩)
    ?_ ?_ B hB
  · intro B _ hB_fixed hs ht
    have h_action (g : G) : B.ρ (s g) = B.ρ (t g) :=
      B.ρ.eq_iff.2 (LinearMap.ext (hB_fixed.trivialOn _ (h_st g)))
    exact apply_eq_of_equiv h_mul h_higman (.mk 1 h_action)
  · intro A B C ι π h_exact _ ihA ihC hs ht
    rw [h_mul (h_exact.restrictAlong s) hs, h_mul (h_exact.restrictAlong t) ht, ihA, ihC]

/-- Let `φ` be a function of the modules that are finite, killed by the prime `l` and fixed by `U`,
with `ρ z - 1` injective, that is multiplicative in short exact sequences and `1` on the modules
with Higman's property relative to `U`. Let `V` be a finite abelian group killed by `l` with two
actions `α`, `β` of `(G ⧸ U) ⧸ S`, where `α` is additive and `β` is affine with linear part `α`.
Then for a `G`-module `B` the functions `V → B` with the diagonal action of `G`
(`diagonalPermModule`) have the same `φ` for `α` and for `β`. -/
lemma apply_diagonalPermModule_eq_of_affine [Fact l.Prime] (h_mul : IsMultiplicative φ)
    (h_higman : ∀ {B : DiscreteModule R G} (hB : B.FiniteKilledFixedInj l U z 1),
      B.IsHigmanProjective U → φ B hB = 1)
    {S : Subgroup (G ⧸ (U : Subgroup G))} [S.Normal] {V : Type} [AddCommGroup V] [Finite V]
    (hV_killed : ∀ x : V, l • x = 0) {α β : MulAction ((G ⧸ (U : Subgroup G)) ⧸ S) V}
    (hα_sub : ∀ (δ : (G ⧸ (U : Subgroup G)) ⧸ S) (x y : V),
      α.toPerm δ x - α.toPerm δ y = α.toPerm δ (x - y))
    (hβ_sub : ∀ (δ : (G ⧸ (U : Subgroup G)) ⧸ S) (x y : V),
      β.toPerm δ x - β.toPerm δ y = α.toPerm δ (x - y))
    (B : DiscreteModule R G)
    (hα : (letI := α; B.diagonalPermModule U S V).FiniteKilledFixedInj l U z 1)
    (hβ : (letI := β; B.diagonalPermModule U S V).FiniteKilledFixedInj l U z 1) :
    φ (letI := α; B.diagonalPermModule U S V) hα =
      φ (letI := β; B.diagonalPermModule U S V) hβ := by
  let : TopologicalSpace (Perm V) := ⊥
  have : DiscreteTopology (Perm V) := ⟨rfl⟩
  -- the quotient map, and the permutations of `V` by which `G` acts
  let q : G →* (G ⧸ (U : Subgroup G)) ⧸ S := (mk' S).comp (mk' (U : Subgroup G))
  let a : G →* Perm V := (α.toPermHom _ V).comp q
  let b : G →* Perm V := (β.toPermHom _ V).comp q
  have h_cont (c : (G ⧸ (U : Subgroup G)) ⧸ S →* Perm V) : Continuous (c.comp q) :=
    (continuous_of_discreteTopology (f := c.comp (mk' S))).comp continuous_mk
  -- `H` consists of the pairs `(g, σ)`, `σ` an affine map of `V` with linear part `a g`
  let H : Subgroup (G × Perm V) :=
    { carrier := {p | ∀ x y : V, p.2 x - p.2 y = a p.1 (x - y)}
      mul_mem' := fun hp hq x y ↦ by simp [hp _, hq _]
      one_mem' := by simp
      inv_mem' := fun hp x y ↦ by simp [eq_symm_apply, ← hp _] }
  -- `a` and `b` give sections of the projection `H → G`
  let s : G →ₜ* H := ⟨((MonoidHom.id G).prod a).codRestrict H fun g ↦ hα_sub (q g),
    (continuous_id.prodMk (h_cont _)).subtype_mk _⟩
  let t : G →ₜ* H := ⟨((MonoidHom.id G).prod b).codRestrict H fun g ↦ hβ_sub (q g),
    (continuous_id.prodMk (h_cont _)).subtype_mk _⟩
  -- they differ by the translations `(1, σ)`, which form a normal subgroup killed by `l`
  let P : Subgroup H := ((MonoidHom.fst G (Perm V)).domRestrict H).ker
  have hP_pow : ∀ g ∈ P, g ^ l = 1 := by
    rintro ⟨⟨g, σ⟩, h_affine⟩ (rfl : g = 1)
    simpa [Subtype.ext_iff] using
      perm_pow_eq_one_of_map_sub hV_killed fun x y ↦ by simpa using h_affine x y
  have h_st (g : G) : (t g)⁻¹ * s g ∈ P := inv_mul_cancel g
  -- by definition the two modules are the restrictions, along `s` and `t`, of the `H`-module of
  -- functions `V → B`
  exact apply_restrictAlong_eq_of_inv_mul_mem h_mul h_higman P hP_pow h_st
    ((B.permModule (Δ := Perm V) V).restrictTo H) hα hβ

end Multiplicative

variable (R) in
/-- Let `l` be prime, `G` a compact topological group and `U` open normal, and let every commutator
`⁅z, g⁆` lie in `U`. Consider the discrete `G`-modules over `R` that are finite, killed by `l` and
fixed by `U`, with `ρ z - 1` injective, and let `φ`, with values in `ℚ≥0`, satisfy `φ B = φ A * φ D`
for every short exact `A → B → D` with `B` of this kind. If `φ B = 1` for every such `B` satisfying
Higman's criterion relative to `U`, that is some additive `τ : B → B` has `∑ g τ g⁻¹ = 1` summed
over representatives `g` of the cosets in `G ⧸ U`, then `φ A = 1` for every such `A`. This is a form
of the known result that the Cartan map has finite cokernel (Serre, Linear Representations of Finite
Groups, §16.1, Theorem 35). -/
lemma IsMultiplicative.eq_one_of_eq_one_on_isHigmanProjective (l : ℕ) [Fact l.Prime]
    (U : OpenNormalSubgroup G) {z : G} {A : DiscreteModule R G}
    (φ : ∀ A : DiscreteModule R G, A.FiniteKilledFixedInj l U z 1 → ℚ≥0)
    [IsTopologicalGroup G] [CompactSpace G] (hz_central : ∀ g : G, ⁅z, g⁆ ∈ U)
    (h_mul : IsMultiplicative φ) (hA : A.FiniteKilledFixedInj l U z 1)
    (h_higman : ∀ {B : DiscreteModule R G} (hB : B.FiniteKilledFixedInj l U z 1),
      B.IsHigmanProjective U → φ B hB = 1) :
    φ A hA = 1 := by
  classical
  -- Let `Δ = (G/U)/S` with `S` from `exists_normal_pow_mem_not_dvd_card`, and `f Y` be `φ` of the
  -- `A`-valued functions on the `Δ`-set `Y`. We apply `eq_one_of_prod_quotient` to the hyperplane
  -- `V` of functions `Δ → ZMod l` of sum zero. Functions on `V × Δ ⧸ K` have the same `φ` as
  -- functions on the product of `Δ ⧸ K` with the hyperplane of sum `1`, which have Higman's
  -- property.
  obtain ⟨S, j, hS, hz_mem, hS_card⟩ := exists_normal_pow_mem_not_dvd_card l U hz_central
  let Δ : Type := (G ⧸ (U : Subgroup G)) ⧸ S
  let V : AddSubgroup (Δ → ZMod l) := (sumValuesHom Δ (ZMod l)).ker
  let : MulAction Δ V := hyperplaneAction 0
  let f (Y : Type) [Finite Y] [MulAction Δ Y] : ℚ≥0 :=
    φ (A.diagonalPermModule U S Y) (hA.diagonalPermModule hz_mem Y)
  have h_empty (Y : Type) [Finite Y] [MulAction Δ Y] (hY : IsEmpty Y) : f Y = 1 :=
    h_higman _ ⟨0, by simp [funext_iff]⟩
  have h_orbit (Y : Type) [Finite Y] [MulAction Δ Y] (y : Y) :
      f Y = f (orbitCompl Δ y) * f (Δ ⧸ stabilizer Δ y) := by
    obtain ⟨ι, π, h_exact⟩ := A.exists_isShortExact_permModule (mk' S) y
    exact h_mul (h_exact.restrictAlong _) (hA.diagonalPermModule hz_mem Y)
  have h_prod (K : Subgroup Δ) : f (V × Δ ⧸ K) = 1 := by
    -- `C e`: the functions `V → Δ ⧸ K → A`, where `V` is read as the hyperplane through `e`
    let B : DiscreteModule R G := A.diagonalPermModule U S (Δ ⧸ K)
    have hB : B.FiniteKilledFixedInj l U z 1 := hA.diagonalPermModule hz_mem (Δ ⧸ K)
    let C (e : Δ → ZMod l) : DiscreteModule R G :=
      letI : MulAction Δ V := hyperplaneAction e; B.diagonalPermModule U S V
    have hC (e : Δ → ZMod l) : (C e).FiniteKilledFixedInj l U z 1 :=
      letI : MulAction Δ V := hyperplaneAction e; hB.diagonalPermModule hz_mem V
    let e₁ : Δ → ZMod l := Pi.single 1 1
    have hC_higman : (C e₁).IsHigmanProjective U :=
      letI : MulAction Δ V := hyperplaneAction e₁
      isHigmanProjective_diagonalPermModule hB.nsmul_eq_zero hS_card (fun y : V ↦ e₁ 1 + y.val 1)
        fun y ↦ (sum_hyperplaneAction_toPerm_apply_one e₁ y).trans (by simp [e₁])
    have hV_killed (x : V) : l • x = 0 := by simp [Subtype.ext_iff, funext_iff, ZMod.natCast_self]
    -- curry, then pass from the hyperplane through `0` to the one through `e₁`
    calc f (V × Δ ⧸ K) = φ (C 0) (hC 0) :=
        apply_eq_of_equiv h_mul h_higman (.mk (.curry R A V (Δ ⧸ K)) fun _ ↦ rfl)
      _ = φ (C e₁) (hC e₁) :=
        apply_diagonalPermModule_eq_of_affine h_mul h_higman hV_killed
          (hyperplaneAction_toPerm_sub 0) (hyperplaneAction_toPerm_sub e₁) B (hC 0) (hC e₁)
      _ = 1 := h_higman (hC e₁) hC_higman
  -- `A` is the module of functions on the point `Δ ⧸ ⊤`
  have h_point : φ A hA = f (Δ ⧸ (⊤ : Subgroup Δ)) := by
    have : Subsingleton (Δ ⧸ (⊤ : Subgroup Δ)) := subsingleton_quotient_top
    have : Unique (Δ ⧸ (⊤ : Subgroup Δ)) := uniqueOfSubsingleton ⟦1⟧
    exact apply_eq_of_equiv h_mul h_higman (.mk (LinearEquiv.funUnique _ R A).symm fun _ ↦ rfl)
  have h_zero : (0 : V) ∈ MulAction.fixedPoints Δ V := fun g ↦
    Subtype.ext <| funext fun d ↦ (hyperplaneAction_toPerm_apply 0 g 0 d).trans (by simp)
  exact h_point.trans (eq_one_of_prod_quotient Δ f ⟨0, h_zero⟩ h_empty h_orbit h_prod ⊤)

end New.DiscreteModule
