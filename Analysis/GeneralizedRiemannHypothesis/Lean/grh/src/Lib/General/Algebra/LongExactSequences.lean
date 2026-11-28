import Lib.Cohomology.Etale.Basic

/-!
# Long exact sequences, four and five lemmas, and Ext with disjoint unions and products

Long exact sequences of abelian groups are packaged as a structure, so that diagram chases, among
them the four and five lemmas, are proved once for all cohomology sequences. In the category
`New.Variety.AbFunctor C` of functors from `C` to abelian groups, with `New.Variety.H N F n`
denoting Ext^n(N, F), short exact sequences in either variable give long exact Ext sequences, and
comparison maps give morphisms between them.

## Main definitions and results

* `New.Variety.LongExactSeq`, `New.Variety.LongExactSeq.Hom`: the sequences and their morphisms.
* `New.Variety.LongExactSeq.Hom.four_lemma` (four lemma) and
  `New.Variety.LongExactSeq.Hom.five_lemma` (five lemma).
* `New.Variety.LongExactSeq.contravariant`, `New.Variety.LongExactSeq.covariant`: the long exact Ext
  sequences of a short exact sequence in the first and in the second variable;
  `New.Variety.Comparison.pull_hom_contravariant` and `New.Variety.Comparison.pull_hom_covariant`
  say that comparison maps give morphisms between them.
* `New.Variety.isCohomEquiv_iff_subsingleton`: in a short exact sequence 0 → X₁ → X₂ → X₃ → 0, the
  map X₁ → X₂ is an equivalence for F iff the quotient X₃ has no cohomology with values in F.
* `New.Variety.H.sigma_bijective`: the cohomology `New.Variety.H (freeAb.obj Y) F n` of a disjoint
  union `Y = New.Variety.sigma X` of set-valued functors is the product of the cohomology groups of
  the `X i`, by pull-back (`New.Variety.H.map`) along the inclusions.
* `New.Variety.H.pi_bijective`: the map Ext^n(N, ∏ F_i) → ∏ Ext^n(N, F_i) is bijective, for the
  objectwise product `New.Variety.piAbFunctor`.

Notions from other files:
* `New.Variety.IsCohomEquiv`: α: N' → N is an equivalence for F: the pull-back
  Ext^n(N,F) → Ext^n(N',F) is bijective for every n; `New.Variety.AllBijective f` says that every
  map f n is bijective.
-/

/-!
## Long exact sequences, their morphisms and their rotation

* `New.Variety.LongExactSeq.rotate`: the same sequence with a `0` put in front, so that the terms
  `C (n - 1)`, `A n`, `B n` take the three places; a statement about one place then applies to the
  other two. `New.Variety.LongExactSeq.Hom.rotate` does the same for a morphism of sequences.
-/

section LongExactSeq

open Function

namespace New.Variety

/-- A long exact sequence of abelian groups 0 → A⁰ → B⁰ → C⁰ → A¹ → B¹ → C¹ → ⋯. -/
structure LongExactSeq.{u} where
  /-- The first terms A n of the sequence, the middle terms B n and the third terms C n. -/
  {A B C : ℕ → Ab.{u}}
  /-- The maps A n → B n. -/
  f (n : ℕ) : A n →+ B n
  /-- The maps B n → C n. -/
  g (n : ℕ) : B n →+ C n
  /-- The connecting maps C n → A (n + 1). -/
  δ (n : ℕ) : C n →+ A (n + 1)
  /-- Exactness at A 0: the first map A 0 → B 0 is injective. -/
  injective_f : Injective (f 0)
  /-- Exactness at B n. -/
  exact_f_g (n : ℕ) : Exact (f n) (g n)
  /-- Exactness at C n. -/
  exact_g_delta (n : ℕ) : Exact (g n) (δ n)
  /-- Exactness at A (n + 1). -/
  exact_delta_f (n : ℕ) : Exact (δ n) (f (n + 1))

/-- Given additive maps a n, b n, c n on the terms of long exact sequences L and L', the statement
that they form a morphism L → L', that is commute with the maps f, g and the connecting maps δ. -/
structure LongExactSeq.Hom (L L' : LongExactSeq) (a : ∀ n : ℕ, L.A n →+ L'.A n)
    (b : ∀ n : ℕ, L.B n →+ L'.B n) (c : ∀ n : ℕ, L.C n →+ L'.C n) where
  /-- The square formed by a n, b n and the maps A n → B n commutes. -/
  comm_f (n : ℕ) (x : L.A n) : b n (L.f n x) = L'.f n (a n x)
  /-- The square formed by b n, c n and the maps B n → C n commutes. -/
  comm_g (n : ℕ) (x : L.B n) : c n (L.g n x) = L'.g n (b n x)
  /-- The square formed by c n, a (n + 1) and the connecting maps C n → A (n + 1) commutes. -/
  comm_delta (n : ℕ) (x : L.C n) : a (n + 1) (L.δ n x) = L'.δ n (c n x)

/-- The sequence L moved by one place, 0 → 0 → A⁰ → B⁰ → C⁰ → ⋯: its terms in degree n are
C^(n-1), Aⁿ, Bⁿ, with C^(-1) = 0. -/
abbrev LongExactSeq.rotate (L : LongExactSeq) : LongExactSeq where
  A
    | 0 => AddCommGrpCat.of PUnit
    | n + 1 => L.C n
  B := L.A
  C := L.B
  f
    | 0 => 0
    | n + 1 => L.δ n
  g := L.f
  δ := L.g
  injective_f := fun x y _ ↦ (rfl : x = y) -- the group in degree `0` is `PUnit`
  exact_f_g
    -- exactness of `0 → L.A 0 → L.B 0` is the injectivity of `L.f 0`
    | 0 => by simp [Exact, ← L.injective_f.eq_iff, eq_comm]
    | n + 1 => L.exact_delta_f n
  exact_g_delta := L.exact_f_g
  exact_delta_f := L.exact_g_delta

/-- Maps cₙ : Cⁿ → C'ⁿ between the third terms of L and L' give maps between the first terms of the
rotated sequences: the zero map in degree 0 and cₙ in degree n + 1. -/
def LongExactSeq.rotateMap {L L' : LongExactSeq} (c : (n : ℕ) → L.C n →+ L'.C n) :
    (n : ℕ) → L.rotate.A n →+ L'.rotate.A n
  | 0 => 0
  | n + 1 => c n

/-- A morphism (a, b, c) of long exact sequences L → L' gives one between the rotated sequences,
whose components are `rotateMap c` = (0, c₀, c₁, …), a and b. -/
lemma LongExactSeq.Hom.rotate {L L' : LongExactSeq} {a : (n : ℕ) → L.A n →+ L'.A n}
    {b : (n : ℕ) → L.B n →+ L'.B n} {c : (n : ℕ) → L.C n →+ L'.C n} (h : Hom L L' a b c) :
    L.rotate.Hom L'.rotate (rotateMap c) a b where
  comm_f
    | 0, _ => map_zero (a 0) -- in degree `0` both maps `f` are zero
    | n + 1, x => h.comm_delta n x
  comm_g := h.comm_f
  comm_delta := h.comm_g

end New.Variety

end LongExactSeq

/-!
## Four and five lemmas and the long exact Ext sequences
-/

namespace New.Variety

open CategoryTheory Abelian.Ext Function LongExactSeq H ShortComplex

variable {A B A' B' : ℕ → Type*} (f : ∀ n : ℕ, A n → B n) {r : ℕ}
  {C C' : Type 1} [Category C] [Category C']
  {F N : AbFunctor C} {F' : AbFunctor C'} {n : ℕ} {N' : AbFunctor C'} {L : LongExactSeq}
  {L' : LongExactSeq} {S : ShortComplex (AbFunctor C)} {S' : ShortComplex (AbFunctor C')}
  {a : (n : ℕ) → L.A n →+ L'.A n} {b : (n : ℕ) → L.B n →+ L'.B n} {c : (n : ℕ) → L.C n →+ L'.C n}

/-! ### Bijectivity up to a given place and bijective sides of a square -/

/-- For maps f_n: A_n → B_n, the first r of the conditions: f₀ injective, f₀ surjective, f₁
injective, f₁ surjective, and so on. -/
def BijectiveUpTo (r : ℕ) : Prop :=
  ∀ n : ℕ, (2 * n < r → Function.Injective (f n)) ∧ (2 * n + 1 < r → Surjective (f n))

variable {f}

lemma BijectiveUpTo.injective (h : BijectiveUpTo f r) (hn : 2 * n < r) : Function.Injective (f n) :=
  (h n).1 hn

lemma BijectiveUpTo.surjective (h : BijectiveUpTo f r) (hn : 2 * n + 1 < r) : Surjective (f n) :=
  (h n).2 hn

lemma allBijective_iff_forall_bijectiveUpTo : AllBijective f ↔ ∀ r : ℕ, BijectiveUpTo f r :=
  -- for the converse, the first 2n + 2 conditions contain both conditions on f n
  ⟨fun h r n ↦ ⟨fun _ ↦ (h n).injective, fun _ ↦ (h n).surjective⟩,
    fun h n ↦ ⟨(h (2 * n + 2)).injective (by lia), (h (2 * n + 2)).surjective (by lia)⟩⟩

/-- If bijections a_n: A_n → A'_n and b_n: B_n → B'_n carry the maps f_n to the maps g_n, then f
satisfies the first r conditions of `BijectiveUpTo` (f₀ injective, f₀ surjective, f₁ injective, …)
exactly when g does. -/
lemma BijectiveUpTo.congr {g : ∀ n : ℕ, A' n → B' n} {a : (i : ℕ) → A i → A' i}
    {b : (i : ℕ) → B i → B' i} (ha : AllBijective a) (hb : AllBijective b)
    (h_sq : ∀ (n : ℕ) (x : A n), b n (f n x) = g n (a n x)) :
    BijectiveUpTo f r ↔ BijectiveUpTo g r := by
  refine forall_congr' fun n ↦ ?_
  have h_comm : b n ∘ f n = g n ∘ a n := funext (h_sq n)
  rw [← (hb n).injective.of_comp_iff, ← Surjective.of_comp_iff' (hb n), h_comm,
    Injective.of_comp_iff' _ (ha n), Surjective.of_comp_iff _ (ha n).surjective]

/-- In a commutative square with two opposite sides bijective, one of the other two sides is
bijective iff the other is. -/
lemma Comparison.bijective_iff_of_comm_sq {A B A' B' : Sort*} {f : A → B} {f' : A' → B'}
    {g : A → A'} {g' : B → B'} (h_comm : ∀ x : A, f' (g x) = g' (f x)) (hg : Bijective g)
    (hg' : Bijective g') : Bijective f ↔ Bijective f' := by
  rw [← hg.of_comp_iff f', show f' ∘ g = g' ∘ f from funext h_comm, hg'.of_comp_iff']

namespace LongExactSeq

/-! ### The long exact Ext sequences and the diagram chases -/

lemma exact_of_shortComplex_exact {S : ShortComplex Ab} (hS : S.Exact) : Function.Exact S.f S.g :=
  S.ab_exact_iff_function_exact.1 hS

/-- For 0 → S₁ → S₂ → S₃ → 0 short exact, the long exact sequence Ext^n(S₃,F) → Ext^n(S₂,F) →
Ext^n(S₁,F) → Ext^{n+1}(S₃,F) of abelian groups. -/
noncomputable def contravariant (hS : S.ShortExact) (F : AbFunctor C) : LongExactSeq :=
  -- The groups `H S.X₃ F n`, `H S.X₂ F n`, `H S.X₁ F n` and the connecting map, composition with
  -- `hS.extClass`, are read off the exactness statements; `f` and `g` are then named as pull-backs.
  { mk _ _ _ (injective_f := precomp_mk₀_injective_of_epi F (hg := hS.epi_g))
    (exact_f_g := fun n ↦ exact_of_shortComplex_exact (contravariant_sequence_exact₂' hS F n))
    (exact_g_delta :=
      fun n ↦ exact_of_shortComplex_exact (contravariant_sequence_exact₁' hS F n (n + 1) (by lia)))
    (exact_delta_f := fun _ ↦ exact_of_shortComplex_exact (contravariant_sequence_exact₃' ..)) with
    f := H.map F S.g
    g := H.map F S.f }

/-- For 0 → S₁ → S₂ → S₃ → 0 short exact, the long exact sequence Ext^n(N,S₁) → Ext^n(N,S₂) →
Ext^n(N,S₃) → Ext^{n+1}(N,S₁) of abelian groups. -/
noncomputable def covariant (hS : S.ShortExact) (N : AbFunctor C) : LongExactSeq :=
  -- The groups `H N S.X₁ n`, `H N S.X₂ n`, `H N S.X₃ n` and the maps, composition with `S.f`, `S.g`
  -- and `hS.extClass`, are read off the exactness statements.
  mk _ _ _ (injective_f := postcomp_mk₀_injective_of_mono N (hf := hS.mono_f))
    (exact_f_g := fun n ↦ exact_of_shortComplex_exact (covariant_sequence_exact₂' N hS n))
    (exact_g_delta :=
      fun n ↦ exact_of_shortComplex_exact (covariant_sequence_exact₃' N hS n (n + 1) rfl))
    (exact_delta_f := fun _ ↦ exact_of_shortComplex_exact (covariant_sequence_exact₁' ..))

namespace Hom

/-- Let (a i, b i, c i) be morphisms from the long exact sequence L to the sequences L' i. If the
connecting maps δ out of degree n are onto in L and in all L' i, and the maps x ↦ (b i n x)ᵢ and
x ↦ (c i n x)ᵢ into the products are bijective, then so is x ↦ (a i (n + 1) x)ᵢ. -/
lemma bijective_succ_family {ι : Type*} {L' : ι → LongExactSeq}
    {a : (i : ι) → (n : ℕ) → L.A n →+ (L' i).A n} {b : (i : ι) → (n : ℕ) → L.B n →+ (L' i).B n}
    {c : (i : ι) → (n : ℕ) → L.C n →+ (L' i).C n} (hom : ∀ i : ι, Hom L (L' i) (a i) (b i) (c i))
    (hb : Bijective (swap fun (i : ι) (x : L.B n) ↦ b i n x))
    (hc : Bijective (swap fun (i : ι) (x : L.C n) ↦ c i n x)) (hδ : Surjective (L.δ n))
    (hδ' : ∀ i : ι, Surjective ((L' i).δ n)) :
    Bijective (swap fun (i : ι) (x : L.A n.succ) ↦ a i n.succ x) := by
  -- As the connecting maps are onto, Aⁿ⁺¹ is the cokernel of Bⁿ → Cⁿ, and likewise for each `L' i`.
  refine ⟨(injective_iff_map_eq_zero (AddMonoidHom.pi _)).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · -- write `x = δ w`; each `c i n w` is killed by δ, so it comes from `(L' i).B n`
    obtain ⟨w, rfl⟩ := hδ x
    have h_delta (i : ι) : (L' i).δ n (c i n w) = 0 :=
      ((hom i).comm_delta n w).symm.trans (congrFun hx i)
    choose v hv using fun i : ι ↦ ((L' i).exact_g_delta n _).1 (h_delta i)
    -- the family `v` comes from one `z` in `L.B n`, and `g z = w` since `c` is jointly injective
    obtain ⟨z, rfl⟩ := hb.surjective v
    have hz : L.g n z = w := hc.injective (funext fun i ↦ ((hom i).comm_g n z).trans (hv i))
    exact (L.exact_g_delta n w).2 ⟨z, hz⟩
  · -- lift `y` along the connecting maps of the `L' i`, then along `c`
    choose u hu using fun i : ι ↦ hδ' i (y i)
    obtain ⟨w, rfl⟩ := hc.surjective u
    exact ⟨L.δ n w, funext fun i ↦ ((hom i).comm_delta n w).trans (hu i)⟩

/-- The injectivity chase for a morphism (a, b, c) from a long exact sequence L to a second one L':
if a is onto and b is injective in degree n, then an element of the third term Cⁿ of L that is
killed by c and by the connecting map δ is zero. -/
lemma eq_zero_of_delta_eq_zero (h : LongExactSeq.Hom L L' a b c) (ha : Surjective (a n))
    (hb : Function.Injective (b n)) (x : L.C n) (hc : c n x = 0) (hδ : L.δ n x = 0) : x = 0 := by
  -- `x = g z`; then `b z = f' (a w) = b (f w)`, so `z = f w` and `x = g (f w) = 0`
  obtain ⟨z, rfl⟩ : ∃ z : L.B n, L.g n z = x := (L.exact_g_delta n x).1 hδ
  have hgbz : L'.g n (b n z) = 0 := by rw [← h.comm_g, hc]
  obtain ⟨w', hw'⟩ : ∃ w' : L'.A n, L'.f n w' = b n z := (L'.exact_f_g n (b n z)).1 hgbz
  obtain ⟨w, rfl⟩ : ∃ w : L.A n, a n w = w' := ha w'
  have hzw : L.f n w = z := hb (by rw [h.comm_f, hw'])
  rw [← hzw, (L.exact_f_g n).apply_apply_eq_zero]

/-- For a morphism (a, b, c) from a long exact sequence L to a second one L', with maps f' : A' → B'
and g' : B' → C': if a is injective in degree n + 1 and `c x = g' y`, then `x = g z` for some z
such that `y - b z` lies in the image of f'. -/
lemma exists_preimage_mod_f (h : LongExactSeq.Hom L L' a b c)
    (ha_inj : Function.Injective (a n.succ)) (y : L'.B n) (x : L.C n) (hxy : c n x = L'.g n y) :
    ∃ z : L.B n, (∃ w : L'.A n, y = b n z + L'.f n w) ∧ L.g n z = x := by
  -- `a (δ x) = δ' (g' y) = 0`, so `δ x = 0` and `x = g z`; then `g'` kills `y - b z`
  have hδ : L.δ n x = 0 := (map_eq_zero_iff _ ha_inj).1 <| by
    rw [h.comm_delta, hxy, (L'.exact_g_delta n).apply_apply_eq_zero]
  obtain ⟨z, hz⟩ := (L.exact_g_delta n x).1 hδ
  obtain ⟨w, hw⟩ := (L'.exact_f_g n (y - b n z)).1 (by rw [map_sub, ← h.comm_g, hz, hxy, sub_self])
  exact ⟨z, ⟨w, by rw [hw, add_sub_cancel]⟩, hz⟩

/-- The surjectivity chase for a morphism h = (a, b, c) of long exact sequences L → L': if a is onto
in degree n and injective in degree n + 1, and `c x = g' y`, then some z has `b z = y` and
`g z = x`. -/
lemma exists_preimage (h : Hom L L' a b c) (ha : Surjective (a n))
    (ha_inj : Function.Injective (a n.succ)) (y : L'.B n) (x : L.C n) (hxy : c n x = L'.g n y) :
    ∃ z : L.B n, b n z = y ∧ L.g n z = x := by
  obtain ⟨z, ⟨w', hy⟩, hz⟩ := h.exists_preimage_mod_f ha_inj y x hxy
  -- lift the correction term along a and add its image to z
  obtain ⟨w, hw⟩ := ha w'
  exact ⟨z + L.f n w, by simp [h.comm_f, hw, hy], by simp [hz, (L.exact_f_g n).apply_apply_eq_zero]⟩

/-- For maps c m : C m → C' m, the component in degree n of `rotateMap c` (c m for n = m + 1, a map
between zero groups for n = 0) is injective if c m is so for n = m + 1. -/
lemma rotateMap_injective (c : (m : ℕ) → L.C m →+ L'.C m)
    (hc : ∀ m : ℕ, n = m + 1 → Function.Injective (c m)) : Function.Injective (rotateMap c n) := by
  cases n with
  | zero => exact fun (x y : PUnit) _ ↦ Subsingleton.elim x y
  | succ m => exact hc m rfl

/-- For maps c m : C m → C' m, the component in degree n of `rotateMap c` (c m for n = m + 1, a map
between zero groups for n = 0) is surjective if c m is so for n = m + 1. -/
lemma rotateMap_surjective (c : (m : ℕ) → L.C m →+ L'.C m)
    (hc : ∀ m : ℕ, n = m + 1 → Surjective (c m)) : Surjective (rotateMap c n) := by
  cases n with
  | zero => exact fun (y : PUnit) ↦ ⟨0, Subsingleton.elim (α := PUnit) _ y⟩
  | succ m => exact hc m rfl

/-- Four lemma for a morphism h = (a, b, c) from L to L', long exact sequences
0 → A⁰ → B⁰ → C⁰ → A¹ → ⋯: if b satisfies the first r of the conditions "injective in degree 0,
surjective in degree 0, injective in degree 1, …" (`BijectiveUpTo`) and c the first r − 1, then a
satisfies the first r. -/
lemma four_lemma (h : Hom L L' a b c) (hb : BijectiveUpTo (fun n : ℕ ↦ b n) r)
    (hc : BijectiveUpTo (fun n : ℕ ↦ c n) (r - 1)) :
    BijectiveUpTo (fun n : ℕ ↦ a n) r := by
  -- Both halves are one of the chases above for a rotation of the sequences, in which the maps of
  -- degree n - 1 are the components in degree n (`rotateMap`; zero maps of zero groups for n = 0).
  refine fun n ↦ ⟨fun hn ↦ ?_, fun hn y ↦ ?_⟩
  · -- injectivity on Aⁿ, from Bⁿ⁻¹ → Cⁿ⁻¹ → Aⁿ → Bⁿ
    refine (injective_iff_map_eq_zero (a n)).2 fun (x : L.A n) (hx : a n x = 0) ↦ ?_
    have hfx : L.f n x = 0 := hb.injective hn (by simp [h.comm_f, hx])
    have hb_prev : Surjective (rotateMap (L := L.rotate) (L' := L'.rotate) b n) :=
      rotateMap_surjective _ fun m hm ↦ hb.surjective (by lia)
    have hc_prev : Function.Injective (rotateMap c n) :=
      rotateMap_injective c fun m hm ↦ hc.injective (by lia)
    exact h.rotate.rotate.eq_zero_of_delta_eq_zero hb_prev hc_prev x hx hfx
  · -- surjectivity on Aⁿ, from Cⁿ⁻¹ → Aⁿ → Bⁿ → Cⁿ: first lift the image of `y` in B'ⁿ
    obtain ⟨x, hx⟩ : ∃ x : L.B n, b n x = L'.f n y := hb.surjective hn _
    have hc_prev : Surjective (rotateMap c n) :=
      rotateMap_surjective c fun m hm ↦ hc.surjective (by lia)
    obtain ⟨z, hz, -⟩ := h.rotate.exists_preimage (n := n) hc_prev (hc.injective (by lia)) y x hx
    exact ⟨z, hz⟩

/-- Five lemma for the morphism h = (a, b, c) from the long exact sequence L to L': if c is
bijective in all degrees (`AllBijective`), then b is bijective in all degrees exactly when a is. -/
lemma five_lemma (h : Hom L L' a b c) (hc : AllBijective fun n : ℕ ↦ c n) :
    (AllBijective fun n : ℕ ↦ b n) ↔ AllBijective fun n : ℕ ↦ a n := by
  refine ⟨fun hb ↦ ?_, fun ha ↦ ?_⟩
  · -- apply the four lemma for every bound r
    rw [allBijective_iff_forall_bijectiveUpTo] at hb hc ⊢
    exact fun r ↦ h.four_lemma (hb r) (hc (r - 1))
  · -- Rotated twice, the morphism has b (n - 1), c (n - 1), a n as its components in degree n, so
    -- the four lemma applied to it gives all b n, as the components in degree n + 1.
    have hc' : AllBijective fun m : ℕ ↦ rotateMap c m := fun m ↦
      ⟨rotateMap_injective c fun k _ ↦ (hc k).injective,
        rotateMap_surjective c fun k _ ↦ (hc k).surjective⟩
    have hb_upTo (r : ℕ) :
        BijectiveUpTo (fun m : ℕ ↦ rotateMap (L := L.rotate) (L' := L'.rotate) b m) r :=
      h.rotate.rotate.four_lemma (allBijective_iff_forall_bijectiveUpTo.1 hc' r)
        (allBijective_iff_forall_bijectiveUpTo.1 ha (r - 1))
    -- the component of `rotateMap b` in degree n + 1 is b n by definition
    exact fun n ↦ allBijective_iff_forall_bijectiveUpTo.2 hb_upTo (n + 1)

end Hom

end LongExactSeq

set_option backward.isDefEq.respectTransparency false

/-- In a long exact sequence, if all maps g : B m → C m with m < n are surjective, then
f : A n → B n is injective. -/
lemma LongExactSeq.f_injective_of_g_surjective (L : LongExactSeq)
    (hg : ∀ m : ℕ, m < n → Surjective (L.g m)) : Function.Injective (L.f n) := by
  cases n with
  | zero => exact L.injective_f
  | succ m =>
    -- the kernel of `f` is the image of `δ`, which vanishes as `g` is onto
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
    obtain ⟨y, rfl⟩ := (L.exact_delta_f m x).1 hx
    exact (L.exact_g_delta m y).2 (hg m m.lt_succ_self y)

/-- The comparison map of c = (φ, β), with φ = c.functor : C' ⥤ C and β = c.coeffHom : φ ⋙ F → F',
along α: N' → N∘φ sends a class x to α · (x∘φ) · β, where · is the composition of Ext classes and
x∘φ is the restriction of x along φ. -/
lemma Comparison.pull_apply {F : AbFunctor C} {F' : AbFunctor C'} (c : Comparison F F')
    (α : N' ⟶ c.functor ⋙ N) (x : H N F n) :
    c.pull α n x = (mk₀ α).comp
      ((x.mapExactFunctor (restrictAlong c.functor)).comp (mk₀ c.coeffHom) (add_zero n))
        (zero_add n) :=
  rfl

/-- Let c = (φ, β) be a comparison from F on C to F' on C', that is φ : C' ⥤ C and β : φ ⋙ F → F',
and let τ be a morphism from S' to the restriction of S along φ, for short exact complexes S and
S'. Then the maps c.pull τᵢ (restrict along φ, push by β, pull back by τᵢ) form a morphism from
the contravariant Ext sequence of (S, F) to that of (S', F'). -/
lemma Comparison.pull_hom_contravariant (hS : S.ShortExact) (hS' : S'.ShortExact)
    (c : Comparison F F') (τ : S' ⟶ S.map (restrictAlong c.functor)) :
    (contravariant hS F).Hom (contravariant hS' F') (c.pull τ.τ₃) (c.pull τ.τ₂) (c.pull τ.τ₁) := by
  constructor
  · -- τ commutes with the second maps of the complexes
    simp [contravariant, pull_apply, H.map, mapExactFunctor_comp, mapExactFunctor_mk₀, ← τ.comm₂₃]
  · -- τ commutes with the first maps of the complexes
    simp [contravariant, pull_apply, H.map, mapExactFunctor_comp, mapExactFunctor_mk₀, ← τ.comm₁₂]
  · -- the extension class is natural
    simp [contravariant, pull_apply, mapExactFunctor_comp, mapExactFunctor_extClass,
      ← comp_assoc (h₁₂ := zero_add 1), add_comm, ← hS'.extClass_naturality]

/-- For short exact complexes S and S', a morphism τ from the restriction of S along φ to S' and a
map α : N' → N ∘ φ give a morphism from the covariant Ext sequence of (N, S) to that of (N', S').
Its components are the maps pull ⟨φ, τᵢ⟩ α: restrict along φ, push by τᵢ and pull back by α. -/
lemma Comparison.pull_hom_covariant (hS : S.ShortExact) (hS' : S'.ShortExact) {φ : C' ⥤ C}
    (τ : S.map (restrictAlong φ) ⟶ S') (α : N' ⟶ φ ⋙ N) :
    LongExactSeq.Hom (LongExactSeq.covariant hS N) (LongExactSeq.covariant hS' N')
      (pull ⟨φ, τ.τ₁⟩ α) (pull ⟨φ, τ.τ₂⟩ α) (pull ⟨φ, τ.τ₃⟩ α) := by
  constructor
  · -- τ commutes with the first maps of the complexes
    simp [covariant, pull_apply, mapExactFunctor_comp, mapExactFunctor_mk₀,
      comp_assoc (h₂₃ := rfl), τ.comm₁₂]
  · -- τ commutes with the second maps of the complexes
    simp [covariant, pull_apply, mapExactFunctor_comp, mapExactFunctor_mk₀,
      comp_assoc (h₂₃ := rfl), τ.comm₂₃]
  · -- the extension class is natural
    simp [covariant, pull_apply, mapExactFunctor_comp, mapExactFunctor_extClass,
      comp_assoc (h₂₃ := rfl), ShortExact.extClass_naturality (h₂ := hS')]

/-- For 0 → X₁ → X₂ → X₃ → 0 short exact, X₁ → X₂ induces bijections on Extⁿ(-, F) for all n (it is
a cohomological equivalence for F) exactly when Extⁿ(X₃, F) = 0 for all n. -/
lemma isCohomEquiv_iff_subsingleton (hS : S.ShortExact) :
    IsCohomEquiv F S.f ↔ ∀ n : ℕ, Subsingleton (H S.X₃ F n) := by
  -- The long exact sequence `contravariant hS F` is Hⁿ(X₃) → Hⁿ(X₂) → Hⁿ(X₁) → Hⁿ⁺¹(X₃), and its
  -- middle map is the pull-back along `S.f`.
  refine ⟨fun h n ↦ ?_, fun h n ↦ ⟨?_, fun y ↦ ?_⟩⟩
  · -- The middle map is onto in all degrees, so Hⁿ(X₃) → Hⁿ(X₂) is injective; its image is killed
    -- by the injective middle map, so it is zero.
    have hf_inj : Function.Injective ((contravariant hS F).f n) :=
      (contravariant hS F).f_injective_of_g_surjective fun m _ ↦ (h m).surjective
    have h_comp (x : H S.X₃ F n) : H.map F S.f n ((contravariant hS F).f n x) = 0 :=
      ((contravariant hS F).exact_f_g n).apply_apply_eq_zero x
    exact ⟨fun x y ↦ hf_inj ((h n).injective ((h_comp x).trans (h_comp y).symm))⟩
  · -- injective: the kernel is the image of Hⁿ(X₃) = 0
    refine (injective_iff_map_eq_zero _).2 fun (x : H S.X₂ F n) (hx : H.map F S.f n x = 0) ↦ ?_
    obtain ⟨z, rfl⟩ := ((contravariant hS F).exact_f_g n x).1 hx
    exact (congrArg _ ((h n).elim z 0)).trans (map_zero _)
  · -- onto: the connecting map lands in Hⁿ⁺¹(X₃) = 0
    exact ((contravariant hS F).exact_g_delta n y).1 ((h (n + 1)).allEq _ _)

/-- For a short exact sequence 0 → X₁ → X₂ → X₃ → 0 of functors with Extⁿ(X₁,F) = 0 for all n,
the pull-back Extⁿ(X₃,F) → Extⁿ(X₂,F) is bijective for all n. -/
lemma isCohomEquiv_quotient_of_acyclic (hS : S.ShortExact)
    (hX₁ : ∀ (n : ℕ) (x : H S.X₁ F n), x = 0) : IsCohomEquiv F S.g := by
  -- the pull-back along `S.g` is the first map of `contravariant hS F`, whose third terms vanish
  intro n
  have hg_surj (m : ℕ) : Surjective ((contravariant hS F).g m) :=
    fun z ↦ ⟨0, (map_zero _).trans (hX₁ m z).symm⟩
  exact ⟨(contravariant hS F).f_injective_of_g_surjective fun m _ ↦ hg_surj m,
    fun y ↦ ((contravariant hS F).exact_f_g n y).1 (hX₁ n _)⟩

end New.Variety

/-! ## Cohomology of disjoint unions -/

section DisjointUnions

open CategoryTheory Abelian.Ext Function New.Variety Comparison LongExactSeq ShortComplex

/-- Let Y = `New.Variety.sigma X` be the disjoint union of a family of set-valued functors X_i.
Write ℤ[Y] = `freeAb.obj Y` for the free abelian functor on Y and H^n(Y, F) for Ext^n(ℤ[Y], F).
Then H^n(Y, F) is in bijection with the product of the H^n(X_i, F): the bijection sends a class to
the family of its pull-backs (`H.map`) along the maps ℤ[X_i] → ℤ[Y] induced by the inclusions. -/
lemma New.Variety.H.sigma_bijective {C : Type 1} [Category C] {ι : Type 1} (X : ι → C ⥤ Type 1)
    (F : AbFunctor C) (n : ℕ) :
    Bijective fun (x : H (freeAb.obj (sigma X)) F n) (i : ι) ↦
      map F (freeAb.map (sigma.ι (C := C) (J := ι) X i)) n x := by
  -- Dimension shifting: induction on `n`, for all coefficients `F` at once.
  induction n generalizing F with
  | zero =>
    -- In degree zero, `H (freeAb.obj Y) F 0` is the set of maps from `Y` to `F ⋙ forget _`.
    let e (Y : C ⥤ Type 1) : (Y ⟶ F ⋙ forget _) ≃ H (freeAb.obj Y) F 0 :=
      (homEquiv₀.trans (freeAb.homEquiv Y F)).symm
    -- A map out of the disjoint union is the same as a family of maps out of the `X i`.
    have h_bij : Bijective fun (f : sigma X ⟶ F ⋙ forget Ab) (i : ι) ↦ sigma.ι X i ≫ f :=
      (Equiv.mk (fun f (i : ι) ↦ sigma.ι X i ≫ f) sigma.desc (fun f ↦ rfl) fun f ↦ rfl).bijective
    -- Under `e`, pull-back along `sigma.ι X i` is composition with it.
    refine (bijective_iff_of_comm_sq (fun f ↦ funext fun i ↦ ?_) (e _).bijective
      (.piMap fun _ ↦ (e _).bijective)).1 h_bij
    show map F (freeAb.map (sigma.ι X i)) 0 (e (sigma X) f) = e (X i) (sigma.ι X i ≫ f)
    simp +instances [e, Adjunction.homEquiv, map, freeAb]
  | succ n ih =>
    -- Embed `F` in the injective `Injective.under F` and compare the long exact sequences of
    -- 0 → F → Injective.under F → cokernel → 0.
    have hS : (ShortComplex.mk _ _ (Limits.cokernel.condition (Injective.ι F))).ShortExact :=
      ⟨exact_cokernel _⟩
    -- The connecting maps are onto because `Injective.under F` has no cohomology in degree
    -- `n + 1`.
    have δ_surj (N : AbFunctor C) : Surjective ((LongExactSeq.covariant hS N).δ n) :=
      fun y ↦ (exact_delta_f _ n y).1 (eq_zero_of_injective _)
    -- write the pull-backs as comparison maps `pull` along the identity comparison
    simp only [← id_pull] at ih ⊢
    -- Pull-back is a morphism of long exact sequences (`pull_hom_covariant`), so the claim in
    -- degree n for `Injective.under F` and for the cokernel gives it in degree n + 1 for F.
    exact Hom.bijective_succ_family (fun _ ↦ pull_hom_covariant (φ := 𝟭 C) hS hS (𝟙 _) _) (ih _)
      (ih _) (δ_surj _) fun _ ↦ δ_surj _

end DisjointUnions

/-!
## Acyclic covers and Ext of products of coefficients

* `New.Variety.exists_acyclic_cover`: each `M` is a quotient of the free abelian functor on a
  disjoint union of representable functors, with surjective connecting maps in `Ext`; this allows
  dimension shifting.
-/

namespace New.Variety

open CategoryTheory Abelian.Ext Comparison piAbFunctor LongExactSeq Function AddCommGrpCat

variable {C : Type 1} [Category C]
  {N : AbFunctor C} {I : Type} {F : I → AbFunctor C} {M G : AbFunctor C} (β : M ⟶ G)

/-- For a morphism β: M → G of abelian-group-valued functors, the three-term complex ker β → M →
G, with the kernel taken objectwise and included into M. -/
def kerComplex : ShortComplex (AbFunctor C) where
  X₁ :=
    { obj A := AddCommGrpCat.of (β.app A).hom.ker
      map f := ofHom (((M.map f).hom.domRestrict _).codRestrict _ (by simp_all)) }
  X₂ := M
  X₃ := G
  f := { app _ := ofHom (AddSubgroup.subtype _) }
  g := β
  zero := by
    ext A ⟨x, hx⟩
    exact hx

lemma kerComplex_shortExact {α : M ⟶ G} (hα : ∀ c : C, Surjective (α c)) :
    (kerComplex α).ShortExact :=
  (shortExact_of_app (by simp) (by simp [Exact]) hα).2

/-- Every functor M from C to abelian groups is a quotient, by some map g, of the free abelian
functor ℤ[⊔ h_{c_i}] on a disjoint union of representable functors h_{c_i} = `reprBy (c i)`, such
that, for K = ker g (the first term of the short exact sequence `kerComplex g`), the connecting map
Ext^n(K,F) → Ext^{n+1}(M,F) of the Ext sequence `contravariant` is surjective for all F and n. -/
lemma exists_acyclic_cover (M : C ⥤ Ab) :
    ∃ (ι : Type 1) (c : ι → C) (g : freeAb (sigma fun i : ι ↦ reprBy (c i)) ⟶ M)
      (h_ses : (kerComplex g).ShortExact),
      ∀ (F : AbFunctor C) (n : ℕ), Surjective ((contravariant h_ses F).δ n) := by
  -- Take one copy of h_A for each object A and each element x of M(A), mapped to M by Yoneda.
  let c : (Σ A : C, M.obj A) → C := fun x ↦ x.1
  let g : freeAb.obj (sigma fun x ↦ reprBy (c x)) ⟶ M :=
    (freeAb.homEquiv ..).symm (sigma.desc fun x ↦ pointMap x.2)
  have hg (A : C) : Surjective (g.app A) := by
    intro x
    -- `x` is the image of the identity of A in the copy indexed by (A, x)
    refine ⟨FreeAbelianGroup.of ⟨⟨A, x⟩, ULift.up (𝟙 A)⟩, ?_⟩
    calc g.app A (FreeAbelianGroup.of ⟨⟨A, x⟩, ULift.up (𝟙 A)⟩)
      _ = (pointMap (Y := M ⋙ forget Ab) x).app A (ULift.up (𝟙 A)) :=
        FreeAbelianGroup.lift_apply_of _ _
      _ = x := (uliftCoyonedaEquiv (F := M ⋙ forget Ab)).apply_symm_apply x
  refine ⟨Σ A : C, M.obj A, c, g, kerComplex_shortExact hg, fun F n x ↦ ?_⟩
  -- on each summand ℤ[h_A] the pull-back of `x` vanishes, as this summand is projective
  have h_pullback : (mk₀ g).comp x (zero_add _) = 0 := (H.sigma_bijective _ F (n + 1)).injective <|
    funext fun _ ↦ (eq_zero_of_projective _).trans (eq_zero_of_projective _).symm
  -- so, by exactness, `x` is in the image of the connecting map
  exact contravariant_sequence_exact₃ _ F x h_pullback (add_comm 1 n)

/-- Given natural transformations N→F_i for each index i, the natural transformation from N to
the pointwise product of the functors F_i having these as components. -/
def piAbFunctor.lift (f : ∀ i : I, N ⟶ F i) : N ⟶ piAbFunctor F where
  app A := ofHom (AddMonoidHom.pi fun i ↦ ((f i).app A).hom)
  naturality A B φ := by
    ext x
    exact funext fun i ↦ (f i).naturality_apply φ x

/-- Ext commutes with products in the coefficients: the map Ext^n(N, ∏ F_i) → ∏ Ext^n(N, F_i)
sending a class to the family of its push-forwards (`push`) along the projections π F i of the
objectwise product `piAbFunctor F` is bijective. -/
lemma H.pi_bijective (n : ℕ) :
    Bijective fun (x : H N (piAbFunctor F) n) (i : I) ↦ push N (π F i) n x := by
  -- Dimension shifting. The push-forwards are written as comparison maps along the identity
  -- functor, so that `pull_hom_contravariant` makes them morphisms of long exact Ext sequences.
  simp only [← pull_id_eq_push]
  induction n generalizing N with
  | zero =>
    -- Ext⁰ is Hom, and a map to the product is a family of maps
    have h_hom : Bijective fun (x : N ⟶ piAbFunctor F) (i : I) ↦ x ≫ π F i :=
      (Equiv.mk (fun x (i : I) ↦ x ≫ π F i) lift (fun x ↦ rfl) fun f ↦ rfl).bijective
    refine (bijective_iff_of_comm_sq (fun x ↦ funext fun i ↦ ?_)
      (mk₀_bijective N (piAbFunctor F)) (.piMap fun i ↦ mk₀_bijective N (F i))).1 h_hom
    -- pushing forward a class of degree 0 is composition with the projection
    show pull (⟨𝟭 C, π F i⟩ : Comparison (piAbFunctor F) (F i)) (𝟙 N) 0 (mk₀ x) = mk₀ (x ≫ π F i)
    simp [pull_apply, mapExactFunctor_mk₀, show (𝟭 C).whiskerLeft x = x from rfl]
  | succ n ih =>
    -- for 0 → K → ℤ[⊔ h_c] → N → 0 with onto connecting maps, degree n + 1 for N follows from
    -- degree n for the two other terms (`bijective_succ_family`, a five lemma for families)
    obtain ⟨ι, c, g, h_ses, hδ⟩ := exists_acyclic_cover N
    -- the components are push-forwards along the π F i (found by unification) followed by
    -- pull-backs along identities
    exact Hom.bijective_succ_family (fun _ ↦ pull_hom_contravariant h_ses h_ses ⟨𝟭 C, _⟩ (𝟙 _))
      ih ih (hδ _ n) fun i ↦ hδ (F i) n

end New.Variety
