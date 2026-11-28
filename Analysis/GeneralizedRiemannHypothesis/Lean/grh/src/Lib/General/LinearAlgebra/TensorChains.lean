import Lib.Base

/-!
# Chains of linear maps, tensor products of their data, and separation by forms

The file composes initial segments of a chain of linear maps and computes the index of the
stabiliser of a nonzero vector in a finite general linear group. It extends a chain of bilinear
steps from pure data to arbitrary tensors of the data.

## Main definitions and results

* `New.index_stabilizer_GL_vector`: over a finite field `F`, the stabiliser in `GL n F` of a nonzero
  vector has index `|F| ^ |n| - 1`, by orbit-stabiliser.
* `New.TensorChain`: the tensor product `S (j-1) ⊗ (⋯ ⊗ (S 0 ⊗ ℂ))`, which is `ℂ` for `j = 0`.
* `New.TensorChain.lift`, `New.TensorChain.lift_pure`: for `x` in `M 0`, the linear map to `M j`
  that sends a pure tensor to the composite (`New.compUpTo`) of the maps `b i (f i)`, `i < j`,
  applied to `x`.
* `New.TensorChain.ofPairs`, `New.TensorChain.lift_ofPairs`: data of double steps regrouped into
  single factors.
* `New.tensor_eq_zero_of_separating`: over a principal ideal domain, if the forms `f i` on `U` have
  no common zero but `0` and `V` is torsion-free, then the maps `U ⊗ V → V`,
  `u ⊗ v ↦ f i u • v`, have no common zero but `0`.
-/

noncomputable section

/-!
## Composites of chains and the stabiliser of a vector in a finite GL

* `New.exists_GL_smul_single`: a vector with a unit entry is a column of an invertible matrix.
-/

section CompositionChain

variable {R n : Type _} [CommRing R] [Fintype n] [DecidableEq n]

/-- For linear maps `L i : M i → M (i + 1)`, the composite `L (j-1) ∘ ⋯ ∘ L 0 : M 0 → M j`; the
identity for `j = 0`. -/
def New.compUpTo {M : ℕ → Type _} [∀ j : ℕ, AddCommGroup (M j)] [∀ j : ℕ, Module R (M j)]
    (L : ∀ j : ℕ, M j →ₗ[R] M (j + 1)) : ∀ j : ℕ, M 0 →ₗ[R] M j
  | 0 => LinearMap.id
  | j + 1 => L j ∘ₗ compUpTo L j

section

variable {M : ℕ → Type*} [∀ j : ℕ, AddCommGroup (M j)] [∀ j : ℕ, Module R (M j)]
  (L : ∀ j : ℕ, M j →ₗ[R] M (j + 1))

lemma New.compUpTo_zero_apply (x : M 0) : compUpTo L 0 x = x :=
  rfl

lemma New.compUpTo_succ_apply (j : ℕ) (x : M 0) : compUpTo L (j + 1) x = L j (compUpTo L j x) :=
  rfl

end

open Matrix MulAction

/-- Over a commutative ring, a vector with a unit entry is, for any `i`, the `i`-th column
`g • Pi.single i 1` of an invertible matrix `g`. -/
lemma New.exists_GL_smul_single {v : n → R} (hv : ∃ j : n, IsUnit (v j)) (i : n) :
    ∃ g : GL n R, g • Pi.single i 1 = v := by
  -- Put `v` in the `j`-th column of the identity (determinant `v j`), then swap columns `i` and
  -- `j`.
  obtain ⟨j, hj⟩ := hv
  have h_det : IsUnit (updateCol 1 j v).det := by simpa [← cramer_apply] using hj
  exact ⟨.mk'' _ h_det * .swap R j i, funext fun _ ↦ by simp [Units.smul_def]⟩

/-- Over a finite field `F`, the stabiliser in `GL n F` of a nonzero vector has index
`|F| ^ |n| - 1`, the number of nonzero vectors. -/
lemma New.index_stabilizer_GL_vector {F : Type*} [Field F] [Finite F] {u : n → F} (hu : u ≠ 0) :
    (stabilizer (GL n F) u).index = Nat.card F ^ Fintype.card n - 1 := by
  -- By orbit-stabiliser the index is the size of the orbit, which is the set of nonzero vectors.
  -- Any index `j` will do (one exists as `u ≠ 0`): compute the orbit of the basis vector `e_j`.
  obtain ⟨j, -⟩ := Function.ne_iff.1 hu
  have h_mem_orbit (v : n → F) (hv : v ≠ 0) : v ∈ orbit (GL n F) (Pi.single j 1 : n → F) :=
    exists_GL_smul_single (by simpa [Function.ne_iff] using hv) j
  have h_orbit : orbit (GL n F) u = {0}ᶜ := by
    rw [orbit_eq_iff.2 (h_mem_orbit u hu)]
    -- An invertible matrix does not send `e_j` to `0`.
    exact subset_antisymm (by simp [mem_orbit_iff, smul_eq_zero_iff_eq]) h_mem_orbit
  rw [index_stabilizer, h_orbit, Set.ncard_compl]
  simp [Nat.card_fun]

end CompositionChain

/-!
## Iterated tensor products of data and the multilinear chain of maps

A chain of bilinear steps `b j : S j → M j → M (j + 1)` is multilinear in its data, so it factors
through the tensor product of the spaces `S j`, and so extends from pure data to arbitrary tensors.
-/

section TensorChain

open TensorProduct LinearMap Finset

variable (S : ℕ → Type)
  {M : ℕ → Type*} [∀ j : ℕ, AddCommGroup (S j)] [∀ j : ℕ, Module ℂ (S j)]
  [∀ j : ℕ, AddCommGroup (M j)] [∀ j : ℕ, Module ℂ (M j)]
  (b : ∀ j : ℕ, S j →ₗ[ℂ] M j →ₗ[ℂ] M (j + 1)) (t : ∀ j : ℕ, S j →ₗ[ℂ] S j) (f : ∀ j : ℕ, S j)

/-- The complex tensor product `S (j-1) ⊗ (⋯ ⊗ (S 0 ⊗ ℂ))`, equal to `ℂ` for `j = 0`. Below it is
written `S (j-1) ⊗ ⋯ ⊗ S 0`, the last factor `ℂ` (and `1` in pure tensors) being left out. -/
def New.TensorChain : ℕ → ModuleCat ℂ
  | 0 => ModuleCat.of ℂ ℂ
  | j + 1 => ModuleCat.of ℂ (S j ⊗[ℂ] TensorChain j)

namespace New.TensorChain

variable {S}

/-- For a family of vectors `f i` in `S i`, the pure tensor `f (j-1) ⊗ ⋯ ⊗ f 0` in
`S (j-1) ⊗ ⋯ ⊗ S 0`; it is `1 : ℂ` for `j = 0`. -/
def pure (j : ℕ) : TensorChain S j :=
  compUpTo (M := fun i : ℕ ↦ TensorChain S i)
    (fun i : ℕ ↦ TensorProduct.mk ℂ (S i) (TensorChain S i) (f i)) j (1 : ℂ)

lemma pure_zero : pure f 0 = (1 : ℂ) :=
  rfl

lemma pure_succ (j : ℕ) : pure f (j + 1) = f j ⊗ₜ[ℂ] pure f j :=
  rfl

/-- Two steps at once: the linear map from `S (2 * i) ⊗ S (2 * i + 1)` to
`Hom (M (2 * i), M (2 * i + 2))` sending `s ⊗ s'` to `b (2 * i + 1) s' ∘ b (2 * i) s`. -/
def liftInPairs (i : ℕ) : S (2 * i) ⊗[ℂ] S (2 * i + 1) →ₗ[ℂ] M (2 * i) →ₗ[ℂ] M (2 * (i + 1)) :=
  lift ((llcomp ℂ (M (2 * i)) (M (2 * i + 1)) (M (2 * i + 1 + 1))).compl₁₂ (b (2 * i + 1))
    (b (2 * i))).flip

/-- For bilinear maps `b i : S i → M i → M (i + 1)` and `x` in `M 0`, the linear map from
`S (j-1) ⊗ ⋯ ⊗ S 0` to `M j` that sends `f (j-1) ⊗ ⋯ ⊗ f 0` to
`(b (j-1) (f (j-1)) ∘ ⋯ ∘ b 0 (f 0)) x`. -/
def lift (x : M 0) : ∀ j : ℕ, TensorChain S j →ₗ[ℂ] M j
  | 0 => toSpanSingleton ℂ (M 0) x
  | j + 1 => TensorProduct.lift ((b j).compl₂ (lift x j))

lemma lift_zero_apply (x : M 0) (c : ℂ) : lift b x 0 c = c • x :=
  rfl

/-- On `s ⊗ z`, the lift of length `j + 1` applies the step `b j s` to the lift of `z`. -/
lemma lift_succ_tmul (x : M 0) (j : ℕ) (s : S j) (z : TensorChain S j) :
    lift b x (j + 1) (s ⊗ₜ[ℂ] z) = b j s (lift b x j z) :=
  rfl

/-- On the pure tensor `f (j-1) ⊗ ⋯ ⊗ f 0`, the map `lift b x j` takes the value
`(b (j-1) (f (j-1)) ∘ ⋯ ∘ b 0 (f 0)) x`, the composite `compUpTo` of the steps applied to `x`. -/
@[simp] lemma lift_pure (x : M 0) (j : ℕ) :
    lift b x j (pure f j) = compUpTo (fun i : ℕ ↦ b i (f i)) j x := by
  induction j with
  | zero => rw [pure_zero, lift_zero_apply, one_smul, compUpTo_zero_apply]
  | succ j ih => rw [pure_succ, lift_succ_tmul, ih, compUpTo_succ_apply]

/-- The lift is additive in the starting vector: at `x - y` it is the difference of the lifts at `x`
and at `y`. -/
lemma lift_sub (x y : M 0) (m : ℕ) (s : TensorChain S m) :
    lift b (x - y) m s = lift b x m s - lift b y m s := by
  induction m with
  | zero => exact smul_sub (show ℂ from s) x y
  | succ m ih =>
    -- Both sides are linear in `s`, so it is enough to compare them on `u ⊗ r`.
    refine LinearMap.congr_fun (g := lift b x (m + 1) - lift b y (m + 1))
      (TensorProduct.ext' (M := S m) (N := TensorChain S m) fun u r ↦ ?_) s
    change b m u (lift b (x - y) m r) = b m u (lift b x m r) - b m u (lift b y m r)
    rw [ih r, map_sub]

/-- For endomorphisms `t i` of `S i`, the endomorphism `t (j-1) ⊗ ⋯ ⊗ t 0` of
`S (j-1) ⊗ ⋯ ⊗ S 0`; the identity of `ℂ` for `j = 0`. -/
def map : (j : ℕ) → TensorChain S j →ₗ[ℂ] TensorChain S j :=
  lift (M := fun i : ℕ ↦ TensorChain S i)
    (fun i : ℕ ↦ TensorProduct.mk ℂ (S i) (TensorChain S i) ∘ₗ t i) (1 : ℂ)

/-- The map `t (j-1) ⊗ ⋯ ⊗ t 0` sends the pure tensor `f (j-1) ⊗ ⋯ ⊗ f 0` to the pure tensor
with factors `t i (f i)`. -/
@[simp] lemma map_pure (j : ℕ) : map t j (pure f j) = pure (fun i : ℕ ↦ t i (f i)) j :=
  lift_pure (M := fun i : ℕ ↦ TensorChain S i)
    (fun i : ℕ ↦ TensorProduct.mk ℂ (S i) (TensorChain S i) ∘ₗ t i) f (1 : ℂ) j

/-- Scaling the factor `f j` by `c j` for each `j < m` scales the pure tensor
`f (m-1) ⊗ ⋯ ⊗ f 0` by the product of the `c j`. -/
lemma pure_smul {g : ∀ j : ℕ, S j} (c : ℕ → ℂ) (m : ℕ) (hg : ∀ j : ℕ, j < m → g j = c j • f j) :
    pure g m = (∏ j ∈ range m, c j) • pure f m := by
  induction m with
  | zero => rw [prod_range_zero, one_smul, pure_zero, pure_zero]
  | succ m ih =>
    simp only [pure_succ, hg m m.lt_succ_self, ih fun j hj ↦ hg j (hj.trans m.lt_succ_self),
      prod_range_succ_comm]
    exact smul_tmul_smul (c m) (∏ j ∈ range m, c j) (f m) (pure f m)

/-- The pure tensor `g (m-1) ⊗ ⋯ ⊗ g 0` depends only on the factors of index less than `m`. -/
@[congr] lemma pure_congr {g h : ∀ j : ℕ, S j} {m : ℕ} (hgh : ∀ j : ℕ, j < m → g j = h j) :
    pure g m = pure h m := by
  simpa using pure_smul h (g := g) 1 m (by simpa using hgh)

/-- Multilinearity: the pure tensor of the finite sums `∑ a, g j a`, `j < n`, is the sum over the
tuples of indices `y` of the pure tensors of the terms `g j (y j)`. Here `F y` is any family with
`F y j = g j (y j)` for `j < n`. -/
lemma pure_sum {Y : ℕ → Type*} [∀ j : ℕ, Fintype (Y j)] (g : ∀ j : ℕ, Y j → S j) {n : ℕ}
    (F : (∀ i : Fin n, Y i) → ∀ j : ℕ, S j)
    (hF : ∀ (y : ∀ i : Fin n, Y i) (i : Fin n), F y i = g i (y i)) :
    pure (fun j : ℕ ↦ ∑ a : Y j, g j a) n = ∑ y : (∀ i : Fin n, Y i), pure (F y) n := by
  induction n with
  | zero => rw [Fintype.sum_unique, pure_zero, pure_zero]
  | succ n ih =>
    -- A tuple of length `n + 1` is a last index `a` and a tuple `z` of length `n`.
    let e : Y n × (∀ i : Fin n, Y i) ≃ ∀ i : Fin (n + 1), Y i := Fin.snocEquiv fun i ↦ Y i
    have h_last (a : Y n) (z : ∀ i : Fin n, Y i) : F (e (a, z)) n = g n a := by
      simpa [e, Fin.snocEquiv] using hF (e (a, z)) (Fin.last n)
    have h_init (a : Y n) :
        pure (fun j : ℕ ↦ ∑ a' : Y j, g j a') n = ∑ z : (∀ i : Fin n, Y i), pure (F (e (a, z))) n :=
      ih _ fun z i ↦ by simpa [e, Fin.snocEquiv] using hF (e (a, z)) i.castSucc
    rw [← e.sum_comp, Fintype.sum_prod_type, pure_succ, sum_tmul]
    refine sum_congr rfl fun a _ ↦ ?_
    rw [h_init a, tmul_sum]
    exact sum_congr rfl fun z _ ↦ by rw [pure_succ, h_last]

/-- The double step with datum `s ⊗ s'` is the step `b (2 * i) s` followed by
`b (2 * i + 1) s'`. -/
lemma liftInPairs_tmul (i : ℕ) (s : S (2 * i)) (s' : S (2 * i + 1)) (y : M (2 * i)) :
    liftInPairs b i (s ⊗ₜ s') y = b (2 * i + 1) s' (b (2 * i) s y) :=
  rfl

/-- Let `b j : S j →ₗ M j →ₗ M (j + 1)` be bilinear steps and `f j : S j`. Composing the double
steps `liftInPairs b i (f (2 * i) ⊗ₜ f (2 * i + 1))` for `i < p` gives the same value at `x` as
composing the single steps `b j (f j)` for `j < 2 * p`. -/
lemma compUpTo_liftInPairs_tmul (p : ℕ) (x : M 0) :
    compUpTo (M := fun i : ℕ ↦ M (2 * i))
        (fun i : ℕ ↦ liftInPairs b i (f (2 * i) ⊗ₜ[ℂ] f (2 * i + 1))) p x =
      compUpTo (fun j : ℕ ↦ b j (f j)) (2 * p) x := by
  induction p with
  | zero => rfl
  | succ p ih =>
    -- The right side has `2 * (p + 1) = 2 * p + 1 + 1` steps.
    rw [compUpTo_succ_apply, ih, liftInPairs_tmul]
    rfl

/-- For data `τ i` in `S (2 * i) ⊗ S (2 * i + 1)` of `p` double steps, the tensor
`τ (p-1) ⊗ ⋯ ⊗ τ 0` regrouped into `2 * p` single factors. -/
def ofPairs (τ : ∀ i : ℕ, S (2 * i) ⊗[ℂ] S (2 * i + 1)) (p : ℕ) : TensorChain S (2 * p) :=
  compUpTo (M := fun i : ℕ ↦ TensorChain S (2 * i))
    (fun i : ℕ ↦ liftInPairs (M := fun j : ℕ ↦ TensorChain S j)
      (fun j : ℕ ↦ TensorProduct.mk ℂ (S j) (TensorChain S j)) i (τ i)) p (1 : ℂ)

/-- The chain of `2 * p` steps with the regrouped tensor `ofPairs τ p` as data is the composite of
the `p` double steps with data `τ i`. -/
lemma lift_ofPairs (τ : ∀ i : ℕ, S (2 * i) ⊗[ℂ] S (2 * i + 1)) (p : ℕ) (x : M 0) :
    lift b x (2 * p) (ofPairs τ p) =
      compUpTo (M := fun i : ℕ ↦ M (2 * i)) (fun i : ℕ ↦ liftInPairs b i (τ i)) p x := by
  induction p with
  | zero => exact one_smul ℂ x
  | succ p ih =>
    have h_step (s : S (2 * p) ⊗[ℂ] S (2 * p + 1)) (r : TensorChain S (2 * p)) :
        lift b x (2 * (p + 1)) (liftInPairs (M := fun j : ℕ ↦ TensorChain S j)
            (fun j : ℕ ↦ TensorProduct.mk ℂ (S j) (TensorChain S j)) p s r) =
          liftInPairs b p s (lift b x (2 * p) r) := by
      induction s with
      | tmul s s' => rfl
      | add s s' hs hs' => simp [hs, hs']
    rw [compUpTo_succ_apply, ← ih]
    exact h_step (τ p) (ofPairs τ p)

/-- Acting by `t j` on each factor of the regrouped tensor `ofPairs τ p` is acting by
`t (2 * i) ⊗ t (2 * i + 1)` on each `τ i`. -/
lemma map_ofPairs (τ : ∀ i : ℕ, S (2 * i) ⊗[ℂ] S (2 * i + 1)) (p : ℕ) :
    map t (2 * p) (ofPairs τ p) =
      ofPairs (fun i : ℕ ↦ TensorProduct.map (t (2 * i)) (t (2 * i + 1)) (τ i)) p := by
  let mkChain (j : ℕ) : S j →ₗ[ℂ] TensorChain S j →ₗ[ℂ] TensorChain S (j + 1) :=
    TensorProduct.mk ℂ (S j) (TensorChain S j)
  have h_pair (i : ℕ) : liftInPairs (fun j : ℕ ↦ mkChain j ∘ₗ t j) i =
      liftInPairs mkChain i ∘ₗ TensorProduct.map (t (2 * i)) (t (2 * i + 1)) :=
    TensorProduct.ext' fun s s' ↦ rfl
  refine (lift_ofPairs (fun j : ℕ ↦ mkChain j ∘ₗ t j) τ p (1 : ℂ)).trans ?_
  simp only [h_pair, comp_apply, ofPairs, mkChain]

end New.TensorChain

end TensorChain

/-! ## Linear forms separating the points of a tensor product -/

section TensorSeparation

open LinearMap TensorProduct Module

variable {k U V W : Type*} [AddCommGroup U] [AddCommGroup V]

/-- Let `R` be a principal ideal domain, `V` a torsion-free `R`-module and `f i` linear forms on
`U` whose only common zero is `0`. An element of `U ⊗ V` killed by all the maps
`u ⊗ v ↦ f i u • v` is `0`. -/
lemma New.tensor_eq_zero_of_separating {R : Type*} {ι : Sort*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [Module R U] [Module R V] [IsTorsionFree R V] {f : ι → Dual R U}
    (hf : ∀ {a : U}, (∀ i : ι, f i a = 0) → a = 0) (Z : U ⊗[R] V)
    (hZ : ∀ i : ι, lift (lsmul R V ∘ₗ f i) Z = 0) :
    Z = 0 := by
  -- `Z` comes from `U ⊗ S` for a finitely generated `S ≤ V`, which is free; write
  -- `Z = ∑ j, c j ⊗ e j` in a basis `e` of `S`. Applying `u ⊗ v ↦ f i u • v` gives a relation among
  -- the `e j`, so every `f i (c j)` vanishes, hence every `c j` does.
  obtain ⟨S, hS, Z', rfl⟩ :
      ∃ S : Submodule R V, Module.Finite R S ∧ ∃ Z' : U ⊗[R] S, lTensor U S.subtype Z' = Z := by
    simpa using exists_finite_submodule_right_of_setFinite {Z}
  let e : Basis (Fin (finrank R S)) R S := finBasis R S
  obtain ⟨c, rfl⟩ := Z'.eq_repr_basis_right e
  have h_relation (i : ι) : ∑ j : Fin (finrank R S), f i (c j) • e j = 0 := by
    simpa [c.sum_fintype, Subtype.ext_iff] using hZ i
  have hc : c = 0 := Finsupp.ext fun j ↦
    hf fun i ↦ Fintype.linearIndependent_iff.1 e.linearIndependent _ (h_relation i) j
  simp [hc]

end TensorSeparation

end
