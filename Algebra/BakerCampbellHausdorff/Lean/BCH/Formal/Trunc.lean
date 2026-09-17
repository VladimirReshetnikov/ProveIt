/-
# The truncated regular representation of the free algebra

To transfer the analytic Lie-series property (`BCH.LieCoeff`) to the free
algebra `𝕂⟨X, Y⟩` we use a finite-dimensional representation that is faithful in
degrees `≤ N`: the algebra acts on the space `V N` of functions on words of
length `≤ N` by left multiplication, truncated (a letter maps a word to the
longer word if that has length `≤ N`, and to `0` otherwise). The operators on
`V N` form a finite-dimensional Banach algebra, so the results of `BCH.LieCoeff`
apply there.

* `rho 𝕂 N : FreeTwo 𝕂 →ₐ[𝕂] (V 𝕂 N →L[𝕂] V 𝕂 N)`, the representation;
* `rho_apply_delta`: applying `rho a` to the basis vector of the empty word
  recovers the coefficients of `a` on short words;
* `proj_eq_zero_of_rho_eq_zero`: if `rho a = 0` then the homogeneous components
  of `a` of degree `≤ N` vanish.
-/
import BCH.Formal.Free
import BCH.LieCoeff
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.StdBasis

open Finset

attribute [local instance 100] LieRing.ofAssociativeRing

namespace BCH

section Trunc

variable (𝕂 : Type*) [RCLike 𝕂] (N : ℕ)

/-- Words of length at most `N`. -/
def ShortWord : Type := {w : FreeMonoid (Fin 2) // FreeMonoid.length w ≤ N}

instance : Finite (ShortWord N) := by
  have h : Finite {l : List (Fin 2) // l.length ≤ N} :=
    (List.finite_length_le (α := Fin 2) (n := N)).to_subtype
  exact Finite.of_injective
    (fun w : ShortWord N => (⟨FreeMonoid.toList w.1, w.2⟩ : {l : List (Fin 2) // l.length ≤ N}))
    (fun w w' h => Subtype.ext (FreeMonoid.toList.injective (congrArg Subtype.val h)))

noncomputable instance : Fintype (ShortWord N) := Fintype.ofFinite _

noncomputable instance : DecidableEq (ShortWord N) := Classical.decEq _

/-- The finite-dimensional space of functions on words of length `≤ N`. -/
abbrev V := ShortWord N → 𝕂

/-- The empty word, as a short word. -/
def emptyWord : ShortWord N := ⟨1, by rw [FreeMonoid.length_one]; exact Nat.zero_le N⟩

/-- The basis vector of a short word. -/
noncomputable def δ (u : ShortWord N) : V 𝕂 N := Pi.single u 1

/-- The action of a letter on a basis vector: prepend the letter, or `0` if the word becomes
too long. -/
noncomputable def shift (i : Fin 2) (u : ShortWord N) : V 𝕂 N :=
  if h : FreeMonoid.length (FreeMonoid.of i * u.1) ≤ N then δ 𝕂 N ⟨FreeMonoid.of i * u.1, h⟩
  else 0

/-- The action of a letter, as a linear map. -/
noncomputable def act (i : Fin 2) : V 𝕂 N →ₗ[𝕂] V 𝕂 N :=
  (Pi.basisFun 𝕂 (ShortWord N)).constr 𝕂 (shift 𝕂 N i)

lemma act_delta (i : Fin 2) (u : ShortWord N) : act 𝕂 N i (δ 𝕂 N u) = shift 𝕂 N i u := by
  have := (Pi.basisFun 𝕂 (ShortWord N)).constr_basis 𝕂 (shift 𝕂 N i) u
  rwa [Pi.basisFun_apply] at this

/-- The monoid homomorphism from words to operators. -/
noncomputable def wordAct : FreeMonoid (Fin 2) →* (V 𝕂 N →L[𝕂] V 𝕂 N) :=
  FreeMonoid.lift fun i => LinearMap.toContinuousLinearMap (act 𝕂 N i)

/-- The truncated regular representation `𝕂⟨X, Y⟩ → End(V N)`. -/
noncomputable def rho : FreeTwo 𝕂 →ₐ[𝕂] (V 𝕂 N →L[𝕂] V 𝕂 N) :=
  MonoidAlgebra.lift 𝕂 (V 𝕂 N →L[𝕂] V 𝕂 N) (FreeMonoid (Fin 2)) (wordAct 𝕂 N)

lemma rho_single (w : FreeMonoid (Fin 2)) (c : 𝕂) :
    rho 𝕂 N (MonoidAlgebra.single w c) = c • wordAct 𝕂 N w :=
  MonoidAlgebra.lift_single (wordAct 𝕂 N) w c

/-- A word acts on the empty word by producing the word if it is short, and `0` otherwise. -/
lemma wordAct_delta (w : FreeMonoid (Fin 2)) :
    wordAct 𝕂 N w (δ 𝕂 N (emptyWord N)) =
      if h : FreeMonoid.length w ≤ N then δ 𝕂 N ⟨w, h⟩ else 0 := by
  induction w using FreeMonoid.inductionOn' with
  | one =>
    rw [map_one, one_apply_eq_self, dif_pos (by rw [FreeMonoid.length_one]; exact Nat.zero_le N)]
    rfl
  | mul_of i w ih =>
    rw [map_mul, mul_apply_eq_comp, ih]
    have hlen : FreeMonoid.length (FreeMonoid.of i * w) = FreeMonoid.length w + 1 := by
      rw [FreeMonoid.length_mul, FreeMonoid.length_of, add_comm]
    split_ifs with h1 h2 h2
    · rw [wordAct, FreeMonoid.lift_eval_of, LinearMap.coe_toContinuousLinearMap', act_delta]
      simp only [shift, dif_pos h2]
    · rw [wordAct, FreeMonoid.lift_eval_of, LinearMap.coe_toContinuousLinearMap', act_delta]
      simp only [shift, dif_neg h2]
    · exfalso
      rw [hlen] at h2
      omega
    · simp

/-- The representation applied to the empty word recovers the coefficients on short words. -/
lemma rho_apply_delta (a : FreeTwo 𝕂) (u : ShortWord N) :
    rho 𝕂 N a (δ 𝕂 N (emptyWord N)) u = a.coeff u.1 := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, add_apply, Pi.add_apply, ha, hb, MonoidAlgebra.coeff_add, Finsupp.add_apply]
  | single w c =>
    rw [rho_single, smul_apply, Pi.smul_apply, wordAct_delta, MonoidAlgebra.coeff_single,
      Finsupp.single_apply]
    split_ifs with h1 h2 h2
    · have : (⟨w, h1⟩ : ShortWord N) = u := Subtype.ext h2
      rw [this]
      simp [δ]
    · have : u ≠ ⟨w, h1⟩ := fun h => h2 (congrArg Subtype.val h).symm
      simp [δ, this]
    · exfalso
      exact h1 (h2 ▸ u.2)
    · simp

/-- If `rho a = 0` then the homogeneous components of `a` of degree `≤ N` vanish. -/
lemma proj_eq_zero_of_rho_eq_zero {a : FreeTwo 𝕂} (ha : rho 𝕂 N a = 0) {n : ℕ} (hn : n ≤ N) :
    proj n a = 0 := by
  apply MonoidAlgebra.coeff_injective
  ext w
  rw [proj_coeff]
  split_ifs with hw
  · have hwN : FreeMonoid.length w ≤ N := hw ▸ hn
    have h := rho_apply_delta 𝕂 N a ⟨w, hwN⟩
    rw [ha] at h
    have h0 : (0 : V 𝕂 N →L[𝕂] V 𝕂 N) (δ 𝕂 N (emptyWord N)) ⟨w, hwN⟩ = 0 := rfl
    rw [h0] at h
    simp [← h]
  · rfl

end Trunc

end BCH
