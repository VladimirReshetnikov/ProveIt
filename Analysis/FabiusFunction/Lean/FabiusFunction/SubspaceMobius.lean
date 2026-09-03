import FabiusFunction.SubspaceCount
import FabiusFunction.QBinomialInversion
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The Möbius function of the subspace lattice

This module proves the Gaussian evaluation of the Möbius function of the lattice of submodules
of a finite module, in the interval form:

`μ(U, W) = (-1) ^ r * Q ^ (r choose 2)`,  where `r = dim W - dim U` and `Q = |K|`,

together with the numbered special case `μ(0, V) = (-1) ^ d * Q ^ (d choose 2)` and its literal
`K ^ n` instance.

## What is covered

Both displays of the source statement, namely the numbered equation and the "more generally"
sentence.  The general interval statement is the primary result (`mu_submodule`); the numbered
display is recovered as `mu_bot_submodule` at `W = ⊤`, packaged as `eulerChar_submodule`, and the
literal `𝔽_Q ^ n` form is `mu_submodule_pi`.

The Lean statements are strictly more general than the source in four independent directions,
each of which is free:

* `K` is an arbitrary finite **division ring**, `Q = Fintype.card K`.  Neither primality of `Q`
  nor commutativity of `K` is ever used.  (This is the same generalization that
  `SubspaceCount` already took for the counting theorem.)
* `V` is an arbitrary finite `K`-module, not `Fin d → K`.  No basis and no dimension bound is
  assumed anywhere.
* The coefficient ring of the incidence algebra is an arbitrary `[CommRing R]`, not `ℤ`.  The
  induction is coefficient-agnostic, and `sum_gaussianBinomial_alternating` already holds over
  every commutative ring, so this costs nothing.  (`CommRing` rather than `Ring` only because
  that corpus lemma is stated over a commutative ring; `IncidenceAlgebra.mu` itself needs only
  `AddCommGroup` and `One`.)
* The order and decidability data on `Submodule K V` are taken as instance-implicit hypotheses
  `[LocallyFiniteOrder (Submodule K V)]` and `[DecidableEq (Submodule K V)]` rather than being
  baked in, so the results hold for whatever instances a caller has.  `Subsingleton
  (LocallyFiniteOrder α)` makes this unambiguous, and `locallyFiniteOrderSubmodule` is exported
  for callers that have none.

## What is *not* covered

* The source's own reduction step — "the correspondence `X ↦ X/U` is an isomorphism from the
  interval `[U, W]` onto the lattice of subspaces of `W/U`, and the Möbius function of a poset
  depends only on the isomorphism type of the interval" — is **not** formalized, deliberately.
  Mathlib has no transport lemma for `IncidenceAlgebra.mu` along an `OrderIso`, and none
  identifying the Möbius function computed inside a `Set.Ici` sub-poset with the ambient one.
  Instead the general interval statement is proved **directly**, by strong induction on
  `r = finrank K W - finrank K U`, using the quotient correspondence only as a *cardinality*
  statement (`intervalQuotientEquiv`, an `Equiv`, never an `OrderIso` transport of `mu`).  Both
  halves of the omitted sentence are true and textbook; the gap is a formalization obstruction,
  not an error in the source.  A `mu`-along-an-`OrderIso` transport lemma remains an open,
  generally useful Mathlib-shaped statement.
* Nothing is proved about `μ(U, W)` for incomparable `U, W` beyond recording Mathlib's
  convention `mu_apply_eq_zero_of_not_le`; the source display leaves that case unspecified.
* The rank `r` is written with truncated natural subtraction `finrank K W - finrank K U`.  That
  this really is `dim (W/U)` is `mu_submodule_quotient`, which states the same value with
  `r = finrank K (W.map U.mkQ)`, the rank of the image of `W` in `V ⧸ U`.

## Main results

* `card_submodule_le_finrank_eq_gaussianBinomial` — the bottom-interval count.
* `card_interval_finrank_eq_gaussianBinomial` — the general-interval count.
* `mu_submodule` — **the theorem**, in interval form.
* `mu_bot_submodule`, `eulerChar_submodule`, `mu_submodule_pi` — the numbered display.
* `gaussianBinomialInverseKernel_eq_mu_mul_gaussianBinomial` — the identification of the
  `q`-binomial inversion kernel with `μ` times the number of intermediate subspaces.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

/-! ## A scalar lemma: the alternating Gaussian row truncated below the diagonal -/

/-- The alternating Gaussian row of length `r`, truncated just below the diagonal, equals minus
the omitted diagonal term.  This is the arithmetic content of the induction step: the full row
sums to `(1; q)_r = 0` for `r ≠ 0`. -/
private theorem sum_range_alternating_gaussianBinomial {R : Type*} [CommRing R] (q : R) {r : ℕ}
    (hr : r ≠ 0) :
    ∑ j ∈ Finset.range r, (-1 : R) ^ j * q ^ j.choose 2 * gaussianBinomial q r j
      = -((-1 : R) ^ r * q ^ r.choose 2) := by
  have halt := sum_gaussianBinomial_alternating q r
  rw [if_neg hr, Finset.sum_range_succ, gaussianBinomial_self, mul_one] at halt
  calc ∑ j ∈ Finset.range r, (-1 : R) ^ j * q ^ j.choose 2 * gaussianBinomial q r j
      = (∑ j ∈ Finset.range r, (-1 : R) ^ j * q ^ j.choose 2 * gaussianBinomial q r j)
          + ((-1 : R) ^ r * q ^ r.choose 2) - ((-1 : R) ^ r * q ^ r.choose 2) := by ring
    _ = 0 - ((-1 : R) ^ r * q ^ r.choose 2) := by rw [halt]
    _ = -((-1 : R) ^ r * q ^ r.choose 2) := by ring

/-- Gaussian coefficients commute with the canonical map `ℕ → R`.  A convenience wrapper around
`map_gaussianBinomial` for the ring homomorphism `Nat.castRingHom`. -/
private theorem natCast_gaussianBinomial {R : Type*} [CommRing R] (Q n j : ℕ) :
    ((gaussianBinomial Q n j : ℕ) : R) = gaussianBinomial (Q : R) n j := by
  simpa using map_gaussianBinomial (Nat.castRingHom R) Q n j

/-! ## Counting the bottom interval of the submodule lattice -/

section BotInterval

variable {K : Type*} [DivisionRing K] [Fintype K]
variable {M : Type*} [AddCommGroup M] [Module K M] [Finite M]

/-- Submodules of `M` contained in `W` correspond to submodules of `W`, and the correspondence
preserves the rank.  This is `Submodule.MapSubtype.orderIso` restricted to a fixed rank layer,
packaged as an `Equiv` so that it can be used for counting. -/
def leSubmoduleEquiv (W : Submodule K M) (j : ℕ) :
    {Z : Submodule K W // Module.finrank K Z = j} ≃
      {X : Submodule K M // X ≤ W ∧ Module.finrank K X = j} where
  toFun Z :=
    ⟨Submodule.map W.subtype Z.1, Submodule.map_subtype_le W Z.1, by
      rw [Submodule.finrank_map_subtype_eq]
      exact Z.2⟩
  invFun X :=
    ⟨Submodule.comap W.subtype X.1, by
      rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe X.2.1)]
      exact X.2.2⟩
  left_inv Z := Subtype.ext <| by
    show Submodule.comap W.subtype (Submodule.map W.subtype Z.1) = Z.1
    rw [Submodule.comap_map_eq, Submodule.ker_subtype, sup_bot_eq]
  right_inv X := Subtype.ext <| by
    show Submodule.map W.subtype (Submodule.comap W.subtype X.1) = X.1
    rw [Submodule.map_comap_subtype, inf_of_le_right X.2.1]

/-- **Counting the bottom interval.**  Over a finite division ring `K` with `Q = |K|`, the number
of submodules of a finite `K`-module `M` that are contained in `W` and have rank `j` is
`[finrank K W, j]_Q`.

No bound relating `j` and `finrank K W` is assumed: above the diagonal both sides vanish. -/
theorem card_submodule_le_finrank_eq_gaussianBinomial (W : Submodule K M) (j : ℕ) :
    Nat.card {X : Submodule K M // X ≤ W ∧ Module.finrank K X = j}
      = gaussianBinomial (Fintype.card K) (Module.finrank K W) j := by
  rw [← Nat.card_congr (leSubmoduleEquiv W j)]
  exact card_submodule_finrank_eq_gaussianBinomial j

end BotInterval

/-! ## Counting a general interval of the submodule lattice -/

section Interval

variable {K V : Type*} [DivisionRing K] [Fintype K] [AddCommGroup V] [Module K V] [Finite V]

/-- **Rank of an intermediate submodule modulo `U`.**  If `U ≤ X` then `dim (X/U) + dim U =
dim X`, with `X/U` realized as the image of `X` in `V ⧸ U`.  This is rank–nullity for
`U.mkQ ∘ X.subtype`. -/
theorem finrank_map_mkQ_add {U X : Submodule K V} (h : U ≤ X) :
    Module.finrank K (Submodule.map U.mkQ X) + Module.finrank K U = Module.finrank K X := by
  have hrange : LinearMap.range (U.mkQ.comp X.subtype) = Submodule.map U.mkQ X := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hker : LinearMap.ker (U.mkQ.comp X.subtype) = Submodule.comap X.subtype U := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hkerrank :
      Module.finrank K (LinearMap.ker (U.mkQ.comp X.subtype)) = Module.finrank K U := by
    rw [hker]
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe h)
  have hrn := LinearMap.finrank_range_add_finrank_ker (U.mkQ.comp X.subtype)
  rw [hrange, hkerrank] at hrn
  exact hrn

/-- The rank of `X/U` in subtracted form. -/
theorem finrank_map_mkQ {U X : Submodule K V} (h : U ≤ X) :
    Module.finrank K (Submodule.map U.mkQ X) = Module.finrank K X - Module.finrank K U := by
  have h1 := finrank_map_mkQ_add h
  omega

/-- Taking the preimage of the image under `U.mkQ` is the identity on submodules above `U`. -/
private theorem comap_map_mkQ_of_le {U X : Submodule K V} (h : U ≤ X) :
    Submodule.comap U.mkQ (Submodule.map U.mkQ X) = X := by
  rw [Submodule.comap_map_mkQ, sup_of_le_right h]

/-- Taking the image of the preimage under `U.mkQ` is the identity, since `U.mkQ` is onto. -/
private theorem map_comap_mkQ {U : Submodule K V} (Y : Submodule K (V ⧸ U)) :
    Submodule.map U.mkQ (Submodule.comap U.mkQ Y) = Y :=
  Submodule.map_comap_eq_self (by rw [Submodule.range_mkQ]; exact le_top)

/-- The forward direction of the interval correspondence, on the level of the defining
properties. -/
private theorem map_mkQ_spec {U W X : Submodule K V} {j : ℕ}
    (hX : U ≤ X ∧ X ≤ W ∧ Module.finrank K X = Module.finrank K U + j) :
    Submodule.map U.mkQ X ≤ Submodule.map U.mkQ W ∧
      Module.finrank K (Submodule.map U.mkQ X) = j := by
  refine ⟨Submodule.map_mono hX.2.1, ?_⟩
  have h1 := finrank_map_mkQ_add hX.1
  have h2 := hX.2.2
  omega

/-- The backward direction of the interval correspondence, on the level of the defining
properties. -/
private theorem comap_mkQ_spec {U W : Submodule K V} (hUW : U ≤ W) {Y : Submodule K (V ⧸ U)}
    {j : ℕ} (hY : Y ≤ Submodule.map U.mkQ W ∧ Module.finrank K Y = j) :
    U ≤ Submodule.comap U.mkQ Y ∧ Submodule.comap U.mkQ Y ≤ W ∧
      Module.finrank K (Submodule.comap U.mkQ Y) = Module.finrank K U + j := by
  refine ⟨Submodule.le_comap_mkQ U Y, ?_, ?_⟩
  · have hle := Submodule.comap_mono (f := U.mkQ) hY.1
    rwa [comap_map_mkQ_of_le hUW] at hle
  · have h1 := finrank_map_mkQ_add (Submodule.le_comap_mkQ U Y)
    rw [map_comap_mkQ Y] at h1
    have h2 := hY.2
    omega

/-- **The interval correspondence, as an equivalence of rank layers.**  For `U ≤ W`, the
submodules `X` with `U ≤ X ≤ W` and `dim X = dim U + j` correspond to the rank-`j` submodules of
`V ⧸ U` contained in the image of `W`.

This is only the *bijection*; it is deliberately not upgraded to an order isomorphism, because
the proof of `mu_submodule` uses it purely as a counting device. -/
def intervalQuotientEquiv {U W : Submodule K V} (hUW : U ≤ W) (j : ℕ) :
    {X : Submodule K V // U ≤ X ∧ X ≤ W ∧ Module.finrank K X = Module.finrank K U + j} ≃
      {Y : Submodule K (V ⧸ U) //
        Y ≤ Submodule.map U.mkQ W ∧ Module.finrank K Y = j} where
  toFun X := ⟨Submodule.map U.mkQ X.1, map_mkQ_spec (W := W) X.2⟩
  invFun Y := ⟨Submodule.comap U.mkQ Y.1, comap_mkQ_spec hUW Y.2⟩
  left_inv X := Subtype.ext <| by
    show Submodule.comap U.mkQ (Submodule.map U.mkQ X.1) = X.1
    exact comap_map_mkQ_of_le X.2.1
  right_inv Y := Subtype.ext <| by
    show Submodule.map U.mkQ (Submodule.comap U.mkQ Y.1) = Y.1
    exact map_comap_mkQ Y.1

/-- **Counting a general interval.**  For `U ≤ W` the number of submodules `X` with
`U ≤ X ≤ W` and `dim X = dim U + j` is `[dim W - dim U, j]_Q`. -/
theorem card_interval_finrank_eq_gaussianBinomial {U W : Submodule K V} (hUW : U ≤ W) (j : ℕ) :
    Nat.card {X : Submodule K V //
        U ≤ X ∧ X ≤ W ∧ Module.finrank K X = Module.finrank K U + j}
      = gaussianBinomial (Fintype.card K) (Module.finrank K W - Module.finrank K U) j := by
  haveI : Finite (V ⧸ U) := Finite.of_surjective _ U.mkQ_surjective
  rw [Nat.card_congr (intervalQuotientEquiv hUW j),
    card_submodule_le_finrank_eq_gaussianBinomial (Submodule.map U.mkQ W) j,
    finrank_map_mkQ hUW]

end Interval

/-! ## The subspace lattice is locally finite -/

section LocallyFinite

variable {K V : Type*} [DivisionRing K] [Fintype K] [AddCommGroup V] [Module K V] [Finite V]

/-- The submodule lattice of a finite module is a locally finite order.

This is a `def`, not an `instance`, so that it does not pollute downstream elaboration; the
results below take `LocallyFiniteOrder (Submodule K V)` as a hypothesis instead.  Since
`LocallyFiniteOrder α` is a subsingleton, it makes no difference which one a caller supplies. -/
noncomputable def locallyFiniteOrderSubmodule : LocallyFiniteOrder (Submodule K V) :=
  LocallyFiniteOrder.ofFiniteIcc fun _ _ => Set.toFinite _

end LocallyFinite

/-! ## The Möbius function of the submodule lattice -/

section Mobius

variable {K V : Type*} [DivisionRing K] [Fintype K] [AddCommGroup V] [Module K V] [Finite V]
variable {R : Type*} [CommRing R]
variable [LocallyFiniteOrder (Submodule K V)] [DecidableEq (Submodule K V)]

/-- Mathlib's Möbius function vanishes off the order relation.  The source display characterizes
`μ` only on comparable pairs; this records the standard completion. -/
theorem mu_apply_eq_zero_of_not_le {U W : Submodule K V} (h : ¬U ≤ W) :
    IncidenceAlgebra.mu R U W = 0 :=
  IncidenceAlgebra.apply_eq_zero_of_not_le h (IncidenceAlgebra.mu R)

/-- The theorem, in the form the strong induction on `r = dim W - dim U` produces. -/
private theorem mu_aux (r : ℕ) : ∀ U W : Submodule K V, U ≤ W →
    Module.finrank K W - Module.finrank K U = r →
    IncidenceAlgebra.mu R U W = (-1 : R) ^ r * (Fintype.card K : R) ^ r.choose 2 := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro U W hUW hr
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · subst hr0
      have hmono : Module.finrank K U ≤ Module.finrank K W := Submodule.finrank_mono hUW
      have hUeqW : U = W := Submodule.eq_of_le_of_finrank_eq hUW (by omega)
      have hchoose : Nat.choose 0 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hUeqW]
      simp [hchoose]
    · have hne : U ≠ W := by
        rintro rfl
        omega
      have hmu : IncidenceAlgebra.mu R U W
          = -∑ X ∈ Finset.Ico U W, IncidenceAlgebra.mu R U X :=
        IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hne
      -- Every strictly intermediate submodule sits at a strictly smaller relative rank.
      have hmem : ∀ X ∈ Finset.Ico U W, Module.finrank K X - Module.finrank K U < r := by
        intro X hX
        rw [Finset.mem_Ico] at hX
        have h1 : Module.finrank K U ≤ Module.finrank K X := Submodule.finrank_mono hX.1
        have h2 : Module.finrank K X < Module.finrank K W :=
          Submodule.finrank_lt_finrank_of_lt hX.2
        omega
      have hIH : ∀ X ∈ Finset.Ico U W,
          IncidenceAlgebra.mu R U X
            = (-1 : R) ^ (Module.finrank K X - Module.finrank K U)
              * (Fintype.card K : R) ^ (Module.finrank K X - Module.finrank K U).choose 2 := by
        intro X hX
        exact ih _ (hmem X hX) U X (Finset.mem_Ico.mp hX).1 rfl
      -- The fibres of the relative-rank map are the interval layers counted above.
      have hcardnat : ∀ j : ℕ, j < r →
          ((Finset.Ico U W).filter
              (fun X : Submodule K V => Module.finrank K X - Module.finrank K U = j)).card
            = gaussianBinomial (Fintype.card K) r j := by
        intro j hj
        have hint := card_interval_finrank_eq_gaussianBinomial hUW j
        rw [hr] at hint
        rw [← hint]
        refine (Nat.subtype_card _ ?_).symm
        intro X
        simp only [Finset.mem_filter, Finset.mem_Ico]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          have h4 : Module.finrank K U ≤ Module.finrank K X := Submodule.finrank_mono h1
          exact ⟨h1, le_of_lt h2, by omega⟩
        · rintro ⟨h1, h2, h3⟩
          have h4 : Module.finrank K U ≤ Module.finrank K W := Submodule.finrank_mono hUW
          refine ⟨⟨h1, lt_of_le_of_ne h2 ?_⟩, by omega⟩
          rintro rfl
          omega
      have hmaps : ∀ X ∈ Finset.Ico U W,
          Module.finrank K X - Module.finrank K U ∈ Finset.range r :=
        fun X hX => Finset.mem_range.mpr (hmem X hX)
      have hfiber :
          ∑ j ∈ Finset.range r,
              ∑ X ∈ (Finset.Ico U W).filter
                  (fun X : Submodule K V => Module.finrank K X - Module.finrank K U = j),
                ((-1 : R) ^ j * (Fintype.card K : R) ^ j.choose 2)
            = ∑ X ∈ Finset.Ico U W,
                ((-1 : R) ^ (Module.finrank K X - Module.finrank K U)
                  * (Fintype.card K : R)
                      ^ (Module.finrank K X - Module.finrank K U).choose 2) :=
        Finset.sum_fiberwise_of_maps_to' hmaps
          (fun j => (-1 : R) ^ j * (Fintype.card K : R) ^ j.choose 2)
      have hchain : ∑ X ∈ Finset.Ico U W, IncidenceAlgebra.mu R U X
          = -((-1 : R) ^ r * (Fintype.card K : R) ^ r.choose 2) :=
        calc ∑ X ∈ Finset.Ico U W, IncidenceAlgebra.mu R U X
            = ∑ X ∈ Finset.Ico U W,
                ((-1 : R) ^ (Module.finrank K X - Module.finrank K U)
                  * (Fintype.card K : R)
                      ^ (Module.finrank K X - Module.finrank K U).choose 2) :=
              Finset.sum_congr rfl hIH
          _ = ∑ j ∈ Finset.range r,
                ∑ X ∈ (Finset.Ico U W).filter
                    (fun X : Submodule K V => Module.finrank K X - Module.finrank K U = j),
                  ((-1 : R) ^ j * (Fintype.card K : R) ^ j.choose 2) := hfiber.symm
          _ = ∑ j ∈ Finset.range r,
                (((Finset.Ico U W).filter
                    (fun X : Submodule K V => Module.finrank K X - Module.finrank K U = j)).card : R)
                  * ((-1 : R) ^ j * (Fintype.card K : R) ^ j.choose 2) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_const, nsmul_eq_mul]
          _ = ∑ j ∈ Finset.range r,
                (-1 : R) ^ j * (Fintype.card K : R) ^ j.choose 2
                  * gaussianBinomial (Fintype.card K : R) r j := by
              refine Finset.sum_congr rfl fun j hj => ?_
              rw [hcardnat j (Finset.mem_range.mp hj), natCast_gaussianBinomial]
              ring
          _ = -((-1 : R) ^ r * (Fintype.card K : R) ^ r.choose 2) :=
              sum_range_alternating_gaussianBinomial _ (by omega)
      rw [hmu, hchain, neg_neg]

/-- **The Möbius function of the submodule lattice.**  For `U ≤ W` submodules of a finite module
`V` over a finite division ring `K` with `Q = |K|`,

`μ(U, W) = (-1) ^ r * Q ^ (r choose 2)`,  where `r = finrank K W - finrank K U`,

with values in an arbitrary commutative ring `R`.

This is the "more generally" clause of the source statement, and the numbered display is its
special case `U = ⊥`, `W = ⊤` (see `eulerChar_submodule`).  The source proves it by transporting
the numbered display along the interval isomorphism `[U, W] ≃ 𝓛(W/U)`; here it is proved
directly by strong induction on `r`, the quotient correspondence entering only as the counting
statement `card_interval_finrank_eq_gaussianBinomial`. -/
theorem mu_submodule {U W : Submodule K V} (h : U ≤ W) :
    IncidenceAlgebra.mu R U W
      = (-1 : R) ^ (Module.finrank K W - Module.finrank K U)
        * (Fintype.card K : R) ^ (Module.finrank K W - Module.finrank K U).choose 2 :=
  mu_aux (Module.finrank K W - Module.finrank K U) U W h rfl

/-- The same value with the rank written as `dim (W/U)`, the rank of the image of `W` in
`V ⧸ U`.  This is the source's own `r = dim (W/U)`, without truncated subtraction. -/
theorem mu_submodule_quotient {U W : Submodule K V} (h : U ≤ W) :
    IncidenceAlgebra.mu R U W
      = (-1 : R) ^ Module.finrank K (Submodule.map U.mkQ W)
        * (Fintype.card K : R) ^ (Module.finrank K (Submodule.map U.mkQ W)).choose 2 := by
  rw [finrank_map_mkQ h]
  exact mu_submodule h

/-- The Möbius function from the zero submodule: `μ(0, W) = (-1) ^ dim W * Q ^ (dim W choose 2)`
for every submodule `W`. -/
theorem mu_bot_submodule (W : Submodule K V) :
    IncidenceAlgebra.mu R (⊥ : Submodule K V) W
      = (-1 : R) ^ Module.finrank K W
        * (Fintype.card K : R) ^ (Module.finrank K W).choose 2 := by
  have hbot : Module.finrank K (⊥ : Submodule K V) = 0 := by simp
  have h := mu_submodule (R := R) (bot_le : (⊥ : Submodule K V) ≤ W)
  rw [hbot, Nat.sub_zero] at h
  exact h

/-- **The numbered display.**  The Euler characteristic of the submodule lattice of a
`d`-dimensional module is `(-1) ^ d * Q ^ (d choose 2)`, i.e. `μ(0, V) = (-1) ^ d Q ^ (d
choose 2)`. -/
theorem eulerChar_submodule :
    IncidenceAlgebra.eulerChar R (Submodule K V)
      = (-1 : R) ^ Module.finrank K V
        * (Fintype.card K : R) ^ (Module.finrank K V).choose 2 := by
  have htop : Module.finrank K (⊤ : Submodule K V) = Module.finrank K V := by simp
  have h := mu_bot_submodule (R := R) (⊤ : Submodule K V)
  rw [htop] at h
  exact h

/-- **The inversion kernel is Möbius times the number of intermediate subspaces.**  If `U ≤ W`
are submodules with `finrank K W - finrank K U = n - j`, then the signed inverse Gaussian kernel
of `q`-binomial inversion at `(n, j)` is `μ(U, W) * [n, j]_Q`.  This certifies the source's
remark identifying `q`-binomial inversion with Möbius inversion over the subspace lattice for
functions depending only on dimension. -/
theorem gaussianBinomialInverseKernel_eq_mu_mul_gaussianBinomial {U W : Submodule K V}
    (hUW : U ≤ W) {n j : ℕ} (hn : n - j = Module.finrank K W - Module.finrank K U) :
    gaussianBinomialInverseKernel (Fintype.card K : R) n j
      = IncidenceAlgebra.mu R U W * gaussianBinomial (Fintype.card K : R) n j := by
  unfold gaussianBinomialInverseKernel
  rw [mu_submodule (R := R) hUW, ← hn]

end Mobius

/-! ## The literal source statement over `K ^ n` -/

/-- **The source statement verbatim.**  In the lattice of subspaces of `K ^ n`, for `K` a finite
division ring with `Q = |K|`,

`μ(0, K ^ n) = (-1) ^ n * Q ^ (n choose 2)`.

The source assumes `Q` a prime power; primality is never used. -/
theorem mu_submodule_pi {K : Type*} [DivisionRing K] [Fintype K] {R : Type*} [CommRing R]
    (n : ℕ) [LocallyFiniteOrder (Submodule K (Fin n → K))]
    [DecidableEq (Submodule K (Fin n → K))] :
    IncidenceAlgebra.mu R (⊥ : Submodule K (Fin n → K)) ⊤
      = (-1 : R) ^ n * (Fintype.card K : R) ^ n.choose 2 := by
  have htop : Module.finrank K (⊤ : Submodule K (Fin n → K)) = n := by
    simp [Module.finrank_fintype_fun_eq_card]
  have h := mu_bot_submodule (K := K) (V := Fin n → K) (R := R) ⊤
  rw [htop] at h
  exact h

end Fabius
