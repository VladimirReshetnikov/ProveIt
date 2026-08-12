import PolynomialFormulas.LazardOptimality
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Relrank
import Mathlib.Tactic

/-!
# The valid degree and radical-count core of Lazard's Theorem 4

The leastness assertion in the printed theorem is false for Lazard's literal
definition of radical extension.  Its tower-law calculation is nevertheless
valid: if the fifth-root-of-unity field has degree `2^d` and the relative
splitting field has Galois group of order `5 * 2^e`, then the total degree is
`5 * 2^(d+e)`.

This file also gives an exact predicate for the phrase "defined by `n` square
roots and one fifth root".  The predicate contains the actual successive
power-membership proofs; no degree calculation is silently converted into a
radical presentation.  The general construction below derives the generators
from an exact index-two Galois tower and a final Kummer layer; this remains
logically distinct from the elementary degree theorem.
-/

namespace LeanProofs.PolynomialFormulas.LazardOptimalityTheoremFourDegree

open IntermediateField
open Polynomial
open LeanProofs.PolynomialFormulas.LazardOptimality

set_option autoImplicit false

section Degree

variable (F K L : Type*) [Field F] [Field K] [Field L]
variable [Algebra F K] [Algebra K L] [Algebra F L]
variable [IsScalarTower F K L]
variable [FiniteDimensional F K] [FiniteDimensional K L]

/-- The tower-law arithmetic in the last sentence of Lazard's Theorem 4. -/
theorem finrank_five_mul_two_pow_add
    (d e : ℕ)
    (hcyclotomic : Module.finrank F K = 2 ^ d)
    (hrelative : Module.finrank K L = 5 * 2 ^ e) :
    Module.finrank F L = 5 * 2 ^ (d + e) := by
  calc
    Module.finrank F L =
        Module.finrank F K * Module.finrank K L :=
      (Module.finrank_mul_finrank F K L).symm
    _ = (2 ^ d) * (5 * 2 ^ e) := by rw [hcyclotomic, hrelative]
    _ = 5 * 2 ^ (d + e) := by rw [pow_add]; ring

/-- Paper-shaped version: for a finite Galois relative extension, its degree
is the order of its Galois group, so the preceding tower calculation applies
directly to the order hypothesis printed by Lazard. -/
theorem finrank_five_mul_two_pow_add_of_galois_order
    [IsGalois K L]
    (d e : ℕ)
    (hcyclotomic : Module.finrank F K = 2 ^ d)
    (hgal : Nat.card (L ≃ₐ[K] L) = 5 * 2 ^ e) :
    Module.finrank F L = 5 * 2 ^ (d + e) := by
  apply finrank_five_mul_two_pow_add F K L d e hcyclotomic
  exact (IsGalois.card_aut_eq_finrank K L).symm.trans hgal

end Degree

section RadicalCount

variable (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]

/-- A finite Galois extension of prime degree is cyclic.  This is the small
group-theoretic bridge used for every index-two layer and for the final
degree-five layer below. -/
theorem isCyclic_gal_of_prime_finrank
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} [Fact p.Prime]
    (hdegree : Module.finrank K L = p) :
    IsCyclic Gal(L/K) := by
  apply isCyclic_of_prime_card (p := p)
  rw [IsGalois.card_aut_eq_finrank K L, hdegree]

/-- Ambient-field form of the Kummer generator theorem.  Mathlib produces a
generator in the relative extension type `extendScalars hKL`; this lemma
forgets the subtype and identifies the corresponding compositum inside the
fixed ambient field `Ω`.

The roots-of-unity hypothesis is essential.  In particular, this theorem
does not infer a radical presentation from the numerical degree alone. -/
theorem exists_ambient_power_generator_of_isCyclic
    {K L : IntermediateField F Ω} (hKL : K ≤ L)
    [FiniteDimensional K (IntermediateField.extendScalars hKL)]
    [IsGalois K (IntermediateField.extendScalars hKL)]
    [IsCyclic Gal((IntermediateField.extendScalars hKL)/K)]
    (hroots :
      (primitiveRoots
        (Module.finrank K (IntermediateField.extendScalars hKL)) K).Nonempty) :
    ∃ α : Ω,
      α ^ Module.finrank K (IntermediateField.extendScalars hKL) ∈ K ∧
        L = K ⊔ IntermediateField.adjoin F {α} := by
  let E : IntermediateField K Ω := IntermediateField.extendScalars hKL
  obtain ⟨α, hαpow, hαtop⟩ :=
    exists_root_adjoin_eq_top_of_isCyclic K E hroots
  refine ⟨(α : Ω), ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hαpow
    change ((α ^ Module.finrank K E : E) : Ω) ∈ K
    rw [← ha]
    exact a.property
  · apply le_antisymm
    · intro x hx
      let y : E := ⟨x, hx⟩
      have hy : y ∈ IntermediateField.adjoin K ({α} : Set E) := by
        rw [hαtop]
        exact trivial
      exact IntermediateField.adjoin_induction K
        (E := E) (s := ({α} : Set E))
        (p := fun z _ => (z : Ω) ∈
          K ⊔ IntermediateField.adjoin F {(α : Ω)})
        (by
          rintro z rfl
          exact
            (show IntermediateField.adjoin F {(z : Ω)} ≤
                K ⊔ IntermediateField.adjoin F {(z : Ω)} from
              le_sup_right)
            (IntermediateField.mem_adjoin_simple_self F (z : Ω)))
        (fun z =>
          (show K ≤ K ⊔ IntermediateField.adjoin F {(α : Ω)} from
            le_sup_left) z.property)
        (fun _ _ _ _ hz hw => add_mem hz hw)
        (fun _ _ hz => inv_mem hz)
        (fun _ _ _ _ hz hw => mul_mem hz hw)
        hy
    · exact sup_le hKL (IntermediateField.adjoin_le_iff.mpr (by
        rintro z rfl
        exact α.property))

/-- An exact-length tower obtained by adjoining one square root at each step.
The terminal field is definitionally the successive compositum of the simple
adjunctions, rather than an arbitrary field merely having degree `2^n`. -/
inductive IsSquareRadicalTower
    (K : IntermediateField F Ω) : ℕ → IntermediateField F Ω → Prop
  | zero : IsSquareRadicalTower K 0 K
  | succ {n : ℕ} {L : IntermediateField F Ω}
      (h : IsSquareRadicalTower K n L)
      (α : Ω) (hpow : α ^ 2 ∈ L) :
      IsSquareRadicalTower K (n + 1)
        (L ⊔ IntermediateField.adjoin F {α})

/-- A supplied tower of finite Galois layers of relative degree two.  This
is the field-theoretic form of an index-two subgroup chain under Galois
correspondence.  Unlike `IsSquareRadicalTower`, its constructors do not
contain radical generators; those are derived from Kummer theory in
`isSquareRadicalTower` below. -/
inductive IsIndexTwoGaloisTower
    (K : IntermediateField F Ω) : ℕ → IntermediateField F Ω → Prop
  | zero : IsIndexTwoGaloisTower K 0 K
  | succ {n : ℕ} {L M : IntermediateField F Ω}
      (tower : IsIndexTwoGaloisTower K n L)
      (hLM : L ≤ M)
      (finite : FiniteDimensional L (IntermediateField.extendScalars hLM))
      (galois : IsGalois L (IntermediateField.extendScalars hLM))
      (index_two :
        Module.finrank L (IntermediateField.extendScalars hLM) = 2) :
      IsIndexTwoGaloisTower K (n + 1) M

namespace IsIndexTwoGaloisTower

theorem le
    {K L : IntermediateField F Ω} {n : ℕ}
    (h : IsIndexTwoGaloisTower F Ω K n L) : K ≤ L := by
  induction h with
  | zero => exact le_rfl
  | succ _ hLM _ _ _ ih => exact ih.trans hLM

/-- In characteristic zero, every supplied index-two Galois tower is an
actual tower of square-root adjunctions of the same exact length.  The proof
uses `-1` as the primitive square root of unity at each layer and obtains the
radical generator from Mathlib's cyclic Kummer theorem. -/
theorem isSquareRadicalTower
    [CharZero Ω]
    {K L : IntermediateField F Ω} {n : ℕ}
    (h : IsIndexTwoGaloisTower F Ω K n L) :
    IsSquareRadicalTower F Ω K n L := by
  letI : CharZero F := RingHom.charZero (algebraMap F Ω)
  induction h with
  | zero => exact IsSquareRadicalTower.zero
  | @succ n L M tower hLM hfinite hgalois hindex ih =>
      let E : IntermediateField L Ω := IntermediateField.extendScalars hLM
      letI : FiniteDimensional L E := hfinite
      letI : IsGalois L E := hgalois
      letI : IsCyclic Gal(E/L) :=
        isCyclic_gal_of_prime_finrank L E hindex
      have hroots :
          (primitiveRoots (Module.finrank L E) L).Nonempty := by
        rw [hindex]
        refine ⟨-1, (mem_primitiveRoots (by norm_num : 0 < 2)).mpr ?_⟩
        exact IsPrimitiveRoot.neg_one 0 (by norm_num)
      obtain ⟨α, hαpow, hM⟩ :=
        exists_ambient_power_generator_of_isCyclic F Ω hLM hroots
      have hαsquare : α ^ 2 ∈ L := by
        simpa only [hindex] using hαpow
      rw [hM]
      exact IsSquareRadicalTower.succ ih α hαsquare

end IsIndexTwoGaloisTower

namespace IsSquareRadicalTower

theorem le
    {K L : IntermediateField F Ω} {n : ℕ}
    (h : IsSquareRadicalTower F Ω K n L) : K ≤ L := by
  induction h with
  | zero => exact le_rfl
  | succ h _ _ ih => exact ih.trans le_sup_left

/-- Every certified square-root tower is a radical extension under Lazard's
literal definition. -/
theorem isRadicalExtension
    {K L : IntermediateField F Ω} {n : ℕ}
    (h : IsSquareRadicalTower F Ω K n L) :
    IsRadicalExtension F Ω K L := by
  induction h with
  | zero => exact isRadicalExtension_refl F Ω _
  | succ h α hpow ih =>
      exact
        LeanProofs.PolynomialFormulas.LazardOptimality.IsRadicalExtension.adjoin_square
          F Ω ih α hpow

/-- Concatenate two certified square-root towers. -/
theorem trans
    {K L M : IntermediateField F Ω} {m n : ℕ}
    (hKL : IsSquareRadicalTower F Ω K m L)
    (hLM : IsSquareRadicalTower F Ω L n M) :
    IsSquareRadicalTower F Ω K (m + n) M := by
  induction hLM with
  | zero => simpa using hKL
  | succ h α hpow ih =>
      simpa [Nat.add_assoc] using
        (IsSquareRadicalTower.succ ih α hpow)

/-- Base-change every stage of an exact square-root tower by a fixed
intermediate field.  The number of displayed square adjunctions is preserved. -/
theorem sup_left
    {K L : IntermediateField F Ω} {n : ℕ}
    (h : IsSquareRadicalTower F Ω K n L)
    (A : IntermediateField F Ω) :
    IsSquareRadicalTower F Ω (A ⊔ K) n (A ⊔ L) := by
  induction h with
  | zero => exact IsSquareRadicalTower.zero
  | @succ n L h α hpow ih =>
      simpa only [sup_assoc] using
        (IsSquareRadicalTower.succ ih α
          ((le_sup_right : L ≤ A ⊔ L) hpow))

/-- Transport a displayed square-root tower along an algebra embedding.  In
particular, this is the honest bridge from the canonical splitting field to a
common ambient splitting field: every radical witness is mapped, and its
square-membership proof is mapped with it. -/
theorem map
    {Ω' : Type*} [Field Ω'] [Algebra F Ω']
    {K L : IntermediateField F Ω} {n : ℕ}
    (h : IsSquareRadicalTower F Ω K n L) (f : Ω →ₐ[F] Ω') :
    IsSquareRadicalTower F Ω' (K.map f) n (L.map f) := by
  induction h with
  | zero => simpa using
      (IsSquareRadicalTower.zero (K := K.map f))
  | @succ n L h α hpow ih =>
      have hpow' : f α ^ 2 ∈ L.map f := by
        simpa only [map_pow] using
          (IntermediateField.map_mem_map (S := L) f).2 hpow
      simpa only [IntermediateField.map_sup,
          IntermediateField.adjoin_map, Set.image_singleton] using
        (IsSquareRadicalTower.succ ih (f α) hpow')

/-- Adjoining an element whose square belongs to an intermediate field
multiplies its absolute degree by at most two.  This is a minpoly bound, not
an assumption that the displayed adjunction is genuinely quadratic. -/
theorem finrank_sup_adjoin_simple_le_of_sq_mem
    (B : IntermediateField F Ω) {x : Ω} (hpow : x ^ 2 ∈ B) :
    Module.finrank F
        ((B ⊔ IntermediateField.adjoin F ({x} : Set Ω)) :
          IntermediateField F Ω) ≤
      Module.finrank F B * 2 := by
  let a : B := ⟨x ^ 2, hpow⟩
  let p : B[X] := Polynomial.X ^ 2 - Polynomial.C a
  have hp : p.Monic := Polynomial.monic_X_pow_sub_C a (by norm_num)
  have heval : Polynomial.aeval x p = 0 := by
    simp [p, a]
  have hx : IsIntegral B x := ⟨p, hp, heval⟩
  have hrelative : Module.finrank B B⟮x⟯ ≤ 2 := by
    rw [IntermediateField.adjoin.finrank hx]
    have hdvd : minpoly B x ∣ p := minpoly.dvd B x heval
    have hle := Polynomial.natDegree_le_of_dvd hdvd hp.ne_zero
    simpa only [p, Polynomial.natDegree_X_pow_sub_C] using hle
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup
    (F := F) B ({x} : Set Ω)]
  change Module.finrank F B⟮x⟯ ≤ Module.finrank F B * 2
  rw [← Module.finrank_mul_finrank F B B⟮x⟯]
  exact Nat.mul_le_mul_left (Module.finrank F B) hrelative

/-- An `n`-step displayed square tower has degree at most `2^n` times the
degree of its starting field.  Collapsed square adjunctions are deliberately
allowed, so this is an inequality rather than an equality. -/
theorem finrank_le_mul_two_pow
    {K L : IntermediateField F Ω} {n : ℕ}
    (h : IsSquareRadicalTower F Ω K n L) :
    Module.finrank F L ≤ Module.finrank F K * 2 ^ n := by
  induction h with
  | zero => simp
  | @succ n L h α hpow ih =>
      calc
        Module.finrank F
            ((L ⊔ IntermediateField.adjoin F ({α} : Set Ω)) :
              IntermediateField F Ω) ≤
            Module.finrank F L * 2 :=
          finrank_sup_adjoin_simple_le_of_sq_mem F Ω L hpow
        _ ≤ (Module.finrank F K * 2 ^ n) * 2 :=
          Nat.mul_le_mul_right 2 ih
        _ = Module.finrank F K * 2 ^ (n + 1) := by
          rw [pow_succ]
          ring

/-- Delete every collapsed step from a displayed square-root tower.  The
remaining length is at most the displayed length, the endpoint is unchanged,
and its relative degree over the starting field is exactly the corresponding
power of two. -/
theorem compress_relfinrank
    [FiniteDimensional F Ω]
    {K L : IntermediateField F Ω} {n : ℕ}
    (h : IsSquareRadicalTower F Ω K n L) :
    ∃ m : ℕ, m ≤ n ∧
      IsSquareRadicalTower F Ω K m L ∧
      K.relfinrank L = 2 ^ m := by
  induction h with
  | zero =>
      exact ⟨0, le_rfl, IsSquareRadicalTower.zero,
        IntermediateField.relfinrank_self K⟩
  | @succ n L h α hpow ih =>
      obtain ⟨m, hmn, hm, hmdegree⟩ := ih
      by_cases hα : α ∈ L
      · have hfield :
          L ⊔ IntermediateField.adjoin F {α} = L :=
          sup_eq_left.mpr
            (IntermediateField.adjoin_simple_le_iff.mpr hα)
        rw [hfield]
        exact ⟨m, by omega, hm, hmdegree⟩
      · let M : IntermediateField F Ω :=
          L ⊔ IntermediateField.adjoin F {α}
        let hLM : L ≤ M := le_sup_left
        let E : IntermediateField L Ω :=
          IntermediateField.extendScalars hLM
        have hstepAbsolute :
            Module.finrank F M ≤ Module.finrank F L * 2 := by
          simpa only [M] using
            finrank_sup_adjoin_simple_le_of_sq_mem F Ω L hpow
        have htower := Module.finrank_mul_finrank F L E
        change Module.finrank F L * Module.finrank L E =
          Module.finrank F M at htower
        have hstepLe : Module.finrank L E ≤ 2 := by
          have hmul :
              Module.finrank F L * Module.finrank L E ≤
                Module.finrank F L * 2 := by
            rw [htower]
            exact hstepAbsolute
          exact Nat.le_of_mul_le_mul_left hmul Module.finrank_pos
        have hstepNeOne : Module.finrank L E ≠ 1 := by
          intro hdegreeOne
          have hrelOne : L.relfinrank M = 1 := by
            rw [IntermediateField.relfinrank_eq_finrank_of_le hLM]
            exact hdegreeOne
          have hML : M ≤ L :=
            IntermediateField.relfinrank_eq_one_iff.mp hrelOne
          apply hα
          exact hML
            ((show IntermediateField.adjoin F {α} ≤ M from le_sup_right)
              (IntermediateField.mem_adjoin_simple_self F α))
        have hstepEq : Module.finrank L E = 2 := by
          have hstepPos : 0 < Module.finrank L E := Module.finrank_pos
          omega
        have hrelStep : L.relfinrank M = 2 := by
          rw [IntermediateField.relfinrank_eq_finrank_of_le hLM]
          exact hstepEq
        have hm' : IsSquareRadicalTower F Ω K (m + 1) M :=
          IsSquareRadicalTower.succ hm α hpow
        have hdegreeM : K.relfinrank M = 2 ^ (m + 1) := by
          calc
            K.relfinrank M =
                K.relfinrank L * L.relfinrank M :=
              (IntermediateField.relfinrank_mul_relfinrank hm.le hLM).symm
            _ = 2 ^ m * 2 := by rw [hmdegree, hrelStep]
            _ = 2 ^ (m + 1) := by rw [pow_succ]
        simpa only [M] using
          (show ∃ r : ℕ, r ≤ n + 1 ∧
              IsSquareRadicalTower F Ω K r M ∧
              K.relfinrank M = 2 ^ r from
            ⟨m + 1, by omega, hm', hdegreeM⟩)

/-- Compression also gives the exact absolute degree.  This is just the
tower law written as `[L:F] = [K:F] * [L:K]`; it remains valid even when the
starting field is not the ground field. -/
theorem compress
    [FiniteDimensional F Ω]
    {K L : IntermediateField F Ω} {n : ℕ}
    (h : IsSquareRadicalTower F Ω K n L) :
    ∃ m : ℕ, m ≤ n ∧
      IsSquareRadicalTower F Ω K m L ∧
      K.relfinrank L = 2 ^ m ∧
      Module.finrank F L = Module.finrank F K * 2 ^ m := by
  obtain ⟨m, hmn, hm, hrelative⟩ := h.compress_relfinrank
  refine ⟨m, hmn, hm, hrelative, ?_⟩
  have htower := IntermediateField.finrank_bot_mul_relfinrank hm.le
  rw [hrelative] at htower
  exact htower.symm

end IsSquareRadicalTower

/-- Literal proposition that `L/K` is defined by exactly `n` square-root
adjunctions followed by one fifth-root adjunction.  The witnesses live under
existentials because a proof-irrelevant `Prop` cannot expose data fields. -/
def IsDefinedBySquareRootsAndFifthRoot
    (K L : IntermediateField F Ω) (n : ℕ) : Prop :=
  ∃ middle : IntermediateField F Ω,
    IsSquareRadicalTower F Ω K n middle ∧
    ∃ fifthRoot : Ω,
      fifthRoot ^ 5 ∈ middle ∧
      L = middle ⊔ IntermediateField.adjoin F {fifthRoot}

namespace IsDefinedBySquareRootsAndFifthRoot

/-- Such a presentation is honestly a radical extension: each power fact is
consumed by the corresponding constructor. -/
theorem isRadicalExtension
    {K L : IntermediateField F Ω} {n : ℕ}
    (h : IsDefinedBySquareRootsAndFifthRoot F Ω K L n) :
    IsRadicalExtension F Ω K L := by
  rcases h with ⟨middle, hsquare, fifthRoot, hfifth, rfl⟩
  exact hsquare.isRadicalExtension.adjoin_fifth F Ω fifthRoot hfifth

/-- Combining a `d`-step cyclotomic square tower with an `e`-step formula
square tower gives the `d+e` count printed in Theorem 4, provided the final
fifth-root power membership is actually supplied. -/
theorem of_two_square_towers
    {K W M : IntermediateField F Ω} {d e : ℕ}
    (hcyclotomic : IsSquareRadicalTower F Ω K d W)
    (hformula : IsSquareRadicalTower F Ω W e M)
    (p : Ω) (hp : p ^ 5 ∈ M) :
    IsDefinedBySquareRootsAndFifthRoot F Ω K
      (M ⊔ IntermediateField.adjoin F {p}) (d + e) :=
  ⟨M, IsSquareRadicalTower.trans F Ω hcyclotomic hformula, p, hp, rfl⟩

/-- General corrected `d+e` path behind the radical-presentation sentence in
Lazard's Theorem 4.

The two supplied towers are exact chains of index-two finite Galois layers.
Their square-root generators are derived by Kummer theory rather than stored
in the hypotheses.  The final layer is a degree-five Galois extension, hence
cyclic; its base is additionally required to contain a primitive fifth root
of unity.  That last roots-of-unity premise is precisely the Kummer hypothesis
which cannot be recovered from the numerical degree alone. -/
theorem of_index_two_galois_towers_and_fifth_kummer
    [CharZero Ω]
    {K W M L : IntermediateField F Ω} {d e : ℕ}
    (hcyclotomic : IsIndexTwoGaloisTower F Ω K d W)
    (hformula : IsIndexTwoGaloisTower F Ω W e M)
    (hML : M ≤ L)
    [FiniteDimensional M (IntermediateField.extendScalars hML)]
    [IsGalois M (IntermediateField.extendScalars hML)]
    (hdegree :
      Module.finrank M (IntermediateField.extendScalars hML) = 5)
    (hroots : (primitiveRoots 5 M).Nonempty) :
    IsDefinedBySquareRootsAndFifthRoot F Ω K L (d + e) := by
  let E : IntermediateField M Ω := IntermediateField.extendScalars hML
  have hdegreeE : Module.finrank M E = 5 := by
    simpa [E] using hdegree
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  letI : IsCyclic Gal(E/M) :=
    isCyclic_gal_of_prime_finrank M E hdegreeE
  have hroots' :
      (primitiveRoots (Module.finrank M E) M).Nonempty := by
    simpa only [hdegreeE] using hroots
  obtain ⟨p, hppow, hL⟩ :=
    exists_ambient_power_generator_of_isCyclic F Ω hML hroots'
  have hp : p ^ 5 ∈ M := by
    simpa only [hdegree] using hppow
  rw [hL]
  exact of_two_square_towers F Ω
    (IsIndexTwoGaloisTower.isSquareRadicalTower F Ω hcyclotomic)
    (IsIndexTwoGaloisTower.isSquareRadicalTower F Ω hformula) p hp

/-- Kummer closes any already-displayed square tower by one fifth-root
adjunction, provided the terminal degree-five layer is genuinely Galois and
its base contains a primitive fifth root of unity.  This form is convenient
after base-changing a fixed-field tower, where the square presentation has
already been transported but the index-two Galois structure need not have
been transported stage by stage. -/
theorem of_square_tower_and_fifth_kummer
    [CharZero Ω]
    {K M L : IntermediateField F Ω} {n : ℕ}
    (hsquare : IsSquareRadicalTower F Ω K n M)
    (hML : M ≤ L)
    [FiniteDimensional M (IntermediateField.extendScalars hML)]
    [IsGalois M (IntermediateField.extendScalars hML)]
    (hdegree :
      Module.finrank M (IntermediateField.extendScalars hML) = 5)
    (hroots : (primitiveRoots 5 M).Nonempty) :
    IsDefinedBySquareRootsAndFifthRoot F Ω K L n := by
  let E : IntermediateField M Ω := IntermediateField.extendScalars hML
  have hdegreeE : Module.finrank M E = 5 := by
    simpa [E] using hdegree
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  letI : IsCyclic Gal(E/M) :=
    isCyclic_gal_of_prime_finrank M E hdegreeE
  have hroots' :
      (primitiveRoots (Module.finrank M E) M).Nonempty := by
    simpa only [hdegreeE] using hroots
  obtain ⟨p, hppow, hL⟩ :=
    exists_ambient_power_generator_of_isCyclic F Ω hML hroots'
  have hp : p ^ 5 ∈ M := by
    simpa only [hdegree] using hppow
  rw [hL]
  exact ⟨M, hsquare, p, hp, rfl⟩

/-- The concrete square/square/fifth pattern used by Lazard carries an
exact two-square-root presentation.  Unlike the degree formula above, this
theorem consumes the three power-membership proofs explicitly. -/
theorem of_two_squares
    {K : IntermediateField F Ω} (ε t p : Ω)
    (hε : ε ^ 2 ∈ K)
    (ht : t ^ 2 ∈ K ⊔ IntermediateField.adjoin F {ε})
    (hp : p ^ 5 ∈
      (K ⊔ IntermediateField.adjoin F {ε}) ⊔
        IntermediateField.adjoin F {t}) :
    IsDefinedBySquareRootsAndFifthRoot F Ω K
      (squareSquareFifthField F Ω K ε t p) 2 := by
  refine ⟨
    (K ⊔ IntermediateField.adjoin F {ε}) ⊔
      IntermediateField.adjoin F {t}, ?_, p, hp, rfl⟩
  have hzero : IsSquareRadicalTower F Ω K 0 K :=
    IsSquareRadicalTower.zero
  have hone := IsSquareRadicalTower.succ hzero ε hε
  have htwo := IsSquareRadicalTower.succ hone t ht
  simpa using htwo

end IsDefinedBySquareRootsAndFifthRoot

end RadicalCount

end LeanProofs.PolynomialFormulas.LazardOptimalityTheoremFourDegree
