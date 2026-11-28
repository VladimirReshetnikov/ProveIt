import Lib.GaloisRep.Main.Defs
import Lib.PadicHodge.Crystalline.HodgeTateJumps
import Lib.PadicHodge.Crystalline.Regularity

/-!
# Local conditions on ℓ-adic Galois representations and their passage to retracts

This file defines local conditions on an `ℓ`-adic representation `r` of `Gal(Ω/E)` (`New.GalRep`) at
a place `A` of `Ω`, that is a `ClosurePlace`: a valuation subring of the fixed field `Ω`, with
valuation `A.valuation`. For `A` above `ℓ`, each condition is stated along the local data
`New.GaloisRep.PadicPlaceEmbedding E A ℓ`. These data consist of an embedding of `Ω` in `ℚ̄_ℓ` that
induces `A`, and a map with open image from the decomposition group to the Galois group of `ℚ_ℓ`.
This map respects Frobenius elements, inertia and the cyclotomic character. Finite type and killing
polynomials pass from a representation to one that embeds in it near the identity. This covers
subrepresentations, restriction to open subgroups and conjugation by automorphisms of `Ω`.

## Main definitions and results

* `New.GaloisRep.IsGoodAt`: unramified, or crystalline.
* `New.GaloisRep.IsFiniteTypeAt`: trivial on an open part of inertia, or potentially crystalline.
* `New.GaloisRep.PolyKillsAt`: the polynomial `P` kills `s`.
* `New.GaloisRep.JumpsRelAt`, `New.GaloisRep.HasJumpsAt`: the Hodge–Tate jumps compared with
  multisets `J`.
* `New.GaloisRep.IsSphericalAbove`: the three conditions that hold at a spherical place `w` of `E`.
* `New.GaloisRep.isFiniteTypeAt_of_retract`, `New.GaloisRep.polyKillsAt_of_retract`,
  `New.GaloisRep.jumpsRelAt_of_retract` (under an extra hypothesis), bundled in
  `New.GaloisRep.local_clauses_of_retract`: finite type, killing polynomials and jumps pass from
  `r'` to a representation `r` that embeds in `r'` near the identity.

Notions from other files:
* `New.Gp`: The absolute Galois group G_p = Gal(Q̄_p over Q_p).
* `New.Period.IsCrystalline`: The elements of B⊗T fixed by the whole group (for
  `New.Period.IsPotentiallyCrystalline`: by the elements near 1) span B⊗T over the period ring B.
* `New.Period.IsWeilPair`: (s, m) with s in G_p acting on the residue field as x ↦ x^(1/p^m).
* `New.Period.IsKilledBy`: T is potentially crystalline and P(β_{s,m}) = 0 on B⊗T, where β_{s,m} is
  the operator `New.Period.linearFrob` of the pair (s, m).
* `New.IsFrob`: `σ` stabilises the valuation subring `A` and `σ • x ≡ x ^ q` modulo the maximal
  ideal for all `x ∈ A`.
* `New.inertiaGroup`: the σ with `New.IsFrob A 1 σ`.

## Relation to the literature

Known; see `Lib.GaloisRep.Main.OddRank` and `Lib.ClassField.Places.LocalFields` for sources.
-/

/-!
## Local conditions at a place

All conditions except those on jumps also have a clause for `A` not above `ℓ` (`A.valuation ℓ = 1`).
-/

namespace New.GaloisRep

open Period

variable (ℓ : ℕ) [ThePrime ℓ] (E m : Type) [Fintype m] [DecidableEq m] [Field E] [Algebra E Ω]

/-- A homomorphism from Gal(Ω/E) to the invertible matrices over ℚ̄_ℓ with rows and columns
indexed by m; continuity is not part of the definition. -/
abbrev _root_.New.GalRep : Type := Gal(Ω/E) →* GL m (PadicAlgCl ℓ)

/-- An embedding of Ω in ℚ̄_ℓ that induces the place A, together with a homomorphism with open image
from the decomposition group of A to Gal(ℚ̄_ℓ/ℚ_ℓ) that goes with it (j(g)(e x) = e(g x) for g in
the decomposition group, the valuation ring of ℚ̄_ℓ pulls back along e to A, and j is an open
embedding) in the sense of `New.GaloisRep.InducesPlace`. -/
class PadicPlaceEmbedding (A : ClosurePlace) (ℓ : outParam ℕ) [ThePrime ℓ] extends OverGp
  (decompGroup Gal(Ω/E) A) ℓ where
  /-- The embedding of Ω in ℚ̄_ℓ. -/
  e : Ω →+* PadicAlgCl ℓ
  /-- The embedding induces the place A, and the map of the decomposition group goes with it. -/
  inducesPlace : InducesPlace E A e toGp

variable {ℓ E m} (r : GalRep ℓ E m)
  (A : ClosurePlace) [NumberField E] [PadicIso ℓ]
  (R : ℕ → ℕ → Prop) (J : (E →+* ℂ) → Multiset ℤ) (w : FinPlace E)

/-- The restriction of r to the decomposition group of A, acting on column vectors over ℚ̄_ℓ. -/
noncomputable abbrev decompRep :
    Representation (PadicAlgCl ℓ) (decompGroup Gal(Ω/E) A) (m → PadicAlgCl ℓ) :=
  matrixRep (r.comp (decompGroup Gal(Ω/E) A).subtype)

/-- The representation r is good at the place A of Ω: r is trivial on the inertia group of A if ℓ
is a unit at A, and its restriction to the decomposition group of A is crystalline along every
local datum `New.GaloisRep.PadicPlaceEmbedding E A ℓ` (an embedding in Q̄_ℓ inducing A). -/
def IsGoodAt : Prop :=
  -- when `ℓ` is a unit at `A`: trivial on the inertia group
  (A.valuation ℓ = 1 → ∀ s ∈ inertiaGroup Gal(Ω/E) A, r s = 1) ∧
  -- for every local datum at `A`: crystalline
  ∀ [PadicPlaceEmbedding E A ℓ], IsCrystalline (decompRep r A)

/-- r is trivial on the inertia elements in a neighbourhood of 1 if ℓ is a unit at A, and
potentially crystalline along every embedding in Q̄_ℓ inducing A.

This corresponds to the classical condition that the Weil–Deligne representation of r at A is
defined and has zero monodromy operator (Grothendieck, Fontaine, Berger). -/
def IsFiniteTypeAt : Prop :=
  -- when `ℓ` is a unit at `A`: trivial on the elements of inertia near `1`
  (A.valuation ℓ = 1 → ∀ᶠ s : Gal(Ω/E) in nhds 1, s ∈ inertiaGroup Gal(Ω/E) A → r s = 1) ∧
  -- for every local datum at `A`: potentially crystalline
  ∀ [PadicPlaceEmbedding E A ℓ], IsPotentiallyCrystalline (decompRep r A)

/-- The polynomial P kills the element s of Gal(Ω/E) at the place A for r: P(r(s)) = 0 if ℓ is a
unit at A, and `New.Period.IsKilledBy` holds for every Weil pair (j s, k) with s in the
decomposition group, along every local datum (e, j) at A.

Of the Weil–Deligne representation of r at A (Fontaine's, for A above ℓ), this records only which
polynomials kill a Weil group element; for `A` above `ℓ` the monodromy operator does not enter. -/
def PolyKillsAt (s : Gal(Ω/E)) (P : Polynomial (PadicAlgCl ℓ)) : Prop :=
  (A.valuation ℓ = 1 → Polynomial.aeval (r s : Matrix m m (PadicAlgCl ℓ)) P = 0) ∧
  -- for every local datum at `A`: `IsKilledBy` for every Weil pair `(toGp s, k)`
  ∀ [L : PadicPlaceEmbedding E A ℓ] ⦃hs : s ∈ decompGroup Gal(Ω/E) A⦄ ⦃k : ℕ⦄,
    IsWeilPair (L.toGp ⟨s, hs⟩) k → IsKilledBy (decompRep r A) ⟨s, hs⟩ k P

/-- Comparison of the Hodge–Tate jumps of `r` at `A` with given multisets `J τ`. For each local
datum at `A` with embedding `e`, each `γ` that agrees with an element `g` of `Gal(ℚ̄_ℓ/ℚ_ℓ)`, and
each integer `u`, the relation `R` holds between two multiplicities. The first is the multiplicity
of `u` in `J` at the embedding `ιℓ⁻¹ ∘ g⁻¹ ∘ e` of `E` in `ℂ`. The second is the multiplicity of `u`
as a jump of `r` at `γ`. For `R = (· = ·)` the jumps are exactly `J` (`New.GaloisRep.HasJumpsAt`).
For `R = New.GaloisRep.OccursIn` every member of `J` is a jump. The condition holds vacuously if
there is no local datum at `A`. Here `ιℓ : ℂ ≃+* ℚ̄_ℓ` is the isomorphism fixed by `New.PadicIso ℓ`,
and `New.Period.jump` is the dimension of the space of Hodge–Tate maps of weight `u`. -/
def JumpsRelAt : Prop :=
  -- for every local datum at `A`, and for every `γ` induced by an element `g` of `Gp ℓ`
  ∀ ⦃L : PadicPlaceEmbedding E A ℓ⦄ ⦃γ : PadicAlgCl ℓ →ₐ[ℤ_[ℓ]] ℂ_[ℓ]⦄ ⦃g : Gp ℓ⦄,
    (∀ x : PadicAlgCl ℓ, γ x = ↑(g x)) →
    -- the multiplicity of `u` in `J` at the complex embedding given by `g⁻¹ ∘ e` is related to
    -- its multiplicity as a jump at `γ`
    ∀ u : ℤ, R ((J (RingHom.comp ιℓ.symm
        (RingHom.comp ↑g⁻¹ (L.e.comp (algebraMap E Ω)) : E →+* PadicAlgCl ℓ))).count u)
      (jump (decompRep r A) γ u)

/-- For each local datum at `A` with embedding `e` and each `g` in `Gal(ℚ̄_ℓ/ℚ_ℓ)`, the Hodge–Tate
jumps of `r` at `g`, with multiplicity, are `J` at the embedding `ιℓ⁻¹ ∘ g⁻¹ ∘ e` of `E` in `ℂ`. -/
abbrev HasJumpsAt : Prop := JumpsRelAt r A Eq J

/-- Occurrence, as a relation between multiplicities: if m is nonzero, so is n. -/
abbrev OccursIn (m n : ℕ) : Prop := m ≠ 0 → n ≠ 0

/-- At every place A of Ω above the finite place w of E (`New.IsPlaceOver A w`): r is good at A
(`New.GaloisRep.IsGoodAt`), its jump multiplicities are related to J by R, and P kills every
geometric Frobenius s at A, that is every s whose inverse is an arithmetic Frobenius for the
residue field size `w.q` of w. -/
def IsSphericalAbove (P : Polynomial (PadicAlgCl ℓ)) : Prop :=
  ∀ ⦃A : ClosurePlace⦄, IsPlaceOver A w →
    -- (a) unramified or crystalline
    IsGoodAt r A ∧
    -- (b) the jumps are related to `J` by `R`
    JumpsRelAt r A R J ∧
    -- (c) `P` kills every geometric Frobenius element
    ∀ s : Gal(Ω/E), IsFrob A w.q s⁻¹ → PolyKillsAt r A s P

end New.GaloisRep

/-!
## Local embeddings and Frobenii, inertia and the cyclotomic character

Take the data `New.GaloisRep.PadicPlaceEmbedding E A ℓ`. The map of the decomposition group of `A`
into Gal(ℚ̄_ℓ over ℚ_ℓ) respects Frobenius elements
(`New.GaloisRep.PadicPlaceEmbedding.isFrob_iff`). It respects inertia
(`New.GaloisRep.PadicPlaceEmbedding.isWeilPair_zero_iff`). It respects the cyclotomic character
(`New.GaloisRep.PadicPlaceEmbedding.cyclotomicGp_eq_cyclotomicChar`).
-/

namespace New.GaloisRep.PadicPlaceEmbedding

variable {ℓ : ℕ} [ThePrime ℓ]
  {E : Type} [Field E] [Algebra E Ω]
  {A : ClosurePlace} [h : PadicPlaceEmbedding E A ℓ]

/-- Let the local datum h at A consist of the embedding e of Ω in ℚ̄_ℓ and the map j = `h.toGp` of
decomposition groups. Then s in the decomposition group of A is an arithmetic q-Frobenius at A
exactly when j(s) is one for the valuation ring of ℚ̄_ℓ. -/
lemma isFrob_iff {q : ℕ} {s : decompGroup Gal(Ω/E) A} :
    IsFrob (intQpBar ℓ) q (h.toGp s) ↔ IsFrob A q s.val := by
  -- Taking the datum apart replaces `A` by `(intQpBar ℓ).comap e`.
  obtain @⟨_, e, ⟨rfl, h_equivariant⟩, -⟩ := h
  -- The Frobenius congruence is a closed condition on `x`: the integers are open and the open
  -- unit ball is closed. So it passes from the dense image of `e` to all of `PadicAlgCl ℓ`.
  let g : Gp ℓ := Period.OverGp.toGp s
  have h_closed : IsClosed {x : PadicAlgCl ℓ | ‖x‖₊ ≤ 1 → g • x - x ^ q ∈ Metric.ball 0 1} :=
    isClosed_imp (Valued.isOpen_integer (PadicAlgCl ℓ))
      ((IsUltrametricDist.isClosed_ball (0 : PadicAlgCl ℓ) 1).preimage (by fun_prop))
  -- Both valuations are read off from the norm of `PadicAlgCl ℓ`; `Metric.mem_ball` stays folded,
  -- as the closedness argument above is stated with the open unit ball.
  calc IsFrob (intQpBar ℓ) q g
      ↔ ∀ x : PadicAlgCl ℓ, ‖x‖₊ ≤ 1 → g • x - x ^ q ∈ Metric.ball 0 1 := by
        simp [IsFrob, isLocalGalois_padic.mem_decompGroup, ← mem_ball_zero_iff, -Metric.mem_ball]
    _ ↔ ∀ x : Ω, ‖e x‖₊ ≤ 1 → g (e x) - e x ^ q ∈ Metric.ball 0 1 :=
        ⟨fun h_all x ↦ h_all (e x), isClosed_property (denseRange_emb_padicAlgCl e) h_closed⟩
    _ ↔ IsFrob ((intQpBar ℓ).comap e) q s.val := by
        simp [g, IsFrob, comap_apply_lt_one_iff, ← h_equivariant, ← mem_ball_zero_iff,
          -Metric.mem_ball,
          -AlgEquiv.smul_def]

/-- Let j = `h.toGp` be the map of decomposition groups of the local datum h at A. For s in the
decomposition group of A, (j s, 0) is a Weil pair, that is j s lies in the inertia group of ℚ̄_ℓ,
exactly when s lies in the inertia group of A. -/
lemma isWeilPair_zero_iff {s : decompGroup Gal(Ω/E) A} :
    Period.IsWeilPair (h.toGp s) 0 ↔ ↑s ∈ inertiaGroup (decompGroup Gal(Ω/E) A) A :=
  -- Both inertia groups consist of the Frobenius elements for `q = 1`.
  Period.isWeilPair_zero_iff.trans isFrob_iff

/-- Let j = `h.toGp` be the map of decomposition groups of the local datum h at A. For g in the
decomposition group of A, the cyclotomic character of Gal(ℚ̄_ℓ/ℚ_ℓ) at j g equals the ℓ-adic
cyclotomic character of Gal(Ω/E) at g. -/
lemma cyclotomicGp_eq_cyclotomicChar (g : decompGroup Gal(Ω/E) A) :
    cyclotomicGp (h.toGp g) = cyclotomicChar Ω ℓ g.val := by
  -- `j g` acts on the image of `e` as `g` acts on `Ω`.
  obtain ⟨⟨-, h_equivariant⟩, -⟩ := h.inducesPlace
  have h_e_smul (x : Ω) : h.e (g.val • x) = h.toGp g • h.e x := (h_equivariant g x).symm
  exact (cyclotomicChar_eq_of_equivariant ℓ h_e_smul).symm

end New.GaloisRep.PadicPlaceEmbedding

/-!
## Passage of local conditions to retracts and open embeddings

`New.GaloisRep.isFiniteTypeAt_of_retract`, `New.GaloisRep.jumpsRelAt_of_retract` and
`New.GaloisRep.polyKillsAt_of_retract` move local conditions from a Galois representation `r'` to a
representation `r` that embeds in it near the identity (for jumps, isomorphically near the
identity), possibly over another number field. They also cover isomorphic representations.
-/

section LocalTransfer

open Matrix Topology New.Period

/-- If `P' * P = 1`, then `P *ᵥ x = 0` only for `x = 0`. -/
private lemma Matrix.eq_zero_of_mulVec_eq_zero_of_mul_eq_one {R m m' : Type*} [CommRing R]
    [Fintype m] [DecidableEq m] [Fintype m'] {P : Matrix m' m R} {P' : Matrix m m' R}
    (hP : P' * P = 1) {x : m → R} (hx : P *ᵥ x = 0) : x = 0 := by
  rw [← one_mulVec x, ← hP, ← mulVec_mulVec, hx, mulVec_zero]

/-! ### Local data read through conjugation by an automorphism `c` of `Ω` -/

namespace New.GaloisRep

variable {ℓ : ℕ} [ThePrime ℓ] {E E' m m' : Type} [Fintype m] [DecidableEq m] [Fintype m']
  [DecidableEq m'] [Field E] [Algebra E Ω] [Field E'] [EmbeddedNumberField E'] {A : ClosurePlace}
  (c : Ω ≃+* Ω) {φ : Gal(Ω/E') →* Gal(Ω/E)} {r : GalRep ℓ E m}
  {r' : Gal(Ω/E') →* GL m' (PadicAlgCl ℓ)} {P : Matrix m' m (PadicAlgCl ℓ)}
  {P' : Matrix m m' (PadicAlgCl ℓ)} {S : Set Gal(Ω/E')}

/-- Let `φ : Gal(Ω/E') → Gal(Ω/E)` be conjugation by the automorphism `c` of `Ω`, that is
`φ g (c x) = c (g x)`. Then `φ g` lies in the decomposition group of `A` exactly when `g` lies in
that of `A.comap c`. -/
private lemma apply_mem_decompGroup_iff
    (hφ : ∀ (g : Gal(Ω/E')) (x : Ω), φ g (c x) = c (g x)) (g : Gal(Ω/E')) :
    φ g ∈ decompGroup Gal(Ω/E) A ↔ g ∈ decompGroup Gal(Ω/E') (A.comap c.toRingHom) := by
  -- Both are read on `c x`, `x ∈ Ω`, as `c` is onto.
  rw [mem_decompGroup_iff, mem_decompGroup_iff, c.surjective.forall]
  simp [hφ]

/-- For `φ` conjugation by `c` as in `New.GaloisRep.apply_mem_decompGroup_iff`: if `φ g` lies in
the inertia group of `A`, then `g` lies in that of `A.comap c`. -/
private lemma mem_inertiaGroup_comap_of_apply_mem_inertiaGroup
    (hφ : ∀ (g : Gal(Ω/E')) (x : Ω), φ g (c x) = c (g x)) {g : Gal(Ω/E')}
    (hg : φ g ∈ inertiaGroup Gal(Ω/E) A) : g ∈ inertiaGroup Gal(Ω/E') (A.comap c.toRingHom) := by
  obtain ⟨hg_dec, hg_small⟩ : φ g ∈ decompGroup Gal(Ω/E) A ∧
      ∀ y : Ω, A.valuation y ≤ 1 → A.valuation (φ g • y - y ^ 1) < 1 := hg
  refine ⟨(apply_mem_decompGroup_iff c hφ g).mp hg_dec, fun x hx ↦ comap_apply_lt_one_iff.mpr ?_⟩
  have h_eq : φ g • c x - c x ^ 1 = c (g • x - x ^ 1) := by simp [hφ]
  have hx_mem : c x ∈ A :=
    ValuationSubring.mem_comap.mp (((A.comap c.toRingHom).valuation_le_one_iff x).mp hx)
  change A.valuation (c (g • x - x ^ 1)) < 1
  rw [← h_eq]
  exact hg_small (c x) ((A.valuation_le_one_iff (c x)).mpr hx_mem)

/-- For `φ` conjugation by `c`, the map `g ↦ φ g` from the decomposition group of `A.comap c` in
`Gal(Ω/E')` to that of `A` in `Gal(Ω/E)`. -/
private noncomputable def decompComap (hφ : ∀ (g : Gal(Ω/E')) (x : Ω), φ g (c x) = c (g x)) :
    decompGroup Gal(Ω/E') (A.comap c.toRingHom) →* decompGroup Gal(Ω/E) A :=
  φ.restrict fun g hg ↦ (apply_mem_decompGroup_iff c hφ g).mpr hg

/-- Let `L` be a local datum at `A`, with embedding `e` and map `j` of decomposition groups, and
`φ` conjugation by `c`. Then `e ∘ c` induces `A.comap c`, with map `j ∘ decompComap c hφ` of
decomposition groups. -/
private lemma PadicPlaceEmbedding.inducesPlace_comp (L : PadicPlaceEmbedding E A ℓ)
    (hφ : ∀ (g : Gal(Ω/E')) (x : Ω), φ g (c x) = c (g x)) :
    InducesPlace E' (A.comap c.toRingHom) (L.e.comp c.toRingHom)
      (L.toGp.comp (decompComap c hφ)) := by
  -- `e ∘ c` induces `A.comap c` with some map `j'`; `j'` and `j ∘ decompComap c hφ` agree on the
  -- dense image of `e ∘ c`, so they are equal.
  obtain ⟨⟨h_comap_e, h_e_equivariant⟩, -⟩ : InducesPlace E A L.e L.toGp := L.inducesPlace
  have h_comap : (intQpBar ℓ).comap (L.e.comp c.toRingHom) = A.comap c.toRingHom := by
    rw [← ValuationSubring.comap_comap, h_comap_e]
  obtain ⟨j', hj'⟩ := exists_inducesPlace E' Gal(Ω/E') h_comap
  suffices hj'_eq : j' = L.toGp.comp (decompComap c hφ) by rwa [hj'_eq] at hj'
  obtain ⟨⟨-, hj'_equivariant⟩, -⟩ := hj'
  refine j'.ext fun g ↦ eq_of_smul_eq_smul <|
    (denseRange_emb_padicAlgCl (L.e.comp c.toRingHom)).eq fun x ↦ ?_
  calc j' g (L.e (c x)) = L.e (c (g.val • x)) := hj'_equivariant g x
    _ = L.e ((decompComap c hφ g).val • c x) := congrArg L.e (hφ g x).symm
    _ = L.toGp (decompComap c hφ g) (L.e (c x)) := (h_e_equivariant _ (c x)).symm

/-- The map `j ∘ decompComap c hφ` of decomposition groups that goes with the embedding `e ∘ c`
(`L` has embedding `e` and map `j`) is an open embedding. -/
private lemma PadicPlaceEmbedding.isOpenEmbedding_comp
    (L : PadicPlaceEmbedding E A ℓ) (hφ : ∀ (g : Gal(Ω/E')) (x : Ω), φ g (c x) = c (g x)) :
    IsOpenEmbedding (L.toGp.comp (decompComap c hφ)) := by
  obtain ⟨-, h_open, -⟩ := L.inducesPlace_comp c hφ
  exact h_open

/-- The local datum at `A.comap c` given by a local datum `L` at `A` (embedding `e`, map `j`) and
conjugation `φ` by `c`: the embedding `e ∘ c` and the map `j ∘ decompComap c hφ`. -/
private noncomputable abbrev PadicPlaceEmbedding.comap (L : PadicPlaceEmbedding E A ℓ)
    (hφ : ∀ (g : Gal(Ω/E')) (x : Ω), φ g (c x) = c (g x)) :
    PadicPlaceEmbedding E' (A.comap c.toRingHom) ℓ :=
  { toGp := L.toGp.comp (decompComap c hφ),
    isOpen_range := ⟨(L.isOpenEmbedding_comp c hφ).isOpen_range⟩,
    e := L.e.comp c,
    inducesPlace := L.inducesPlace_comp c hφ }

/-- The map `decompComap c hφ` carries the filter of elements near `1` (along `L.comap c hφ`) to
that along `L`. -/
private lemma PadicPlaceEmbedding.map_nearOne_comap (L : PadicPlaceEmbedding E A ℓ)
    (hφ : ∀ (g : Gal(Ω/E')) (x : Ω), φ g (c x) = c (g x)) :
    (nearOne (decompGroup Gal(Ω/E') (A.comap c.toRingHom)) (𝒥 := (L.comap c hφ).toOverGp)).map
        (decompComap c hφ) = nearOne (decompGroup Gal(Ω/E) A) := by
  obtain ⟨-, h_open, -⟩ := L.inducesPlace
  exact map_nearOne (decompComap c hφ) h_open.injective _

/-- Let `r' g * P = P * r (φ g)` for `g` in `S`. Then multiplication by `P` carries
`decompRep (r ∘ φ) B` to `decompRep r' B` at the elements of `S` in the decomposition group of
`B`. -/
private lemma toLin'_decompRep_comp_of_mem
    (h_comm : ∀ g ∈ S, (r' g).val * P = P * (r (φ g)).val) {B : ClosurePlace}
    (g : decompGroup Gal(Ω/E') B) (hg : (g : Gal(Ω/E')) ∈ S) (x : m → PadicAlgCl ℓ) :
    P.toLin'.restrictScalars ℤ_[ℓ] (decompRep (r.comp φ) B g x) =
      decompRep r' B g (P.toLin'.restrictScalars ℤ_[ℓ] x) := by
  simp [mulVec_mulVec, h_comm g hg]

/-- With `P` and `S` as in `New.GaloisRep.toLin'_decompRep_comp_of_mem` and `S` a neighbourhood of
`1`: the same holds at the elements near `1` along the local datum `L.comap c hφ`. -/
private lemma PadicPlaceEmbedding.eventually_toLin'_decompRep
    (L : PadicPlaceEmbedding E A ℓ) (hφ : ∀ (g : Gal(Ω/E')) (x : Ω), φ g (c x) = c (g x))
    (hS : S ∈ 𝓝 1) (h_comm : ∀ g ∈ S, (r' g).val * P = P * (r (φ g)).val) :
    ∀ᶠ g in nearOne (decompGroup Gal(Ω/E') (A.comap c.toRingHom)) (𝒥 := (L.comap c hφ).toOverGp),
      ∀ x : m → PadicAlgCl ℓ,
        P.toLin'.restrictScalars ℤ_[ℓ] (decompRep (r.comp φ) (A.comap c.toRingHom) g x) =
          decompRep r' (A.comap c.toRingHom) g (P.toLin'.restrictScalars ℤ_[ℓ] x) := by
  rw [nearOne_eq_nhds_one (𝒥 := (L.comap c hφ).toOverGp) (L.isOpenEmbedding_comp c hφ)]
  exact (continuousAt_subtype_val.eventually_mem hS).mono (toLin'_decompRep_comp_of_mem h_comm)

/-- Let `P' * P = 1` and `r' g * P = P * r (φ g)` on a neighbourhood `S` of `1`. If `r'` is
potentially crystalline on the decomposition group of `A.comap c` along `L.comap c hφ`, then `r`
is potentially crystalline on that of `A` along `L`. -/
private lemma PadicPlaceEmbedding.isPotentiallyCrystalline_decompRep_of_comap
    (L : PadicPlaceEmbedding E A ℓ) (hφ : ∀ (g : Gal(Ω/E')) (x : Ω), φ g (c x) = c (g x))
    (hS : S ∈ 𝓝 1) (h_comm : ∀ g ∈ S, (r' g).val * P = P * (r (φ g)).val) (hP : P' * P = 1)
    (h_r' : IsPotentiallyCrystalline (𝒥 := (L.comap c hφ).toOverGp)
      (decompRep r' (A.comap c.toRingHom))) :
    IsPotentiallyCrystalline (𝒥 := L.toOverGp) (decompRep r A) := by
  -- `P` embeds `decompRep (r ∘ φ)` in `decompRep r'` near `1`; then read back along
  -- `decompComap c hφ`.
  let _ : PadicPlaceEmbedding E' (A.comap c.toRingHom) ℓ := L.comap c hφ
  rw [IsPotentiallyCrystalline, ← L.map_nearOne_comap c hφ,
    ← isAdmissible_comp_iff (decompComap c hφ) (L.comap c hφ).isOpen_range]
  exact .of_jointly_injective le_rfl (fun _ ↦ h_r') (fun _ ↦ P.toLin'.restrictScalars ℤ_[ℓ])
    (fun _ ↦ L.eventually_toLin'_decompRep c hφ hS h_comm)
    (fun x hx ↦ eq_zero_of_mulVec_eq_zero_of_mul_eq_one hP (hx ()))

/-- With `P`, `P'` and `S` as in `isPotentiallyCrystalline_decompRep_of_comap`, let `s ∈ S` lie in
the decomposition group of `A.comap c`. If `Q` kills the Weil pair `(j' s, k)` on `r'` along
`L.comap c hφ` (map `j'`), then `Q` kills the Weil pair `(j (φ s), k)` on `r` along `L`
(map `j`). -/
private lemma PadicPlaceEmbedding.isKilledBy_decompRep_of_comap
    (L : PadicPlaceEmbedding E A ℓ) (hφ : ∀ (g : Gal(Ω/E')) (x : Ω), φ g (c x) = c (g x))
    (hS : S ∈ 𝓝 1) (h_comm : ∀ g ∈ S, (r' g).val * P = P * (r (φ g)).val) (hP : P' * P = 1)
    {s : decompGroup Gal(Ω/E') (A.comap c.toRingHom)} (hs : (s : Gal(Ω/E')) ∈ S) {k : ℕ}
    (hk : IsWeilPair ((L.comap c hφ).toGp s) k) {Q : Polynomial (PadicAlgCl ℓ)}
    (h_r' : IsKilledBy (𝒥 := (L.comap c hφ).toOverGp) (decompRep r' (A.comap c.toRingHom)) s k Q) :
    IsKilledBy (𝒥 := L.toOverGp) (decompRep r A) (decompComap c hφ s) k Q := by
  let _ : PadicPlaceEmbedding E' (A.comap c.toRingHom) ℓ := L.comap c hφ
  let f : (m → PadicAlgCl ℓ) →ₗ[ℤ_[ℓ]] (m' → PadicAlgCl ℓ) := P.toLin'.restrictScalars ℤ_[ℓ]
  -- `f` is equivariant near `1` and at `s`, and commutes with scalars.
  have h_f_near : ∀ᶠ g in nearOne (decompGroup Gal(Ω/E') (A.comap c.toRingHom))
      (𝒥 := (L.comap c hφ).toOverGp) ⊔ pure s, ∀ x : m → PadicAlgCl ℓ,
        f (decompRep (r.comp φ) (A.comap c.toRingHom) g x) =
          decompRep r' (A.comap c.toRingHom) g (f x) :=
    Filter.eventually_sup.mpr ⟨L.eventually_toLin'_decompRep c hφ hS h_comm,
      Filter.eventually_pure.mpr (toLin'_decompRep_comp_of_mem h_comm s hs)⟩
  -- `f` is injective, as `P` has the left inverse `P'`.
  have h_f_inj (x : m → PadicAlgCl ℓ) (hx : ∀ _ : Unit, f x = 0) : x = 0 :=
    eq_zero_of_mulVec_eq_zero_of_mul_eq_one hP (hx ())
  -- Apply `IsKilledBy.of_jointly_injective` to the family `f` with one member.
  have h_killed : IsKilledBy (decompRep (r.comp φ) (A.comap c.toRingHom)) s k Q :=
    .of_jointly_injective hk (fun _ ↦ f) (fun _ ↦ h_f_near) h_f_inj le_rfl (fun _ ↦ h_r')
      Q.map_id (fun _ a x ↦ by simp [f])
  -- `decompRep (r ∘ φ)` is `decompRep r` read along `decompComap c hφ`.
  simp only [IsPotentiallyCrystalline, IsKilledBy, linearFrob, Dpcris, ← L.map_nearOne_comap c hφ]
  exact h_killed

/-- With `P`, `P'` and `S` as in `isPotentiallyCrystalline_decompRep_of_comap`, and also
`P * P' = 1`: the multiplicity of the Hodge–Tate jump `u` at `γ` is the same for `r'` along
`L.comap c hφ` and for `r` along `L`. -/
private lemma PadicPlaceEmbedding.jump_decompRep_comap
    (L : PadicPlaceEmbedding E A ℓ) (hφ : ∀ (g : Gal(Ω/E')) (x : Ω), φ g (c x) = c (g x))
    (hS : S ∈ 𝓝 1) (h_comm : ∀ g ∈ S, (r' g).val * P = P * (r (φ g)).val) (hP : P' * P = 1)
    (hP' : P * P' = 1) (γ : PadicAlgCl ℓ →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) (u : ℤ) :
    jump (𝒥 := (L.comap c hφ).toOverGp) (decompRep r' (A.comap c.toRingHom)) γ u =
      jump (𝒥 := L.toOverGp) (decompRep r A) γ u := by
  -- `P` is an isomorphism from `decompRep (r ∘ φ)` to `decompRep r'` near `1`.
  let _ : PadicPlaceEmbedding E' (A.comap c.toRingHom) ℓ := L.comap c hφ
  let b := Pi.basisFun (PadicAlgCl ℓ) m
  have h_jump_r' : jump (decompRep r' (A.comap c.toRingHom)) γ u =
      jump (decompRep (r.comp φ) (A.comap c.toRingHom)) γ u :=
    jump_baseChange (φ := 1) _ b (b.map (toLin'OfInv hP hP'))
      (fun a ↦ (b.map_apply (toLin'OfInv hP hP') a).symm)
      (L.eventually_toLin'_decompRep c hφ hS h_comm)
  -- Jumps are defined near `1`, and `decompComap c hφ` carries the elements near `1` to those
  -- near `1`.
  have h_maps : hodgeTateMaps (𝒥 := (L.comap c hφ).toOverGp)
      (decompRep (r.comp φ) (A.comap c.toRingHom)) γ u = hodgeTateMaps (decompRep r A) γ u := by
    simp [hodgeTateMaps, ← L.map_nearOne_comap c hφ]
    -- the two sides agree once `decompComap c hφ` is unfolded
    rfl
  exact h_jump_r'.trans (LinearEquiv.finrank_eq (.ofEq _ _ h_maps))

omit [ThePrime ℓ] in
/-- If `ℓ` is a unit at `A`, it is a unit at `A.comap c`, for an automorphism `c` of `Ω`. -/
private lemma valuation_comap_eq_one (hℓ : A.valuation ℓ = 1) :
    (A.comap (c : Ω →+* Ω)).valuation ℓ = 1 := by
  simpa [isEquiv_comap.eq_one_iff_eq_one] using hℓ

/-- Let `φ : Gal(Ω/E') → Gal(Ω/E)` be conjugation by the automorphism `c` of `Ω`
(`φ g (c x) = c (g x)`), an open embedding. Let `P` have the left inverse `P'`, and let
`r' g * P = P * r (φ g)` for `g` in a neighbourhood `S` of `1`. If `r'` is of finite type at
`A.comap c`, then `r` is of finite type at `A`. -/
lemma isFiniteTypeAt_of_retract (hφ : ∀ (g : Gal(Ω/E')) (x : Ω), φ g (c x) = c (g x))
    (hφ_open : IsOpenEmbedding φ) (hS : S ∈ 𝓝 1)
    (h_comm : ∀ g ∈ S, (r' g).val * P = P * (r (φ g)).val) (hP : P' * P = 1)
    (h_finite : IsFiniteTypeAt r' (A.comap ↑c)) : IsFiniteTypeAt r A := by
  obtain ⟨h_inertia_r', h_potCrys_r'⟩ := h_finite
  refine ⟨fun hℓ ↦ ?_, ?_⟩
  · -- Away from `ℓ`: `r (φ g) = P' r'(g) P = 1` for `g` in `S` and in inertia near `1`.
    rw [← map_one φ, ← hφ_open.map_nhds_eq]
    refine (h_inertia_r' (valuation_comap_eq_one c hℓ)).mp (.mono hS fun g hg h_triv hI ↦ ?_)
    have h_r'_one : r' g = 1 := h_triv (mem_inertiaGroup_comap_of_apply_mem_inertiaGroup c hφ hI)
    refine Units.ext ?_
    calc (r (φ g)).val = P' * P * (r (φ g)).val := by rw [hP, Matrix.one_mul]
      _ = P' * ((r' g).val * P) := by rw [Matrix.mul_assoc, h_comm g hg]
      _ = 1 := by rw [h_r'_one, Units.val_one, Matrix.one_mul, hP]
  · -- Above `ℓ`: read `r'` along the local datum `L.comap c hφ` at `A.comap c`.
    intro L
    let _ : PadicPlaceEmbedding E' (A.comap ↑c) ℓ := L.comap c hφ
    exact L.isPotentiallyCrystalline_decompRep_of_comap c hφ hS h_comm hP h_potCrys_r'

/-- Let `φ`, `P`, `P'` and `S` be as in `New.GaloisRep.isFiniteTypeAt_of_retract`, without asking
`φ` to be open, let also `P * P' = 1`, and let `i : E → E'` satisfy `c (i x) = x` on `E`. If the
jumps of `r'` at `A.comap c` are related by `R` to `J` read on the restrictions `σ ∘ i`, then
the jumps of `r` at `A` are related by `R` to `J`. -/
lemma jumpsRelAt_of_retract [PadicIso ℓ] (i : E →+* E')
    (hi : ∀ x : E, c (algebraMap E' Ω (i x)) = algebraMap E Ω x)
    (hφ : ∀ (g : Gal(Ω/E')) (x : Ω), φ g (c x) = c (g x)) (hS : S ∈ 𝓝 1)
    (h_comm : ∀ g ∈ S, (r' g).val * P = P * (r (φ g)).val) (hP : P' * P = 1)
    (hP_right : P * P' = 1) {R : ℕ → ℕ → Prop} {J : (E →+* ℂ) → Multiset ℤ}
    (h_jumps : JumpsRelAt r' (A.comap ↑c) R (fun σ : E' →+* ℂ ↦ J (σ.comp i))) :
    JumpsRelAt r A R J := by
  -- Read the hypothesis along `L.comap c hφ`, whose embedding `e ∘ c` restricts along `i` to `e`.
  intro L γ g hg u
  let L' : PadicPlaceEmbedding E' (A.comap ↑c) ℓ := L.comap c hφ
  let ιg : PadicAlgCl ℓ →+* ℂ := RingHom.comp ιℓ.symm ((g⁻¹ : Gp ℓ) : PadicAlgCl ℓ →+* PadicAlgCl ℓ)
  have h_emb : ((L.e.comp ↑c).comp (algebraMap E' Ω)).comp i = L.e.comp (algebraMap E Ω) :=
    RingHom.ext fun x ↦ by simp [hi x]
  have h_r' : R ((J ((ιg.comp ((L.e.comp ↑c).comp (algebraMap E' Ω))).comp i)).count u)
      (jump (decompRep r' (A.comap ↑c)) γ u) := h_jumps (L := L') hg u
  have h_jump : jump (decompRep r' (A.comap ↑c)) γ u = jump (decompRep r A) γ u :=
    L.jump_decompRep_comap c hφ hS h_comm hP hP_right γ u
  rwa [RingHom.comp_assoc, h_emb, h_jump] at h_r'

/-- Let `φ`, `P`, `P'` and `S` be as in `New.GaloisRep.isFiniteTypeAt_of_retract`, without asking
`φ` to be open, and let `s ∈ S`. A polynomial `Q` that kills `s` for `r'` at `A.comap c` kills
`φ s` for `r` at `A`. -/
lemma polyKillsAt_of_retract (hφ : ∀ (g : Gal(Ω/E')) (x : Ω), φ g (c x) = c (g x))
    (hS : S ∈ 𝓝 1) (h_comm : ∀ g ∈ S, (r' g).val * P = P * (r (φ g)).val) (hP : P' * P = 1)
    {s : Gal(Ω/E')} (hs : s ∈ S) {Q : Polynomial (PadicAlgCl ℓ)}
    (h_kills : PolyKillsAt r' (A.comap ↑c) s Q) : PolyKillsAt r A (φ s) Q := by
  obtain ⟨h_kills_away, h_kills_above⟩ := h_kills
  refine ⟨fun hℓ ↦ ?_, ?_⟩
  · -- Away from `ℓ`: `Q (r (φ s)) = P' Q (r' s) P = 0`.
    have h_semiconj : P * Polynomial.aeval (r (φ s)).val Q = Polynomial.aeval (r' s).val Q * P :=
      aeval_semiconj (h_comm s hs).symm Q
    calc Polynomial.aeval (r (φ s)).val Q = P' * (P * Polynomial.aeval (r (φ s)).val Q) := by
          rw [← Matrix.mul_assoc, hP, Matrix.one_mul]
      _ = 0 := by rw [h_semiconj, h_kills_away (valuation_comap_eq_one c hℓ), Matrix.zero_mul,
            Matrix.mul_zero]
  · -- Above `ℓ`: `Q` kills `s` on `r'` along `L.comap c hφ`, hence `φ s` on `r` along `L`.
    intro L hφs k hk
    let L' : PadicPlaceEmbedding E' (A.comap ↑c) ℓ := L.comap c hφ
    have hk' : IsWeilPair (L'.toGp ⟨s, (apply_mem_decompGroup_iff c hφ s).mp hφs⟩) k := hk
    exact L.isKilledBy_decompRep_of_comap c hφ hS h_comm hP hs hk' (h_kills_above hk')

end New.GaloisRep

/-- Let `c` be an automorphism of `Ω` that carries `i : E → E'` to the inclusion of `E`, and let
`φ : Gal(Ω/E') → Gal(Ω/E)` be conjugation by `c`, an open embedding. Let `P` have a left inverse
`P'` and intertwine `r ∘ φ` with `r'` on a neighbourhood `S` of `1`. Put `A' = c⁻¹ A`. Then: (a) if
`r'` is of finite type at `A'` (trivial on inertia near `1` if ℓ is a unit there, potentially
crystalline otherwise), so is `r` at `A`; (b) if also `P * P' = 1`, a relation `R` between the
multiplicities in `J` and those of the Hodge–Tate jumps passes from `r'` (with `J` read on the
restrictions `σ ∘ i` of the embeddings `σ` of `E'` in `ℂ`) to `r`; (c) a polynomial that kills
`s ∈ S` for `r'` at `A'` (`PolyKillsAt`) kills `φ s` for `r` at `A`.

This is the form in which the compatibility of Weil–Deligne representations and Hodge–Tate weights
with subrepresentations, restriction and conjugation is used; it goes from `r'` to `r` only. -/
lemma New.GaloisRep.local_clauses_of_retract {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {E E' m m' : Type}
    [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] {P : Matrix m' m (PadicAlgCl ℓ)}
    {P' : Matrix m m' (PadicAlgCl ℓ)} [Field E] [Algebra E Ω] [Field E'] [EmbeddedNumberField E']
    {r : GalRep ℓ E m} {r' : Gal(Ω/E') →* GL m' (PadicAlgCl ℓ)} {A : ClosurePlace} (c : Ω ≃+* Ω)
    (i : E →+* E') (hi : ∀ x : E, c (algebraMap E' Ω (i x)) = algebraMap E Ω x)
    {φ : Gal(Ω/E') →* Gal(Ω/E)} (hφ : ∀ (g : Gal(Ω/E')) (x : Ω), φ g (c x) = c (g x))
    (hφ_open : IsOpenEmbedding φ) {S : Set Gal(Ω/E')} (hS : S ∈ 𝓝 1)
    (h_comm : ∀ g ∈ S, (r' g).val * P = P * (r (φ g)).val) (hP : P' * P = 1) :
    -- (a)
    (IsFiniteTypeAt r' (A.comap ↑c) → IsFiniteTypeAt r A) ∧
    -- (b)
    (P * P' = 1 →
     ∀ {R : ℕ → ℕ → Prop} {J : (E →+* ℂ) → Multiset ℤ},
       JumpsRelAt r' (A.comap ↑c) R (fun σ : E' →+* ℂ ↦ J (σ.comp i)) →
       JumpsRelAt r A R J) ∧
    -- (c)
    ∀ s ∈ S, ∀ {Q : Polynomial (PadicAlgCl ℓ)},
      PolyKillsAt r' (A.comap ↑c) s Q → PolyKillsAt r A (φ s) Q :=
  ⟨isFiniteTypeAt_of_retract c hφ hφ_open hS h_comm hP,
    fun hP_right _ _ h_jumps ↦ jumpsRelAt_of_retract c i hi hφ hS h_comm hP hP_right h_jumps,
    fun _ hs _ h_kills ↦ polyKillsAt_of_retract c hφ hS h_comm hP hs h_kills⟩

end LocalTransfer
