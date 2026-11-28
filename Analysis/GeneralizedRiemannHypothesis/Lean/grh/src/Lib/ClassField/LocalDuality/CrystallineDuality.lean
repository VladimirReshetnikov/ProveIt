import Lib.GaloisRep.Main.Defs
import Lib.PadicComparison.Descent.TestCategory
import Lib.PadicHodge.BlochKato
import Lib.PadicHodge.Crystalline.Regularity

/-!
# Classes of Galois lattices, pairings and local duality for crystalline cocycles

The file studies classes of Galois lattices given by admissibility, allowed Hodge–Tate jumps and
polynomials that kill inertia. It shows how a class changes under twisted duals, tensor products and
jointly injective maps. It also defines pairings `Y × L → ℤ/p^m(1)` and the extensions of `O` by
`(Y ⊗ L)^∨(1)` that they give. At `ℓ`, it proves local duality statements for potentially
crystalline lattices: a perfect `ℤ_[ℓ]`-pairing of a lattice with its dual, the sizes of the
crystalline cocycles modulo `ℓ ^ m` and a divisibility of indices. Here Z_f denotes the crystalline
cocycles `New.Period.crysCocycles`.

## Main definitions and results

* `New.Lift.InClass`: the class of lattices given by admissibility, allowed jumps and polynomials
  that kill inertia.
* `New.Lift.Pairing`: an `O(1)`-valued form on `Y ⊗ L` whose coboundary is `p ^ m` times a
  crystalline cocycle.
* `New.Lift.cupOrthogonal`: the functions `Γ → L` whose cup products with crystalline cocycles of
  the lattices of a class are coboundaries.
* `New.Lift.dualDefect`: the length of the crystalline cocycles of `L` modulo those in
  `New.Lift.cupOrthogonal`.
* `New.Period.IsPotentiallyCrystalline.index_mul_index_dual`: the sizes of Z_f(L) and Z_f(L') modulo
  `ℓ ^ m`.
* `New.Period.IsPotentiallyCrystalline.relIndex_dvd_of_orthogonal`: a divisibility of indices from
  local Tate duality, which bounds the cocycles of `L / ℓ ^ m` orthogonal to a subgroup of Z_f(L').

Notions from other files, for a representation `ρ` of `Γ` on an `O`-module `T`:
* `New.Period.IsAdmissible ρ F`: the elements of `Bmax ⊗ T` fixed by `F`-almost all `g` span
  `Bmax ⊗ T` over `Bmax`; `New.Period.nearOne Γ` is the pull-back to `Γ` of the neighbourhoods of
  `1` in `G_p`.
* `New.Period.IsPotentiallyCrystalline ρ`: `ρ` is admissible along `New.Period.nearOne Γ`.
* `New.Period.IsKilledBy ρ s m Q`: `ρ` is potentially crystalline and `Q` evaluated at the linear
  Frobenius `New.Period.linearFrob ρ s m` is zero.
* `New.Period.IsWeilPair s 0`: `s` lies in the inertia group of `G_p`.
* `New.Period.jump ρ γ u`: the multiplicity of the Hodge–Tate jump `u : ℤ` of `ρ` at the
  `ℤ_[p]`-algebra map `γ : O → ℂ_[p]`. It is the dimension over Q̄_p (zero if infinite) of the space
  of `γ`-semilinear maps f : T → ℂ_p with f(gx) = χ(g)^(−u)·g f(x) for g near 1.
* `New.Period.HasJumps ρ γ J`: for every integer `u`, the multiplicity `jump ρ γ u` equals the
  number of times `u` occurs in the multiset `J`.

## Relation to the literature

Known result: Local Tate duality in degree 1 as an upper bound for orthogonal cocycle groups. Only
an inequality is proved. The bound is proved by Kummer theory and dévissage when `Γ` acts by
elements of `ℓ`-power order. For a general finite module `M`,
`New.DiscreteModule.local_duality_card_dvd` gives only a divisibility, by descent from an open
subgroup `U` of index prime to `#M`. It takes as a hypothesis a largest orthogonal pair of cocycle
groups over `U`, and this file supplies that pair for the reductions of crystalline cocycles
(`h_orth`, `h_max` in `card_pairingAnnihilator_mul_card_dvd`). Perfectness of the duality and the
Euler characteristic formula are outside the scope of this file, and no result in it uses them.
Source: J.-P. Serre, Galois Cohomology (1997), II §5.2 Thm 2 and §5.7; J. S. Milne, Arithmetic
Duality Theorems (2nd ed. 2006), I 2.3, 2.8.

See also `Lib.PadicHodge.Crystalline.Regularity` and `Lib.PadicHodge.ArtinSchreierSequence`.
-/

noncomputable section

/-!
## Classes of Galois lattices under duals and tensor products; pairings

The group `Γ` acts on periods through the map `toGp : Γ → G_p` given by `[OverGp Γ p]`. The results
on twisted duals, tensor products and jointly injective maps assume that `O` is a domain, finite
over `ℤ_[p]`.
-/

namespace New.Lift

section

variable {p : ℕ} [ThePrime p] (O Γ : Type) [CommRing O] [Algebra ℤ_[p] O] [Group Γ]

/-- A finite free O-module, with compatible Z_p-module structure, together with an O-linear
representation of the group Γ on it. -/
structure GalLattice where
  /-- The underlying module `Λ`. -/
  (Carrier : Type)
  /-- `Λ` is an abelian group. -/
  [addCommGroup : AddCommGroup Carrier]
  /-- `Λ` is an `O`-module. -/
  [moduleO : Module O Carrier]
  /-- `Λ` is a `ℤ_p`-module. -/
  [moduleZp : Module ℤ_[p] Carrier]
  /-- The two module structures are compatible. -/
  [isScalarTower : IsScalarTower ℤ_[p] O Carrier]
  /-- `Λ` is free over `O`. -/
  [free : Module.Free O Carrier]
  /-- `Λ` is finitely generated over `O`. -/
  [module_finite : Module.Finite O Carrier]
  /-- The `O`-linear action of `Γ` on `Λ`. -/
  ρ : Representation O Γ Carrier

open Module Submodule Period GalLattice TensorProduct Polynomial AdjoinRoot IsWeilPair

attribute [instance] GalLattice.addCommGroup moduleO moduleZp GalLattice.isScalarTower free
  module_finite

/-- A lattice is read as its underlying type. -/
instance : CoeSort (GalLattice O Γ) Type := ⟨Carrier⟩

variable {O Γ} [OverGp Γ p]
  (F : Filter Γ) (K : Γ → O[X] → Prop) (U : (O →ₐ[ℤ_[p]] ℂ_[p]) → Finset ℤ) (Y L : GalLattice O Γ)

/-- The twisted dual L^∨(1) = Hom_O(L, O(1)) of a lattice L, with Γ acting on O(1) through the
cyclotomic character. -/
abbrev GalLattice.tateDual : GalLattice O Γ := mk (L.Carrier →ₗ[O] O) (L.ρ.linHom (actionRep O O χ))

/-- The lattice `Y` lies in the class given by a filter `F` on `Γ`, a relation `K`, and finite sets
`U g` of integers for the `ℤ_[p]`-algebra maps `g : O → ℂ_[p]`. The periods of `Y` fixed by almost
all elements of `Γ` for the supremum of `F` and the filter 'near 1' span
(`New.Period.IsAdmissible`); every Hodge–Tate jump of `Y` at `g` lies in `U g`; and if `K s Q` holds
and `toGp s` is in inertia, the polynomial `Q` over `O` kills `s` on the periods of `Y`
(`New.Period.IsKilledBy`). For `K = ⊥` the last condition is empty. -/
def InClass : Prop :=
  IsAdmissible Y.ρ (nearOne Γ ⊔ F) ∧
  (∀ (g : O →ₐ[ℤ_[p]] ℂ_[p]) (u : ℤ), jump Y.ρ g u ≠ 0 → u ∈ U g) ∧
  ∀ (s : Γ) (Q : O[X]), K s Q → IsWeilPair (toGp s) 0 → IsKilledBy Y.ρ s 0 Q

section Projections

variable {F K U Y}

lemma InClass.isAdmissible (h : InClass F K U Y) : IsAdmissible Y.ρ (nearOne Γ ⊔ F) := h.left

/-- The jumps of a lattice in the class at the embedding `g` lie in `U g`. -/
lemma InClass.mem_of_jump_ne_zero (h : InClass F K U Y) ⦃g : O →ₐ[ℤ_[p]] ℂ_[p]⦄ ⦃u : ℤ⦄
    (hu : jump Y.ρ g u ≠ 0) : u ∈ U g := h.right.left g u hu

/-- If `K s Q` holds and `toGp s` is in inertia, then `Q` kills `s` on a lattice in the class. -/
lemma InClass.isKilledBy_of_isWeilPair (h : InClass F K U Y) ⦃s : Γ⦄ ⦃Q : O[X]⦄ (hK : K s Q)
    (hs : IsWeilPair (toGp s) 0) : IsKilledBy Y.ρ s 0 Q := h.right.right s Q hK hs

end Projections

/-- If the lattice `Y` lies in the class `InClass F K U`, then its representation `Y.ρ` is
potentially crystalline. Lying in the class means its periods are admissible, its Hodge–Tate jumps
lie in `U`, and it satisfies the killing condition `K`. -/
lemma InClass.isPotentiallyCrystalline (h : InClass F K U Y) : IsPotentiallyCrystalline Y.ρ :=
  h.isAdmissible.mono le_sup_left

/-- The tensor product Y ⊗_O L of two lattices, with the diagonal action of Γ. -/
abbrev GalLattice.tensor : GalLattice O Γ := mk (Y.Carrier ⊗[O] L.Carrier) (Y.ρ.tprod L.ρ)

/-- A pairing of Y and L modulo p^m, with m = `exponent`: an O-linear ψ = `integralForm` :
Y ⊗ L → O(1) with gψ − ψ = p^m c(g) for a crystalline cocycle c = `cocycle`, and a Z_p-linear
f = `toZp` : O → Z_p. -/
structure Pairing where
  /-- The exponent `m` of the modulus `p ^ m`. -/
  (exponent : ℕ)
  /-- An `O`-linear form `ψ : Y ⊗ L → O(1)`, an element of `Z = (Y.tensor L).tateDual`. -/
  integralForm : (Y.tensor L).tateDual.Carrier
  /-- A `ℤ_p`-linear map `f : O → ℤ_p`; the pairing is its composite with `ψ`, modulo `p ^ m`. -/
  (toZp : Dual ℤ_[p] O)
  /-- A crystalline cocycle `c` of `Z`; it defines an extension `Z ⊕ O` of `O` by `Z`. -/
  (cocycle : crysCocycles (tateDual (Y.tensor L)).ρ)
  /-- The coboundary of `ψ` is `p ^ m` times the cocycle. -/
  pow_smul_cocycle (g : Γ) :
    p ^ exponent • cocycle.val g = ρ (Y.tensor L).tateDual g integralForm - integralForm

variable {Y L} (P : Pairing Y L)

/-- The Z_p-bilinear pairing Y × L → Z_p/p^m sending (y, l) to f(ψ(y ⊗ l)) modulo p^m, for the
form ψ and the functional f: O → Z_p of P. -/
def Pairing.modPairing : Y.Carrier →ₗ[ℤ_[p]] L.Carrier →ₗ[ℤ_[p]] QuotSpan
  ((p : ℤ_[p]) ^ P.exponent) :=
  ((curry P.integralForm).restrictScalars₁₂ ℤ_[p] ℤ_[p]).compr₂
    (Qₗ := QuotSpan (p ^ P.exponent : ℤ_[p]))
      (mkQ (Ideal.span {(p : ℤ_[p]) ^ P.exponent}) ∘ₗ P.toZp)

/-- The cup product (g, h) ↦ b(a(g), g·c(h)) for b = `P.modPairing`, with Z/p^m(1) embedded in
Q̄_p^×, is the coboundary of a continuous cochain Γ → Q̄_p^×. -/
def Pairing.IsCupCoboundary [TopologicalSpace Γ] (a : Γ → Y.Carrier) (c : Γ → L.Carrier) : Prop :=
  (fun q : Γ × Γ ↦ zmodPowToUnits P.exponent (P.modPairing (a q.fst) (L.ρ q.fst (c q.snd)))) ∈
    B2 (unitsRep.comp toGp)

/-- The annihilator `L^{⊥𝒬}` of a class `𝒬` of lattices: the `O`-module of functions `c : Γ → L`
(not assumed to be cocycles) such that for every lattice `Y` in `𝒬`, every `m`, every pairing
`P : Y × L → ℤ/p^m(1)` (`New.Lift.Pairing`) and every crystalline cocycle `a` of `Y`
(`New.Period.crysCocycles`), the cup product of `a` and `c` under `P` is a coboundary
(`New.Lift.Pairing.IsCupCoboundary`). -/
def cupOrthogonal [TopologicalSpace Γ] (𝒬 : GalLattice O Γ → Prop) (L : GalLattice O Γ) :
    Submodule O (Γ → L.Carrier) where
  carrier := {c : Γ → L | ∀ (Y : GalLattice O Γ) (P : Pairing Y L), 𝒬 Y →
    ∀ a ∈ crysCocycles Y.ρ, P.IsCupCoboundary a c}
  add_mem' := by simp_all [← Pi.add_def, add_mem, Pairing.IsCupCoboundary]
  zero_mem' := by simp [← Pi.zero_def, Pairing.IsCupCoboundary]
  smul_mem' (o : O) c hc Y P hY a ha := by
    -- `integralForm` is a form on the tensor product over `O`, so the scalar moves from `c` to `a`
    simpa [Pairing.modPairing, Pairing.IsCupCoboundary] using hc Y P hY (o • a) (smul_mem _ o ha)

/-- The defect on the dual side: the length over `O`, not normalised, of the crystalline cocycles of
`L` modulo those in the annihilator `cupOrthogonal 𝒬 L` of the class `𝒬` under cup products. -/
def dualDefect [TopologicalSpace Γ] (𝒬 : GalLattice O Γ → Prop) (L : GalLattice O Γ) : ℕ∞ :=
  relLength (crysCocycles L.ρ) (cupOrthogonal 𝒬 L)

/-- The defect vanishes exactly when all crystalline cocycles of `L` are orthogonal to `𝒬`. -/
lemma dualDefect_eq_zero_iff [TopologicalSpace Γ] {𝒬 : GalLattice O Γ → Prop}
    {L : GalLattice O Γ} : dualDefect 𝒬 L = 0 ↔ crysCocycles L.ρ ≤ cupOrthogonal 𝒬 L :=
  relLength_eq_zero

/-- The power `p ^ e` carries every crystalline cocycle of `L` into the annihilator
`cupOrthogonal 𝒬 L` of the class `𝒬` under cup products. -/
def HasCupExponent [TopologicalSpace Γ] (𝒬 : GalLattice O Γ → Prop) (L : GalLattice O Γ) (e : ℕ) :
    Prop := ∀ x : Γ → L, x ∈ crysCocycles L.ρ → (p : O) ^ e • x ∈ cupOrthogonal 𝒬 L

/-- A larger power of `p` also carries the crystalline cocycles into `cupOrthogonal 𝒬 L`. -/
lemma HasCupExponent.mono [TopologicalSpace Γ] {𝒬 : GalLattice O Γ → Prop} {L : GalLattice O Γ}
    {e e' : ℕ} (h : HasCupExponent 𝒬 L e) (h_le : e ≤ e') : HasCupExponent 𝒬 L e' := by
  intro x hx
  rw [← Nat.sub_add_cancel h_le, pow_add, mul_smul]
  exact smul_mem _ _ (h x hx)

variable [Free ℤ_[p] O]

instance : Free ℤ_[p] L := .trans (S := O)

/-- The O-valued pairing ((λ, o), t) ↦ (p^m λ + oψ)(t) of the extension of O by (Y ⊗ L)^∨(1)
along the cocycle c of P with Y ⊗ L. -/
def Pairing.extensionForm : (Y.tensor L).tateDual.Carrier × O →ₗ[O] (Y.tensor L).tateDual.Carrier :=
  (p ^ P.exponent • LinearMap.id).coprod (.toSpanSingleton O (Y.tensor L).tateDual P.integralForm)

/-- The pairing β = `P.extensionForm` of the extension of O by (Y ⊗ L)^∨(1) with Y ⊗ L is
equivariant into the Tate twist: β(gx, gt) = χ(g)·β(x, t) for g in Γ, where `g` acts on the
extension (`extensionRep`) by (λ, o) ↦ (gλ + o·c(g), o), with χ the cyclotomic character. -/
lemma Pairing.extensionForm_equivariant (g : Γ) (x : (Y.tensor L).tateDual × O) (t : Y.tensor L) :
    P.extensionForm (extensionRep
        (LinearMap.toSpanSingleton O (crysCocycles (Y.tensor L).tateDual.ρ) P.cocycle) g x)
        (ρ (Y.tensor L) g t) = χ g • P.extensionForm x t := by
  -- `extensionForm x` is the form `p ^ m • x.1 + x.2 • integralForm`. By `P.pow_smul_cocycle`,
  -- `p ^ m • cocycle g = g integralForm - integralForm`, so `extensionForm` of the action on the
  -- extension is `g` applied to this form, and the dual action twists by `χ g`.
  simp [extensionForm, smul_comm (p ^ _), P.pow_smul_cocycle, -Representation.tprod_apply,
    smul_sub, -nsmul_eq_mul, extensionRep, Units.smul_def, add_assoc]

/-- Let `Y`, `L` be lattices over the `ℤ_[p]`-algebra `O` with an action of the group `Γ`. The
pairing `Y × L → ℤ_p / p ^ m` of `P` is equivariant into the Tate twist: `⟨g y, g l⟩ = χ(g) ⟨y, l⟩`,
with `χ` the cyclotomic character. -/
lemma Pairing.modPairing_rho (g : Γ) (y : Y) (l : L) :
    P.modPairing (Y.ρ g y) (L.ρ g l) = χ g • P.modPairing y l := by
  -- `extensionForm (0, 1) = ψ` and `extensionForm (g (0, 1)) = p ^ m • cocycle g + ψ` for
  -- `ψ = integralForm`. Apply `toZp` to the equivariance of `extensionForm` and reduce modulo
  -- `p ^ m`, which kills the term in `cocycle g`.
  have h_toZp : (P.toZp (P.integralForm (Y.ρ g y ⊗ₜ L.ρ g l)) : QuotSpan (p ^ P.exponent : ℤ_[p])) =
      (χ g • P.toZp (P.integralForm (y ⊗ₜ l)) : ℤ_[p]) := by
    simpa [extensionForm, Selmer.nsmul_quot_eq_zero, -nsmul_eq_mul, extensionRep] using
      congrArg (fun z ↦ (P.toZp z : QuotSpan (p ^ P.exponent : ℤ_[p])))
        (P.extensionForm_equivariant g (0, 1) (y ⊗ₜ l))
  simpa [Pairing.modPairing, Units.smul_def, Algebra.smul_def] using h_toZp

end

open Module Submodule Period GalLattice TensorProduct Polynomial AdjoinRoot IsWeilPair

variable {p : ℕ} [ThePrime p] {O Γ : Type} [CommRing O] [Algebra ℤ_[p] O] [Group Γ] [OverGp Γ p]
  {F : Filter Γ} {K : Γ → O[X] → Prop} {U : (O →ₐ[ℤ_[p]] ℂ_[p]) → Finset ℤ} {Y L : GalLattice O Γ}
  [Module.Finite ℤ_[p] O] {K' : Γ → O[X] → Prop}
  {U' : (O →ₐ[ℤ_[p]] ℂ_[p]) → Finset ℤ}

instance : Module.Finite ℤ_[p] L := .trans O _

/-- If every `g : Γ` acts on `L` by the scalar `χ g ^ c`, where `χ` is the cyclotomic character,
then `L` satisfies `InClass F ⊥ U` for every filter `F`, with `U` equal to `{-c}` at every embedding
`O → ℂ_[p]`. This means its periods are admissible, its only Hodge–Tate jump is `-c`, and the empty
relation `⊥` imposes no killing condition. -/
lemma InClass.of_cyclotomic_pow (c : ℤ) (h_action : ∀ (g : Γ) (x : L), L.ρ g x = χ g ^ c • x) :
    InClass F ⊥ (fun _ : O →ₐ[ℤ_[p]] ℂ_[p] ↦ {-c}) L := by
  refine ⟨isAdmissible_of_cyclotomicGp_zpow c h_action, fun g u hu ↦ ?_, nofun⟩
  rw [hasJumps_of_cyclotomicGp_zpow c h_action u, Multiset.count_ne_zero] at hu
  exact Finset.mem_singleton.2 (Multiset.eq_of_mem_replicate hu)

/-- Let `toGp` have open image and L be potentially crystalline. At each embedding γ, the
multiplicity of the jump u of the twisted dual L^∨(1) equals that of the jump −u − 1 of L. -/
lemma jump_tateDual (h : IsPotentiallyCrystalline L.ρ) (γ : O →ₐ[ℤ_[p]] ℂ_[p]) (u : ℤ) :
    jump (tateDual L).ρ γ u = jump L.ρ γ (-u - 1) :=
  jump_eq_of_pairing h 1 1 (by simp [Units.smul_def])

/-- A lattice `Y` with jointly injective equivariant `O`-linear maps to finitely many lattices of a
class lies in that class. -/
lemma InClass.of_jointly_injective [IsDomain O] {ι : Type*} [Fintype ι] {M : ι → GalLattice O Γ}
    (h : ∀ a : ι, InClass F K U (M a)) (f : ∀ a : ι, Y →ₗ[O] M a)
    (hf : ∀ (a : ι) (g : Γ) (x : Y), f a (Y.ρ g x) = (M a).ρ g (f a x))
    (h_inj : ∀ x : Y, (∀ a : ι, f a x = 0) → x = 0) : InClass F K U Y := by
  refine ⟨?_, fun g u hu ↦ ?_, fun s Q hK hs ↦ ?_⟩
  · exact .of_jointly_injective le_sup_left (fun a ↦ (h a).isAdmissible) (fun a ↦ f a)
      (fun a ↦ .of_forall (hf a)) h_inj
  · -- a jump of `Y` is a jump of some `M a`
    obtain ⟨a, ha⟩ : ∃ a : ι, jump (M a).ρ g u ≠ 0 :=
      exists_jump_of_jointly_injective (fun a ↦ (h a).isPotentiallyCrystalline) f hf h_inj hu
    exact (h a).mem_of_jump_ne_zero ha
  · -- `Q` kills `s` on every `M a`, hence on `Y`
    exact .of_jointly_injective hs (fun a ↦ (f a).restrictScalars ℤ_[p])
      (fun a ↦ .of_forall (hf a)) h_inj le_rfl (fun a ↦ (h a).isKilledBy_of_isWeilPair hK hs) map_id
        (by simp)

/-- The twisted dual `Hom(Y, O(1))` of a lattice of a class lies in the class with the same filter
`F`. Its jumps at `g` are among the `-u - 1` with `u ∈ U g`, and `Q` kills `s` on it if `K s⁻¹ Q`
holds and `toGp s` is in inertia. -/
lemma InClass.dual (h : InClass F K U Y) :
    InClass F (fun s : Γ ↦ K s⁻¹)
      (fun g : O →ₐ[ℤ_[p]] ℂ_[p] ↦ (U g).image fun u : ℤ ↦ -u - 1) Y.tateDual := by
  -- the evaluation pairing makes the dual admissible; what kills `s` on `Y` kills `s⁻¹` on it
  obtain ⟨h_adm, h_killed⟩ : IsAdmissible Y.tateDual.ρ (nearOne Γ ⊔ F) ∧
      ∀ (s : Γ) (Q : O[X]), IsWeilPair (toGp s) 0 → IsKilledBy Y.ρ s 0 Q →
        IsKilledBy Y.tateDual.ρ s⁻¹ 0 Q :=
    h.isAdmissible.of_pairing (σ := Y.tateDual.ρ) (by simp) 1 1 (by simp [Units.smul_def])
  refine ⟨h_adm, fun g u hu ↦ ?_, fun s Q hK hs ↦ ?_⟩
  · -- if `u` is a jump of the dual, then `-u - 1` is a jump of `Y`
    rw [jump_tateDual h.isPotentiallyCrystalline] at hu
    exact Finset.mem_image.2 ⟨-u - 1, h.mem_of_jump_ne_zero hu, by ring⟩
  · -- `Q` kills `s⁻¹` on `Y`, hence `s` on the dual
    simpa using h_killed s⁻¹ Q hs.inv (h.isKilledBy_of_isWeilPair hK hs.inv)

variable [IsDomain O]

/-- Let `O` be a domain, finite over `ℤ_[p]`. Let `Y` lie in the class `InClass F K U` and `L` in
`InClass F K' U'`, with the same filter `F`. Such a class says that the periods fixed by almost all
elements of `Γ` (for `F` and 'near 1') span, that every Hodge–Tate jump at `g` lies in `U g`, and
that `K s Q` with `toGp s` in inertia forces `Q` to kill `s`. Then `Y ⊗ L` lies in the class with
filter `F`, allowed jumps `U g + U' g` at `g`, and the empty relation `⊥`, so no killing condition.

This is a form of the additivity of Hodge–Tate weights in tensor products: an inclusion of sets of
weights, without multiplicities. -/
lemma InClass.tensor (h : InClass F K U Y) (h' : InClass F K' U' L) :
    InClass F ⊥ (fun g : O →ₐ[ℤ_[p]] ℂ_[p] ↦ (U g).image₂ (· + ·) (U' g)) (Y.tensor L) := by
  -- admissibility passes to `Y ⊗ L`, which the pure tensors span
  have h_adm : IsAdmissible (Y.tensor L).ρ (nearOne Γ ⊔ F) :=
    .of_bilinear ((mk O Y L).restrictScalars₁₂ ℤ_[p] ℤ_[p]) (fun _ _ _ ↦ rfl) h.isAdmissible
      h'.isAdmissible (mapOfCompatibleSMul_surjective O ℤ_[p] ℤ_[p] Y L)
  refine ⟨h_adm, fun g u hu ↦ ?_, nofun⟩
  -- If `P⁻¹`, `Q⁻¹` have Hodge–Tate rows for `Y`, `L` with jumps `k`, `l`, then their Kronecker
  -- product has Hodge–Tate rows for the tensor product with jumps `k a + l b`.
  obtain ⟨P, k, hPk, hk, -⟩ := h.isPotentiallyCrystalline.exists_isHodgeTateFrame (finBasis ..) g
  obtain ⟨Q, l, hQl, hl, -⟩ := h'.isPotentiallyCrystalline.exists_isHodgeTateFrame (finBasis ..) g
  have jumps : HasJumps (Y.tensor L).ρ g (Finset.univ.1.map (k · + l ·).uncurry) := by
    refine (hasJumps_of_rows ((finBasis O Y).tensorProduct (finBasis O L)) (kroneckerGL P⁻¹ Q⁻¹) _
      ?_).1
    filter_upwards [hPk, hQl] with x hPx hQx ⟨a, b⟩ ⟨a', b'⟩
    -- the row identity at `((a, b), (a', b'))` is the product of those for `P⁻¹` and for `Q⁻¹`
    simpa [Matrix.mul_apply, zpow_add, mul_smul, Finset.sum_mul_sum, Fintype.sum_prod_type,
      LinearMap.toMatrix_apply, mul_comm (_ : O), kroneckerGL, mul_mul_mul_comm] using
      congrArg₂ HMul.hMul (inv_mul_apply_of_isHodgeTateFrame hPx a a')
        (inv_mul_apply_of_isHodgeTateFrame hQx b b')
  -- so a jump is some `k a + l b`, where `k a` is a jump of `Y` and `l b` is a jump of `L`
  obtain ⟨a, b, rfl⟩ : ∃ a b, k a + l b = u := by simpa [jumps _] using hu
  exact Finset.mem_image₂_of_mem (h.mem_of_jump_ne_zero (by simp [hk _, -Fin.univ_val_map]))
    (h'.mem_of_jump_ne_zero (by simp [hl _, -Fin.univ_val_map]))

/-- Let `O` be a domain, finite over `ℤ_[p]`. Let `Y` lie in the class `InClass F K U` and `L` in
`InClass F K' U'`, with the same filter `F`. Such a class says that the periods fixed by almost all
of `Γ` (for `F` and 'near 1') span, that the Hodge–Tate jumps at `g` lie in `U g`, and that a
relation `K s Q` with `toGp s` in inertia forces `Q` to kill `s`. If `toGp s` is in inertia and `K`,
`K'` relate `s` to the images in `O[X]` of monic `q`, `r` over `ℤ_[p]`, then some monic `e` over
`ℤ_[p]` with degree at most `deg q * deg r` kills `(s⁻¹, 0)` on the twisted dual `(Y ⊗ L)^∨(1)`:
evaluated at the linear Frobenius of `s⁻¹`, it vanishes on `Bmax ⊗ (Y ⊗ L)^∨(1)`. -/
lemma exists_isKilledBy_tateDual_tensor (h : InClass F K U Y) (h' : InClass F K' U' L) {s : Γ}
    {q r : ℤ_[p][X]} (hs : IsWeilPair (toGp s) 0) (hq : Monic q) (hr : Monic r)
    (hKq : K s (q.map (algebraMap ℤ_[p] O))) (hKr : K' s (r.map (algebraMap ℤ_[p] O))) :
    ∃ e : ℤ_[p][X], Monic e ∧ e.natDegree ≤ q.natDegree * r.natDegree ∧
      IsKilledBy (tateDual (Y.tensor L)).ρ s⁻¹ 0 (e.map (algebraMap ℤ_[p] O)) := by
  -- Take the characteristic polynomial of multiplication by `x ⊗ x'` on
  -- `ℤ_p[x] / q ⊗ ℤ_p[x'] / r`. By Cayley–Hamilton it kills `s` on the tensor product, hence
  -- `s⁻¹` on the dual.
  obtain ⟨hY, killY⟩ := h.isKilledBy_of_isWeilPair hKq hs
  obtain ⟨hL, killL⟩ := h'.isKilledBy_of_isWeilPair hKr hs
  have hYL : IsPotentiallyCrystalline (Y.tensor L).ρ := (h.tensor h').isPotentiallyCrystalline
  let f := algEquivMatrix ((powerBasisAux' hq).tensorProduct (powerBasisAux' hr))
  let A := f (.mulLeft _ (root q ⊗ₜ root r))
  -- `Y ⊗ L` lies in the class whose killing condition is `IsKilledBy` itself; pass to the dual.
  have h_in : InClass F (fun s Q ↦ IsKilledBy (Y.tensor L).ρ s 0 Q)
      (fun g ↦ Finset.image₂ (· + ·) (U g) (U' g)) (Y.tensor L) :=
    ⟨(h.tensor h').isAdmissible, (h.tensor h').mem_of_jump_ne_zero, fun _ _ hQ _ ↦ hQ⟩
  refine ⟨A.charpoly, A.charpoly_monic, by
    simp, h_in.dual.isKilledBy_of_isWeilPair ⟨hYL, ?_⟩ hs.inv⟩
  -- Write `β` for `linearFrob _ s 0`. The maps attached to `s ^ n` respect the tensor product:
  -- `β_n a ⊗ β_n b = β_n (a ⊗ b)`, and `β_n = β ^ n` (`linearFrob_pow`).
  let B := (mk O Y L).restrictScalars₁₂ ℤ_[p] ℤ_[p]
  have frob_tensor n := linearFrob_baseChangePairing hL (hs.pow n) hY B (by tauto) hYL
  ext z
  refine z.inductionOn (fun a b ↦ ?_) (by simp_all [tmul_add])
  -- `Φ` sends `u(x) ⊗ v(x')` to `u(β) a ⊗ v(β) b`, read on remainders modulo `q`, `r` (these kill
  -- `β`); by `frob_tensor` it sends `(x ⊗ x') ^ n` to `β ^ n (a ⊗ b)`.
  let Φ : AdjoinRoot q ⊗[ℤ_[p]] AdjoinRoot r →ₗ[ℤ_[p]] Bmax ⊗[ℤ_[p]] (Y ⊗[O] L) :=
    TensorProduct.lift (((baseChangePairing B).restrictScalars₁₂ ..).compl₁₂
      ((aeval (linearFrob Y.ρ s 0)).toLinearMap.flip (1 ⊗ₜ a) ∘ₗ modByMonicHom hq)
      ((aeval (linearFrob L.ρ s 0)).toLinearMap.flip (1 ⊗ₜ b) ∘ₗ modByMonicHom hr))
  have cayley : Φ (f.symm (aeval A A.charpoly) 1) = 0 := by simp [A.aeval_self_charpoly]
  -- expanding the characteristic polynomial in powers of `A` turns `cayley` into the goal
  simp_all [Φ, coeffEnd, A, B, baseChangePairing, (Matrix.charpoly _).aeval_eq_sum_range,
    aeval_modByMonic_eq_self_of_root, eval₂_map, ← mk_X, -map_eq_zero, ← aeval_def, ← map_pow,
    aeval_X_pow, LinearMap.ext_iff, ← linearFrob_pow]

end New.Lift

/-!
## Perfect pairings and local duality for crystalline cocycles

`R` is the integer ring of a finite extension of `ℚ_ℓ`, and `Γ` maps by `𝒥.toGp` with open image to
the absolute Galois group of `ℚ_ℓ`. `L` and `L'` are potentially crystalline lattices. `b`
identifies `L'` equivariantly with the `ℤ_[ℓ]`-dual of `L`, twisted by the cyclotomic character `χ`.
-/

section CrystallineDuality

namespace New

open Period Lift Module LE Submodule Function crysCocycles NeZero AddSubgroup Multiset Topology Nat
  Algebra LinearMap IsDiscreteValuationRing PadicInt MulAction Equiv DFunLike IsLocalGalois Selmer

variable {ℓ : ℕ} [ThePrime ℓ] {R Γ : Type} [CommRing R] [PadicIntegerRing R ℓ] [Group Γ]
  {L L' : GalLattice R Γ}

/-- There is a `ℤ_[ℓ]`-linear form `f` on `R` such that `(φ, x) ↦ f (φ x)` is a perfect pairing
over `ℤ_[ℓ]` between the `R`-dual of the lattice `L` and `L`. -/
lemma Selmer.exists_perfect_pairing :
    ∃ f : Dual ℤ_[ℓ] R, Bijective ((restrictScalarsₗ ℤ_[ℓ] R L R ℤ_[ℓ]).compr₂ f) := by
  -- The `ℤ_[ℓ]`-dual `D` of `R` is a free `R`-module of rank one; take a generator for `f`.
  let D : Type := Dual ℤ_[ℓ] R
  let instModuleD : Module R D := compHom (R := Rᵈᵐᵃ) D (algebraMap R Rᵐᵒᵖ)
  have smul_apply (o : R) (y : D) (x : R) : (o • y) x = y (o * x) := rfl
  have h_tower : IsScalarTower ℤ_[ℓ] R D := ⟨by aesop⟩
  have h_finite : Module.Finite R D := Finite.right ℤ_[ℓ] R D
  -- a nonzero `o` divides a nonzero `k` of `ℤ_[ℓ]`, and `k` acts injectively on `D`
  have h_torsion_free : IsTorsionFree R D := ⟨fun o ho ↦ by
    obtain ⟨c, k, hk, hc⟩ : ∃ (c : R) (k : ℤ_[ℓ]), k ≠ 0 ∧ k • (1 : R) = o * c :=
      Algebra.IsAlgebraic.exists_smul_eq_mul ℤ_[ℓ] 1 ho.ne_zero
    exact .of_mul (a := c) fun y ↦ by simp [mul_comm, ← hc, hk]⟩
  have h_rank : finrank R D = finrank R R := by
    simpa [finrank_linearMap, finrank_pos.ne', D] using finrank_mul_finrank ℤ_[ℓ] R D
  let t : D ≃ₗ[R] R := .ofFinrankEq D R h_rank
  -- `ψ ↦ f ∘ ψ` has the inverse `l ↦ (x ↦ t (o ↦ l (o • x)))`
  let inv (l : L →ₗ[ℤ_[ℓ]] ℤ_[ℓ]) : L →ₗ[R] R := t.toLinearMap ∘ₗ
    { toFun x := l ∘ₗ .smulRight LinearMap.id x
      map_add' := by simp [DFunLike.ext_iff, D]
      map_smul' := by simp [DFunLike.ext_iff, D, smul_apply, smul_smul, mul_comm, -smul_eq_mul] }
  -- `t.symm o` is `o` times the generator `t.symm 1`
  have h_gen (o x : R) : t.symm o x = t.symm 1 (o * x) := by simp [← smul_apply, ← map_smul]
  refine ⟨t.symm 1, bijective_iff_has_inverse.2 ⟨inv, fun ψ ↦ ?_, fun l ↦ LinearMap.ext fun x ↦ ?_⟩⟩
  · simp [inv, D, ← t.eq_symm_apply, DFunLike.ext_iff, h_gen (ψ _), mul_comm]
  · simpa [inv, D] using (h_gen (t (l ∘ₗ .smulRight LinearMap.id x)) 1).symm

/-- The crystalline cocycles Z_f(L), Z_f(L') (`crysCocycles`) of two potentially crystalline
lattices in duality `b` have complementary sizes: the orders of Z_f(L) / ℓᵐ Z_f(L) and Z_f(L') / ℓᵐ
Z_f(L') multiply to `(ℓ ^ m) ^ (d (n + 2))`. Here `d` is the rank of `L` over `ℤ_[ℓ]`, and `n` is
the index of the image of `𝒥.toGp`.

The proof uses only the duality of Hodge–Tate jumps (`jump_eq_of_pairing`) and the rank formula
`crysCocycles.finrank_eq`. Classically the same count follows from Bloch–Kato duality for
crystalline classes and Tate's Euler characteristic formula, but neither is used here; only the
product of the orders is stated, not mutual annihilation. -/
lemma Period.IsPotentiallyCrystalline.index_mul_index_dual [𝒥 : OverGp Γ ℓ]
    (hL : IsPotentiallyCrystalline L.ρ)
    (hL' : IsPotentiallyCrystalline L'.ρ) (b : L' ≃ₗ[ℤ_[ℓ]] Dual ℤ_[ℓ] L)
    (hb : ∀ (g : Γ) (x : L') (y : L), b (L'.ρ g x) (L.ρ g y) = χ g • b x y) (m : ℕ) :
    (pPowMultiples (crysCocycles L.ρ) m).index * (pPowMultiples (crysCocycles L'.ρ) m).index =
      ((ℓ ^ m) ^ finrank ℤ_[ℓ] L) ^ (2 + 𝒥.toGp.range.index) := by
  -- The jumps of `L'` are the `-u - 1` for the jumps `u` of `L`, so the numbers of negative jumps
  -- of the two lattices add up to the rank `d`. By `crysCocycles.finrank_eq` the ranks of the two
  -- modules of cocycles add up to `2 d + n d`, with `n` the index of the image of `toGp`.
  obtain ⟨J, hJ_card, hJ⟩ : ∃ J : Multiset ℤ, J.card = finrank ℤ_[ℓ] L ∧
      HasJumps (overZp L.ρ) (ofId ℤ_[ℓ] ℂ_[ℓ]) J :=
    hL.exists_hasJumps (ρ := overZp _) (ofId ℤ_[ℓ] ℂ_[ℓ])
  have hJ' : HasJumps (overZp L'.ρ) (ofId ℤ_[ℓ] ℂ_[ℓ]) (J.map fun u ↦ -u - 1) := by
    intro u
    have h_inj : Injective fun u : ℤ ↦ -u - 1 := fun u₁ u₂ h_eq ↦ by lia
    have h_dual : jump (overZp L'.ρ) (ofId ℤ_[ℓ] ℂ_[ℓ]) u =
        jump (overZp L.ρ) (ofId ℤ_[ℓ] ℂ_[ℓ]) (-u - 1) :=
      jump_eq_of_pairing (ρ := overZp _) hL b 1 (by simpa [Units.smul_def] using hb)
    simpa [← J.count_map_eq_count' (fun u ↦ -u - 1) h_inj] using h_dual.trans (hJ _)
  have h_count : J.countP (· < 0) + (J.map fun u ↦ -u - 1).countP (· < 0) = finrank ℤ_[ℓ] L := by
    grind [countP_map, countP_eq_card_filter, card_eq_countP_add_countP]
  obtain ⟨h_fin, h_rank⟩ : Module.Finite ℤ_[ℓ] (crysCocycles L.ρ) ∧
      finrank ℤ_[ℓ] (crysCocycles L.ρ) =
        finrank ℤ_[ℓ] L + 𝒥.toGp.range.index * J.countP (· < 0) :=
    finrank_eq hL hJ
  obtain ⟨h_fin', h_rank'⟩ : Module.Finite ℤ_[ℓ] (crysCocycles L'.ρ) ∧
      finrank ℤ_[ℓ] (crysCocycles L'.ρ) =
        finrank ℤ_[ℓ] L' + 𝒥.toGp.range.index * (J.map fun u ↦ -u - 1).countP (· < 0) :=
    finrank_eq hL' hJ'
  have h_sum : finrank ℤ_[ℓ] (crysCocycles L.ρ) + finrank ℤ_[ℓ] (crysCocycles L'.ρ) =
      finrank ℤ_[ℓ] L * (2 + 𝒥.toGp.range.index) := by
    grind [b.finrank_eq, finrank_linearMap_self]
  -- Each index is `ℓᵐ` to the power of the rank.
  simp [← pow_add, ← pow_mul, ← mul_add, h_sum, mul_assoc]

/-- The pairing `b` reduced modulo `ℓᵐ` gives a map from `L'` onto the dual `Hom(V, Q̄_ℓ^×)` of
`V = L / ℓᵐ L`, with kernel `ℓᵐ L'`. -/
lemma Period.exists_dual_reduction (b : L' ≃ₗ[ℤ_[ℓ]] Dual ℤ_[ℓ] L) {m : ℕ} {V : Type}
    [AddCommGroup V] [Finite V] {q : L →+ V} (hq_surj : Surjective q)
    (hq_ker : q.ker = pPowMultiples L m) :
    ∃ r : L' →+ V →+ DiscreteUnits (PadicAlgCl ℓ),
      (∀ (x : L') (y : L), r x (q y) =
        zmodPowToUnits m (Ideal.Quotient.mk (Ideal.span {(ℓ : ℤ_[ℓ]) ^ m}) (b x y))) ∧
      r.ker = pPowMultiples L' m ∧
      Surjective r := by
  let u : ℤ_[ℓ] →+ DiscreteUnits (PadicAlgCl ℓ) := (zmodPowToUnits m).comp (mkQ _).toAddMonoidHom
  obtain ⟨r, hr⟩ : ∃ r : L' →+ V →+ DiscreteUnits (PadicAlgCl ℓ),
      ∀ (x : L') (y : L), r x (q y) = u (b x y) := by
    let β : L →+ L' →+ DiscreteUnits (PadicAlgCl ℓ) :=
      (toAddMonoidHom'.comp b.flip.toAddMonoidHom).compr₂ u
    have hβ_ker : q.ker ≤ β.ker := by simp [β, hq_ker, le, u, ext_iff]
    exact ⟨(q.liftOfSurjective hq_surj ⟨β, hβ_ker⟩).flip, by simp [β]⟩
  have hr_ker : r.ker = pPowMultiples L' m := by
    ext x
    -- `x` is in the kernel when all values `b x y` are divisible by `ℓᵐ`, and a linear form all
    -- of whose values are divisible by `ℓᵐ` is `ℓᵐ` times a linear form
    have h_ker_iff : x ∈ r.ker ↔ ∀ y : L, ∃ a : ℤ_[ℓ], a * (ℓ : ℤ_[ℓ]) ^ m = b x y := by
      simp [u, ext_iff, hq_surj.forall, hr, zmodPowToUnits, (rootPowHom ..).property,
        map_eq_zero_iff, ← RingHom.mem_ker, ker_toZModPow, mem_span_singleton]
    have h_mult_iff : x ∈ pPowMultiples L' m ↔
        ∃ f : Dual ℤ_[ℓ] L, ∀ y : L, f y * (ℓ : ℤ_[ℓ]) ^ m = b x y := by
      simp [b.symm.surjective.exists, ← b.injective.eq_iff, ext_iff, mul_comm (_ ^ m)]
    rw [h_ker_iff, h_mult_iff]
    refine ⟨fun hx ↦ ?_, fun ⟨f, hf⟩ y ↦ ⟨f y, hf y⟩⟩
    -- divide `b x` by `ℓᵐ`: multiplication by `ℓᵐ ≠ 0` is injective on `ℤ_[ℓ]`
    have h_inj : Injective (mulRight ℤ_[ℓ] ((ℓ : ℤ_[ℓ]) ^ m)) := mul_left_injective₀ out
    exact ⟨(b x).codRestrictOfInjective _ h_inj hx, codRestrictOfInjective_comp_apply _ _ h_inj hx⟩
  refine ⟨r, hr, hr_ker, r.range_eq_top.mp (eq_top_of_card_eq _ ?_)⟩
  -- `L' / ℓᵐ` and the dual of `V` both have the order of `V`
  have h_card : Nat.card V = (ℓ ^ m) ^ finrank ℤ_[ℓ] L := by
    simpa [hq_ker] using (index_comap_of_surjective ⊥ hq_surj).symm
  rw [← index_ker, hr_ker, index_pPowMultiples, b.finrank_eq, finrank_linearMap_self,
    card_congr (β := _ →* _ˣ) AddMonoidHom.toMultiplicativeLeft,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, Nat.card_congr Multiplicative.toAdd, h_card]

variable [TopologicalSpace Γ] [𝒥 : OverGp Γ ℓ]

/-- Division by `l ≠ 0`: some additive `E : ℤ_ℓ → Q̄_ℓ^×`, killed by a power of `ℓ`, takes at `l z`
the value of `zmodPowToUnits m` at the class of `z`. -/
lemma Period.exists_div_rootOfUnity (m : ℕ) {l : ℤ_[ℓ]} (hl : l ≠ 0) :
    ∃ (E : ℤ_[ℓ] →+ DiscreteUnits (PadicAlgCl ℓ)) (n : ℕ),
      (∀ z : ℤ_[ℓ], E (l * z) =
        zmodPowToUnits m (Ideal.Quotient.mk (Ideal.span {(ℓ : ℤ_[ℓ]) ^ m}) z)) ∧
      ∀ z : ℤ_[ℓ], ℓ ^ n • E z = 0 := by
  let u : ℤ_[ℓ] →+ DiscreteUnits (PadicAlgCl ℓ) := (zmodPowToUnits m).comp (mkQ _).toAddMonoidHom
  -- `E` exists because the target is divisible and multiplication by `l` is injective.
  obtain ⟨E, hE⟩ : ∃ E : ℤ_[ℓ] →+ DiscreteUnits (PadicAlgCl ℓ), ∀ z : ℤ_[ℓ], E (l * z) = u z := by
    simpa using QZ.exists_extend (l • AddMonoidHom.id ℤ_[ℓ]) u (by simp [le, hl])
  -- `l` is `ℓ ^ i` up to a unit, so `ℓ ^ (i + m)` kills the values of `E`.
  obtain ⟨i, v, hv⟩ : ∃ i : ℕ, Associated l ((ℓ : ℤ_[ℓ]) ^ i) :=
    associated_pow_irreducible hl irreducible_p
  refine ⟨E, i + m, hE, fun z ↦ ?_⟩
  simp [← E.map_nsmul, pow_add, ← hv, mul_assoc, hE, u]

/-- The cup product `(g, h) ↦ b (g c(h)) (a g)` of maps `a : Γ → L` and `c : Γ → L'`, reduced
modulo `ℓᵐ` and embedded in `Q̄_ℓ^×` by `zmodPowToUnits m`. -/
noncomputable def Period.cupModPow (b : L' ≃ₗ[ℤ_[ℓ]] Dual ℤ_[ℓ] L) (m : ℕ) (a : Γ → L) (c : Γ → L')
    (x : Γ × Γ) : DiscreteUnits (PadicAlgCl ℓ) :=
  zmodPowToUnits m
    (Ideal.Quotient.mk (Ideal.span {(ℓ : ℤ_[ℓ]) ^ m}) (b (L'.ρ x.fst (c x.snd)) (a x.fst)))

/-- A map `s : Γ → V`, with `q : L → V` a reduction modulo `ℓᵐ`, is a continuous cocycle that is
orthogonal under the cup product to the group `H` of maps `Γ → L'`. -/
structure Period.IsCupOrthogonal (b : L' ≃ₗ[ℤ_[ℓ]] Dual ℤ_[ℓ] L) (m : ℕ)
    {V : DiscreteModule ℤ_[ℓ] Γ} (q : L →ₗ[ℤ_[ℓ]] V) (H : AddSubgroup (Γ → L')) (s : Γ → V) :
    Prop where
  /-- `s` is a continuous cocycle. -/
  mem_Z1 : s ∈ Z1 V.ρ
  /-- The cup products of some lift of `s` with the elements of `H` are 2-coboundaries. -/
  exists_lift : ∃ a : Γ → L, q ∘ a = s ∧ ∀ c ∈ H, cupModPow b m a c ∈ B2 (unitsRep.comp 𝒥.toGp)

/-- Let `L`, `L'` be potentially crystalline lattices over `R`, and let `b : L' ≃ Dual L` be a
pairing with `b (ρ' g x) (ρ g y) = χ g • b x y`. Let `q : L → V` be a `Γ`-equivariant map to a
finite discrete `Γ`-module, and let `U` be a subgroup whose `OverGp` structure is the restriction of
that of `Γ`. Then there are potentially crystalline `R`-linear actions `σ`, `σ'` of `Γ` on `L`, `L'`
such that `b` still satisfies the same twisted pairing identity and `q` is still equivariant for
`σ`. Moreover, every Hodge–Tate jump `k` of `σ'` restricted to `U`, read over `ℤ_[ℓ]` at the
standard embedding `ℤ_[ℓ] → ℂ_[ℓ]`, with nonzero multiplicity is positive. -/
lemma Period.IsPotentiallyCrystalline.exists_twist_jump_pos (hL : IsPotentiallyCrystalline L.ρ)
    (hL' : IsPotentiallyCrystalline L'.ρ) (b : L' ≃ₗ[ℤ_[ℓ]] Dual ℤ_[ℓ] L)
    (hb : ∀ (g : Γ) (x : L') (y : L), b (L'.ρ g x) (L.ρ g y) = χ g • b x y)
    {V : DiscreteModule ℤ_[ℓ] Γ} [Finite V] {q : L →ₗ[ℤ_[ℓ]] V}
    (hq_equivariant : ∀ (g : Γ) (x : L), q (L.ρ g x) = V.ρ g (q x))
    (U : Subgroup Γ) [J : OverGp U ℓ] (hJ : ∀ g : U, J.toGp g = 𝒥.toGp g) :
    ∃ (σ : Representation R Γ L) (σ' : Representation R Γ L'),
      IsPotentiallyCrystalline σ ∧
      IsPotentiallyCrystalline σ' ∧
      (∀ (g : Γ) (x : L') (y : L), b (σ' g x) (σ g y) = χ g • b x y) ∧
      (∀ (g : Γ) (x : L), q (σ g x) = V.ρ g (q x)) ∧
      ∀ k : ℤ, jump (overZp (σ'.comp U.subtype)) (ofId ℤ_[ℓ] ℂ_[ℓ]) k ≠ 0 → 0 < k := by
  -- Twist by `χ^(±N)`. Here `N` exceeds the bound `a` on the jumps of `L'` over `U`, and is a
  -- multiple of `#(Perm V)`, so that the unit `χ(g)^N` acts trivially on `V`.
  obtain ⟨a, ha⟩ : ∃ a : ℕ, ∀ k : ℤ,
      jump (overZp (L'.ρ.comp U.subtype)) (ofId ℤ_[ℓ] ℂ_[ℓ]) k ≠ 0 → -(a : ℤ) ≤ k ∧ k ≤ a :=
    exists_jump_bound
  let N : ℤ := (a + 1) * Nat.card (Perm V)
  let σ : Representation R Γ L := smulMonoidHom.comp ((χ ^ N).prod L.ρ)
  let σ' : Representation R Γ L' := smulMonoidHom.comp ((χ ^ (-N)).prod L'.ρ)
  refine ⟨σ, σ', IsAdmissible.tate_twist hL N fun _ _ ↦ rfl,
    IsAdmissible.tate_twist hL' (-N) fun _ _ ↦ rfl, fun g x y ↦ ?_, fun g x ↦ ?_, fun k hk ↦ ?_⟩
  · simp [σ, σ', hb, Units.smul_def]
  · have h_triv : toPermHom ℤ_[ℓ]ˣ V (χ g ^ N) = 1 := by simp [N, zpow_mul, -toPermHom_apply]
    calc q (σ g x) = (χ g ^ N) • q (L.ρ g x) := q.map_smul _ _
      _ = q (L.ρ g x) := Perm.ext_iff.mp h_triv _
      _ = V.ρ g (q x) := hq_equivariant g x
  · -- A jump `k` of `σ'` gives the jump `k - N ≥ -a` of `L'`.
    have h_shift : jump (overZp (L'.ρ.comp U.subtype)) (ofId ℤ_[ℓ] ℂ_[ℓ]) (k - N) =
        jump (overZp (σ'.comp U.subtype)) (ofId ℤ_[ℓ] ℂ_[ℓ]) k :=
      jump_twist_cyclotomicGp N (by simp [σ', hJ, ← Units.smul_def])
    obtain ⟨h_bound, -⟩ : -(a : ℤ) ≤ k - N ∧ k - N ≤ a := ha (k - N) (h_shift.trans_ne hk)
    nlinarith [Nat.card_pos (α := Perm V)]

/-- Suppose `𝒥.toGp` is an open embedding, `L` and `L'` are potentially crystalline, and `b`
identifies `L'` with the `ℤ_[ℓ]`-dual of `L` so that `b (g x) (g y) = χ g • b x y`. If every
Hodge–Tate jump `k` of `L'` with nonzero multiplicity (over `ℤ_[ℓ]`, at the inclusion into `ℂ_[ℓ]`)
is positive, then the cup product modulo `ℓᵐ` of a crystalline cocycle `c` of `L'` with a
crystalline cocycle `w` of `L` is a 2-coboundary. Here the cup product is the map
`(g, h) ↦ ζ^(b (c g) (g • w h))`, with the pairing reduced modulo `ℓ^m` and `ζ` the chosen primitive
`ℓ^m`-th root of unity (`zmodPowToUnits m`), and the coboundary is for `Γ` acting on the units of
Q̄_ℓ through `𝒥.toGp`. -/
lemma Period.IsPotentiallyCrystalline.cup_mem_B2_of_jump_pos [IsTopologicalGroup Γ]
    (hj : IsOpenEmbedding 𝒥.toGp)
    (hL : IsPotentiallyCrystalline L.ρ) (hL' : IsPotentiallyCrystalline L'.ρ)
    (b : L' ≃ₗ[ℤ_[ℓ]] Dual ℤ_[ℓ] L)
    (hb : ∀ (g : Γ) (x : L') (y : L), b (L'.ρ g x) (L.ρ g y) = χ g • b x y)
    (h_pos : ∀ k : ℤ, jump (overZp L'.ρ) (ofId ℤ_[ℓ] ℂ_[ℓ]) k ≠ 0 → 0 < k) (m : ℕ)
    {c : Γ → L'} (hc : c ∈ crysCocycles L'.ρ) {w : Γ → L} (hw : w ∈ crysCocycles L.ρ) :
    (fun x : Γ × Γ ↦ zmodPowToUnits m
      (Ideal.Quotient.mk (Ideal.span {(ℓ : ℤ_[ℓ]) ^ m}) (b (c x.fst) (L.ρ x.fst (w x.snd))))) ∈
      B2 (unitsRep.comp 𝒥.toGp) := by
  -- A multiple `l c` with `l ≠ 0` is the coboundary of some `y`, and `E` divides by `l`. The cup
  -- product is the coboundary of `g ↦ E (b y (w g))`.
  obtain ⟨l, hl, y, hy⟩ : ∃ l : ℤ_[ℓ], l ≠ 0 ∧ ∃ y : L', (fun g : Γ ↦ L'.ρ g y - y) = l • c :=
    hL'.exists_coboundary_eq_smul h_pos hc
  obtain ⟨E, n, hE, hE_tors⟩ := exists_div_rootOfUnity m hl
  refine ⟨fun g ↦ E (b y (w g)), continuous_comp hj hL (E.comp (b y)) (fun x ↦ hE_tors _) hw,
    fun g g' ↦ ?_⟩
  have h_cob : E (b (l • c g) (L.ρ g (w g'))) = E (b (L'.ρ g y - y) (L.ρ g (w g'))) := by
    rw [congrFun hy g, Pi.smul_apply]
  change _ = unitsRep (𝒥.toGp g) (E (b y (w g'))) - E (b y (w (g * g'))) + E (b y (w g))
  rw [← map_cyclotomicGp_smul E hE_tors]
  simpa [apply_mul hw, sub_add, hE, hb, Units.smul_def] using h_cob

/-- Suppose `𝒥.toGp` is an open embedding, `L` and `L'` are potentially crystalline, and `b`
identifies `L'` with the `ℤ_[ℓ]`-dual of `L` so that `b (g x) (g y) = χ g • b x y`. Let `q : L → V`
and `r : L' → V'` be `Γ`-equivariant additive maps into discrete modules, with kernels `ℓ^m L` and
`ℓ^m L'`. Then the number of cocycles `q ∘ c` (for `c` a crystalline cocycle of `L`) times the
number of cocycles `r ∘ c'` (for `c'` a crystalline cocycle of `L'`) equals `((ℓ^m)^n)^(2 + i)`,
where `n` is the `ℤ_[ℓ]`-rank of `L` and `i` is the index of the range of `𝒥.toGp`. -/
lemma Period.IsPotentiallyCrystalline.card_range_reducedCocycle_mul [IsTopologicalGroup Γ]
    (hj : IsOpenEmbedding 𝒥.toGp)
    (hL : IsPotentiallyCrystalline L.ρ) (hL' : IsPotentiallyCrystalline L'.ρ)
    (b : L' ≃ₗ[ℤ_[ℓ]] Dual ℤ_[ℓ] L)
    (hb : ∀ (g : Γ) (x : L') (y : L), b (L'.ρ g x) (L.ρ g y) = χ g • b x y)
    {m : ℕ} {S S' : Type} [CommRing S] [CommRing S'] {V : DiscreteModule S Γ}
    {V' : DiscreteModule S' Γ} {q : L →+ V} {r : L' →+ V'}
    (hq_equivariant : ∀ (g : Γ) (x : L), q (L.ρ g x) = V.ρ g (q x))
    (hq_ker : q.ker = pPowMultiples L m)
    (hr_equivariant : ∀ (g : Γ) (x : L'), r (L'.ρ g x) = V'.ρ g (r x))
    (hr_ker : r.ker = pPowMultiples L' m) :
    Nat.card (hL.reducedCocycle hj hq_equivariant hq_ker).range *
        Nat.card (hL'.reducedCocycle hj hr_equivariant hr_ker).range =
      ((ℓ ^ m) ^ finrank ℤ_[ℓ] L) ^ (2 + 𝒥.toGp.range.index) := by
  rw [← index_ker, ker_reducedCocycle, ← index_ker, ker_reducedCocycle,
    hL.index_mul_index_dual hL' b hb]

omit [TopologicalSpace Γ] in
/-- In the local field cut out by `toGp`, of degree `n` over `ℚ_ℓ` (`n` is the index of the image of
`𝒥.toGp`), the integers modulo `ℓ` have `ℓⁿ` elements. -/
lemma Period.card_quotient_span_localFieldOf :
    Nat.card (valRingBelow (localFieldOf Γ) (intQpBar ℓ) ⧸
        Ideal.span {(ℓ : valRingBelow (localFieldOf Γ) (intQpBar ℓ))}) =
      ℓ ^ 𝒥.toGp.range.index := by
  simp [(of_finite ⟨𝒥.toGp.range, 𝒥.isOpen_range.out⟩).card_quotient,
    isUniformiser_ell.card_quotient_span_eq_pow isLocalGalois_padic 1, residueCard_padic]

/-- For an additive map `f` and a subgroup `H` of its source, the size of the range of `f` divides
the size of the image of `H` times the index of `H`. -/
lemma Period.card_range_dvd_card_map_mul_index {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (H : AddSubgroup A) : Nat.card f.range ∣ Nat.card (H.map f) * H.index := by
  calc Nat.card f.range = f.ker.index := (index_ker f).symm
    _ ∣ (f.ker ⊓ H).index := index_dvd_of_le inf_le_left
    _ = (f.ker ⊓ H).relIndex H * H.index := (relIndex_mul_index inf_le_right).symm
    _ = Nat.card (H.map f) * H.index := by rw [inf_relIndex_right, relIndex_ker]

/-- `Γ` acts on `Q̄_ℓ` through `𝒥.toGp`. -/
local instance instMulSemiringActionPadicAlgCl : MulSemiringAction Γ (PadicAlgCl ℓ) :=
  MulSemiringAction.compHom (PadicAlgCl ℓ) 𝒥.toGp

/-- The reduction `r` of the pairing `b` modulo `ℓᵐ` is an equivariant map from `L'` to the dual
`Hom(V, Q̄_ℓ^×)` of `V`. Here `Γ` acts on `Q̄_ℓ` through `𝒥.toGp`. -/
lemma Period.dual_reduction_equivariant [IsLocalGalois Γ (fixedFieldOf 𝒥.toGp.range) (intQpBar ℓ)]
    (b : L' ≃ₗ[ℤ_[ℓ]] Dual ℤ_[ℓ] L)
    (hb : ∀ (g : Γ) (x : L') (y : L), b (L'.ρ g x) (L.ρ g y) = χ g • b x y)
    {m : ℕ} {V : DiscreteModule ℤ_[ℓ] Γ} [Finite V] {q : L →ₗ[ℤ_[ℓ]] V}
    (hq_equivariant : ∀ (g : Γ) (x : L), q (L.ρ g x) = V.ρ g (q x))
    (hq_surj : Surjective q) {r : L' →+ V →+ DiscreteUnits (PadicAlgCl ℓ)}
    (hr : ∀ (x : L') (y : L),
      r x (q y) = zmodPowToUnits m (Ideal.Quotient.mk (Ideal.span {(ℓ : ℤ_[ℓ]) ^ m}) (b x y)))
    (g : Γ) (x : L') : r (L'.ρ g x) = V.cartierDual.ρ g (r x) := by
  let u : ℤ_[ℓ] →+ DiscreteUnits (PadicAlgCl ℓ) := (zmodPowToUnits m).comp (mkQ _).toAddMonoidHom
  have hru (x : L') (y : L) : r x (q y) = u (b x y) := hr x y
  -- Test on `q (g y)`: both sides are `g` applied to the class of `b x y`.
  refine AddMonoidHom.ext ((hq_surj.comp (L.ρ.apply_bijective g).surjective).forall.mpr fun y ↦ ?_)
  calc r (L'.ρ g x) (q (L.ρ g y)) = u (χ g • b x y) := by rw [hru, hb]
    _ = unitsRep (𝒥.toGp g) (u (b x y)) :=
        map_cyclotomicGp_smul u (fun _ ↦ nsmul_zmodPowToUnits _) (b x y) (𝒥.toGp g)
    _ = unitsRep (𝒥.toGp g) (r x (V.ρ g⁻¹ (q (L.ρ g y)))) := by simp [← hq_equivariant, hru]

/-- Local duality for potentially crystalline Galois lattices `L`, `L'` (`hL`, `hL'`), with
`b : L' ≃ Hom(L, ℤ_ℓ)` satisfying `b (g x) (g y) = χ g • b x y`, and `𝒥.toGp` an open embedding
(`hj`). Let `V = L / ℓᵐ L` (via `q`), whose dual is `L' / ℓᵐ L'` through `r` (the reduction of `b`).
For a group `Y` of cocycles of `V.cartierDual = Hom(V, Q̄_ℓ^×)`, with annihilator `Y^⊥` under the
cup product, `#Y^⊥ · #Y` divides `#V ^ (2 + n)`, with `n` the index of the image of `𝒥.toGp` (the
degree of the local field). Here `Γ` acts on `Q̄_ℓ` through `𝒥.toGp`, and the `IsLocalGalois`
instance follows from `hj` (`isLocalGalois_of_isOpenEmbedding`). -/
lemma Period.IsPotentiallyCrystalline.card_pairingAnnihilator_mul_card_dvd
    (hj : IsOpenEmbedding 𝒥.toGp) [IsLocalGalois Γ (fixedFieldOf 𝒥.toGp.range) (intQpBar ℓ)]
    (hL : IsPotentiallyCrystalline L.ρ) (hL' : IsPotentiallyCrystalline L'.ρ)
    (b : L' ≃ₗ[ℤ_[ℓ]] Dual ℤ_[ℓ] L)
    (hb : ∀ (g : Γ) (x : L') (y : L), b (L'.ρ g x) (L.ρ g y) = χ g • b x y)
    {m : ℕ} {V : DiscreteModule ℤ_[ℓ] Γ} [Finite V] {q : L →ₗ[ℤ_[ℓ]] V}
    (hq_equivariant : ∀ (g : Γ) (x : L), q (L.ρ g x) = V.ρ g (q x))
    (hq_surj : Surjective q) (hq_ker : q.toAddMonoidHom.ker = pPowMultiples L m)
    {r : L' →+ V →+ DiscreteUnits (PadicAlgCl ℓ)}
    (hr : ∀ (x : L') (y : L),
      r x (q y) = zmodPowToUnits m (Ideal.Quotient.mk (Ideal.span {(ℓ : ℤ_[ℓ]) ^ m}) (b x y)))
    (hr_surj : Surjective r) (hr_ker : r.ker = pPowMultiples L' m)
    (Y : AddSubgroup (Z1 V.cartierDual.ρ)) :
    Nat.card (pairingAnnihilator V.evalCup Y) * Nat.card Y ∣
      ((ℓ ^ m) ^ finrank ℤ_[ℓ] L) ^ (2 + 𝒥.toGp.range.index) := by
  -- A Tate twist of `L`, `L'` has the same reductions, and its crystalline cocycles form an
  -- orthogonal pair of the largest size over an open subgroup `U` of index prime to `ℓ`.
  have h_card : Nat.card V = (ℓ ^ m) ^ finrank ℤ_[ℓ] L := by
    simpa [hq_ker] using (index_comap_of_surjective (f := q.toAddMonoidHom) ⊥ hq_surj).symm
  -- An open normal `Q` fixes `V`; over `U` every element acts on `V` with `ℓ`-power order.
  obtain ⟨Q, hQ⟩ := exists_openNormalSubgroup_apply_eq V.continuous
  obtain ⟨U, -, hU_index, hU_pow⟩ := DiscreteModule.exists_open_sylow ℓ Q
  have hU : IsOpenEmbedding (𝒥.toGp.comp U.subtype) := hj.comp U.isOpen.isOpenEmbedding_subtypeVal
  let J : OverGp U.toSubgroup ℓ := ⟨𝒥.toGp.comp U.subtype, ⟨hU.isOpen_range⟩⟩
  obtain ⟨σ, σ', hσ, hσ', hbσ, hqσ, h_pos⟩ :=
    hL.exists_twist_jump_pos hL' b hb hq_equivariant U.toSubgroup (J := J) fun _ ↦ rfl
  have hrσ : ∀ (g : Γ) (x : L'), r (σ' g x) = V.cartierDual.ρ g (r x) :=
    dual_reduction_equivariant (L := ⟨L, σ⟩) (L' := ⟨L', σ'⟩) b hbσ hqσ hq_surj hr
  -- Over `U` the reductions of the crystalline cocycles of the twists are orthogonal.
  let M : GalLattice R U.toSubgroup := ⟨L, σ.comp U.subtype⟩
  let M' : GalLattice R U.toSubgroup := ⟨L', σ'.comp U.subtype⟩
  let Z : AddSubgroup (Z1 (V.restrictTo U).ρ) :=
    (reducedCocycle (V := V.restrictTo U) hU (hσ.comp U.subtype) (fun g ↦ hqσ g) hq_ker).range
  let Z' : AddSubgroup (Z1 (V.cartierDual.restrictTo U).ρ) := (reducedCocycle
    (V := V.cartierDual.restrictTo U) hU (hσ'.comp U.subtype) (fun g ↦ hrσ g) hr_ker).range
  have h_orth : Z ≤ pairingAnnihilator (V.restrictTo U).evalCup Z' := by
    rintro _ ⟨⟨w, hw⟩, rfl⟩ _ ⟨⟨c, hc⟩, rfl⟩
    have h_cup : (fun x : U.toSubgroup × U.toSubgroup ↦ r (c x.fst) (V.ρ x.fst (q (w x.snd)))) ∈
        B2 (unitsRep.comp J.toGp) := by
      simp only [← hqσ, hr]
      exact cup_mem_B2_of_jump_pos (L := M) (L' := M') hU (hσ.comp _) (hσ'.comp _) b
        (fun g ↦ hbσ g) h_pos m hc hw
    exact (ker_mkQ _).ge h_cup
  -- They reach the bound on the size of an orthogonal pair.
  have h_max (X : AddSubgroup (Z1 (V.restrictTo U).cartierDual.ρ))
      (W : AddSubgroup (Z1 (V.restrictTo U).ρ))
      (hXW : X ≤ pairingAnnihilator (V.restrictTo U).evalCup.flip W) :
      Nat.card X * Nat.card W ≤ Nat.card Z' * Nat.card Z := by
    have h_incl (g : (U : Subgroup Γ)) : subgroupIncl (U : Subgroup Γ) g = (g : Γ) := rfl
    have hV : (V.restrictTo U).FiniteKilledFixedInj (ℓ ^ (m * finrank ℤ_[ℓ] L))
        (Q.subgroupOf U) 1 0 :=
      ⟨inferInstance, by simp [pow_mul, ← h_card], fun g hg ↦ by simpa [h_incl] using hQ g hg,
        fun _ ↦ by simp⟩
    calc Nat.card X * Nat.card W ≤ Nat.card V ^ (2 + J.toGp.range.index) :=
        card_mul_card_le_of_orthogonal (J := isLocalGalois_of_isOpenEmbedding (j := J.toGp) hU) _
          card_quotient_span_localFieldOf hV (fun g ↦ hU_pow g g.property) X W hXW
      _ = Nat.card Z' * Nat.card Z := by
        rw [h_card, mul_comm]
        exact (card_range_reducedCocycle_mul (L := M) (L' := M') hU _ _ b (fun g ↦ hbσ g) ..).symm
  have h_coprime : (Nat.card V).Coprime U.toSubgroup.index := by
    simpa only [h_card] using (hU_index.pow_left _).pow_left _
  -- Local duality descends from `U` to `Γ`, as the index of `U` is prime to the order of `V`.
  calc Nat.card (pairingAnnihilator V.evalCup Y) * Nat.card Y
      ∣ Nat.card (hσ.reducedCocycle hj hqσ hq_ker).range *
          Nat.card (hσ'.reducedCocycle (V := V.cartierDual) hj hrσ hr_ker).range :=
        V.local_duality_card_dvd (hσ'.holdsCorestrictions hj hrσ hr_ker hr_surj hU)
          (hσ.holdsCorestrictions hj hqσ hq_ker hq_surj hU) h_coprime h_orth h_max Y
    _ = ((ℓ ^ m) ^ finrank ℤ_[ℓ] L) ^ (2 + 𝒥.toGp.range.index) :=
        card_range_reducedCocycle_mul (L := ⟨L, σ⟩) (L' := ⟨L', σ'⟩) hj hσ hσ' b hbσ ..

/-- The inequality of local duality. Suppose `𝒥.toGp` is an open embedding of `Γ` into the Galois
group of `ℚ_ℓ`, `L` and `L'` are potentially crystalline lattices in perfect equivariant duality `b`
into `ℤ_ℓ(1)`, and `q` presents the finite module `V = L / ℓᵐ L` as a `Γ`-module. Let `A` be the
image under `q` of the crystalline cocycles `Z_f(L)` (`crysCocycles`), as maps `Γ → V`; if the
elements of `A` and of `S` are continuous cocycles orthogonal to `H` under the cup product built
from `b` modulo `ℓᵐ`, then `[S : S ∩ A]` divides `[Z_f(L') : H ∩ Z_f(L')]`.

One divisibility in Bloch–Kato duality for crystalline classes. -/
lemma Period.IsPotentiallyCrystalline.relIndex_dvd_of_orthogonal [IsTopologicalGroup Γ]
    (hj : IsOpenEmbedding 𝒥.toGp)
    (hL : IsPotentiallyCrystalline L.ρ) (hL' : IsPotentiallyCrystalline L'.ρ)
    (b : L' ≃ₗ[ℤ_[ℓ]] Dual ℤ_[ℓ] L)
    (hb : ∀ (g : Γ) (x : L') (y : L), b (L'.ρ g x) (L.ρ g y) = χ g • b x y)
    {m : ℕ} {V : DiscreteModule ℤ_[ℓ] Γ} [Finite V] {q : L →ₗ[ℤ_[ℓ]] V}
    (hq_equivariant : ∀ (g : Γ) (x : L), q (L.ρ g x) = V.ρ g (q x))
    (hq_surj : Surjective q) (hq_ker : q.toAddMonoidHom.ker = pPowMultiples L m)
    {H : AddSubgroup (Γ → L')} {S : AddSubgroup (Γ → V)}
    (h_crys_orth : ∀ z ∈ crysCocycles L.ρ, IsCupOrthogonal b m q H (q ∘ z))
    (hS_orth : ∀ s ∈ S, IsCupOrthogonal b m q H s) :
    ((crysCocycles L.ρ).toAddSubgroup.map (q.toAddMonoidHom.compLeft Γ)).relIndex S ∣
      H.relIndex (crysCocycles L'.ρ).toAddSubgroup := by
  -- Reduce `b` modulo `ℓᵐ` to identify `L' / ℓᵐ` with the dual of `V`. Local duality bounds
  -- `#Y^⊥ · #Y` for `Y` the reduction of `H ⊓ crysCocycles L'.ρ`, and `Y^⊥` contains `A ⊔ S`.
  have h_localGalois := isLocalGalois_of_isOpenEmbedding hj
  obtain ⟨r, hr, hr_ker, hr_surj⟩ : ∃ r : L' →+ V.cartierDual,
      (∀ (x : L') (y : L), r x (q y) = zmodPowToUnits m (Ideal.Quotient.mk _ (b x y))) ∧
        r.ker = pPowMultiples L' m ∧ Surjective r :=
    exists_dual_reduction b hq_surj hq_ker
  have hrL : ∀ (g : Γ) (x : L'), r (L'.ρ g x) = V.cartierDual.ρ g (r x) :=
    dual_reduction_equivariant b hb hq_equivariant hq_surj hr
  set A : AddSubgroup (Γ → V) :=
    (crysCocycles L.ρ).toAddSubgroup.map (q.toAddMonoidHom.compLeft Γ)
  let H' := H.addSubgroupOf (crysCocycles L'.ρ).toAddSubgroup
  let Y : AddSubgroup (Z1 V.cartierDual.ρ) := H'.map (hL'.reducedCocycle hj hrL hr_ker)
  -- The elements of `A ⊔ S` are cocycles that annihilate `Y`.
  have h_mem_annih {s : Γ → V} (hs : IsCupOrthogonal b m q H s) :
      s ∈ (pairingAnnihilator V.evalCup Y).map (Z1 V.ρ).toAddSubgroup.subtype := by
    obtain ⟨hs_mem, a, rfl, h_cup⟩ := hs
    refine ⟨⟨q ∘ a, hs_mem⟩, ?_, rfl⟩
    rintro _ ⟨c, hc, rfl⟩
    -- Up to sign, the cup product of `r ∘ c` and `q ∘ a` is the class of `cupModPow b m a c`.
    have h_mem : (fun x : Γ × Γ ↦ V.cartierDual.ρ x.fst (r (c.val x.snd)) (q (a x.fst))) ∈
        B2 (unitsRep.comp 𝒥.toGp) := by
      simp only [← hrL, hr]
      exact h_cup c hc
    exact neg_eq_zero.mp ((cupProduct_flip ..).symm.trans ((ker_mkQ _).ge h_mem))
  have h_sub : A ⊔ S ≤ (pairingAnnihilator V.evalCup Y).map (Z1 V.ρ).toAddSubgroup.subtype := by
    refine sup_le ?_ fun s hs ↦ h_mem_annih (hS_orth s hs)
    rintro _ ⟨z, hz, rfl⟩
    exact h_mem_annih (h_crys_orth z hz)
  have hA : Nat.card A = Nat.card (hL.reducedCocycle hj hq_equivariant hq_ker).range := by
    rw [← relIndex_ker, ← index_ker, AddMonoidHom.ker_codRestrict]
    rfl
  have h_sup : Nat.card ↥(A ⊔ S) = Nat.card A * A.relIndex S := by
    simp [← relIndex_bot_left, ← relIndex_mul_relIndex _ A _ bot_le le_sup_left]
  set N : ℕ := ((ℓ ^ m) ^ finrank ℤ_[ℓ] L) ^ (2 + 𝒥.toGp.range.index) with hN
  have h_key : Nat.card A * Nat.card Y * A.relIndex S ∣ N :=
    calc _ = Nat.card ↥(A ⊔ S) * Nat.card Y := by rw [h_sup, mul_right_comm]
      _ ∣ Nat.card (pairingAnnihilator V.evalCup Y) * Nat.card Y :=
          mul_dvd_mul_right ((card_dvd_of_le h_sub).trans (card_map_dvd ..)) _
      _ ∣ N := hL.card_pairingAnnihilator_mul_card_dvd hj hL' b hb hq_equivariant hq_surj hq_ker hr
          hr_surj hr_ker Y
  -- The same number counts the reductions of the crystalline cocycles of `L` and `L'`.
  have h_count : N ∣ Nat.card A * Nat.card Y * H'.index := by
    rw [hN, ← hL.card_range_reducedCocycle_mul hj hL' b hb hq_equivariant hq_ker hrL hr_ker, ← hA,
      mul_assoc]
    exact mul_dvd_mul_left _ (card_range_dvd_card_map_mul_index _ H')
  have h_ne : Nat.card A * Nat.card Y ≠ 0 :=
    left_ne_zero_of_mul (ne_zero_of_dvd_ne_zero (NeZero.ne N) h_key)
  exact (mul_dvd_mul_iff_left h_ne).mp (h_key.trans h_count)

end New

end CrystallineDuality

end
