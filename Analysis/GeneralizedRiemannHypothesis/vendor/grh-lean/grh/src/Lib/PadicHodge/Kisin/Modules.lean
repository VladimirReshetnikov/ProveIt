import Lib.ClassField.LocalDuality.CrystallineDuality
import Lib.PadicHodge.ArtinSchreierSequence
import Lib.PadicHodge.Kisin.KummerChartDeRham

/-!
# Kisin modules of Kummer charts: lattices with jump sets, letter projectors, invariant forms

For a Kummer chart `k : New.Lift.KummerChart Γ` there is a ring S ⊂ A_inf, the image of Λ⟦X⟧ with
Λ = W(𝔽_{p^f}), and a subgroup Γ' of Γ. Kisin modules are defined inside `L.Ambient = W(C^♭) ⊗ L`
for a lattice L with prescribed jump sets. The objects are functorial in L and compatible with
Frobenius and with Γ'. They split according to the letters `i ∈ 𝔽_{p^f}ˣ`, on which the root of
unity ζ of the coefficients acts as the Teichmüller lift `ω i = letterTeich i`.

## Main definitions and results

* `New.Lift.KummerChart.Letter`: the letters, the units i of 𝔽_{p^f}. For coefficients O with
  ζ^(p^f − 1) = 1 (`New.Lift.KummerChart.Coeffs`), the letter i cuts out the part
  `New.Lift.KummerChart.JumpLattice.letterPart` where ζ = [i].
* `New.Lift.KummerChart.JumpLattice`: a lattice L, crystalline over Γ', with a finite set
  `jumpSet i` of integers for each letter that holds its jumps at the embeddings above i.
* `New.Lift.KummerChart.JumpLattice.forms`: forms, A_inf-linear maps to B_dR that are Γ'-equivariant
  on 1 ⊗ L.
* `New.Lift.KummerChart.JumpLattice.kisinAinf`, `New.Lift.KummerChart.JumpLattice.kisinModule`,
  `New.Lift.KummerChart.JumpLattice.kisinLoc`: an A_inf-module cut out by forms, the Kisin module N,
  and N with all φ^a E inverted.
* `New.Lift.KummerChart.JumpLattice.mem_letterPart_iff_letterProj`,
  `New.Lift.KummerChart.JumpLattice.sum_letterProj`: `e i = letterProj i` projects onto the letter
  `i`, and the `e i` sum to the identity.
* `New.Lift.KummerChart.JumpLattice.exists_span_formsOfType_mod_pred`: the functionals of type `u`
  at `i`, modulo those of type `u - 1`, are spanned over Q̄_p by at most `L.jumpMultiplicity i u` of
  them.
* `New.Lift.KummerChart.JumpLattice.formsOfType_subset_pred_of_notMem`: if `n ∉ L.jumpSet i`, the
  functionals of type `n` at `i` are of type `n - 1`.

Notions from other files:
* `New.Lift.KummerChart`: a chart Λ⟦X⟧ → A_inf (ring `S`, element `E` generating ker θ,
  `frobE a` = φ^a(E)) together with a subgroup Γ' of Γ whose fixed field it belongs to.
* `New.Lift.GalLattice`: a finite free O-module with an O-linear representation of Γ.
* `New.Period.WittCFlat`: the ring W(C^♭) of p-typical Witt vectors over the fraction field C^♭ of
  the tilt O^♭ of the ring of integers of C_p.
* `New.Period.overZp`: a representation of Γ on a module T over a Z_p-algebra R, regarded as a
  Z_p-linear representation.
* `New.Period.jump`: the multiplicity of a Hodge–Tate jump u of a representation at an embedding γ
  of the coefficients into ℂ_p.

## Relation to the literature

Known result: Hodge–Tate weights of Kisin modules. This is the analogue, for the Kisin module of one
Kummer chart inside A_inf, of the statements on Wach modules in the literature. This file proves
only the bounds on the weights, not that the Galois action is trivial modulo the variable. It holds
per unramified embedding of the coefficients, and it gives only upper bounds by the multiplicity of
each jump.
Source: L. Berger, Limites de représentations cristallines, Compositio Math. 140 (2004), 1473–1498,
§III; N. Wach, Représentations p-adiques potentiellement cristallines, Bull. SMF 124 (1996),
375–400.

See also `Lib.PadicHodge.Kisin.PeriodMatrixFrame`.
-/

noncomputable section

/-!
## Letters, lattices with jump sets, forms and Kisin modules

* `New.Lift.saturateBy`: the saturation of a submodule P by a submonoid M, the x with mx in P for
  some m in M.
* `New.Lift.KummerChart.Letter`, `New.Lift.KummerChart.Coeffs`,
  `New.Lift.KummerChart.JumpLattice`: the letters, rings of coefficients with a root ζ, and
  lattices with jump sets.
* `New.Lift.KummerChart.JumpLattice.letterOp`, `letterPart`, `letterProj`: the operator ω(i)⁻¹ζ,
  the part at the letter i, and the projector onto it.

Conventions: `New.Lift.FrobGroup Γ` = ℤ × Γ acts on W(C^♭) ⊗ L, with φ the Frobenius;
`DiagTensor.mk 1 t` is 1 ⊗ t; `hodgeFil n` is tⁿB_dR^+; E is an element of S, a generator of ker θ,
and `k.frobE a` is φ^a E.
-/

namespace New.Lift

open Period WittVector Submodule Set FrobGroup Module Fintype Algebra

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p] [k : KummerChart Γ]
  {R X : Type*} [CommRing R] [AddCommGroup X] [Module R X] {Q : Submodule R X}

/-- The actions of ℤ_p and of A_inf on W(C^♭) commute. -/
instance : SMulCommClass ℤ_[p] Ainf WittCFlat := inferInstance

/-! ### Saturation of a submodule -/

/-- The saturation of a submodule P of X by a submonoid M: the x in X with mx in P for some m in
M. -/
def saturateBy (M : Submonoid R) (P : Submodule R X) : Submodule R X :=
  -- the preimage of the `M`-torsion of `X ⧸ P`, with its carrier written out
  ((torsion' R (X ⧸ P) M).comap P.mkQ).copy {x : X | ∃ r ∈ M, r • x ∈ P}
    (by simp [← Quotient.mk_smul])

lemma mem_saturateBy_of_mem {M : Submonoid R} {x : X} (hx : x ∈ Q) : x ∈ saturateBy M Q :=
  ⟨1, one_mem M, by simpa using hx⟩

/-- If `r` divides an element `s` of `M` and `r • x` lies in the saturation of `Q` by `M`, then
so does `x`. -/
lemma mem_saturateBy_of_smul {M : Submonoid R} {r s : R} {x : X} (hrs : r ∣ s) (hs : s ∈ M)
    (hx : r • x ∈ saturateBy M Q) : x ∈ saturateBy M Q := by
  obtain ⟨c, rfl⟩ := hrs
  obtain ⟨a, ha, hax⟩ : ∃ a ∈ M, a • r • x ∈ Q := hx
  -- `(a * (r * c)) • x = c • a • r • x`
  exact ⟨a * (r * c), mul_mem ha hs, by simpa [mul_smul, smul_comm c] using smul_mem Q c hax⟩

/-- Induction on the saturation by the monoid generated by the f(a): a property that holds on Q
and passes from f(a)·x to x holds on all of the saturation. -/
@[elab_as_elim]
lemma saturateBy_induction {ι : Sort*} {x : X} {f : ι → R} {C : X → Prop}
    (hx : x ∈ saturateBy (Submonoid.closure (range f)) Q) (h₀ : ∀ x ∈ Q, C x)
    (h₁ : ∀ (a : ι) (x : X), C (f a • x) → C x) : C x := by
  obtain ⟨r, hr, hrx⟩ : ∃ r ∈ Submonoid.closure (range f), r • x ∈ Q := hx
  -- Induction on the number of factors `f a` in `r`, where `r • x ∈ Q`.
  induction hr using Submonoid.closure_induction_right generalizing x with
  | one => exact h₀ x (by simpa using hrx)
  | mul_right r _ s hs ih =>
    obtain ⟨a, rfl⟩ := hs
    exact h₁ a x (ih (by simpa [mul_smul] using hrx))

namespace KummerChart

/-! ### Letters, coefficients and lattices with jump sets -/

/-- The letters of a Kummer chart: the multiplicative group of the field with p^f elements in
O^♭. A letter i singles out the embeddings g of a ring of coefficients into ℂ_p with g(ζ) = θ([i]),
[i] the Teichmüller lift; these are the embeddings above i, and φ^a sends [i] to [i^(p^a)]. -/
def Letter : Type := (flatFq k.f)ˣ
  deriving CommGroup, Finite, IsCyclic

/-- The letters form a finite type. -/
instance : Fintype Letter := .ofFinite _

/-- The number `p ^ f - 1` of letters is invertible in `ℤ_[p]`, being a unit modulo `p`. -/
instance : Invertible (card Letter : ℤ_[p]) :=
  IsUnit.invertible <| .of_map PadicInt.toZMod _ <| by
    simp [↓card_eq_nat_card, Letter, Nat.card_units, NeZero.pos, ZMod.natCast_self]

/-- The permutation i ↦ i^p of the letters, the units of the field with p^f elements. -/
def letterFrob : Equiv.Perm Letter :=
  (Units.mapEquiv (frobeniusEquiv (flatFq k.f) p).toMulEquiv).toEquiv

/-- The multiplicative map sending a letter to its Teichmüller lift in the Witt vectors of the
field with p^f elements, viewed in the ring S of the chart. -/
def letterTeich : Letter →* k.S :=
  (algebraMap (WittFq k.f) k.S).toMonoidHom.comp ((teichmuller p).comp (Units.coeHom (flatFq k.f)))

/-- The elements ζ of O with ζ^q = 1, where q = p^f − 1 is the number of letters of the chart. -/
abbrev LetterRoot (O : Type*) [Monoid O] : Type _ := {ζ : O // ζ ^ Nat.card Letter = 1}

/-- A ring of coefficients: a finite free Z_p-algebra O with an element ζ, ζ^{p^f−1} = 1, which
cuts out the letters. -/
structure Coeffs where
  /-- The ring of coefficients O. -/
  (O : Type)
  /-- O is a commutative ring. -/
  [commRing : CommRing O]
  /-- O is a ℤ_p-algebra. -/
  [padicIntegerRing : PadicIntegerRing O p]
  /-- An element ζ of O with ζ^(p^f − 1) = 1. -/
  ζ : LetterRoot O

attribute [instance] Coeffs.commRing Coeffs.padicIntegerRing

-- A ring of coefficients is read as its underlying type.
instance : CoeSort Coeffs Type := ⟨Coeffs.O⟩

/-- A lattice with jump sets: a finite free O-module with an action of Γ, crystalline over Γ', with,
for each letter i, a finite set of integers that contains its jumps at every embedding g of O with
g(ζ) = θ(ω(i)). -/
structure JumpLattice (O : Coeffs) extends toGalLattice : GalLattice O Γ where
  /-- For each letter, a finite set of integers that holds the jumps at that letter. -/
  jumpSet : Letter → Finset ℤ
  /-- One set of integers for each embedding of O. -/
  embJumps : (O →ₐ[ℤ_[p]] ℂ_[p]) → Finset ℤ
  /-- The lattice is crystalline over Γ' and has its jumps at each embedding in the set given for
  that embedding. -/
  inClass : InClass (Filter.map k.subgroup.subtype ⊤) ⊥ embJumps toGalLattice
  /-- The set at a letter i contains the set of every embedding g with g(ζ) = θ(ω(i)). -/
  embJumps_subset {g : O →ₐ[ℤ_[p]] ℂ_[p]} {i : Letter} :
      g O.ζ = (theta (k.letterTeich i)).1 → embJumps g ⊆ jumpSet i

variable {k} {O : Coeffs} {L : JumpLattice O} (L' : JumpLattice O) (i : Letter) (l a : ℕ) (u : ℤ)

/-- The letter a steps before i: the image of i under the a-th power of the inverse of the
permutation x ↦ x^p, so that φ^a sends its Teichmüller lift to that of i. -/
@[simp]
abbrev Letter.stepBack : Letter := (k.letterFrob ^ a)⁻¹ i

/-- The standard exponent at the step `a` for the level `l` and the weight `u`: `0` for `a < l`
and `-u` for `a ≥ l`. -/
@[grind]
def stdOrders : ℤ := if a < l then 0 else -u

namespace JumpLattice

/-! ### Forms and the Kisin module -/

/-- The module W(C^♭)⊗L for the lattice underlying L. -/
abbrev Ambient : Type := DiagTensor (Rep.of (overZp L.ρ))

/-- For an O-linear map F: L → L' of lattices, the W(C^♭)-linear map W(C^♭) ⊗ L → W(C^♭) ⊗ L'
obtained by extension of scalars. -/
abbrev wittMap (F : L.Carrier →ₗ[O] L'.Carrier) : L.Ambient →ₗ[WittCFlat] L'.Ambient :=
  DiagTensor.map F

/-- The A_inf-submodule of W(C^♭) ⊗ L spanned by the elements 1 ⊗ y, y in L. -/
def ainfLattice : Submodule Ainf L.Ambient := span Ainf (M := L.Ambient) (range (DiagTensor.mk 1))

/-- The type of A_inf-linear maps from W(C^♭) ⊗ L to B_dR. -/
abbrev Functional : Type := L.Ambient →ₗ[Ainf] BdR

/-- The set of A_inf-linear maps μ: W(C^♭) ⊗ L → B_dR that are Γ'-equivariant on 1 ⊗ L, that is,
μ(1 ⊗ gt) = g·μ(1 ⊗ t). -/
def forms : Set L.Functional :=
  {μ : L.Functional | ∀ (t : L.Carrier) (g : k.subgroup),
    μ (DiagTensor.mk 1 (L.ρ g t)) = toGp g.val • μ (DiagTensor.mk 1 t)}

/-- The action of m ∈ ℤ × Γ on W(C^♭) ⊗ L is semilinear: m • (r • x) = (m • r) • (m • x). -/
lemma frobGroup_smul_smul (m : FrobGroup Γ) (r : Ainf) (x : L.Ambient) :
    m • r • x = (m • r) • m • x := smul_distrib_smul m r x

/-- The action of an element m of ℤ × Γ on W(C^♭) ⊗ L, as a map semilinear for the action of m
on A_inf. -/
@[simps]
def semilinearAct (m : FrobGroup Γ) :
    L.Ambient →ₛₗ[MulSemiringAction.toRingHom (FrobGroup Γ) Ainf m] L.Ambient where
  toFun x := m • x
  map_add' := smul_add m
  map_smul' := frobGroup_smul_smul m

/-- The A_inf-module of the x in A_inf[1/τ] ⊗ L (some power of the element `tau` of A_inf sends x
into the A_inf-span of the 1 ⊗ y, y in L) with μ(φ^n x) in B_dR^+ for all n ≥ 1 and all μ in
`New.Lift.KummerChart.JumpLattice.forms`. -/
def kisinAinf : Submodule Ainf L.Ambient :=
  saturateBy (Submonoid.powers tau) L.ainfLattice ⊓
    { carrier := {x : Ambient | ∀ n : ℕ, ∀ μ ∈ L.forms, μ (φ ^ (n + 1) • x) ∈ hodgeFil 0}
      add_mem' := by aesop
      zero_mem' := by simp
      smul_mem' := by simp_all [frobGroup_smul_smul, smul_of_tower_mem] }

/-- The invariant functionals μ (`New.Lift.KummerChart.JumpLattice.forms`) whose restriction to
1 ⊗ L comes from a Z_p-linear map of L into the period ring `Bmax`. -/
def crysForms : Set L.Functional :=
  {μ ∈ L.forms | ∃ l : L.Carrier →ₗ[ℤ_[p]] Bmax, ∀ t : Rep.of (overZp L.ρ),
    μ (DiagTensor.mk 1 t) = algebraMap Bmax BdR (l t)}

/-- For an A_inf-submodule Q of W(C^♭) ⊗ L, the S-submodule of the x in Q on which every form in
`New.Lift.KummerChart.JumpLattice.forms` takes values in the field 𝒦₀ = `valueField 0`, a subfield
of B_dR that contains the image of S. -/
def valueFieldPoints (Q : Submodule Ainf L.Ambient) : Submodule k.S L.Ambient where
  carrier := {x ∈ Q | ∀ μ ∈ L.forms, μ x ∈ valueField 0}
  add_mem' := by aesop
  zero_mem' := by simp
  smul_mem' s x hx := by
    obtain ⟨hx_mem, hx_val⟩ := hx
    refine ⟨smul_mem _ _ hx_mem, fun μ hμ ↦ ?_⟩
    -- `μ (s • x)` is the product of the image of `s` and `μ x`, both in `valueField 0`
    simpa [phiInvToBdR, smul_def', IsScalarTower.algebraMap_apply k.S Ainf BdR] using
      mul_mem (phiInvToBdR_mem_valueField s) (hx_val μ hμ)

/-- The Kisin module of L: the S-module of the x in `New.Lift.KummerChart.JumpLattice.kisinAinf` on
which all Γ'-equivariant forms take values in the field 𝒦₀ (`New.Lift.KummerChart.valueField`). -/
abbrev kisinModule : Submodule k.S L.Ambient := valueFieldPoints L.kisinAinf

/-- The image of `New.Lift.KummerChart.JumpLattice.kisinAinf` under φ^l. It is the A_inf-submodule
of the x in W(C^♭)⊗L with φ^{−l}x in `New.Lift.KummerChart.JumpLattice.kisinAinf`. -/
def frobKisinAinf : Submodule Ainf L.Ambient := L.kisinAinf.comap (semilinearAct (φ ^ l)⁻¹)

/-- The x in W(C^♭) ⊗ L that some product of the φ^a E multiplies into
`New.Lift.KummerChart.JumpLattice.kisinAinf`. -/
def kisinLocAinf : Submodule Ainf L.Ambient :=
  saturateBy (Submonoid.closure (range fun a ↦ (k.frobE a).1)) L.kisinAinf

/-- The Kisin module N with all φ^a E inverted: the x in
`New.Lift.KummerChart.JumpLattice.kisinLocAinf` on which all forms take values in the field 𝒦₀. -/
def kisinLoc : Submodule k.S L.Ambient := L.valueFieldPoints kisinLocAinf

/-! ### Equivariant maps -/

/-- A Γ-equivariant O-linear map L → L' between lattices over the same coefficients O. -/
abbrev Hom : Type := L.ρ.IntertwiningMap L'.ρ

/-- For an equivariant map F : L → L', the W(C^♭)-linear map W(C^♭)⊗L → W(C^♭)⊗L' obtained by
extension of scalars. -/
abbrev Hom.wittMap {L' : JumpLattice O} (F : L.Hom L') : L.Ambient →ₗ[WittCFlat] L'.Ambient :=
  L.wittMap L' F.toLinearMap

/-- Scalar multiplication on L by the root of unity ζ of the coefficient ring O, as an
equivariant map from L to itself. -/
def mulZeta : L.Hom L := ⟨LinearMap.lsmul O L.Carrier O.ζ, by aesop⟩

/-- The endomorphism ω(i)⁻¹ζ of W(C^♭) ⊗ L, with ζ acting through L and ω(i), the Teichmüller
lift of the letter i, as a scalar. -/
def letterOp : L.Ambient →ₗ[WittCFlat] L.Ambient := k.letterTeich i⁻¹ • L.mulZeta.wittMap

/-- The part of W(C^♭) ⊗ L at the letter i: the A_inf-submodule on which ζ acts as the
Teichmüller lift ω(i). -/
def letterPart : Submodule Ainf L.Ambient := (L.letterOp i - 1).ker.restrictScalars Ainf

/-- The endomorphism q⁻¹ Σ_{n<q} (ω(i)⁻¹ζ)^n of W(C^♭) ⊗ L, q = p^f − 1; as ζ^q = 1 it
projects to the part at the letter i. -/
def letterProj : L.Ambient →ₗ[WittCFlat] L.Ambient :=
  ⅟(card Letter : ℤ_[p]) • ∑ n ∈ Finset.range (card Letter), L.letterOp i ^ n

/-- The A_inf-linear μ: W(C^♭) ⊗ L → B_dR that are Γ'-equivariant on 1 ⊗ L and send the
projection of 1 ⊗ L to the letter i into t^{−u}B_dR^+. -/
def formsOfType : Set L.Functional :=
  {μ ∈ L.forms | ∀ t : Rep.of (overZp L.ρ), μ (L.letterProj i (DiagTensor.mk 1 t)) ∈ hodgeFil (-u)}

open scoped Classical in
/-- The total multiplicity of the Hodge–Tate jump u of L over all embeddings γ of O in ℂ_p above
the letter i, that is, with γ(ζ) = θ(ω(i)). -/
abbrev jumpMultiplicity : ℕ :=
  ∑ γ : O.O →ₐ[ℤ_[p]] ℂ_[p] with γ O.ζ = ↑(theta (k.letterTeich i)), jump L.ρ γ u

/-- The x in W(C^♭) ⊗ L that some non-zero divisor of A_inf multiplies into the A_inf-span of
the elements 1 ⊗ y, y in L. -/
abbrev fracSpan : Submodule Ainf L.Ambient := saturateBy (nonZeroDivisors Ainf) L.ainfLattice

/-- The least natural number a such that all Hodge–Tate jumps of L, as a Z_p-representation of
Γ', lie in [−a, a]; it is 0 if there is none. -/
def jumpBound : ℕ :=
  sInf {a : ℕ | ∀ u : ℤ,
    jump ((overZp L.ρ).comp k.subgroup.subtype) (ofId ℤ_[p] ℂ_[p]) u ≠ 0 → -a ≤ u ∧ u ≤ a}

/-- For an A_inf-linear μ: W(C^♭) ⊗ L → B_dR, the map μ ∘ φ^{−a}, semilinear for φ^{−a}: A_inf →
B_dR. -/
def valueAt (μ : L.Functional) : L.Ambient →ₛₗ[phiInvToBdR a] BdR where
  toAddHom := μ.toAddHom.comp (semilinearAct (φ ^ a)⁻¹).toAddHom
  map_smul' := by simp [phiInvToBdR, smul_def']

end JumpLattice

end KummerChart

end New.Lift

/-!
## Letter projectors, functoriality, and forms of a given type

A functional is an `A_inf`-linear map `L.Ambient → B_dR`. It is invariant (`forms`) if it is
`Γ'`-equivariant on `1 ⊗ L`. It is of type `u` at `i` (`formsOfType`) if moreover it maps
`letterProj i (1 ⊗ L)` into `t ^ (-u) B_dR⁺`.
-/

namespace New.Lift.KummerChart.JumpLattice

open Period WittVector Submodule Set FrobGroup Module RingHom Finset Algebra

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p]
  {k : KummerChart Γ} {O : Coeffs} {L L' : JumpLattice O} {l a b : ℕ} {i i' : Letter} {n : ℤ}
  {x : L.Ambient} (g : k.galMonoid) (F : L.Hom L') (m : FrobGroup Γ) {μ : L.Functional}

/-- The map `W(C^♭) ⊗ L → W(C^♭) ⊗ L'` induced by an equivariant `F` commutes with the action of
`m` in ℤ × Γ. -/
@[simp] lemma Hom.wittMap_smul (x : L.Ambient) : F.wittMap (m • x) = m • F.wittMap x := by
  induction x using DiagTensor.induction with
  | h_mk a t => simp [F.isIntertwining]
  | h_add x y hx hy => simp [hx, hy]

/-- The map induced by an O-linear `F : L → L'` sends the A_inf-span of the `1 ⊗ y`, y in L, into
the corresponding span for L'. -/
lemma wittMap_mem_ainfLattice (F : L.Carrier →ₗ[O.O] L'.Carrier) :
    x ∈ L.ainfLattice → L.wittMap L' F x ∈ L'.ainfLattice := fun hx ↦
  mapsTo_span (f := (L.wittMap L' F).restrictScalars Ainf) (by simp) hx

/-- Composing an invariant functional on `L'` with the map induced by `F` gives an invariant
functional on `L`. -/
lemma Hom.comp_wittMap_mem_forms {μ : L'.Functional} :
    μ ∈ L'.forms → μ ∘ₗ F.wittMap ∈ L.forms := by
  intro hμ t g
  -- `F.wittMap (1 ⊗ t) = 1 ⊗ F t`, and `F` commutes with `ρ g`.
  simpa [F.isIntertwining] using hμ (F t) g

/-- Let `F : L → L'` be an equivariant map of lattices with jump sets, and let
`F.wittMap : W(C^♭) ⊗ L → W(C^♭) ⊗ L'` be its extension of scalars. Then `F.wittMap` sends
`L.kisinAinf` into `L'.kisinAinf`. Here `kisinAinf` is the A_inf-module of those x in A_inf[1/τ] ⊗ L
with μ(φ^n x) ∈ B_dR^+ for all n ≥ 1 and all μ in `forms`. -/
lemma Hom.wittMap_mem_kisinAinf : x ∈ L.kisinAinf → F.wittMap x ∈ L'.kisinAinf := by
  rintro ⟨⟨r, hr, hrx⟩, h_fil⟩
  -- `F.wittMap` commutes with `r` and maps the lattice of `L` into that of `L'`.
  have h_lattice : r • F.wittMap x ∈ L'.ainfLattice := by
    simpa using wittMap_mem_ainfLattice F.toLinearMap hrx
  refine ⟨⟨r, hr, h_lattice⟩, fun n μ hμ ↦ ?_⟩
  -- `F.wittMap` commutes with `φ`, and `μ ∘ F.wittMap` is again invariant
  simpa [F.wittMap_smul] using h_fil n _ (F.comp_wittMap_mem_forms hμ)

/-- The map induced by an equivariant `F : L → L'` sends the Kisin module of L into that of L'. -/
lemma Hom.wittMap_mem_kisinModule (hx : x ∈ L.kisinModule) : F.wittMap x ∈ L'.kisinModule := by
  obtain ⟨hx_ainf, hx_value⟩ := hx
  exact ⟨F.wittMap_mem_kisinAinf hx_ainf, fun μ hμ ↦ hx_value _ (F.comp_wittMap_mem_forms hμ)⟩

/-- The map induced by an equivariant `F : L → L'` sends `L.frobKisinAinf l`, the image of
`L.kisinAinf` under φ^l, into `L'.frobKisinAinf l`. -/
lemma Hom.wittMap_mem_frobKisinAinf :
    x ∈ L.frobKisinAinf l → F.wittMap x ∈ L'.frobKisinAinf l := fun hx ↦ by
  simpa [frobKisinAinf] using F.wittMap_mem_kisinAinf hx

/-! ### The projectors to the letters -/

/-- The n-th power of `letterOp i`, that is of ω(i)⁻¹ζ, on a pure tensor `a ⊗ t`. -/
@[simp]
lemma letterOp_pow_mk (n : ℕ) (a : WittCFlat) (t : Rep.of (overZp L.ρ)) :
    (L.letterOp i ^ n) (no_index (DiagTensor.mk a t)) =
      k.letterTeich i⁻¹ ^ n • .mk a (O.ζ.val ^ n • t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    simp [letterOp, pow_succ', mulZeta, smul_smul, mul_comm]

/-- x lies in the part at the letter i exactly when ζ acts on it as the Teichmüller lift ω(i). -/
lemma mem_letterPart_iff_mulZeta :
    x ∈ letterPart i ↔ L.mulZeta.wittMap x = k.letterTeich i • x :=
  sub_eq_zero.trans (inv_smul_eq_iff (g := k.letterTeich.toHomUnits i))

/-- The ring S of the chart acts on W(C^♭) ⊗ L through its inclusion in A_inf. -/
lemma smul_eq_val_smul (s : k.S) : s • x = s.val • x := rfl

/-- The map induced by an equivariant `F : L → L'` commutes with the projectors to the letter i. -/
@[simp] lemma Hom.wittMap_letterProj (x : L.Ambient) :
    F.wittMap (L.letterProj i x) = L'.letterProj i (F.wittMap x) := by
  induction x using DiagTensor.induction with
  | h_mk a t => simp [letterProj]
  | h_add x y hx hy => simp [hx, hy]

/-- If `m` in ℤ × Γ sends ω(i)⁻¹ to ω(i')⁻¹, it carries the projector to the letter i into the
projector to the letter i'. -/
lemma smul_letterProj {m : FrobGroup Γ}
    (h_teich : m • (k.letterTeich i⁻¹).val = k.letterTeich i'⁻¹) (x : L.Ambient) :
    m • L.letterProj i x = L.letterProj i' (m • x) := by
  induction x using DiagTensor.induction with
  | h_mk a t => simp [letterProj, smul_comm m, smul_sum, smul_eq_val_smul, h_teich,
    frobGroup_smul_smul]
  | h_add x y hx hy => simp [hx, hy]

/-- An element `g` of the Galois monoid of the chart commutes with the projector to each letter. -/
lemma gal_smul_letterProj (x : L.Ambient) :
    g.val • L.letterProj i x = L.letterProj i (g.val • x) := by
  -- `g` comes from `Γ'`, which fixes the Teichmüller lift `letterTeich i⁻¹`
  obtain ⟨γ, hγ⟩ := g.property
  refine smul_letterProj ?_ x
  rw [← hγ]
  exact (fixes γ).1 _

/-- φ^l sends ω(i)⁻¹ to ω(j)⁻¹, where j is the image of i under the l-th power of i ↦ i^p. -/
lemma phi_pow_smul_letterTeich :
    φ ^ l • (k.letterTeich i⁻¹).val = k.letterTeich ((k.letterFrob ^ l) i)⁻¹ := by
  -- `φ ^ l` raises the Teichmüller lift `letterTeich i⁻¹` to the power `p ^ l`, as `letterFrob ^ l`
  -- does with `i`. We use `erw`, as `frobEnd` is `x ↦ x ^ p` only up to unfolding.
  erw [phi_pow_smul, k.letterFrob.coe_pow, pow_iterate, map_pow, k.S.coe_pow, Subtype.coe_mk,
    map_teichmuller]
  simp

/-- The projector to the letter i takes values in the part at the letter i. -/
lemma letterProj_mem_letterPart : L.letterProj i x ∈ letterPart i := by
  -- Let `q` be the order of `k.Letter`. The geometric sum gives
  -- `(letterOp i - 1) * ∑ n < q, letterOp i ^ n = letterOp i ^ q - 1`, and `letterOp i ^ q = 1`
  -- because `ζ ^ q = 1` and `i⁻¹ ^ q = 1`.
  have hζ : O.ζ.val ^ Fintype.card k.Letter = 1 := by simpa using O.ζ.property
  have h_order (y : L.Ambient) : (L.letterOp i ^ Fintype.card k.Letter) y = y := by
    induction y using DiagTensor.induction with
    | h_mk a t => simp [← map_pow, hζ, map_one]
    | h_add y z hy hz => rw [map_add, hy, hz]
  change ((L.letterOp i - 1) * L.letterProj i) x = 0
  simp [letterProj, mul_geom_sum, h_order]

/-- x lies in the part at the letter i exactly when the projector to i fixes it. -/
lemma mem_letterPart_iff_letterProj : x ∈ letterPart i ↔ L.letterProj i x = x := by
  constructor
  · -- if `letterOp i` fixes `x`, so do its powers, and `letterProj i` is their average
    intro hx
    simp_all [letterProj, End.pow_apply, letterPart, Function.iterate_fixed, sub_eq_zero,
      invOf_smul_eq_iff, Nat.cast_smul_eq_nsmul]
  · intro h_fixed
    simpa [h_fixed] using (letterProj_mem_letterPart : L.letterProj i x ∈ letterPart i)

/-- The part at each letter is stable under the Galois monoid of the chart, in both directions. -/
lemma gal_smul_mem_letterPart : g • x ∈ letterPart i ↔ x ∈ letterPart i := by
  simp [mem_letterPart_iff_letterProj, k.galMonoid.smul_def, ← gal_smul_letterProj,
    smul_left_cancel_iff]

/-- `φ ^ a • x` lies in the part at the letter i exactly when x lies in the part at `i.stepBack a`,
the letter whose `p ^ a`-th power is i. -/
lemma phi_pow_smul_mem_letterPart_iff :
    φ ^ a • x ∈ letterPart i ↔ x ∈ letterPart (i.stepBack a) := by
  have h_comm (y : L.Ambient) :
      φ ^ a • L.letterProj (i.stepBack a) y = L.letterProj i (φ ^ a • y) := by
    simpa using smul_letterProj (phi_pow_smul_letterTeich (l := a) (i := i.stepBack a)) y
  simp [mem_letterPart_iff_letterProj, ← h_comm, smul_left_cancel_iff]

/-! ### Small facts on the Kisin module and the constants -/

lemma frobKisinAinf_zero : L.frobKisinAinf 0 = L.kisinAinf := by
  simp [frobKisinAinf, Submodule.ext_iff]

/-- The unit `frobEUnit a` acts by the element φ^a E of S, also on powers. -/
lemma frobEUnit_pow_smul (n : ℕ) : k.frobEUnit a ^ n • x = (k.frobE a).val ^ n • x := by
  simp [Units.smul_def, frobEUnit, ← map_pow]

omit Γ in
/-- The Witt vectors of the field with p^f elements have rank f over ℤ_p. -/
lemma finrank_wittFq {f : ℕ+} : Module.finrank ℤ_[p] (WittFq f) = f := by
  -- Count the quotient modulo `p` in two ways: it has `p ^ finrank` elements, and it is the
  -- residue field `flatFq f`, which has `p ^ f` elements.
  have h_ideal : pPowMultiples (WittFq f) 1 = (Ideal.span {(p : WittFq f)}).toAddSubgroup :=
    AddSubgroup.ext fun y ↦ by simp [mem_span_singleton, mul_comm, Nat.cast_smul_eq_nsmul]
  have h_index : (pPowMultiples (WittFq f) 1).index = Nat.card (flatFq f) :=
    (congrArg AddSubgroup.index h_ideal).trans (Nat.card_congr quotientPEquiv.toEquiv)
  simpa [Nat.pow_right_inj Fact.out] using h_index

lemma zTauUnit_smul : k.zTauUnit • x = k.zTau • x := (rfl)

@[simp]
lemma frobEUnit_smul : k.frobEUnit a • x = (k.frobE a).val • x := (rfl)

/-- The B_dR-linear map sending μ: W(C^♭) ⊗ L → B_dR to the vector of its values μ(1 ⊗ e_l) on a
chosen Z_p-basis (e_l) of L. -/
noncomputable def basisValues : L.Functional →ₗ[BdR] Fin (Module.finrank ℤ_[p] L.Carrier) → BdR :=
  LinearMap.pi fun l ↦ LinearMap.applyₗ' BdR
    (DiagTensor.mk 1 (finBasis ℤ_[p] (Rep.of (overZp L.ρ)) l))

/-- The A_inf-span of the `1 ⊗ y`, y in L, is spanned by the `1 ⊗ e_l` for the chosen ℤ_p-basis
(e_l) of L. -/
lemma ainfLattice_eq_span_basis :
    L.ainfLattice = span Ainf
      (Set.range (DiagTensor.mk 1 ∘ finBasis ℤ_[p] (Rep.of (overZp L.ρ)))) := by
  -- the vectors `1 ⊗ t` are the `ℤ_[p]`-span of those with `t` in the basis
  rw [← span_span_of_tower ℤ_[p], range_comp, ← map_span, Module.Basis.span_eq, Submodule.map_top,
    LinearMap.coe_range]
  rfl

/-! ### Invariant functionals and their conjugates -/

/-- Two functionals that agree on `1 ⊗ L` agree on `L.fracSpan`, since `B_dR` is torsion-free over
`A_inf`. -/
lemma apply_eq_of_mem_fracSpan (f f' : L.Functional) (h_values : basisValues f = basisValues f') :
    x ∈ L.fracSpan → f x = f' x := by
  rintro ⟨r, hr, hrx⟩
  -- `f` and `f'` agree on the span of the `1 ⊗ e_l`, which contains `r • x`.
  have h_eqOn : Set.EqOn f f'
      (Set.range (DiagTensor.mk 1 ∘ finBasis ℤ_[p] (Rep.of (overZp L.ρ)))) := by
    simpa [basisValues, funext_iff] using h_values
  have h_smul : f (r • x) = f' (r • x) := f.eqOn_span h_eqOn (ainfLattice_eq_span_basis.le hrx)
  simpa [smul_right_inj, show r ≠ 0 by simpa using hr] using h_smul

/-- An element g of Γ, embedded in ℤ × Γ, acts on A_inf through `toGp g`. -/
@[simp]
lemma inr_smul {r : Ainf} (g : Γ) : inr g • r = toGp g • r := rfl

/-- The conjugate of an A_inf-linear map μ: W(C^♭) ⊗ L → B_dR by g in Γ, namely
x ↦ (toGp g)⁻¹ · μ(g x). -/
@[simps]
noncomputable def conjForm (μ : L.Functional) (g : Γ) : L.Functional :=
  ⟨⟨fun x ↦ (toGp g)⁻¹ • μ (inr g • x), by simp⟩, by simp [smul_distrib_smul]⟩

/-- An invariant functional commutes with `Γ'` on all of `L.fracSpan`. -/
lemma form_gal_smul (hμ : μ ∈ L.forms) (hx : x ∈ L.fracSpan) : μ (g • x) = g • μ x := by
  obtain ⟨_, γ, rfl⟩ := g
  -- `conjForm μ γ` and `μ` agree on `1 ⊗ L` by invariance, hence on `L.fracSpan`.
  have h_values : basisValues (conjForm μ γ) = basisValues μ := by
    funext l
    simp [basisValues, hμ _]
  have h_conj : conjForm μ γ x = μ x := apply_eq_of_mem_fracSpan _ _ h_values hx
  exact inv_smul_eq_iff.1 h_conj

/-- The A_inf-span of the `1 ⊗ y`, y in L, is stable under ℤ × Γ. -/
lemma smul_mem_ainfLattice : x ∈ L.ainfLattice → m • x ∈ L.ainfLattice := fun hx ↦
  mapsTo_span (f := semilinearAct m) (by simp) hx

/-- `L.fracSpan` is stable under ℤ × Γ: if r x lies in the lattice, so does (m r)(m x). -/
lemma smul_mem_fracSpan : x ∈ L.fracSpan → m • x ∈ L.fracSpan := by
  rintro ⟨r, hr, hrx⟩
  refine ⟨m • r, ?_, ?_⟩
  · -- `m` acts on A_inf by a ring automorphism, so it keeps non-zero divisors.
    simpa [smul_eq_zero_iff_eq] using hr
  · -- `(m • r) • (m • x) = m • (r • x)`, and `r • x` lies in the lattice.
    rw [← frobGroup_smul_smul]
    exact smul_mem_ainfLattice m hrx

/-- `valueAt a μ`, which is μ ∘ φ^{-a}, turns the action of the n-th power of the unit φ^b E into
multiplication by the n-th power (n ∈ ℤ) of its image `phiInvToBdR a (frobE b)` in B_dR under
φ^{-a}. -/
lemma valueAt_frobEUnit_zpow_smul :
    ∀ x : L.Ambient,
      valueAt a μ (k.frobEUnit b ^ n • x) = phiInvToBdR a (k.frobE b) ^ n * valueAt a μ x := by
  -- Replace `x` by `frobEUnit b ^ (-n).toNat • x`, so that only natural powers of `frobEUnit b`
  -- remain.
  refine (MulAction.surjective (k.frobEUnit b ^ (-n).toNat)).forall.2 ?_
  cases n with
  | ofNat n => simp [frobEUnit_pow_smul]
  | negSucc n =>
    -- `↓`: `smul_smul` must join the unit and its inverse before `frobEUnit_pow_smul` applies.
    simp [↓smul_smul, frobEUnit_pow_smul]

lemma mk_one_mem_ainfLattice (t : Rep.of (overZp L.ρ)) : no_index (.mk 1 t) ∈ L.ainfLattice :=
  subset_span ⟨t, rfl⟩

/-- The projection of `1 ⊗ t` to a letter stays in the A_inf-span of the `1 ⊗ y`. -/
lemma letterProj_mk_mem_ainfLattice (t : Rep.of (overZp L.ρ)) :
    L.letterProj i (DiagTensor.mk 1 t) ∈ L.ainfLattice := by
  simp (maxDischargeDepth := 4) [letterProj, sum_mem, smul_of_tower_mem, mk_one_mem_ainfLattice]

/-- An invariant functional composed with the projector to a letter is again invariant. -/
lemma comp_letterProj_mem_forms (h : μ ∈ L.forms) : μ ∘ₗ L.letterProj i ∈ L.forms := by
  intro t g
  -- `μ` commutes with `g` on `fracSpan`, and `g` commutes with `letterProj i`
  -- Elaborator: `erw`, as the goal carries `letterProj i` with its scalars restricted to A_inf.
  erw [← form_gal_smul ⟨_, g, rfl⟩ h (mem_saturateBy_of_mem (letterProj_mk_mem_ainfLattice t)),
    gal_smul_letterProj]
  simp

lemma valueAt_comp_wittMap {μ : L'.Ambient →ₗ[Ainf] BdR} :
    valueAt a (μ ∘ₗ F.wittMap) x = valueAt a μ (F.wittMap x) := by simp [valueAt]

/-! ### The letters decompose the module -/

/-- The projectors to the letters sum to the identity of W(C^♭) ⊗ L. -/
lemma sum_letterProj (x : L.Ambient) : ∑ i : Letter, L.letterProj i x = x := by
  -- Orthogonality of characters of the cyclic group `k.Letter`, of order `q` say: for `0 < n < q`
  -- the character `i ↦ letterTeich i⁻¹ ^ n` is not trivial, so its values sum to zero.
  have h_orth (n : ℕ) (hn : n ∈ Finset.range (Fintype.card k.Letter)) (hn₀ : n ≠ 0) :
      ∑ i, k.letterTeich i⁻¹ ^ n = 0 := by
    refine sum_hom_units_eq_zero (k.letterTeich.comp invMonoidHom ^ n) fun h_triv ↦ ?_
    have hn_lt : n < Nat.card k.Letter := by simpa using hn
    obtain ⟨i, hi⟩ : ∃ i : k.Letter, i ^ n ≠ 1 := exists_pow_ne_one_of_isCyclic hn₀ hn_lt
    -- The zeroth Witt component of `letterTeich i ^ n = 1` gives `i ^ n = 1`.
    have h_coeff : Units.val (i ^ n : (flatFq k.f)ˣ) = ((1 : (flatFq k.f)ˣ) : flatFq k.f) := by
      -- Elaborator: `using!`; the Teichmüller coefficient is matched only after unfolding.
      simpa [letterTeich, algebraMap_toAlgebra, ← map_pow] using!
        congrArg (fun s : k.S ↦ s.val.coeff 0) (DFunLike.congr_fun h_triv i⁻¹)
    exact hi (Units.ext h_coeff)
  suffices ∑ i : k.Letter, ∑ n ∈ Finset.range (Fintype.card k.Letter),
      k.letterTeich i⁻¹ ^ n • (L.mulZeta.wittMap ^ n) x =
    Fintype.card k.Letter • x by
      simpa [letterProj, letterOp, ← smul_sum, smul_pow, invOf_smul_eq_iff, Nat.cast_smul_eq_nsmul]
  -- After exchanging the two sums only the term `n = 0` survives, and it equals `q • x`.
  rw [sum_comm, sum_eq_single 0 (fun n hn hn₀ ↦ ?_) (by simp)]
  · simp
  · -- Elaborator: `erw`, as the scalar `0` of `S` acts here through A_inf only up to unfolding.
    erw [← sum_smul, h_orth n hn hn₀, zero_smul]

/-! ### Functionals of given type and Hodge–Tate jumps -/

/-- For a lattice with jump sets `L`, a letter `i` and `u : ℤ`, `formsOfType i u` is the set of
A_inf-linear maps W(C^♭) ⊗ L → B_dR that are Γ'-equivariant on 1 ⊗ L and send the projection of
1 ⊗ L to `i` into t^{−u}B_dR^+. `L.jumpMultiplicity i u` is the total multiplicity of the Hodge–Tate
jump `u` over the embeddings of `O` above `i`. There are `r ≤ L.jumpMultiplicity i u` forms `ν m` of
type `u` at `i` such that every form of type `u` at `i` is a `Q̄_p`-combination of the `ν m` modulo
a form in `formsOfType i (u - 1)`. -/
lemma exists_span_formsOfType_mod_pred (i : Letter) (u : ℤ) :
    ∃ r ≤ L.jumpMultiplicity i u, ∃ ν : Fin r → L.formsOfType i u, ∀ μ ∈ L.formsOfType i u,
      ∃ c : Fin r → PadicAlgCl p,
      μ - ∑ m : Fin r, c m • (ν m).val ∈ formsOfType i (u - 1) := by
  -- The symbol `f μ : L.Carrier → ℂ_p` of `μ` is its leading coefficient on the letter `i`; the
  -- symbols are Hodge–Tate maps of weight `u`, so
  -- `IsPotentiallyCrystalline.sum_jump_eq_jump_overZp` bounds their span. In a basis of symbols the
  -- coordinates are Galois invariant, hence algebraic (Ax–Sen–Tate).
  have h_type (μ : L.formsOfType i u) (t : Rep.of (overZp L.ρ)) :
      ∃ y : BdRPlus, y • (tUnit ^ (-u)).1 = μ.1 (L.letterProj i (.mk 1 t)) :=
    mem_span_singleton.1 (μ.property.2 t)
  -- Write `μ (letterProj i (1 ⊗ t)) = a μ t • tUnit ^ (-u)` with `a μ t` in `B_dR⁺`.
  choose a ha using h_type
  -- The leading coefficient can be computed from any expression `y • tUnit ^ (-u)`.
  have theta_a {μ : L.formsOfType i u} {t : Rep.of (overZp L.ρ)} {z : ℂ_[p]} {y : BdRPlus}
      (h : μ.1 (L.letterProj i (.mk 1 t)) = y • (tUnit ^ (-u)).1)
      (hz : thetaBdR y = z := by simp +zetaDelta [smul_def', -toRingHom_ofId]) :
      thetaBdR (a μ t) = z := by
    rw [show a μ t = y from (smul_left_inj (Units.ne_zero _)).1 ((ha μ t).trans h), hz]
  let f (μ : L.formsOfType i u) : L.Carrier →ₛₗ[(ofId ℤ_[p] ℂ_[p] : ℤ_[p] →+* ℂ_[p])] ℂ_[p] :=
    { toFun := thetaBdR ∘ a μ
      map_add' _ _ := theta_a (by simp [add_smul, ← ha]) (map_add ..)
      map_smul' c t := theta_a (y := c • a μ t) (by simp [← ha]) }
  -- `g` multiplies `tUnit ^ (-u)` by the cyclotomic character to the power `-u`, and `ζ` acts on
  -- the letter `i` by `letterTeich i`.
  have f_gal (μ : L.formsOfType i u) (t : Rep.of (overZp L.ρ)) (g : k.subgroup) :
      f μ (L.ρ g t) = (χ g ^ (-u)).1 • toGp g • f μ t :=
    theta_a <| by
      erw [comp_letterProj_mem_forms μ.property.1, ← ha, smul_distrib_smul, smul_tUnit_zpow,
        smul_comm, ← smul_assoc]
  have f_ζ (μ : L.formsOfType i u) (t : Rep.of (overZp L.ρ)) :
      f μ (O.ζ.1 • t) = theta (k.letterTeich i) * f μ t :=
    theta_a (by
      erw [← mulZeta.wittMap_letterProj (.mk 1 t),
        mem_letterPart_iff_mulZeta.1 letterProj_mem_letterPart, μ.1.map_smul, ← ha, ← smul_assoc])
  -- A basis `b` of the span of the symbols, made of symbols `b m = f (ν m)`.
  obtain ⟨b, hb, span_b, b_indep⟩ := exists_fun_fin_finrank_span_eq ℂ_[p] (.range f)
  choose ν hν using hb
  -- The symbols are Hodge–Tate maps of weight `u` on which `ζ` acts by `letterTeich i`, so their
  -- span has dimension at most the jump multiplicity.
  have h_rank :
      Module.finrank ℂ_[p] (Submodule.span ℂ_[p] (Set.range f)) ≤ L.jumpMultiplicity i u :=
    L.inClass.isPotentiallyCrystalline.sum_jump_eq_jump_overZp.2 O.ζ.1 (theta (k.letterTeich i)) u
      (range f)
      (forall_mem_range.2 fun μ ↦ ⟨fun t ↦ nearOne_le (f_gal μ t), f_ζ μ⟩)
  refine ⟨_, h_rank, ν, ?_⟩
  -- `μ` is taken as an element of the subtype `L.formsOfType i u`, the domain of `a` and `f`.
  refine SetCoe.forall'.2 fun μ ↦ ?_
  obtain ⟨c, hc⟩ : ∃ c : _ → ℂ_[p], ∑ m, c m • b m = f μ :=
    (mem_span_range_iff_exists_fun _).1 (span_b.ge (subset_span ⟨μ, rfl⟩))
  -- `f μ` and the `b m` transform in the same way, so `toGp g • c` are coordinates of `f μ` too.
  have c_fixed (g : k.subgroup) (m : Fin _) : toGp g • c m = c m := by
    refine (b_indep.eq_coords_of_eq (g := toGp g • c) (LinearMap.ext ?_) m).symm
    refine (L.ρ.apply_bijective g).2.forall.2 ?_
    simpa [← hc, ← hν, f_gal, smul_sum, -toRingHom_ofId] using (f_gal μ · g)
  choose c' hc' c_eq using fun m ↦ (forall_smul_eq_iff_mem_localFieldOf k.subgroup).1 fun g ↦
    c_fixed g m
  refine ⟨c', fun t g ↦ ?_, fun t ↦ ?_⟩
  · -- The difference is invariant, since `Γ'` fixes the coefficients.
    simp_all [μ.property.1 t, (ν _).property.1 t, smul_sub, smul_sum, smul_def', -toRingHom_ofId]
  · -- The leading coefficient of the difference vanishes, so its pole has order at most `u - 1`.
    have lead : thetaBdR (a μ t - ∑ m, c' m • a (ν m) t) = 0 := by
      simpa [← hν, c_eq, smul_def', sub_eq_zero, -toRingHom_ofId] using!
        LinearMap.congr_fun hc.symm t
    simpa [← ha, ↓← smul_def', sub_smul, sum_smul] using!
      mul_mem_hodgeFil (n := -u) (algebraMap_mem_hodgeFil_one_iff.2 lead) (subset_span rfl)

/-- If n is not in `L.jumpSet i`, every functional of type n at the letter i is of type n - 1. -/
lemma formsOfType_subset_pred_of_notMem (h : n ∉ L.jumpSet i) :
    L.formsOfType i n ⊆ L.formsOfType i (n - 1) := by
  obtain ⟨r, hr, ν, span_ν⟩ := L.exists_span_formsOfType_mod_pred i n
  -- `n` is no jump at any embedding over the letter `i`, so the family `ν` is empty.
  have no_jump : L.jumpMultiplicity i n = 0 := by
    refine sum_eq_zero fun γ hγ ↦ ?_
    by_contra h_jump
    have h_over : γ O.ζ = (theta (letterTeich i) : ℂ_[p]) := by simpa using hγ
    exact h (L.embJumps_subset h_over (L.inClass.mem_of_jump_ne_zero h_jump))
  obtain rfl : r = 0 := Nat.le_zero.1 (hr.trans_eq no_jump)
  intro μ hμ
  simpa using span_ν μ hμ

end New.Lift.KummerChart.JumpLattice

end
