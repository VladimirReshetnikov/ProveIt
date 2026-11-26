import Lib.ClassField.Local.InvariantMap
import Lib.General.Algebra.CartanMap

/-!
# The inequality of local Tate duality for orthogonal groups of cocycles

Throughout, `k` is a local field with absolute Galois group `Γ` (`New.IsLocalGalois`) and `l` is a
prime. The inequality of local duality is proved as a count of cocycles, for a finite discrete
module `M` and its dual `Hom(M, Ωˣ)`.

* `New.card_mul_card_le_of_le_pairingAnnihilator`: for `M` killed by a power of `l`, orthogonal
  groups of cocycles in `Hom(M, Ωˣ)` and `M` have `#X · #W ≤ #M ^ (2 + d)`, where `O` is the
  valuation ring of `k` and `#(O / l) = l ^ d`, if `Γ` acts by elements of `l`-power order.
* `New.DiscreteModule.HoldsCorestrictions.pairingAnnihilator_le`: annihilators descend from an open
  subgroup whose index is invertible on the module.
* `New.DiscreteModule.local_duality_card_dvd`: for an open subgroup `U` of index prime to `#M`, a
  largest orthogonal pair of cocycle groups over `U` bounds `#L^⊥ · #L` for cocycle groups `L` over
  `Γ`.

`New.Z1` is the group of continuous cocycles (not classes), `New.unitsModule` is `Ωˣ` written
additively, `unitsRep` is the action of `Γ` on this `Ωˣ` (so `H2 unitsRep` is `H²(Γ, Ωˣ)`),
`New.DiscreteModule.evalCup` is the cup product `Z¹(Hom(M, Ωˣ)) × Z¹(M) → H²(Ωˣ)`, and
`New.pairingAnnihilator b L` is the annihilator of `L` in the right-hand group of the pairing `b`.

Notions from other files:
* `New.DiscreteModule`: A discrete Γ-module over R: an R-module with the discrete topology and a
  continuous R-linear action of the topological group Γ.
* `New.DiscreteModule.cartierDual`: For finite M, the discrete Γ-module Hom(M, Ω^×) of additive maps
  to `New.unitsModule`, with (gf)(m) = g f(g⁻¹m).

## Relation to the literature

Known; see `Lib.ClassField.LocalDuality.CrystallineDuality` for sources.
-/

namespace New

open DiscreteUnits Cohomology DFunLike DiscreteModule QZChar NeZero QZ Ideal AddSubgroup
  IsLocalGalois Nat Function

variable {Γ k Ω : Type} [Group Γ] [TopologicalSpace Γ] [Field k] [Field Ω] [Algebra k Ω]
  [MulSemiringAction Γ Ω] {A : ValuationSubring Ω} [J : IsLocalGalois Γ k A]
  {l r : ℕ} [Fact l.Prime] {R S : Type} [CommRing R] [CommRing S]
  {M : DiscreteModule R Γ} {N : DiscreteModule S Γ}

/-- Over a local field `k`, a continuous character `χ : Γ → ℚ/ℤ` whose cyclic class `δχ ∪ w` in
`H²(Γ, Ωˣ)` vanishes for every `w` in `kˣ` is zero. -/
lemma Cohomology.char_eq_zero_of_cyclicClass_eq_zero {χ : QZChar Γ}
    (h : ∀ w : Additive kˣ, cyclicClass unitsRep χ (DiscreteUnits.ofBase Γ Ω w) = 0) (g : Γ) :
    χ.val g = 0 := by
  -- The class with invariant `χ g` dies over the fixed field of `ker χ`, since restriction
  -- multiplies the invariant by the index. So it is a symbol `(χ, w)`, hence zero.
  have h_index : (ker χ).index • χ.val g = 0 :=
    congrArg Multiplicative.toAdd
      (by simpa using (ker χ).pow_index_mem g : toHom χ g ^ (ker χ).index = 1)
  obtain ⟨w, hw⟩ : ∃ w : kˣ, classOfInvariant Γ k A (χ.val g) = cyclicClass _ χ
    (ofBase Γ Ω (.ofMul w)) :=
    ((cyclicClass_spec χ).1 _).mp (resH2_classOfInvariant_eq_zero _ h_index)
  -- `classOfInvariant` is injective
  exact (map_eq_zero_iff _ isClassOfInvariant_classOfInvariant.left).mp (hw.trans (h _))

/-- Let `k` be local, `i · [Γ : U]` act as the identity on `M`, `b : M × N → Ωˣ` an equivariant
pairing, and let `X`, `Y` contain the coboundaries and corestrictions of `X'`, `Y'`. If `X'`
contains the cup product annihilator of `Y'` over `U`, then `X` contains that of `Y`. -/
lemma DiscreteModule.HoldsCorestrictions.pairingAnnihilator_le {U : OpenSubgroup Γ}
    {X : AddSubgroup ↥(Z1 M.ρ)} {X' : AddSubgroup ↥(Z1 (M.restrictTo U).ρ)}
    {Y : AddSubgroup ↥(Z1 N.ρ)} {Y' : AddSubgroup ↥(Z1 (N.restrictTo U).ρ)} {i : ℤ}
    (hX : M.HoldsCorestrictions U X' X) (hY : N.HoldsCorestrictions U Y' Y)
    (h_inv : ∀ m : M, i • U.index • m = m)
    {b : (M.restrictTo (U : Subgroup Γ)).V →+ (N.restrictTo (U : Subgroup Γ)).V →+
      (unitsModule (U : Subgroup Γ)).V}
    (h_equivariant : ∀ (g : Γ) (x : M.V) (y : N.V),
      (b ((M.ρ g) x)) ((N.ρ g) y) = ((unitsModule Γ).ρ g) ((b x) y))
    (h_ann :
      pairingAnnihilator
        (cupProduct (unitsModule U.toSubgroup) (M.restrictTo U.toSubgroup)
          (N.restrictTo U.toSubgroup) b fun g : (U : Subgroup Γ) ↦ h_equivariant g).flip
        Y' ≤ X') :
    pairingAnnihilator (cupProduct (unitsModule Γ) M N b h_equivariant).flip Y ≤ X := by
  intro z hz
  -- The restriction of `z` to `U` is orthogonal to `Y'`, hence lies in `X'`.
  let z' : Z1 (M.restrictTo (U : Subgroup Γ)).ρ :=
    pairMapZ1 (subgroupIncl (U : Subgroup Γ)) .id (fun _ _ ↦ rfl) z
  have h_res_mem : z' ∈ X' := by
    refine h_ann fun y hy ↦ ?_
    -- `y` is the Shapiro image of a cocycle `F` in functions on `Γ ⧸ U` with sum in `Y`.
    obtain ⟨F, rfl, hF : (N.sum U).mapZ1 F ∈ Y⟩ := hY.exists_corestriction y hy
    -- Pair `z` with the Shapiro lift `F` of `y`, in functions on `Γ ⧸ U`.
    let β : ((unitsModule Γ).funModule (U : Subgroup Γ)).H2 :=
      cupProduct ((unitsModule Γ).funModule (U : Subgroup Γ)) M (N.funModule _)
        (.mk' (fun m ↦ (b m).compLeft _) (by bound)) (by simp [funext_iff, h_equivariant]) z F
    -- Its Shapiro image is the class to be killed; its sum over `Γ ⧸ U` vanishes by `hz`.
    have h_shapiro_β :
        shapiroH2 U β =
          cupProduct (unitsModule (U : Subgroup Γ)) _ _ b (fun g ↦ h_equivariant g) z'
            (N.shapiroZ1 U F) :=
      -- Both are classes of cocycles that agree pointwise, by evaluating `F` at the trivial coset.
      congrArg (Quotient.mk _)
        (Subtype.ext (funext fun _ ↦ congrArg (b _) (N.funModule_apply_one U ..)))
    have h_sum_β :
        ((unitsModule Γ).sum _).mapH2 β =
          cupProduct (unitsModule Γ) M N b h_equivariant z ((N.sum _).mapZ1 F) :=
      -- The cocycles agree pointwise: the sum over the cosets commutes with the action.
      congrArg (Quotient.mk _) (by
        simp [← (sum ..).isIntertwining]
        simp [sum])
    -- The Shapiro image is the restriction of a class of invariant `s`, and the sum has
    -- invariant `U.index • s`; so `U.index • s = 0` and the restriction vanishes.
    obtain ⟨s, hs⟩ : ∃ s : QZ, (unitsModule Γ).resH2 U (classOfInvariant Γ k A s) = shapiroH2 U β :=
      exists_resH2_classOfInvariant_eq U _
    have h_index : classOfInvariant Γ k A (U.index • s) = 0 := by
      rw [map_nsmul, ← mapH2_sum_eq_index_smul U _ _ hs, h_sum_β]
      exact hz _ hF
    have h_res : (unitsModule Γ).resH2 U (classOfInvariant Γ k A s) = 0 :=
      resH2_classOfInvariant_eq_zero U ((map_eq_zero_iff _
        isClassOfInvariant_classOfInvariant.left).mp h_index)
    exact (hs.trans h_shapiro_β).symm.trans h_res
  -- A corestriction of it lies in `X`, and differs from `U.index • z` by a coboundary.
  obtain ⟨F, sh_F, hF : (M.sum U).mapZ1 F ∈ X⟩ := hX.exists_corestriction z' h_res_mem
  -- On `U`, at the trivial coset, `F` agrees with `z`; so `F` minus the constant lift of `z` is a
  -- coboundary, by Shapiro's lemma.
  have h_sh (u : (U : Subgroup Γ)) : F.val u ⟦1⟧ = z.val u :=
    congrFun (congrArg Subtype.val sh_F) u
  have h_diff (u : (U : Subgroup Γ)) : (F - (M.const _).mapZ1 z).val u ⟦1⟧ = M.ρ u 0 - 0 := by
    simpa [sub_eq_zero, DiscreteModule.const] using h_sh u
  obtain ⟨n, hn⟩ : ∃ n : (M.funModule U).V, ∀ g : Γ,
      (F - (M.const _).mapZ1 z).val g = (M.funModule (U : Subgroup Γ)).ρ g n - n :=
    shapiro_H1 U _ 0 h_diff
  have h_index : U.index • z = (M.sum _).mapZ1 F - M.coboundary (M.sum _ n) := by
    ext g
    -- Sum the equation `hn g` over the cosets.
    have h_const : M.sum (U : Subgroup Γ) (M.const (U : Subgroup Γ) (z.val g)) =
        M.sum (U : Subgroup Γ) fun _ ↦ z.val g := rfl
    simpa [index_smul_eq_sum_const, ← (sum ..).isIntertwining, h_const] using
      congrArg (fun f ↦ M.sum _ (F.val g - f)) (hn g)
  -- Multiplication by `i` inverts multiplication by `U.index`.
  have h_inv' : z = i • U.index • z := Subtype.ext (funext fun g ↦ (h_inv _).symm)
  rw [h_inv', h_index]
  exact zsmul_mem (sub_mem hF (hX.coboundary_mem _)) i

/-- Kummer theory in each coordinate: for a finite trivial module `M` killed by `l`, there are at
most `#M ^ (2 + d)` cocycles in `Hom(M, Ωˣ)`, where `O` is the valuation ring of `k` and
`#(O / l) = l ^ d`. -/
lemma card_dual_cocycles_le_of_trivial [Finite M] {d : ℕ}
    (hd : Nat.card (valRingBelow k A ⧸ span {(l : valRingBelow k A)}) = l ^ d)
    (h_kill : ∀ m : M, l • m = 0) (h_triv : M.TrivialOn ⊤) :
    Nat.card (Z1 M.cartierDual.ρ) ≤ Nat.card M ^ (2 + d) := by
  -- Being killed by `l`, `M` is a vector space over `ZMod l`; take a basis `e`.
  have h_module : Module (ZMod l) M.V := AddCommGroup.zmodModule h_kill
  let e := Module.finBasis (ZMod l) M
  -- `K`: the cocycles in `Ωˣ` killed by `l`; Kummer theory counts them.
  let K : Submodule ℤ ↥(Z1 (unitsModule Γ).ρ) :=
    (l : Module.End ℤ (Z1 (unitsModule Γ).ρ)).ker
  have K_card :
      Nat.card K = l ^ 2 * Nat.card (valRingBelow k A ⧸ span {(l : valRingBelow k A)}) :=
    IsLocalGalois.card_ker_natCast_Z1_unitsModule l
  have : Finite K := IsLocalGalois.finite_ker_natCast_Z1_unitsModule (k := k) (A := A) l
  -- The values of a cocycle at the basis vectors are cocycles in `Ωˣ` killed by `l`.
  let coord (z : Z1 M.cartierDual.ρ) (j : Fin (Module.finrank (ZMod l) M)) : K :=
    ⟨pairMapZ1 (.id _) ⟨⟨fun f ↦ f (e j), by simp⟩, by simp⟩ (by simp [h_triv]) z, by
      ext
      simp [← map_nsmul, h_kill]⟩
  -- They determine the cocycle, as additive maps that agree on a basis over `ZMod l` are equal.
  have h_coord_inj : Function.Injective coord := fun x y h ↦ by
    ext g : 3
    -- The coordinates of `x` and `y` at `g` agree on every basis vector.
    have h_coord (j : Fin (Module.finrank (ZMod l) M)) : (x.val g) (e j) = (y.val g) (e j) :=
      congrArg (fun c : K ↦ (c : Z1 (unitsModule Γ).ρ).val g) (congrFun h j)
    have h_top : ((x.val g).eqLocus (y.val g)).toZModSubmodule l = ⊤ :=
      (Submodule.eq_top_iff_forall_basis_mem e).mpr h_coord
    exact h_top.ge Submodule.mem_top
  calc
    _ ≤ Nat.card (Fin _ → K) := Nat.card_le_card_of_injective _ h_coord_inj
    _ = (l ^ (2 + d)) ^ Module.finrank (ZMod l) M := by simp [Nat.card_fun, K_card, hd, pow_add]
    _ = _ := by simp [Nat.card_congr e.equivFun.toEquiv, pow_right_comm]

/-- One side of the nondegeneracy of the Hilbert symbol, extended to a trivial module. Let `Γ` act
as `Gal(Ω/k)` on an algebraically closed field `Ω` of characteristic 0, with `A ∩ k` a discrete
valuation ring with finite residue field (`IsLocalGalois Γ k A`), and let `M` be a finite discrete
`Γ`-module killed by the prime `l` on which all of `Γ` acts trivially. A continuous 1-cocycle `y`
of `M` is zero if its cup product `M.evalCup x y` vanishes for every continuous 1-cocycle `x` of
`Hom(M, Ωˣ)`. -/
lemma eq_zero_of_evalCup_eq_zero_of_trivialOn [Finite M] (h_kill : ∀ m : M, l • m = 0)
    (h_triv : M.TrivialOn ⊤) {y : Z1 M.ρ} (hy : ∀ x : Z1 M.cartierDual.ρ, M.evalCup x y = 0) :
    y = 0 := by
  have h_units_cont :
      Continuous (uncurry fun (g : Γ) (u : (unitsModule Γ).V) ↦ (unitsModule Γ).ρ g u) :=
    (unitsModule Γ).continuous
  -- It is enough that each coordinate `ξ = j ∘ y` in `ZMod l` vanishes, and for this
  -- (`char_eq_zero_of_cyclicClass_eq_zero`) that its symbol with each `x` in `kˣ` vanishes.
  ext g
  refine eq_zero_of_forall_hom_eq_zero
    ((bijective_ofZMod_comp h_kill).surjective.forall.mpr fun j ↦ ?_)
  let ξ : Z1 (Representation.trivial ℤ Γ (ZMod l)) :=
    ⟨j ∘ y.val, y.prop.imp (by fun_prop) (by simp_all)⟩
  refine char_eq_zero_of_cyclicClass_eq_zero (χ := ofZModCocycle l ξ) (fun x ↦ ?_) g
  -- The Kummer cocycle of an `l`-th root `a` of `x`, twisted by `j`, takes values in `Hom(M, Ωˣ)`.
  obtain ⟨a, ha⟩ : ∃ a : DiscreteUnits Ω, l • a = DiscreteUnits.ofBase Γ Ω x :=
    exists_nsmul (DiscreteUnits.ofBase Γ Ω x).val (out : l ≠ 0)
  let z : Z1 M.cartierDual.ρ :=
    ⟨fun g ↦ .mk' (fun m ↦ (j m).val • (unitsRep g a - a)) (by
        simp [ZMod.val_add, add_smul, ← nsmul_eq_mod_nsmul, smul_sub l, ← map_nsmul, ha,
          DiscreteUnits.ext_iff]),
      .congr (by
        simp
        fun_prop) (leftInverse_invFun coe_injective ∘' _),
      by simp [ext_iff, h_triv, smul_sub]⟩
  -- Its cup product with `y` is minus the symbol (`mk_eq_neg_cyclicClass_ofZModCocycle`).
  exact neg_eq_zero.mp
    ((mk_eq_neg_cyclicClass_ofZModCocycle ha ξ _ (by simp [z, ξ, h_triv])).symm.trans (hy z))

/-- Let `k` be local with valuation ring `O` and `#(O / l) = l ^ d`. Let `M` be a finite module
killed by `l ^ r` and fixed by `Q`, where every `g : Γ` has a power `g ^ l ^ i` in `Q`. This is
`hM : FiniteKilledFixedInj (l ^ r) Q 1 0 M`, the predicate for which dévissage is stated; its last
two arguments `1` and `0` ask that `ρ 1 - 0 = id` be injective, so they impose nothing. If groups
`X` of cocycles in `Hom(M, Ωˣ)` and `W` of cocycles in `M` are orthogonal under the cup product
(`h_orth`), then `#X · #W ≤ #M ^ (2 + d)`: the form of Tate's local duality and Euler
characteristic formula used. -/
lemma card_mul_card_le_of_le_pairingAnnihilator [Finite M] {d : ℕ} (Q : Subgroup Γ)
    (hd : Nat.card (valRingBelow k A ⧸ span {(l : valRingBelow k A)}) = l ^ d)
    (hM : FiniteKilledFixedInj (l ^ r) Q 1 0 M) (h_pow : ∀ g : Γ, ∃ i : ℕ, g ^ l ^ i ∈ Q)
    (X : AddSubgroup ↥(Z1 M.cartierDual.ρ)) (W : AddSubgroup ↥(Z1 M.ρ))
    (h_orth : X ≤ pairingAnnihilator M.evalCup.flip W) :
    Nat.card X * Nat.card W ≤ Nat.card M ^ (2 + d) := by
  -- The dévissage runs over all modules with the same conditions, so prove the bound for each.
  suffices h_all : ∀ (M : DiscreteModule R Γ) (hM : FiniteKilledFixedInj (l ^ r) Q 1 0 M),
      have : Finite M := hM.finite
      ∀ (X : AddSubgroup ↥(Z1 M.cartierDual.ρ)) (W : AddSubgroup ↥(Z1 M.ρ)),
        X ≤ pairingAnnihilator M.evalCup.flip W →
          Nat.card X * Nat.card W ≤ Nat.card M ^ (2 + d) from h_all M hM X W h_orth
  intro M hM
  -- Dévissage: reduce to trivial modules killed by `l` and to extensions.
  have := J.finite_Z1
  refine M.devissage_induction rfl ⊤ Q (by simpa)
    (fun M _ ⟨h_finite, h_kill, h_triv, h_inj⟩ X W h ↦ ?_)
    (fun {M' M M'' ι π} s hM ih' ih'' X W h ↦ ?_) hM
  · -- Trivial modules killed by `l`: the pairing has no kernel in `Z1 M.ρ`.
    have h_ker_bot : M.evalCup.flip.ker ⊓ W = ⊥ := bot_unique fun y hy ↦
      eq_zero_of_evalCup_eq_zero_of_trivialOn h_kill h_triv (ext_iff.mp hy.1)
    calc
      Nat.card X * Nat.card W ≤ Nat.card (pairingAnnihilator M.evalCup.flip W) * Nat.card W := by
        grw [card_le_of_le h]
      _ = Nat.card (Z1 M.cartierDual.ρ) := by
        rw [card_pairingAnnihilator_mul_card _ (.ofBijective _ classOfInvariant_bijective),
          h_ker_bot, card_bot, mul_one]
      _ ≤ Nat.card M ^ (2 + d) := card_dual_cocycles_le_of_trivial hd h_kill h_triv
  -- Extensions `M' → M → M''` of finite modules. A map on `M` that kills `M'` comes from `M''`.
  have ⟨ι_inj, h_exact, π_surj⟩ : Injective ι ∧ Exact ι π ∧ Surjective π := s
  have := hM.finite
  have := (hM.left_of_isShortExact s).finite
  have := (hM.right_of_isShortExact s).finite
  -- The dual maps `f ↦ f ∘ ι` and `f ↦ f ∘ π`, again equivariant.
  let ι' : M.cartierDual.Hom M'.cartierDual :=
    ⟨(AddMonoidHom.compHom' ↑ι).toIntLinearMap, by simp [ι.isIntertwining, ext_iff]⟩
  let π' : M''.cartierDual.Hom M.cartierDual :=
    ⟨(AddMonoidHom.compHom' ↑π).toIntLinearMap, by simp [π.isIntertwining, ext_iff]⟩
  have π'_inj : Injective π' := fun f f' h_eq ↦
    ext f f' (π_surj.forall.mpr (DFunLike.congr_fun h_eq))
  have dual_exact : Exact π' ι' := by
    refine fun f ↦ ⟨fun hf ↦ ?_, ?_⟩
    · -- A map on `M` that kills `M'` extends from `M''`.
      have h_kills (m : M') : f (ι m) = 0 := DFunLike.congr_fun hf m
      obtain ⟨f', hf'⟩ : ∃ f' : M'' →+ DiscreteUnits Ω, ∀ m : M, f' (π m) = f m :=
        exists_extend π.toAddMonoidHom f fun m hm ↦ by
          obtain ⟨m', rfl⟩ := (h_exact m).mp hm
          exact h_kills m'
      exact ⟨f', ext _ _ hf'⟩
    · rintro ⟨f', rfl⟩
      -- `π ∘ ι = 0`.
      exact ext _ _ fun m ↦ by simp [ι', π', h_exact.apply_apply_eq_zero]
  -- The part of `X` from `M''` is orthogonal to the image of `W`, and symmetrically: a map and its
  -- dual are adjoint for the cup products, already on the level of cocycles.
  have orth'' : comap π'.mapZ1 X ≤ pairingAnnihilator M''.evalCup.flip (map π.mapZ1 W) := by
    rintro x hx _ ⟨w, hw, rfl⟩
    have h_cup : M''.evalCup x (π.mapZ1 w) = M.evalCup (π'.mapZ1 x) w :=
      congrArg (Quotient.mk _) (by simp [π', π.isIntertwining])
    exact h_cup.trans (h hx w hw)
  have orth' : map ι'.mapZ1 X ≤ pairingAnnihilator M'.evalCup.flip (comap ι.mapZ1 W) := by
    rintro _ ⟨x, hx, rfl⟩ w hw
    have h_cup : M'.evalCup (ι'.mapZ1 x) w = M.evalCup x (ι.mapZ1 w) :=
      congrArg (Quotient.mk _) (by simp [ι', ι.isIntertwining])
    exact h_cup.trans (h hx (ι.mapZ1 w) hw)
  -- Count `X` and `W` by their two parts, pair the parts crosswise, and multiply the bounds.
  calc Nat.card X * Nat.card W
      = (Nat.card (comap π'.mapZ1 X) * Nat.card (map π.mapZ1 W)) *
          (Nat.card (map ι'.mapZ1 X) * Nat.card (comap ι.mapZ1 W)) := by
        rw [π'.card_eq_card_comap_mul_card_map π'_inj dual_exact X,
          ι.card_eq_card_comap_mul_card_map ι_inj h_exact W]
        ring
    _ ≤ Nat.card M'' ^ (2 + d) * Nat.card M' ^ (2 + d) :=
        Nat.mul_le_mul (ih'' _ _ orth'') (ih' _ _ orth')
    _ = Nat.card M ^ (2 + d) := by rw [s.card_eq_card_mul_card, mul_pow, mul_comm]

/-- Let `M` be a finite module killed by `l ^ r` and fixed by `Q` (`hM`), where every `g : Γ` has a
power `g ^ l ^ i` in `Q`, and let `#(O / l) = l ^ d` for the valuation ring `O = A ∩ k` of the local
field `k`. If groups `X` of cocycles in `Hom(M, Ωˣ)` and `W` of cocycles in `M` are orthogonal under
the cup product `M.evalCup`, then `#X · #W ≤ #M ^ (2 + d)`. This is
`card_mul_card_le_of_le_pairingAnnihilator`, with the finiteness of `M` taken from `hM` inside the
statement.

This inequality is a numerical consequence of Tate local duality and the local Euler characteristic
formula, for 1-cocycles and `l`-primary `M` on which `Γ` acts through an `l`-group; perfectness of
the pairing is not asserted. -/
lemma card_mul_card_le_of_orthogonal {d : ℕ} (Q : Subgroup Γ)
    (hd : Nat.card (valRingBelow k A ⧸ span {(l : valRingBelow k A)}) = l ^ d)
    (hM : FiniteKilledFixedInj (l ^ r) Q 1 0 M) (h_pow : ∀ g : Γ, ∃ i : ℕ, g ^ l ^ i ∈ Q) :
    have : Finite M := hM.finite
    ∀ (X : AddSubgroup ↥(Z1 M.cartierDual.ρ)) (W : AddSubgroup ↥(Z1 M.ρ)),
      X ≤ pairingAnnihilator M.evalCup.flip W → Nat.card X * Nat.card W ≤ Nat.card M ^ (2 + d) :=
  fun X W h_orth ↦
    have : Finite M := hM.finite
    card_mul_card_le_of_le_pairingAnnihilator Q hd hM h_pow X W h_orth

/-- A divisibility form of local duality. Let `M` be finite and `U` an open subgroup of index prime
to `#M`. Let `X'`, `W'` be groups of cocycles of `U` in `Hom(M, Ωˣ)` and `M` that are orthogonal
under the cup product, with `#X' · #W'` largest among such pairs, and let `X`, `W` contain the
coboundaries and corestrictions of `X'`, `W'` (`New.DiscreteModule.HoldsCorestrictions`). Then
`#L^⊥ · #L` divides `#W · #X` for every group `L` of cocycles of `Γ` in `Hom(M, Ωˣ)`, where `L^⊥`
is the annihilator of `L` among the cocycles in `M`. -/
lemma DiscreteModule.local_duality_card_dvd [Finite M] {U : OpenSubgroup Γ}
    {X : AddSubgroup ↥(Z1 M.cartierDual.ρ)} {W : AddSubgroup ↥(Z1 M.ρ)}
    {X' : AddSubgroup ↥(Z1 (M.cartierDual.restrictTo U).ρ)}
    {W' : AddSubgroup ↥(Z1 (M.restrictTo U).ρ)}
    (hX : M.cartierDual.HoldsCorestrictions U X' X) (hW : M.HoldsCorestrictions U W' W)
    (h_coprime : (Nat.card M).Coprime U.index)
    (h_orth : W' ≤ pairingAnnihilator (M.restrictTo U).evalCup X')
    (h_max : ∀ (Y : AddSubgroup ↥(Z1 (M.restrictTo U).cartierDual.ρ))
      (Z : AddSubgroup ↥(Z1 (M.restrictTo U).ρ)),
      Y ≤ pairingAnnihilator (M.restrictTo U).evalCup.flip Z →
      Nat.card Y * Nat.card Z ≤ Nat.card X' * Nat.card W')
    (L : AddSubgroup ↥(Z1 M.cartierDual.ρ)) :
    Nat.card (pairingAnnihilator M.evalCup L) * Nat.card L ∣ Nat.card W * Nat.card X := by
  -- The index of `U` acts invertibly on `M`, being prime to its order.
  obtain ⟨i, index_inv⟩ : ∃ i : ℤ, ∀ m : M, i • U.index • m = m :=
    ⟨_, (nsmulCoprime h_coprime).left_inv⟩
  -- `classOfInvariant` identifies `ℚ/ℤ` with `H²(Γ, Ωˣ)`.
  let e : QZ ≃+ New.H2 unitsRep := AddEquiv.ofBijective _ J.classOfInvariant_bijective
  have := (of_finite U).isLocalGalois.finite_Z1
  -- The orthogonality of `X'` and `W'`, read from the side of `X'`.
  have h_orth' : X' ≤ pairingAnnihilator (M.restrictTo U).evalCup.flip W' := fun x hx w hw ↦
    h_orth hw x hx
  -- `X'` pairs to zero with everything that annihilates it.
  have h_double : X' ≤ pairingAnnihilator (M.restrictTo U).evalCup.flip
      (pairingAnnihilator (M.restrictTo U).evalCup X') := fun x hx w hw ↦ hw x hx
  -- By maximality each of `X'`, `W'` is the whole annihilator of the other.
  have X'_eq : X' = pairingAnnihilator (M.restrictTo U).evalCup.flip W' :=
    eq_of_le_of_card_ge h_orth' (le_of_mul_le_mul_right (h_max _ _ le_rfl) card_pos)
  have W'_eq : W' = pairingAnnihilator (M.restrictTo U).evalCup X' :=
    eq_of_le_of_card_ge h_orth (le_of_mul_le_mul_left (h_max _ _ h_double) (card_pos (α := X')))
  -- Annihilators descend to `Γ`, on both sides; the second uses anticommutativity of the cup.
  -- On `Hom(M, Ωˣ)` too, `i · [Γ : U]` acts as the identity.
  have index_inv_dual (f : M.cartierDual) : i • U.index • f = f :=
    ext _ _ fun m ↦ by simpa using congrArg f (index_inv m)
  have ann_W : pairingAnnihilator M.evalCup.flip W ≤ X :=
    hX.pairingAnnihilator_le hW (i := i) index_inv_dual (by simp) X'_eq.ge
  -- Over `U`, what annihilates `X'` in the flipped pairing annihilates it in the pairing, as the
  -- cup product changes sign when flipped; over `Γ` the same holds for `w` and `X`.
  have ann_X : pairingAnnihilator M.evalCup X ≤ W := fun w hw ↦
    hW.pairingAnnihilator_le hX index_inv (by simp)
      (fun w' hw' ↦ W'_eq.ge fun x hx ↦
        neg_eq_zero.mp ((cupProduct_flip ..).symm.trans (hw' x hx)))
      (fun x hx ↦ (cupProduct_flip ..).trans (by simpa using hw x hx))
  have ker_le : M.evalCup.ker ≤ X := fun x hx ↦ ann_W fun w _ ↦ ext_iff.mp hx w
  calc
    Nat.card (pairingAnnihilator M.evalCup L) * Nat.card L
    _ = Nat.card (Z1 M.ρ) * Nat.card ↥(M.evalCup.ker ⊓ L) := card_pairingAnnihilator_mul_card _ e L
    _ ∣ Nat.card (Z1 M.ρ) * Nat.card ↥(M.evalCup.ker ⊓ X) :=
      mul_dvd_mul_left _ (card_dvd_of_le (inf_le_of_left_le (le_inf le_rfl ker_le)))
    _ = Nat.card (pairingAnnihilator M.evalCup X) * Nat.card X :=
      (card_pairingAnnihilator_mul_card _ e X).symm
    _ ∣ Nat.card W * Nat.card X := mul_dvd_mul_right (card_dvd_of_le ann_X) _

end New
