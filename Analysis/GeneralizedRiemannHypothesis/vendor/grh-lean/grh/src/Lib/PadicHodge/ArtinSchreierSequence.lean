import Lib.PadicHodge.Kisin.KummerChartExistence

/-!
# W(𝔪^♭), the diagonal tensor module W(C^♭) ⊗ T and the Artin–Schreier sequence

`New.Period.OFlat = O^♭` is the tilt of the ring of integers of `ℂ_p`, and `New.Period.CFlat = C^♭`
is its fraction field. We write `New.Period.WittCFlat = W(C^♭)` and `A_inf = W(O^♭)`; the prime is
fixed by `[ThePrime p]`, and `New.Gp p` is the Galois group of `ℚ̄_p` over `ℚ_p`. The ideal
`W(𝔪) = W(𝔪^♭)` of `A_inf` is introduced, and the sets `W(𝔪) + p ^ m W(C^♭)` serve as neighbourhoods
of `0` for which the Galois action on `W(C^♭)` is continuous. For a group Γ (`[GroupOverGp p]`,
elements of type `GroupOverGp.G`) that maps to `Gp p`, and a representation of Γ on a ℤ_p-module T,
the module W(C^♭) ⊗ T with the diagonal action of ℤ × Γ is built, together with base change of
linear and bilinear maps. For T = ℤ_p/p^m(1) this gives an Artin–Schreier sequence: φ − 1 is onto,
and its kernel modulo W(𝔪^♭)·(1 ⊗ 1) is ℤ_p/p^m.

## Main definitions and results

* `New.Lift.wittOfMaxIdeal`: the kernel of the reduction `A_inf → W(k)`; by
  `New.Lift.mem_wittOfMaxIdeal` its elements are the Witt vectors none of whose coefficients is a
  unit.
* `New.Lift.WittCFlat.eventually_smul_sub_mem`: for `a`, `d` in `W(C^♭)` and `g` near `1` in
  `New.Gp p`, the element `(g • a - a) * d` lies in `W(𝔪) + p ^ m W(C^♭)`.
* `New.Lift.DiagTensor`: the module W(C^♭) ⊗ T with its diagonal action.
* `New.Lift.smallPart`: the A_inf-submodule W(𝔪^♭)·(1 ⊗ 1) of M = W(C^♭) ⊗ ℤ_p/p^m(1).
* `New.Lift.TateTwist.exists_eq_phi_smul_sub`,
  `New.Lift.TateTwist.exists_sub_mk_one_mem_smallPart_of_phi_smul_sub_mem` and
  `New.Lift.TateTwist.eq_zero_of_mk_one_mem_smallPart`: φ − 1 is onto M, and its kernel modulo
  W(𝔪^♭)·(1 ⊗ 1) is ℤ_p/p^m.
* `New.Lift.TateTwist.eventually_map_smul_sub_mem_smallPart`: let ρ be a representation with
  ρ(g)y − y divisible by p^m for g near 1, and let L be a linear map from W(C^♭) ⊗ ρ into M. Then
  for each v, L(gv − v) lies in W(𝔪^♭)·(1 ⊗ 1) for g near 1.

Notions from other files:
* `New.Period.toWittResidue`: the ring map `A_inf = W(O^♭) → W(k)`, `k` the residue field of `O^♭`,
  that reduces each Witt coordinate.
* `New.Lift.FrobGroup Γ`: the group `ℤ × Γ`; `FrobGroup.snd` is the projection to `Γ`, `inr g` is
  `(0, g)` and `φ` is `(1, 1)`, which acts as the Frobenius.
* `New.Period.nearOne Γ`: the filter "near `1`" on `Γ`, pulled back from the neighbourhoods of `1`
  in `Gp p`.

## Relation to the literature

Known result: The Artin–Schreier–Witt resolution over the tilt. Only the φ−1 step of Herr's complex
is treated, on Witt vectors of the tilt of C_p modulo p^m, and the Γ-step is not treated. Source: L.
Herr, Sur la cohomologie galoisienne des corps p-adiques, Bull. SMF 126 (1998) 563–600.
-/

noncomputable section

/-! ## The ideal W(𝔪^♭) and continuity of the Galois action on W(C^♭) -/

namespace New.Lift

open Period WittVector Ideal RingHom Algebra algebraMap Valued IsLocalRing IsLocalization
  MonoidWithZeroHom.ValueGroup₀ Witt Variety NeZero Metric Perfection OC nonZeroDivisors

variable {p : ℕ} [ThePrime p]

/-- The ideal W(𝔪^♭) of A_inf: the kernel of the map from A_inf to the Witt vectors of the
residue field of O^♭. -/
noncomputable def wittOfMaxIdeal : Ideal Ainf := ker toWittResidue

/-- An element of `A_inf` lies in `W(𝔪^♭)` exactly when none of its Witt coordinates is a unit. -/
lemma mem_wittOfMaxIdeal {a : Ainf} : a ∈ wittOfMaxIdeal ↔ ∀ n : ℕ, ¬IsUnit (a.coeff n) := by
  simp [wittOfMaxIdeal, toWittResidue, WittVector.ext_iff]

/-- The Teichmüller lift `[x]` of a non-unit `x` of `O^♭` lies in `W(𝔪^♭)`: its zeroth coordinate is
`x` and the others are `0`. -/
lemma teichmuller_mem_wittOfMaxIdeal {x : OFlat} (hx : ¬IsUnit x) :
    WittVector.teichmuller p x ∈ wittOfMaxIdeal :=
  mem_wittOfMaxIdeal.mpr fun
    | 0 => hx
    | n + 1 => by simp

/-- An element `σ` of `Gp p` acts on `O^♭` as the map of tilts induced by its action on `O_C`. -/
private lemma smul_oFlat_eq_tiltMap (σ : Gp p) (x : OFlat) :
    σ • x = tiltMap (MulSemiringAction.toRingHom (Gp p) OC σ) x :=
  pow_one _

/-- The `n`-th coordinate of `O^♭ = PreTilt OC p` is multiplicative (stated for `O^♭`, which is the
perfection of `O_C / p` only by definition). -/
private lemma coeff_oFlat_mul (n : ℕ) (a b : OFlat) :
    Perfection.coeff (ModP OC p) p n (a * b) =
      Perfection.coeff (ModP OC p) p n a * Perfection.coeff (ModP OC p) p n b :=
  map_mul (Perfection.coeff (ModP OC p) p n) a b

/-- The `n`-th coordinate of `O^♭` is additive on differences. -/
private lemma coeff_oFlat_sub (n : ℕ) (a b : OFlat) :
    Perfection.coeff (ModP OC p) p n (a - b) =
      Perfection.coeff (ModP OC p) p n a - Perfection.coeff (ModP OC p) p n b :=
  map_sub (Perfection.coeff (ModP OC p) p n) a b

/-- For `h` near `g`, the elements `h • x` and `g • x` of the tilt have the same `n`-th coordinate
modulo `p`: it comes from the translate of `x.untiltRoot n`, whose orbit map is continuous. -/
lemma eventually_coeff_smul_eq (x : OFlat) (g : Gp p) (n : ℕ) :
    ∀ᶠ h : Gp p in nhds g, Perfection.coeff (ModP OC p) p n (h • x) =
      Perfection.coeff (ModP OC p) p n (g • x) := by
  -- `σ` acts on the tilt coordinate by coordinate (`tiltMap`), so the `n`-th coordinate of `σ • x`
  -- is the class modulo `p` of `σ • x.untiltRoot n`.
  have h_coeff_smul (σ : Gp p) : Perfection.coeff (ModP OC p) p n (σ • x) =
      Ideal.Quotient.mk (span {↑p}) (σ • x.untiltRoot n) :=
    (congrArg _ (smul_oFlat_eq_tiltMap σ x)).trans (coeff_tiltMap _ (x.mk_untiltRoot n)).symm
  have h_near : ∀ᶠ h : Gp p in nhds g,
      dist (h • (x.untiltRoot n).val) (g • (x.untiltRoot n).val) < ‖(p : ℂ_[p])‖ :=
    tendsto_nhds.mp (continuousAt_id.smul_const _) _ (by simp [NeZero.ne])
  filter_upwards [h_near] with h h_dist
  -- The two classes agree as the distance is at most `‖p‖`.
  rw [h_coeff_smul, h_coeff_smul, Ideal.Quotient.eq]
  simpa [mem_span_singleton, valRingCp.dvd_iff_norm_le, dist_eq_norm] using h_dist.le

/-- For the valuation topology on `C^♭`, the orbit map `g ↦ g • y` of each `y` is continuous. -/
private lemma continuous_smul_cFlat (y : CFlat) :
    letI : Valued CFlat (ValuationRing.ValueGroup OFlat CFlat) :=
      mk' (ValuationRing.valuation OFlat CFlat)
    Continuous fun g : Gp p ↦ g • y := by
  let h_valued : Valued CFlat (ValuationRing.ValueGroup OFlat CFlat) :=
    mk' (ValuationRing.valuation OFlat CFlat)
  -- It is enough to treat an integral `x`, since every element is a quotient of two such.
  have cont_int (x : OFlat) : Continuous fun g : Gp p ↦ g • (x : CFlat) := by
    refine continuous_iff_continuousAt.mpr fun g s hs ↦ ?_
    -- The type of this ball is left to Lean: written out, it is too slow to elaborate.
    obtain ⟨γ, h_ball⟩ := mem_nhds.mp hs
    -- The radius `γ` is the valuation of a fraction `c / e`; some coordinate of `c` is not zero.
    obtain ⟨⟨c, e⟩, hγ⟩ : ∃ z : OFlat × OFlat⁰,
        restrict₀ (MonoidWithZeroHom.ofClass
          (Valued.v : Valuation CFlat (ValuationRing.ValueGroup OFlat CFlat)))
          (IsLocalization.mk' CFlat z.1 z.2) = γ.val :=
      ((restrict₀_surjective _).comp (mk'_surjective OFlat⁰)) γ.val
    obtain ⟨n, hn⟩ :
        ∃ n : ℕ, Perfection.coeff (ModP OC p) p n c ≠ Perfection.coeff (ModP OC p) p n 0 :=
      not_forall.mp fun h_all ↦ γ.ne_zero <|
        hγ.symm.trans (restrict₀_eq_zero_iff.2 (by simp [show c = 0 from ext h_all]))
    refine (eventually_coeff_smul_eq x g n).mono fun h h_coeff ↦ ?_
    -- Were `h • x` outside the ball, `c / e` would be an integral multiple of `h • x - g • x`,
    -- whose `n`-th coordinate is zero; so that of `c` would be zero too.
    refine h_ball ?_
    rw [← hγ]
    refine v.restrict_lt_iff.mpr (not_le.mp fun ⟨t, ht⟩ ↦ hn ?_)
    have c_eq : t * (h • x - g • x) * e = c := by
      simpa [eq_div_iff, Algebra.smul_def, ← map_mul, ← map_sub] using ht
    rw [← c_eq, coeff_oFlat_mul, coeff_oFlat_mul, coeff_oFlat_sub, h_coeff, sub_self, mul_zero,
      zero_mul, map_zero]
  obtain ⟨⟨c, e⟩, rfl⟩ := mk'_surjective OFlat⁰ y
  have h_div :
      Continuous ((fun g : Gp p ↦ g • (c : CFlat)) / fun g ↦ g • ((e : OFlat) : CFlat)) :=
    (cont_int c).div (cont_int e) fun g ↦ by simp [smul_eq_zero_iff_eq]
  simpa [smul_div₀', Pi.div_def] using h_div

/-- Continuity of the Galois action on `W(C^♭)`: for `a`, `d` in `W(C^♭)` and `m ≥ 0`, for all `g`
near `1` in `Gp p` the element `(g • a - a) * d` lies in `W(𝔪^♭) + p ^ m W(C^♭)`. -/
lemma WittCFlat.eventually_smul_sub_mem (a d : WittCFlat) (m : ℕ) :
    ∀ᶠ g : Gp p in nhds 1, ∃ b ∈ wittOfMaxIdeal, (p : WittCFlat) ^ m ∣ (g • a - a) * d - b := by
  -- The coefficients of `(g • a - a) * d` are continuous in `g` (`continuous_smul_cFlat`) and
  -- vanish at `g = 1`; the first `m` of them lie in the maximal ideal for `g` near `1`, and `b`
  -- is built from these.
  -- Unfold `WittCFlat` to the Witt vectors of `CFlat`, which the rest of the proof uses.
  unfold WittCFlat at *
  let h_valued : Valued CFlat (ValuationRing.ValueGroup OFlat CFlat) :=
    mk' (ValuationRing.valuation OFlat CFlat)
  -- `Z` is `(g • a - a) * d` as a Witt vector of continuous functions of `g`.
  let Z : WittVector p C(Gp p, CFlat) :=
    (mk p (fun i ↦ (⟨fun g ↦ g • a.coeff i, continuous_smul_cFlat _⟩ : C(Gp p, CFlat))) - a) * d
  have eval_Z (g : Gp p) :
      Z.map (ContinuousMap.evalAlgHom ℤ _ g).toRingHom = (g • a - a) * d := by aesop
  have h_coeff (g : Gp p) (i : ℕ) : ((g • a - a) * d).coeff i = Z.coeff i g :=
    congrArg (·.coeff i) (eval_Z g).symm
  -- The maximal ideal is the open unit ball, a neighbourhood of `0`.
  have near_one (i : ℕ) : ∀ᶠ g : Gp p in nhds 1, ∃ c : maximalIdeal OFlat,
      c.val • (1 : CFlat) = Z.coeff i g - Z.coeff i 1 := by
    refine ((Z.coeff i).continuous.tendsto 1).eventually
      (p := fun y ↦ ∃ c : maximalIdeal OFlat, c.val • 1 = y - Z.coeff i 1)
      (mem_nhds.mpr ⟨1, fun y hy ↦ ?_⟩)
    -- An element of valuation less than `1` is the image of some `c` in `O^♭`, and `1` is no
    -- multiple of it in `O^♭`; so `c` is not a unit.
    obtain ⟨⟨c, hc⟩, h_lt⟩ := v.restrict_lt_one_iff.mp hy
    have hc_max : c ∈ maximalIdeal OFlat := by
      intro hu
      have h_inv : hu.unit⁻¹ • c • (1 : CFlat) = 1 := inv_smul_smul hu.unit 1
      rw [hc] at h_inv
      exact h_lt ⟨hu.unit.inv, h_inv⟩
    exact ⟨⟨c, hc_max⟩, hc⟩
  filter_upwards [(Finset.range m).eventually_all.mpr fun i _ ↦ near_one i] with g hg
  choose! c hc using hg
  refine ⟨mk p fun i ↦ c i, mem_wittOfMaxIdeal.mpr fun i ↦ (c i).prop, ?_⟩
  -- Compare the first `m` coefficients: the `i`-th one of `(g • a - a) * d` is `Z.coeff i g`, and
  -- that of the Witt vector of the `c i` is `Z.coeff i g - Z.coeff i 1` (`hc`), with
  -- `Z.coeff i 1 = 0`.
  rw [Witt.pow_dvd_sub_iff_coeff_eq]
  intro i hi
  have h_coeff_one : Z.coeff i 1 = 0 := by simpa using (h_coeff 1 i).symm
  have h_eq : ((g • a - a) * d).coeff i = (c i).val • (1 : CFlat) := by
    rw [h_coeff, hc i (Finset.mem_range.mpr hi), h_coeff_one, sub_zero]
  -- Both sides are now the image of `c i` in `C^♭`.
  simpa [algebraMap_toAlgebra, Algebra.cast, Algebra.smul_def] using h_eq

end New.Lift

/-!
## The module W(C^♭) ⊗ T with its diagonal action

Let ρ be a representation of Γ on a ℤ_p-module T. `New.Lift.DiagTensor` ρ is W(C^♭) ⊗ T over ℤ_p,
with the action of ℤ × Γ (`New.Lift.FrobGroup`) given by m(a ⊗ t) = ma ⊗ ρ(m₂)t, where m₂ is the
image of m in Γ.
-/

section DiagonalTensor

open TensorProduct New Period

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p]
  {ρ ρ' ρ'' : Rep ℤ_[p] Γ} (f : ρ →ₗ[ℤ_[p]] ρ') (b : ρ →ₗ[ℤ_[p]] ρ' →ₗ[ℤ_[p]] ρ'')
  {R R' : Type*} [Semiring R] [Module R WittCFlat] [SMulCommClass ℤ_[p] R WittCFlat] [Semiring R']
  [Module R' WittCFlat] [SMulCommClass ℤ_[p] R' WittCFlat] [SMul R R']
  [IsScalarTower R R' WittCFlat]

/-- The tensor product `W(C^♭) ⊗ T` over `ℤ_p`, for a representation `T` of `Γ`. -/
def New.Lift.DiagTensor (T : Rep ℤ_[p] Γ) : Type _ := WittCFlat ⊗[ℤ_[p]] T
  deriving AddCommGroup

namespace New.Lift.DiagTensor

instance : Module R (DiagTensor ρ) := leftModule

deriving instance IsScalarTower R R' for DiagTensor ρ

instance : DistribMulAction (FrobGroup Γ) (DiagTensor ρ) :=
  .compHom (WittCFlat ⊗[ℤ_[p]] ρ)
    ((actionRep ℤ_[p] WittCFlat (.id (FrobGroup Γ))).tprod (ρ.ρ.comp FrobGroup.snd))

instance : SMulCommClass (FrobGroup Γ) ℤ_[p] (DiagTensor ρ) :=
  ⟨fun _ c x ↦ (TensorProduct.map _ _).map_smul c x⟩

/-- For a `ℤ_p`-linear map `f : T → T'`, the `W(C^♭)`-linear map `1 ⊗ f` from `W(C^♭) ⊗ T` to
`W(C^♭) ⊗ T'`. -/
def map : DiagTensor ρ →ₗ[WittCFlat] DiagTensor ρ' := f.baseChange WittCFlat

/-- For a `ℤ_p`-bilinear map `b : T × T' → T''`, its `W(C^♭)`-bilinear extension
`(W(C^♭) ⊗ T) × (W(C^♭) ⊗ T') → W(C^♭) ⊗ T''`. -/
def pair : DiagTensor ρ →ₗ[WittCFlat] DiagTensor ρ' →ₗ[WittCFlat] DiagTensor ρ'' :=
  baseChangePairing b

/-- The map `(a, t) ↦ a ⊗ t` into `W(C^♭) ⊗ T`, linear over `W(C^♭)` in `a` and over `ℤ_p` in
`t`. -/
def mk : WittCFlat →ₗ[WittCFlat] ρ →ₗ[ℤ_[p]] DiagTensor ρ :=
  AlgebraTensorModule.mk ℤ_[p] WittCFlat WittCFlat ρ

/-- A property of the elements of `W(C^♭) ⊗ T` that holds for the pure tensors `a ⊗ t` and is
stable under addition holds for all elements. -/
@[elab_as_elim]
protected lemma induction {P : DiagTensor ρ → Prop} (x : DiagTensor ρ)
    (h_mk : ∀ (a : WittCFlat) (t : ρ), P (mk a t))
    (h_add : ∀ x y : DiagTensor ρ, P x → P y → P (x + y)) : P x :=
  TensorProduct.inductionOn (motive := P) x h_mk h_add

/-- `DiagTensor.induction` with the element last. Stability under addition has a default proof,
meant for the case where `P x` says that additive maps agree at `x`. -/
lemma _root_.New.Lift.diagTensor_induction {P : DiagTensor ρ → Prop}
    (h : ∀ (a : WittCFlat) (t : ρ), P (mk a t))
    (h_add : ∀ x y : DiagTensor ρ, P x → P y → P (x + y) := by simp +contextual <;> grind)
    (x : DiagTensor ρ) : P x :=
  DiagTensor.induction x h h_add

@[simp]
lemma smul_mk (m : FrobGroup Γ) (a : WittCFlat) (t : ρ) :
    m • no_index (mk a t) = mk (m • a) (ρ.ρ (FrobGroup.snd m) t) :=
  rfl

instance [SMul (FrobGroup Γ) R] [SMulDistribClass (FrobGroup Γ) R WittCFlat] :
    SMulDistribClass (FrobGroup Γ) R (DiagTensor ρ) where
  smul_distrib_smul m r x := by
    induction x using DiagTensor.induction with
    -- both sides are pure tensors with second factor `ρ.ρ (FrobGroup.snd m) t`
    | h_mk a t => exact congrArg (mk · _) (smul_distrib_smul m r a)
    | h_add x y hx hy => rw [smul_add, smul_add, smul_add, smul_add, hx, hy]

@[simp]
lemma map_mk (a : WittCFlat) (t : ρ) : map f (no_index (mk a t)) = mk a (f t) := rfl

@[simp]
lemma pair_mk (a a' : WittCFlat) (t : ρ) (t' : ρ') :
    pair b (no_index (mk a t)) (no_index (mk a' t')) = mk (a * a') (b t t') :=
  rfl

end New.Lift.DiagTensor

end DiagonalTensor

/-!
## The Artin–Schreier sequence with coefficients ℤ/p^m(1)

Let M be W(C^♭) ⊗ ℤ_p/p^m(1): the module `New.Lift.DiagTensor` of the representation of Γ on ℤ_p/p^m
through the cyclotomic character `New.Period.χ`. In Lean this is
`Rep.of (charRep (QuotSpan (p ^ m)) χ)`, where `QuotSpan` is ℤ_p modulo the span of p^m and
`charRep` makes Γ act through χ.
-/

namespace New.Lift

open Period Algebra TensorProduct Ideal Ideal.Quotient FrobGroup algebraMap WittVector Witt

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p]

/-- The `A_inf`-submodule `W(𝔪^♭) • (1 ⊗ 1)` of `W(C^♭) ⊗ ℤ_p/p^m(1)`: the image of the ideal
`New.Lift.wittOfMaxIdeal` under `a ↦ a • (1 ⊗ 1)`. -/
noncomputable def smallPart (m : ℕ) :
    Submodule Ainf (DiagTensor (Rep.of (charRep (QuotSpan ((p : ℤ_[p]) ^ m)) χ))) :=
  Submodule.map
    (LinearMap.toSpanSingleton Ainf (DiagTensor (Rep.of (charRep (QuotSpan (p ^ m : ℤ_[p])) χ)))
      (DiagTensor.mk 1 1))
    wittOfMaxIdeal

@[simp]
lemma FrobGroup.snd_inr (g : GroupOverGp.G) : snd (FrobGroup.inr g) = g := rfl

@[simp]
lemma FrobGroup.snd_phi : snd φ = 1 := rfl

lemma FrobGroup.commute_phi (n : FrobGroup Γ) : Commute φ n :=
  .prod (.all _ _) (.one_left _)

/-- The submodule `New.Lift.smallPart m` is stable under Γ. -/
lemma smul_mem_smallPart {m : ℕ} (g : Γ)
    {x : DiagTensor (Rep.of (charRep (QuotSpan ((p : ℤ_[p]) ^ m)) χ))} :
    x ∈ smallPart m → inr g • x ∈ smallPart m := by
  rintro ⟨a, ha, rfl⟩
  -- `g` acts on Witt coordinates by an automorphism, so non-units stay non-units.
  have ga_mem : inr g • a ∈ wittOfMaxIdeal := mem_wittOfMaxIdeal.mpr fun i hi ↦
    mem_wittOfMaxIdeal.mp ha i (.of_map (MulDistribMulAction.toMulEquiv ..) _ hi)
  -- `g` sends `a ⊗ 1` to `g a ⊗ χ g`; move the scalar to the left factor.
  refine ⟨χ g • inr g • a, wittOfMaxIdeal.smul_of_tower_mem _ ga_mem, ?_⟩
  -- `using!`: `smul_tmul` is about `W(C^♭) ⊗ T`, which `DiagTensor` is only by definition; the
  -- plain form leaves `(charRep … χ) g 1` unread as `χ g • 1`.
  simpa [smul_distrib_smul] using! smul_tmul ..

/-- If `φ x - x` lies in `W(𝔪)` modulo `p ^ m`, then `x` is a constant of `ℤ_[p]` modulo `W(𝔪)` and
`p ^ m`. -/
lemma exists_const_of_frobenius_sub {m : ℕ} (x : WittCFlat) {a : Ainf} (ha : a ∈ wittOfMaxIdeal)
    (h_dvd : (p : WittCFlat) ^ m ∣ WittVector.frobenius x - x - algebraMap Ainf WittCFlat a) :
    ∃ c : ℤ_[p], ∃ b ∈ wittOfMaxIdeal,
      (p : WittCFlat) ^ m ∣ x - algebraMap ℤ_[p] WittCFlat c - algebraMap Ainf WittCFlat b := by
  -- `φ - 1` is onto, on `Ainf` and on `WittCFlat`: write `a = φ e - e`, and write `w`, where
  -- `φ x - x - a = p ^ m * w`, as `φ y - y`.
  obtain ⟨w, hw⟩ := h_dvd
  obtain ⟨e, rfl⟩ := a.exists_frobEnd_sub_xi_pow_mul_eq 0
  obtain ⟨y, rfl⟩ := artin_schreier_witt 1 w
  -- The reduction of `e` is fixed by Frobenius, so it is a constant `c`, and `e - c ∈ W(𝔪)`.
  have h_frob_residue : WittVector.frobenius (Period.toWittResidue e) = Period.toWittResidue e := by
    simpa [wittOfMaxIdeal, Period.toWittResidue, frobEnd_eq_frobenius, sub_eq_zero,
      WittVector.ext_iff] using ha
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_frobenius_eq _ h_frob_residue
  -- What is left of `x` is fixed by `φ`, so it is a constant too.
  obtain ⟨c', hc'⟩ : ∃ c' : ℤ_[p], algebraMap ℤ_[p] WittCFlat c' = x - (p ^ m * y + ↑(e - c)) := by
    refine exists_algebraMap_eq_of_frobenius_eq _ ?_
    -- `simp_all` applies `φ` termwise and uses `hw` (how `φ` moves `x`) and that `φ` fixes the
    -- constant `c`; `ring` rearranges.
    simp_all [← phi_smul_wittCFlat, phi_smul_ainf, smul_sub, sub_eq_iff_eq_add]
    ring
  refine ⟨c', e - c, ?_, ?_⟩
  · -- `e - c` reduces to `0`, by the choice of `c`.
    simp [wittOfMaxIdeal, ← hc]
  · simp [hc']

omit Γ in
/-- A constant of `ℤ_[p]` that lies in `W(𝔪)` modulo `p ^ m` is divisible by `p ^ m`. -/
lemma pow_dvd_of_pow_dvd_algebraMap_sub {m : ℕ} (c : ℤ_[p]) {a : Ainf} (ha : a ∈ wittOfMaxIdeal)
    (h_dvd : (p : WittCFlat) ^ m ∣ algebraMap ℤ_[p] WittCFlat c - algebraMap Ainf WittCFlat a) :
    (p : ℤ_[p]) ^ m ∣ c := by
  -- Compare the first `m` Witt coordinates: those of `c` lie in `𝔽_p`, those of `a` are not units.
  change (p : WittVector p CFlat) ^ m ∣
    algebraMap ℤ_[p] (WittVector p CFlat) c - algebraMap Ainf (WittVector p CFlat) a at h_dvd
  rw [← wittVector_map_algebraMap (algebraMap OFlat CFlat), Witt.pow_dvd_sub_iff_coeff_eq] at h_dvd
  rw [← map_dvd_iff (equiv p).symm, map_pow, map_natCast, ← sub_zero ((equiv p).symm _),
    Witt.pow_dvd_sub_iff_coeff_eq]
  -- Now `h_dvd` says that `c` and `a` have the same first `m` coordinates in `CFlat`, and the
  -- goal is that the first `m` coordinates of `c` in `W(𝔽_p)` vanish.
  intro i hi
  have h_coeff : (algebraMap ℤ_[p] Ainf c).coeff i = a.coeff i := (coe_inj ..).mp (h_dvd i hi)
  -- A nonzero element of `𝔽_p` is a unit, so it would make `a.coeff i` a unit.
  suffices h_not_unit : ¬IsUnit (((equiv p).symm c).coeff i) by simpa using h_not_unit
  exact fun hu ↦ mem_wittOfMaxIdeal.mp ha i (h_coeff.subst (hu.map _))

/-- `p ^ m` kills `W(C^♭) ⊗ ℤ_p/p^m(1)`. -/
lemma TateTwist.pow_smul_eq_zero {m : ℕ}
    (d : DiagTensor (Rep.of (charRep (QuotSpan ((p : ℤ_[p]) ^ m)) χ))) : p ^ m • d = 0 := by
  induction d using DiagTensor.induction with
  | h_mk x c => rw [← map_nsmul, Selmer.nsmul_quot_eq_zero dvd_rfl, map_zero]
  | h_add d e hd he => rw [nsmul_add, hd, he, add_zero]

/-- The map `x ↦ x ⊗ 1` from `W(C^♭)` onto `W(C^♭) ⊗ ℤ_p/p^m(1)`. -/
private def TateTwist.oneTmul (m : ℕ) (x : WittCFlat) :
    DiagTensor (Rep.of (charRep (QuotSpan ((p : ℤ_[p]) ^ m)) χ)) :=
  .mk x 1

private lemma TateTwist.oneTmul_surjective (m : ℕ) :
    Function.Surjective (TateTwist.oneTmul (Γ := Γ) m) :=
  flip_mk_surjective _ mk_surjective

private lemma TateTwist.oneTmul_sub_oneTmul {m : ℕ} (x y : WittCFlat) :
    TateTwist.oneTmul (Γ := Γ) m x - TateTwist.oneTmul m y = TateTwist.oneTmul m (x - y) :=
  (LinearMap.map_sub₂ ..).symm

/-- The Frobenius `φ` acts on `x ⊗ 1` through its first factor. -/
private lemma TateTwist.phi_smul_oneTmul {m : ℕ} (x : WittCFlat) :
    φ • TateTwist.oneTmul (Γ := Γ) m x = TateTwist.oneTmul m (frobenius x) :=
  (DiagTensor.smul_mk ..).trans (by simp [TateTwist.oneTmul, phi_smul_wittCFlat])

/-- A constant `1 ⊗ c`, for `c` in `ℤ_p`, is `c ⊗ 1`. -/
private lemma TateTwist.mk_one_mk_eq_oneTmul {m : ℕ} (c : ℤ_[p]) :
    .mk 1 (mk (span {(p : ℤ_[p]) ^ m}) c) =
      TateTwist.oneTmul (Γ := Γ) m (algebraMap ℤ_[p] WittCFlat c) :=
  includeRight.commutes c

/-- `x ⊗ 1` lies in `W(𝔪^♭) • (1 ⊗ 1)` exactly when `x` is congruent modulo `p ^ m` to an element
of `W(𝔪^♭)`. -/
private lemma TateTwist.oneTmul_mem_smallPart_iff {m : ℕ} (x : WittCFlat) :
    TateTwist.oneTmul (Γ := Γ) m x ∈ smallPart m ↔
      ∃ a ∈ wittOfMaxIdeal, (p : WittCFlat) ^ m ∣ x - algebraMap Ainf WittCFlat a := by
  -- `y ⊗ 1 = x ⊗ 1` means `x ≡ y` modulo `p ^ m`
  have h_eq (y : WittCFlat) : TateTwist.oneTmul (Γ := Γ) m y = TateTwist.oneTmul m x ↔
      x - y ∈ span {(p : ℤ_[p]) ^ m} • (⊤ : Submodule ℤ_[p] WittCFlat) := by
    have h_quot (z : WittCFlat) : tensorQuotEquivQuotSMul WittCFlat _
        (TateTwist.oneTmul (Γ := Γ) m z) = Submodule.Quotient.mk z :=
      (tensorQuotEquivQuotSMul_tmul_mk ..).trans (by simp)
    rw [← Submodule.Quotient.eq, ← h_quot, ← h_quot, eq_comm]
    exact (LinearEquiv.injective _).eq_iff.symm
  refine exists_congr fun a ↦ and_congr_right' ((h_eq (a • 1)).trans ?_)
  simp [map_span, mem_span_singleton, ← algebraMap_eq_smul_one]

/-- `φ - 1` is onto `W(C^♭) ⊗ ℤ_p/p^m(1)`, as it is onto `W(C^♭)`. -/
lemma TateTwist.exists_eq_phi_smul_sub {m : ℕ}
    (d : DiagTensor (Rep.of (charRep (QuotSpan ((p : ℤ_[p]) ^ m)) χ))) :
    ∃ e : DiagTensor (Rep.of (charRep (QuotSpan ((p : ℤ_[p]) ^ m)) χ)), d = φ • e - e := by
  obtain ⟨x, rfl⟩ := TateTwist.oneTmul_surjective m d
  obtain ⟨y, rfl⟩ := artin_schreier_witt 1 x
  exact ⟨TateTwist.oneTmul m y, by rw [TateTwist.phi_smul_oneTmul, TateTwist.oneTmul_sub_oneTmul,
    one_mul]⟩

/-- If `φ d - d` lies in `W(𝔪^♭) • (1 ⊗ 1)` (`New.Lift.smallPart`), then `d` is a constant `1 ⊗ k`
modulo that submodule. -/
lemma TateTwist.exists_sub_mk_one_mem_smallPart_of_phi_smul_sub_mem {m : ℕ}
    {d : DiagTensor (Rep.of (charRep (QuotSpan ((p : ℤ_[p]) ^ m)) χ))}
    (hd : φ • d - d ∈ smallPart m) :
    ∃ k : (Rep.of (charRep (QuotSpan ((p : ℤ_[p]) ^ m)) χ) : Type),
      d - DiagTensor.mk 1 k ∈ smallPart m := by
  obtain ⟨x, rfl⟩ := TateTwist.oneTmul_surjective m d
  rw [TateTwist.phi_smul_oneTmul, oneTmul_sub_oneTmul, oneTmul_mem_smallPart_iff] at hd
  obtain ⟨a, ha, h_dvd⟩ := hd
  -- `x` is a constant `c` modulo `W(𝔪)` and `p ^ m`
  obtain ⟨c, hc⟩ := exists_const_of_frobenius_sub x ha h_dvd
  refine ⟨mk _ c, ?_⟩
  rwa [mk_one_mk_eq_oneTmul, oneTmul_sub_oneTmul, oneTmul_mem_smallPart_iff]

/-- A constant `1 ⊗ k` of `W(C^♭) ⊗ ℤ_p/p^m(1)` lies in `W(𝔪^♭) • (1 ⊗ 1)` (`New.Lift.smallPart`)
only for `k = 0`. -/
lemma TateTwist.eq_zero_of_mk_one_mem_smallPart {m : ℕ}
    {k : (Rep.of (charRep (QuotSpan ((p : ℤ_[p]) ^ m)) χ) : Type)}
    (hk : DiagTensor.mk 1 k ∈ smallPart m) : k = 0 := by
  -- `k` is the class of some `c : ℤ_[p]`
  obtain ⟨c, rfl⟩ := mk_surjective k
  rw [TateTwist.mk_one_mk_eq_oneTmul, TateTwist.oneTmul_mem_smallPart_iff] at hk
  obtain ⟨a, ha, h_dvd⟩ := hk
  exact (eq_zero_iff_dvd ..).2 (pow_dvd_of_pow_dvd_algebraMap_sub c ha h_dvd)

/-- Let `ρ` be a representation of `Γ` with `g y - y` divisible by `p ^ m` for `g` near `1`, for
each `y`, and `L` a `W(C^♭)`-linear map from `W(C^♭) ⊗ ρ` to `W(C^♭) ⊗ ℤ_p/p^m(1)`. Then for each
`v`, `L (g v - v)` lies in `W(𝔪^♭) • (1 ⊗ 1)` (`New.Lift.smallPart`) for `g` near `1`. -/
lemma TateTwist.eventually_map_smul_sub_mem_smallPart {m : ℕ} {ρ : Rep ℤ_[p] Γ}
    (h_near : ∀ y : ρ, ∀ᶠ g : GroupOverGp.G in nearOne Γ, ∃ w : ρ, ρ.ρ g y - y = p ^ m • w)
    (L : DiagTensor ρ →ₗ[WittCFlat] DiagTensor (Rep.of (charRep (QuotSpan ((p : ℤ_[p]) ^ m)) χ)))
    (v : DiagTensor ρ) :
    ∀ᶠ g : GroupOverGp.G in nearOne Γ, L (inr g • v - v) ∈ smallPart m := by
  induction v using DiagTensor.induction with
  | h_mk x y =>
    -- Write `L (1 ⊗ y) = d ⊗ 1`. Near `1`, `g` fixes `y` modulo `p ^ m`, and `(g x - x) * d` lies
    -- in `W(𝔪)` modulo `p ^ m` (`WittCFlat.eventually_smul_sub_mem`).
    obtain ⟨d, hd⟩ := TateTwist.oneTmul_surjective m (L (.mk 1 y))
    have h_map (a : WittCFlat) : L (.mk a y) = TateTwist.oneTmul m (a * d) := by
      trans a • L (.mk 1 y)
      · simp [← map_smul, ← DiagTensor.mk.map_smul₂]
      · simp [← hd, TateTwist.oneTmul, ← DiagTensor.mk.map_smul₂]
    filter_upwards [(WittCFlat.eventually_smul_sub_mem x d m).comap _, h_near y] with g hg ⟨w, hw⟩
    have h_map_sub : L (inr g • .mk x y - .mk x y) = TateTwist.oneTmul m ((inr g • x - x) * d) := by
      simp [eq_add_of_sub_eq hw, TateTwist.pow_smul_eq_zero, h_map, TateTwist.oneTmul_sub_oneTmul,
        sub_mul]
    rwa [h_map_sub, TateTwist.oneTmul_mem_smallPart_iff]
  | h_add v w hv hw =>
    filter_upwards [hv, hw] with g hv_mem hw_mem
    simpa [add_sub_add_comm] using add_mem hv_mem hw_mem

/-- Five facts about `M = W(C^♭) ⊗ ℤ_p/p^m(1)` and `S = W(𝔪^♭) • (1 ⊗ 1)` (`New.Lift.smallPart`) in
one statement; the elements `1 ⊗ k`, with `k` in ℤ_p/p^m(1) (in (c) and in (d)), are the constants.
They are (a) `TateTwist.pow_smul_eq_zero`, (b) `TateTwist.exists_eq_phi_smul_sub`, (c)
`TateTwist.exists_sub_mk_one_mem_smallPart_of_phi_smul_sub_mem`, (d)
`TateTwist.eq_zero_of_mk_one_mem_smallPart` and (e)
`TateTwist.eventually_map_smul_sub_mem_smallPart`. -/
lemma TateTwist.smallPart_spec {m : ℕ} {ρ : Rep ℤ_[p] Γ}
    (h_near : ∀ y : ρ, ∀ᶠ g : GroupOverGp.G in nearOne Γ, ∃ w : ρ, ρ.ρ g y - y = p ^ m • w)
    (L : DiagTensor ρ →ₗ[WittCFlat] DiagTensor (Rep.of (charRep (QuotSpan (p ^ m : ℤ_[p])) χ))) :
    let S := smallPart m
    (∀ d : DiagTensor (Rep.of (charRep (QuotSpan ((p : ℤ_[p]) ^ m)) χ)),
      -- (a)
      p ^ m • d = 0 ∧
      -- (b)
      (∃ e : DiagTensor (Rep.of (charRep (QuotSpan ((p : ℤ_[p]) ^ m)) χ)), d = φ • e - e) ∧
      -- (c)
      (φ • d - d ∈ S →
       ∃ k : (Rep.of (charRep (QuotSpan ((p : ℤ_[p]) ^ m)) χ) : Type), d - DiagTensor.mk 1 k ∈ S)) ∧
    -- (d)
    (∀ k, DiagTensor.mk 1 k ∈ S → k = 0) ∧
    -- (e)
    ∀ v : DiagTensor ρ, ∀ᶠ g : GroupOverGp.G in nearOne Γ, L (inr g • v - v) ∈ S :=
  ⟨fun d ↦ ⟨pow_smul_eq_zero d, exists_eq_phi_smul_sub d,
      exists_sub_mk_one_mem_smallPart_of_phi_smul_sub_mem⟩,
    fun _ ↦ eq_zero_of_mk_one_mem_smallPart, eventually_map_smul_sub_mem_smallPart h_near L⟩

end New.Lift

end
