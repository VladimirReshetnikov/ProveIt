import Lib.Weil.Construction.ProductsAndTransport

/-!
# Data named by Schwartz–Bruhat functions: Heisenberg laws, transport, Weil action

Let S be a set of finite places disjoint from its conjugate S̄. A Schwartz–Bruhat function Ψ above S
names an operator `V.schrodingerOp S Ψ` on 𝒮(V). The box function names the projection P^S =
`New.Space.projOn` S. Its translates name Heisenberg translates ϱ(αy₊) P^S of it, with α the finite
idele of `New.WeilData`. Naming is compatible with products of data. For general g, Ψ is composed
with g_f⁻¹ and the vector also changes.

## Main definitions and results

* `New.Space.schrodingerOp`: sends ∑ c_y (translate of the indicator by y) to the operator ∑ c_y
  ϱ(αy₊) P^S, with y₊ the part of y above S ∪ S̄ and P^S = `New.Space.projOn` S.
* `New.Space.rho_schrodingerOp`: naming is equivariant for the Heisenberg operators of the parts of
  vectors above S ∪ S̄.
* `New.Space.dataInner_schrodingerOp`: the inner product of two named vectors factors.
* `New.Space.schrodingerOp_union`: for disjoint `S`, `T` with `S ∪ T` disjoint from its conjugate, a
  product of functions names the composite.
* `New.Space.omega_schrodingerOp`: for any `g`, `ω g (schrodingerOp Ψ f) = schrodingerOp (Ψ ∘ g_f⁻¹)
  u`, where `u` is `ω g` applied to the name of the box function composed with `g_f`, and `u` is
  fixed by `V.projOn S`.
* `New.Space.omega_schrodingerOp_of_mem_supportedOn`: `g` supported on `S ∪ S̄` acts by
  `Ψ ↦ Ψ ∘ g⁻¹`, times the conjugate of `New.chiAdelic` at the `S`-part of `det g`.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with
  xᴴJx equal to the diagonal matrix of its signs at the infinite places and 1 at the finite places.
* `New.Space.ϱ`: the Heisenberg operator of an adelic vector `y` on `𝒮 V`.
* `New.Space.projOn`: the operator P^S on 𝒮(V), the mean over y in Ô^n of the finite Heisenberg
  operators `New.Space.finHeisenbergOp` at the part of y above S ∪ S̄ (`S.conjClosure`).
* `New.localInner`: the integral of conj(Ψ) Ψ′ over the finite adelic vectors integral off S,
  normalised so that Ô^n has mass one.
* `New.WeilData`: Weil data on a stably unramified E. They consist of ȷ in E with ȷ = −ȷ̄, Im τȷ > 0
  for every τ in the CM type and (1 − ȷ⁻¹)/2 integral; a finite idele α for which the completed
  integers Ô are self-dual under (z, u) ↦ ψ_f(ȷαᾱzu); and a splitting character υ equal to −1 at
  uniformisers of the places w with w = w̄.

## Relation to the literature

Known; see `Lib.Weil.MixedModel.ZeroTerm` for sources.
-/

noncomputable section

/-!
## Naming vectors by Schwartz–Bruhat functions at split places

Transfer from the Schrödinger model at a set S of finite places to the space 𝒮(V) of the Weil
representation. The Heisenberg group acts on functions above S by `New.schrodingerAct`. For S
disjoint from its conjugate, a Schwartz–Bruhat function above S (`New.IsSchwartzBruhat`) is a
combination of translates of the indicator `New.boxIndicator` of the vectors integral on S.

`New.idem` S is the idempotent of S in the finite adeles. `New.finVec` y is the adelic vector with
finite part αy and zero real part.
-/

namespace New.Space

open NumberField MeasureTheory stdLattice Finset Complex AddChar Matrix IsSchwartzBruhat

variable {E : Type*} [Field E] [CMType E] [WeilData E]
  {n : Type*} [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} {S : Set (FinPlace E)} (hS : S.IsConjDisjoint) (V : Space E n s)
  {Ψ Ψ' : (n → 𝔸f E) → ℂ}

/-- The linear map sending finitely supported coefficients c_y to the operator ∑ c_y ϱ(αy₊) P^S
on 𝒮(V), y₊ the part of y above S ∪ S̄. -/
def heisenbergCombination (S : Set (FinPlace E)) : ((n → 𝔸f E) →₀ ℂ) →ₗ[ℂ] 𝒮 V →L[ℂ] 𝒮 V :=
  Finsupp.lift (𝒮 V →L[ℂ] 𝒮 V) ℂ (n → 𝔸f E) fun y ↦
    V.ϱ (finVec (idem S.conjClosure • y)) ∘L V.projOn S

/-- The linear map Ψ ↦ Ψ⊗ from functions on finite adelic vectors to operators on 𝒮(V):
`New.Space.heisenbergCombination` of chosen coefficients c, with `New.schrodingerCombination` c = Ψ
when such exist. -/
def schrodingerOp (S : Set (FinPlace E)) : ((n → 𝔸f E) → ℂ) →ₗ[ℂ] 𝒮 V →L[ℂ] 𝒮 V :=
  V.heisenbergCombination S ∘ₗ (exists_generalized_inverse (schrodingerCombination S)).choose

/-- `V.schrodingerOp S Ψ` is the operator `Ψ⊗` on `𝒮 V`: a combination of Heisenberg operators
composed with the projection `V.projOn S`, with chosen coefficients whose Schrödinger combination is
`Ψ`, when such coefficients exist. It commutes with every bounded operator `A` on `𝒮 V` that
commutes with `V.ϱ y` for all adelic vectors `y` with zero real part whose finite part is zero off
`S` and its conjugate. -/
lemma commute_schrodingerOp {A : 𝒮 V →L[ℂ] 𝒮 V}
    (h_comm : ∀ y : n → 𝔸 E, (∀ i : n, (y i).1 = 0) →
      (∀ i : n, ∀ w ∉ S.conjClosure, (y i).2 w = 0) → Commute A (V.ϱ y))
    (Ψ : (n → 𝔸f E) → ℂ) : Commute A (V.schrodingerOp S Ψ) := by
  -- The named operator is a combination of translations composed with a mean of translations,
  -- all by vectors supported above `S.conjClosure`.
  have h_shift (y : n → 𝔸f E) (f : 𝒮 V) :
      A (V.ϱ (finVec (idem S.conjClosure • y)) f) =
        V.ϱ (finVec (idem S.conjClosure • y)) (A f) := by
    refine DFunLike.congr_fun (h_comm _ (fun _ ↦ rfl) fun i w hw ↦ ?_).eq f
    simp [finVec, idem_of_notMem hw]
  have h_proj (f : 𝒮 V) : A (V.projOn S f) = V.projOn S (A f) := by
    have h_mean : A (V.projOn S f) = ∫ y : n → 𝔸f E in stdLattice E n,
        V.finHeisenbergOp (idem S.conjClosure • y) (A f) ∂latticeMeasure E n :=
      V.map_projOn A fun y _ ↦ by simp [finHeisenbergOp, h_shift]
    exact h_mean.trans (V.map_projOn (ContinuousLinearMap.id ℂ (𝒮 V)) fun _ _ ↦ rfl).symm
  ext f : 1
  simp [schrodingerOp, heisenbergCombination, Finsupp.sum, h_shift, h_proj]

/-- For v in the Fock space and f in 𝒮(V), v⊗(Ψ⊗f) = Ψ⊗(v⊗f): the operators `New.Space.integrated` v
and `New.Space.schrodingerOp` S Ψ commute. -/
lemma integrated_schrodingerOp (v : Heisenberg.IsVacuum.Model (Fock.realHeisenberg (realSigns E s)))
    (f : 𝒮 V) :
    V.integrated v (V.schrodingerOp S Ψ f) = V.schrodingerOp S Ψ (V.integrated v f) := by
  have h_comm : Commute (V.integrated v) (V.schrodingerOp S Ψ) := by
    refine V.commute_schrodingerOp (fun y hy_real _ ↦ ContinuousLinearMap.ext fun u ↦ ?_) Ψ
    exact (V.rho_integrated v u hy_real).symm
  exact DFunLike.congr_fun h_comm.eq f

/-- For any function `Ψ` on finite adelic vectors, the operator Ψ⊗ = `V.schrodingerOp S Ψ` on 𝒮(V)
commutes with the Heisenberg operator `V.ϱ z` of any adelic vector `z` whose finite components
vanish at the places of S ∪ S̄. -/
lemma commute_rho_schrodingerOp {z : n → 𝔸 E} (hz : ∀ i : n, ∀ w ∈ S.conjClosure, (z i).2 w = 0)
    (Ψ : (n → 𝔸f E) → ℂ) : Commute (V.ϱ z) (V.schrodingerOp S Ψ) := by
  refine V.commute_schrodingerOp (fun y hy_real hy_off ↦ ?_) Ψ
  -- The coordinates of `z` and `y` have disjoint supports, so the commutator is trivial.
  have h_zero (i : n) : star (y i) * z i = 0 := by
    refine Prod.ext (by simp [hy_real]) ?_
    ext w
    by_cases hw : w ∈ S.conjClosure
    · simp [hz i w hw]
    · simp [hy_off i (star w) (by simpa [and_comm] using hw)]
  have h_pair : star y ⬝ᵥ stdForm E s *ᵥ z = 0 := by
    simp [stdForm, dotProduct, mulVec_diagonal, mul_left_comm (star (y _)), h_zero]
  ext f : 1
  simp [V.rho_swap z y, adelicHeisenberg, h_pair]

/-- Naming ignores the projection P^S = `New.Space.projOn` S: `V.schrodingerOp S Ψ` takes the same
value at `P^S f` as at `f`. -/
lemma schrodingerOp_projOn (f : 𝒮 V) :
    V.schrodingerOp S Ψ (V.projOn S f) = V.schrodingerOp S Ψ f := by
  simp [schrodingerOp, ← projOn_union, heisenbergCombination, Finsupp.sum]

lemma smul_schrodingerOp (c : ℂ) (f : 𝒮 V) :
  c • V.schrodingerOp S Ψ f = V.schrodingerOp S (c • Ψ) f := by simp

omit [Fintype n] [DecidableEq n] in
/-- The translation vector `finVec (idem U.conjClosure • y)` vanishes at every place of `T` and of
its conjugate when `U ∪ Ū` is disjoint from `T`: there the idempotent of `U ∪ Ū` is `0`. -/
private lemma finVec_idem_smul_snd_eq_zero_of_disjoint {U T : Set (FinPlace E)}
    (hUT : Disjoint U.conjClosure T) (y : n → 𝔸f E) :
    ∀ i : n, ∀ w ∈ T.conjClosure, (finVec (idem U.conjClosure • y) i).2 w = 0 := by
  intro i w hw
  have hw_not : w ∉ U.conjClosure := by grind [star_star]
  simp [finVec, idem_of_notMem hw_not]

/-- If the set T of finite places is disjoint from S ∪ S̄, then Ψ ⊗ vac, named at S, with
vac = `V.vacElem` the vacuum vector of 𝒮(V), is fixed by the projection P^T. -/
lemma projOn_schrodingerOp_vacElem {T : Set (FinPlace E)} (hT : Disjoint S.conjClosure T) :
    V.projOn T (V.schrodingerOp S Ψ V.vacElem) = V.schrodingerOp S Ψ V.vacElem := by
  -- The projection commutes with translations by vectors that vanish at `T` and its conjugate
  -- (`projOn_rho`), and it fixes the vacuum.
  have h_comm (y : n → 𝔸f E) (f : 𝒮 V) :
      V.projOn T (V.ϱ (finVec (idem S.conjClosure • y)) f) =
        V.ϱ (finVec (idem S.conjClosure • y)) (V.projOn T f) :=
    V.projOn_rho (finVec_idem_smul_snd_eq_zero_of_disjoint hT y) f
  simp [schrodingerOp, h_comm, heisenbergCombination, Finsupp.sum]

/-- For g ∈ GL_n(𝔸_f), take `localInner S` (∫ conj(Ψ) Ψ′ over the finite adelic vectors integral off
S, for the Haar measure giving Ô^n mass one) of the indicator of vectors integral at S against its
transform x ↦ indicator(g x). This equals `‖Δ_f(g_S)‖⁻²`, where `g_S` (`cutGL`) is `g` above `S` and
`1` elsewhere. Here `Δ_f` (`New.glMultiplier`) is χ_f(det u) for the chosen u with uÔ^n = Ô^n ∩
g_S⁻¹Ô^n. -/
lemma localInner_boxIndicator_mulVec (g : GL n (𝔸f E)) :
    localInner S (boxIndicator n S) (fun x : n → 𝔸f E ↦ boxIndicator n S (g.val *ᵥ x)) =
      ((‖glMultiplier (cutGL (idem_mul_self S) g)‖ ^ 2)⁻¹ : ℝ) := by
  classical
  -- Both sides are the volume of the set `A` of integral `x` with `g x` integral on `S`; for the
  -- right side this is `latticeMeasure_inter_eq_glMultiplier`.
  set A : Set (n → 𝔸f E) :=
    {x | (cutGL (idem_mul_self S) g).1 *ᵥ x ∈ stdLattice E n ∧ x ∈ stdLattice E n} with hA
  have hA_open : IsOpen A := (isOpen_stdLattice.preimage (by fun_prop)).inter isOpen_stdLattice
  have h_volume : (((‖glMultiplier (cutGL (idem_mul_self S) g)‖ ^ 2)⁻¹ : ℝ) : ℂ) =
      ∫ x : n → 𝔸f E, ((A.indicator 1 x : ℝ) : ℂ) ∂latticeMeasure E n := by
    rw [← latticeMeasure_inter_eq_glMultiplier, ← hA, integral_complex_ofReal,
      integral_indicator_one hA_open.measurableSet]
  -- The left side is the integral of the indicators over all vectors.
  rw [h_volume, localInner, ← integral_indicator isOpen_integralBox.measurableSet]
  congr
  -- Compare the two indicators place by place: the cut matrix acts as `g` on `S`, as one off `S`.
  simp [hA, Set.indicator, mem_Ô, cutGL, add_mulVec, ↓idem_mul_mem_Ô, apply_ite, mem_integralBox,
    smul_mulVec, mem_stdLattice, idem_apply]
  funext x
  rw [← ite_and, ← ite_and]
  refine if_congr ⟨fun ⟨⟨h_off, h_mul⟩, h_on⟩ ↦ ⟨fun i w ↦ ?_, fun i w ↦ ?_⟩,
    fun ⟨h_cut, h_int⟩ ↦ ⟨⟨fun i w _ ↦ h_int i w, fun i w hw ↦ ?_⟩, fun i w _ ↦ h_int i w⟩⟩ rfl rfl
  · by_cases hw : w ∈ S
    · simpa [hw] using h_mul i w hw
    · simpa [hw] using h_off i w hw
  · by_cases hw : w ∈ S
    · exact h_on i w hw
    · exact h_off i w hw
  · simpa [hw] using h_cut i w

omit [DecidableEq n] in
/-- Over the vectors x integral off S, the integral of F x = 1(x+m) χ(z*(x+m)_S) c 1(z), with 1 the
indicator of integrality on S and χ = `New.stdLattice.selfDualAddChar`, is c if z is integral on S ∪
S̄ and 0 otherwise. The integrand `F` is given by the equation `h`. -/
lemma fourier_boxIndicator {F : (n → 𝔸f E) → ℂ} (m z : n → 𝔸f E) (c : ℂ)
    (h : ∀ x : n → 𝔸f E,
      boxIndicator n S (x + m) * selfDualAddChar E (star z ⬝ᵥ idem S • (x + m)) * c *
        boxIndicator n S z = F x) :
    ∫ x : n → 𝔸f E in integralBox n Sᶜ, F x ∂latticeMeasure E n =
      boxIndicator n S.conjClosure z * c := by
  classical
  -- The two boxes meet in the lattice, over which a character integrates to `1` or `0`.
  have h_lat :
      ∫ x in integralBox n Sᶜ, boxIndicator n S x *
          selfDualAddChar E (star z ⬝ᵥ idem S • x) ∂latticeMeasure E n =
        if star (idem S) • z ∈ stdLattice E n then 1 else 0 := by
    simpa [← integralBox_compl_inter (S := S),
      ← setIntegral_indicator isOpen_integralBox.measurableSet, Set.indicator] using
      integral_selfDualAddChar_stdLattice (star (idem S) • z)
  -- Shifting `x` by the part of `-m` at `S` removes `m` from the integrand.
  have h_shift_mem : idem S • -m ∈ integralBox n Sᶜ := by
    simp +contextual [mem_integralBox, idem_mul_mem_Ô]
  rw [← setIntegral_add_left_eq_self_of_mem (m := idem S • -m) _ h_shift_mem, ← funext h]
  simp_all [↓integral_mul_const, mem_integralBox, idem_mul_mem_Ô, star_idem, mem_stdLattice,
    smul_smul, idem_mul_self]
  -- `z` is integral on `S.conjClosure` when it is integral on `S` and on its conjugate.
  grind

include hS

/-! ### Naming is well defined when `S` is disjoint from its conjugate -/

/-- Let S be disjoint from its conjugate, let c, c′ be finitely supported coefficients indexed by
finite adelic vectors y, and let f, f′ ∈ 𝒮(V). Set A_c = `V.heisenbergCombination S c`, the operator
∑ c_y ϱ(αy₊) P^S on 𝒮(V) with y₊ the part of y above S ∪ S̄, and Ψ_c = `schrodingerCombination S c`,
the function ∑ c_y (`New.schrodingerAct` S y applied to the indicator of vectors integral on S),
where `schrodingerAct S y Φ` is x ↦ `selfDualAddChar E` (½ y*(2x + y)_S) · Φ(x + y). Then
`dataInner` (the pairing ∫ f̄ f′) gives ⟨A_c f, A_{c′} f′⟩ = `localInner S` Ψ_c Ψ_{c′} · ⟨P^S f, P^S
f′⟩, where `localInner S` is ∫ conj(Ψ) Ψ′ over the finite adelic vectors integral off S (Ô^n having
mass one), and P^S = `V.projOn S` is the mean over y ∈ Ô^n of the finite Heisenberg operators at the
part of y above S ∪ S̄. -/
lemma dataInner_heisenbergCombination (c c' : (n → 𝔸f E) →₀ ℂ) (f f' : 𝒮 V) :
    V.dataInner (V.heisenbergCombination S c f) (V.heisenbergCombination S c' f') =
      localInner S (schrodingerCombination S c) (schrodingerCombination S c') *
        V.dataInner (V.projOn S f) (V.projOn S f') := by
  classical
  -- Expand both sides as double sums over the supports of `c` and `c'`, and compare the terms of
  -- the translates by `y` and `y + z`.
  simp [mul_mul_mul_comm,
    (integrableOn_mul (continuous_conj.comp' (locally_constant S).continuous)).const_mul,
    heisenbergCombination, ← heisenbergRep_right_rho, Finsupp.sum, mul_sum, localInner, sum_mul,
    integrable_finsetSum, integral_finsetSum, integral_const_mul]
  congr! 2 with y' - y
  obtain ⟨z, rfl⟩ := add_left_surjective y y'
  -- On the right the integrand is a character on a translate of the box.
  have inner_translates :
      ∫ x in integralBox n Sᶜ, starRingEnd ℂ (schrodingerAct S y (boxIndicator n S) x) *
          schrodingerAct S (y + z) (boxIndicator n S) x ∂latticeMeasure E n =
        boxIndicator n S.conjClosure z *
          schrodingerAct S (-y) (schrodingerAct S (y + z) (boxIndicator n S)) 0 := by
    apply fourier_boxIndicator y z
    simp [schrodingerAct, integralBox, apply_ite, ← add_assoc, ← map_add_eq_mul,
      ← inv_eq_conj, ← map_neg_eq_inv]
    grind [add_mem_cancel_left]
  -- On the left translate back by `-y`, which leaves the translation by `z` between projections.
  rw [← dataInner_rho _ (finVec (idem S.conjClosure • -y)), inner_translates]
  by_cases hz : z ∈ integralBox n S.conjClosure
  · -- `finHeisenbergOp` at `z` fixes the projected vector, and `schrodingerAct S z` fixes the box
    -- up to the same semicharacter factor.
    nth_rw 4 [← V.finHeisenbergOp_projOn hz]
    have scalar :
        (semichar (idem S.conjClosure • z) • schrodingerAct S z (boxIndicator n S)) 0 =
          boxIndicator n S 0 :=
      congrFun (schrodingerAct_boxIndicator hS hz) 0
    simp_all [mem_integralBox, idem_mul_mem_Ô, ← heisenbergRep_right_rho, Heisenberg.Rep.mul,
      Heisenberg.self_eq_one, schrodingerAct_schrodingerAct, finHeisenbergOp, smul_smul,
        idem_mul_self]
    grind
  · -- The projection kills the translate by `z`, which is not integral.
    have proj :
        V.projOn S (V.finHeisenbergOp (idem S.conjClosure • z) (V.projOn S f')) =
          boxIndicator n S.conjClosure (idem S.conjClosure • z) •
            V.finHeisenbergOp (idem S.conjClosure • z) (V.projOn S f') :=
      V.projOn_finHeisenbergOp (V.projOn_projOn f') _
    simp_all [dataInner_projOn, schrodingerAct, integralBox, apply_ite,
      finHeisenbergOp, ← heisenbergRep_right_rho, smul_smul, idem_mul_self, Heisenberg.Rep.mul]

/-- The name does not depend on the choice of coefficients: for `S` disjoint from its conjugate,
the combination of translates of the indicator with coefficients `c` names
`V.heisenbergCombination S c`. -/
lemma schrodingerOp_schrodingerCombination (c : (n → 𝔸f E) →₀ ℂ) (f : 𝒮 V) :
    V.schrodingerOp S (schrodingerCombination S c) f = V.heisenbergCombination S c f := by
  -- By `dataInner_heisenbergCombination` the norm of the difference depends only on the values of
  -- `schrodingerCombination S`, and these agree on `c` and on the coefficients that `schrodingerOp`
  -- chooses.
  refine sub_eq_zero.mp (V.eq_zero_of_dataInner_self ?_)
  grind [schrodingerOp, dataInner_heisenbergCombination, LinearMap.comp_apply]

/-- Let `S` be disjoint from its conjugate. Then `schrodingerOp S` of the Schrödinger translate
`schrodingerAct S y` of the indicator `boxIndicator n S` sends `f` to `V.ϱ (finVec y₊)` applied to
P^S f = `V.projOn S f`, where y₊ = `idem S.conjClosure • y` is the part of `y` at S ∪ S̄.
Multiplying by `semichar y₊` gives the same rule for `finHeisenbergOp y₊`, with the phase of
`New.semichar_smul_schrodingerAct` on the left. -/
@[local simp]
lemma schrodingerOp_schrodingerAct_boxIndicator (y : n → 𝔸f E) (f : 𝒮 V) :
    V.schrodingerOp S (schrodingerAct S y (boxIndicator n S)) f =
      V.ϱ (finVec (idem S.conjClosure • y)) (V.projOn S f) := by
  simpa [heisenbergCombination] using V.schrodingerOp_schrodingerCombination hS (.single y 1) f

/-- For a set S of finite places disjoint from its conjugate, the indicator of the vectors
integral at all places of S names the operator P^S = `New.Space.projOn` S. -/
lemma schrodingerOp_boxIndicator : V.schrodingerOp S (boxIndicator n S) = V.projOn S := by
  simpa [schrodingerAct, ← heisenbergRep_right_rho] using
    funext (V.schrodingerOp_schrodingerAct_boxIndicator hS 0)
/-- Let `S` be disjoint from its conjugate and `Ψ` Schwartz–Bruhat above `S`, and write Ψ⊗ for the
operator `V.schrodingerOp S Ψ` on 𝒮(V). For a finite adelic vector `y`, let y' be `y` kept at S ∪ S̄
and set to 0 elsewhere. Then applying the Heisenberg operator `V.ϱ` of `finVec` y' (zero archimedean
part, finite part αy') to Ψ⊗f gives (`schrodingerAct S y Ψ`)⊗f, where `schrodingerAct S y Ψ` is
x ↦ `selfDualAddChar E` (½ y*(2x + y)_S) · Ψ(x + y). -/
lemma rho_schrodingerOp [IsSchwartzBruhat S Ψ] (y : n → 𝔸f E) (f : 𝒮 V) :
    V.ϱ (finVec (idem S.conjClosure • y)) (V.schrodingerOp S Ψ f) =
      V.schrodingerOp S (schrodingerAct S y Ψ) f := by
  -- Write `Ψ` as a combination of translates of the box: `ϱ` and `schrodingerAct` compose by the
  -- same rule.
  obtain ⟨c, rfl⟩ := mem_range_schrodingerCombination hS (Φ := Ψ) inferInstance
  simp [hS, ← heisenbergRep_right_rho, Finsupp.sum, Heisenberg.Rep.mul,
    schrodingerAct_schrodingerAct]

/-- Let `S` be disjoint from its conjugate and `Ψ`, `Ψ'` Schwartz–Bruhat above `S`, and write Ψ ⊗ f
for `V.schrodingerOp S Ψ f`. Then ⟨Ψ ⊗ f, Ψ′ ⊗ f′⟩ (the pairing `dataInner`, ∫ f̄ f′ on 𝒮(V)) equals
`localInner S Ψ Ψ'` times ⟨P^S f, P^S f′⟩. Here `localInner S Ψ Ψ'` is ∫ conj(Ψ) Ψ′ over the finite
adelic vectors integral off `S`, with Haar measure giving Ô^n mass one. P^S = `V.projOn S` is the
mean over y ∈ Ô^n of `finHeisenbergOp` at the part of y above S ∪ S̄. -/
lemma dataInner_schrodingerOp [IsSchwartzBruhat S Ψ] [IsSchwartzBruhat S Ψ'] (f f' : 𝒮 V) :
    V.dataInner (V.schrodingerOp S Ψ f) (V.schrodingerOp S Ψ' f') =
      localInner S Ψ Ψ' * V.dataInner (V.projOn S f) (V.projOn S f') := by
  -- Both functions are combinations of translates of the box.
  obtain ⟨c, rfl⟩ := mem_range_schrodingerCombination hS (Φ := Ψ) inferInstance
  obtain ⟨c', rfl⟩ := mem_range_schrodingerCombination hS (Φ := Ψ') inferInstance
  rw [V.schrodingerOp_schrodingerCombination hS, V.schrodingerOp_schrodingerCombination hS,
    V.dataInner_heisenbergCombination hS]

attribute [irreducible] schrodingerOp

end New.Space

/-!
## Names under changes of coordinates and products of data

Names on the vacuum are transported by a change of coordinates
(`New.CoordChange.map_schrodingerOp`).
-/

namespace New

open NumberField Matrix Finset Submodule Space Heisenberg

variable {E : Type*} [Field E] [CMType E] [WeilData E]
  {n : Type*} [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  {n₁ n₂ : Type*} [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂]
  {s₁ : n₁ → ℤˣ} {s₂ : n₂ → ℤˣ} {V : Space E n s} {V₁ : Space E n₁ s₁} {V₂ : Space E n₂ s₂}
  {S : Set (FinPlace E)} {Ψ : (n₁ → 𝔸f E) → ℂ} {Ψ' : (n₂ → 𝔸f E) → ℂ}
  {e : n₁ ⊕ n₂ ≃ n} (hs : s ∘ e = s₁ ⊕ᵥ s₂)

omit [Fintype n] [DecidableEq n] in
@[simp]
lemma finVec_zero : finVec (0 : n → 𝔸f E) = 0 := by simp [funext_iff, finVec]

/-- Names are transported by a change of coordinates `D`. Let `S` and `S'` be disjoint from their
conjugates. Let the finite part `D.finEquiv` carry parts at `S'` to parts at `S`, and parts at
`S'.conjClosure` to parts at `S.conjClosure` (the sets with their conjugates). For `Ψ`
Schwartz–Bruhat above `S`, `D.map` sends the vector named by `Ψ` on the vacuum of `V₁` to the vector
named by `σ ∘ Ψ ∘ D.finEquiv`, at `S'`, on the vacuum of `V`. -/
lemma CoordChange.map_schrodingerOp {σ : ℂ →+* ℂ} [RingHomIsometric σ] (D : CoordChange E σ s₁ s)
    {S' : Set (FinPlace E)}
    (h_finEquiv_idem : ∀ x : n → 𝔸f E, D.finEquiv (idem S' • x) = idem S • D.finEquiv x)
    (h_finEquiv_idem_conj : ∀ x : n → 𝔸f E,
      D.finEquiv (idem S'.conjClosure • x) = idem S.conjClosure • D.finEquiv x)
    (hS : S.IsConjDisjoint) (hS' : S'.IsConjDisjoint) [hΨ : IsSchwartzBruhat S Ψ] :
    D.map (V₁.schrodingerOp S Ψ V₁.vacElem) =
      V.schrodingerOp S' (fun x : n → 𝔸f E ↦ σ (Ψ (D.finEquiv x))) V.vacElem := by
  classical
  -- Write `Ψ` as a finite combination of translates of the box function.
  obtain ⟨c, rfl⟩ := mem_range_schrodingerCombination hS hΨ
  -- The transported function is the combination, with coefficients `σ a`, of the translates by
  -- `D.finEquiv.symm y`.
  have h_comb : (fun x ↦ σ (schrodingerCombination S c (D.finEquiv x))) =
      c.sum fun y a ↦ σ a • schrodingerAct S' (D.finEquiv.symm y) (boxIndicator n S') := by
    simp [schrodingerAct, integralBox, ↓← D.selfDualAddChar_finEquiv, h_finEquiv_idem, apply_ite,
      ← D.finEquiv_mem, Finsupp.sum, funext_iff]
  have h_ϱ (x : n → 𝔸 E) : D.map (V₁.ϱ (D.φ x) V₁.vacElem) = V.ϱ x V.vacElem := by
    rw [D.map_rho, D.map_vacElem]
  -- On the vacuum, a translate names `ϱ` of the part of the translation vector above the places
  -- and their conjugates, and `D.map` intertwines `ϱ`.
  rw [h_comb]
  simp [hS, hS', h_finEquiv_idem_conj, apply_finVec, ← h_ϱ, Finsupp.sum,
    schrodingerOp_schrodingerAct_boxIndicator]

/-- The projection P^S commutes with products of data: the product `V.boxProd hs` (the product of
the underlying functions, for a splitting `e : n₁ ⊕ n₂ ≃ n` of the coordinates compatible with the
signs, `hs`) of the projected vectors of `V₁` and `V₂` is the projection of their product. -/
lemma Space.boxProd_projOn (f₁ : 𝒮 V₁) (f₂ : 𝒮 V₂) :
    V.boxProd hs (V₁.projOn S f₁) (V₂.projOn S f₂) = V.projOn S (V.boxProd hs f₁ f₂) := by
  classical
  -- The coefficient function of a product is the product of the coefficient functions, and
  -- `projOn S` multiplies a coefficient function by the indicator of a box.
  refine IsVacuum.ext fun x ↦ ?_
  rw [projOn_val, boxProd_val, boxProd_val]
  -- A vector lies in the box for `n` iff its two parts lie in the boxes for `n₁` and `n₂`.
  -- (`using!`: one condition reads the finite coordinates of `x` at `e (.inl a)`, the other those
  -- of the part `x ∘ e ∘ .inl` at `a`; these agree only by unfolding)
  simpa [projOn_val, reindex_equiv e, ← ite_and, mem_integralBox] using! if_congr and_comm rfl rfl

/-- For any set `S` of finite places and any function `Ψ`, the operator `V.schrodingerOp S Ψ` maps
the finite part `V.finitePart` (the span of the finite Heisenberg translates of the vacuum) into
itself: if `f` lies in `V.finitePart`, so does `V.schrodingerOp S Ψ f`. -/
lemma Space.schrodingerOp_mem_finitePart_of_mem (S : Set (FinPlace E)) (Ψ : (n → 𝔸f E) → ℂ)
    {f : 𝒮 V} (h : f ∈ V.finitePart) :
    V.schrodingerOp S Ψ f ∈ V.finitePart := by
  simp [schrodingerOp, heisenbergCombination, sum_smul_mem, rho_finVec_mem_finitePart,
    projOn_mem_finitePart h, Finsupp.sum]

/-- `New.Space.schrodingerOp_mem_finitePart_of_mem`, with the membership of `f` in `V.finitePart` as
a default argument proved by `simp`. -/
lemma Space.schrodingerOp_mem_finitePart (S : Set (FinPlace E)) (Ψ : (n → 𝔸f E) → ℂ) {f : 𝒮 V}
    (h : f ∈ V.finitePart := by simp [funext_iff, finVec]) :
    V.schrodingerOp S Ψ f ∈ V.finitePart :=
  Space.schrodingerOp_mem_finitePart_of_mem S Ψ h

/-- Let `S` be disjoint from its conjugate, `Ψ`, `Ψ'` Schwartz–Bruhat above `S`, and
`e : n₁ ⊕ n₂ ≃ n` a splitting of the coordinates compatible with the signs (`hs`); write Ψ⊗ for the
operator `schrodingerOp S Ψ` and vac for the vacuum `vacElem`. Then `V.boxProd hs` (the product of
the underlying functions) of Ψ⊗vac in 𝒮(V₁) and Ψ'⊗vac in 𝒮(V₂) equals Θ⊗vac in 𝒮(V). Here
`Θ x = Ψ x₁ * Ψ' x₂`, with x₁, x₂ the two blocks of coordinates of `x` given by `e`. -/
lemma Space.boxProd_schrodingerOp {Θ : (n → 𝔸f E) → ℂ} (hS : S.IsConjDisjoint)
    [hΨ : IsSchwartzBruhat S Ψ] [hΨ' : IsSchwartzBruhat S Ψ']
    (h : Θ = fun x : n → 𝔸f E ↦ Ψ (x ∘ e ∘ Sum.inl) * Ψ' (x ∘ e ∘ Sum.inr)) :
    V.boxProd hs (V₁.schrodingerOp S Ψ V₁.vacElem) (V₂.schrodingerOp S Ψ' V₂.vacElem) =
      V.schrodingerOp S Θ V.vacElem := by
  classical
  -- Both sides are bilinear in `Ψ`, `Ψ'`; write each as a combination of translates of the box.
  obtain ⟨c, rfl⟩ := mem_range_schrodingerCombination hS hΨ
  obtain ⟨c', rfl⟩ := mem_range_schrodingerCombination hS hΨ'
  -- The product of the translates by `y` and `y'` is the translate by the joined vector.
  have h_prod (y : n₁ → 𝔸f E) (y' : n₂ → 𝔸f E) :
      (fun x : n → 𝔸f E ↦
          schrodingerAct S y (boxIndicator n₁ S) (x ∘ e ∘ .inl) *
            schrodingerAct S y' (boxIndicator n₂ S) (x ∘ e ∘ .inr)) =
        schrodingerAct S ((y ⊕ᵥ y') ∘ e.symm) (boxIndicator n S) := by
    simp [reindex_equiv e, dotProduct, ← e.sum_comp, AddChar.map_add_eq_mul, schrodingerAct,
      mul_add, sum_add_distrib, mem_integralBox, funext_iff]
    grind
  -- Expanded, both sides are double sums of the same multiples of `V.ϱ _ V.vacElem`, up to joining
  -- the two vectors before or after `finVec`.
  have h_join (y₁ : n₁ → 𝔸f E) (y₂ : n₂ → 𝔸f E) :
      (finVec (idem S.conjClosure • y₁) ⊕ᵥ finVec (idem S.conjClosure • y₂)) ∘ e.symm =
        finVec (idem S.conjClosure • (y₁ ⊕ᵥ y₂) ∘ e.symm) := by
    simp [reindex_equiv e, funext_iff, finVec]
  simp [h, h_prod, h_join, hS, ← sum_fn, boxProd_rho, sum_mul, mul_sum, -smul_eq_mul, ← Pi.smul_def,
    Finsupp.sum, schrodingerOp_schrodingerAct_boxIndicator]

end New

/-! ## The Weil action on names and names over disjoint sets of places -/

namespace New.Space

open Matrix Gf stdLattice Finset

variable {E : Type*} [Field E] [CMType E] [WeilData E]
  {n : Type*} [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} {S : Set (FinPlace E)} (hS : S.IsConjDisjoint) (V : Space E n s)
  {Ψ : (n → 𝔸f E) → ℂ} [hΨ : IsSchwartzBruhat (n := n) S Ψ]

/-- Let S, T be disjoint sets of finite places with S ∪ T disjoint from its conjugate, let Ψ be
Schwartz–Bruhat above S and Ψ′ above T, and let f ∈ 𝒮(V). Then `V.schrodingerOp (S ∪ T) (Ψ * Ψ')`
f = `V.schrodingerOp S Ψ` (`V.schrodingerOp T Ψ'` f). Here `schrodingerOp S Ψ` is the operator Ψ⊗ on
𝒮(V) given by the combination ∑ c_y ϱ(αy₊) P^S (`heisenbergCombination`) for coefficients c whose
matching function `schrodingerCombination S c` equals Ψ. -/
lemma schrodingerOp_union {Ψ' : (n → 𝔸f E) → ℂ} {T : Set (FinPlace E)}
    (h_half : (S ∪ T).IsConjDisjoint) (h_disj : Disjoint S T) [hΨ' : IsSchwartzBruhat T Ψ']
    (f : 𝒮 V) :
    V.schrodingerOp (S ∪ T) (Ψ * Ψ') f = V.schrodingerOp S Ψ (V.schrodingerOp T Ψ' f) := by
  obtain ⟨hS, hT⟩ : S.IsConjDisjoint ∧ T.IsConjDisjoint := by simp_all [Set.IsConjDisjoint]
  -- Write each function as a combination of translates of its box function.
  obtain ⟨c, rfl⟩ := mem_range_schrodingerCombination hS hΨ
  obtain ⟨c', rfl⟩ := mem_range_schrodingerCombination hT hΨ'
  -- Both sides are bilinear in the coefficients, so it suffices to take one translate of each box.
  have h_term (z y : n → 𝔸f E) :
      V.schrodingerOp (S ∪ T)
          (schrodingerAct S z (boxIndicator n S) * schrodingerAct T y (boxIndicator n T)) f =
        V.schrodingerOp S (schrodingerAct S z (boxIndicator n S))
          (V.schrodingerOp T (schrodingerAct T y (boxIndicator n T)) f) := by
    -- The product is the box function of `S ∪ T` translated by the part of `y` above `T ∪ T̄` and
    -- then by that of `z` above `S ∪ S̄`; the sets `S`, `S̄`, `T`, `T̄` are pairwise disjoint.
    have h_prod :
        schrodingerAct S z (boxIndicator n S) * schrodingerAct T y (boxIndicator n T) =
          schrodingerAct (S ∪ T) (idem S.conjClosure • z)
            (schrodingerAct (S ∪ T) (idem T.conjClosure • y) (boxIndicator n (S ∪ T))) := by
      ext x
      simp_all [schrodingerAct, ← ite_and, Set.disjoint_left, Finsupp.sum.eq_1]
      -- One goal for the box and one for each of the two phases.
      congr! 3 <;> simp [mem_integralBox, idem_mul_mem_Ô, DFunLike.ext_iff, idem_apply] <;> grind
    -- The translation by the part of `y` vanishes above `S ∪ S̄`, so it commutes with `projOn S`.
    have h_off : ∀ i, ∀ w ∈ S.conjClosure, (finVec (idem T.conjClosure • y) i).2 w = 0 := by
      simp_all [Set.disjoint_left, finVec, Finsupp.sum.eq_1, idem_apply]
      grind [star_star]
    have h_idem (U : Set (FinPlace E)) (hU : U ⊆ S ∪ T) :
        idem (S ∪ T).conjClosure * idem U.conjClosure = idem U.conjClosure := by
      simp [DFunLike.ext_iff, idem_apply]
      grind
    rw [h_prod, ← rho_schrodingerOp h_half, schrodingerOp_schrodingerAct_boxIndicator h_half,
      schrodingerOp_schrodingerAct_boxIndicator hT, schrodingerOp_schrodingerAct_boxIndicator hS]
    simp [projOn_union, projOn_rho _ h_off, smul_smul, h_idem]
  simp [sum_mul, mul_sum, Finsupp.sum.eq_1, h_term]

omit [WeilData E] in
/-- The finite parts of the entries of `g.adeleMatrix` are the entries of the finite component
`g.snd`. -/
private lemma map_snd_adeleMatrix (g : G E s) :
    g.adeleMatrix.map (fun a : 𝔸 E ↦ a.2) = ((↑g.snd : GL n (𝔸f E)) : Matrix n n (𝔸f E)) :=
  Matrix.ext fun _ _ ↦ rfl

include hS
/-- Let S be disjoint from its conjugate, Ψ be Schwartz–Bruhat above S, g ∈ `G E s` with finite
component g_f = `g.snd`, and f ∈ 𝒮(V), and write Φ⊗ = `V.schrodingerOp S Φ` for the operator ∑ c_y
ϱ(αy₊) P^S (`heisenbergCombination`) whose matching function `schrodingerCombination S c` is Φ. Let
u = `V.ω g` (B⊗ f), where B(x) = `boxIndicator n S` (g_f x) is the indicator of the x with g_f x
integral at every place of S. Then u is fixed by P^S = `V.projOn S` (the mean over y ∈ Ô^n of the
finite Heisenberg operators above S ∪ S̄), and `V.ω g` (Ψ⊗ f) = Ψ′⊗ u with Ψ′(x) = Ψ(g_f⁻¹ x). -/
lemma omega_schrodingerOp (g : G E s) (f : 𝒮 V) :
    let u : 𝒮 V := V.ω g (V.schrodingerOp S (fun x : n → 𝔸f E ↦ boxIndicator n S (g.snd *ᵥ x)) f)
    V.projOn S u = u ∧
    V.ω g (V.schrodingerOp S Ψ f) = V.schrodingerOp S (fun x : n → 𝔸f E ↦ Ψ (↑g.snd⁻¹ *ᵥ x)) u := by
  classical
  intro u
  -- The linear map `T Φ = ω g (Φ (g ·) ⊗ f)` sends the box function to `u`, and it turns the
  -- action `schrodingerAct` on functions into `ϱ`.
  let M : Matrix n n (𝔸f E) := (↑g.snd : GL n (𝔸f E))
  let T : ((n → 𝔸f E) → ℂ) →ₗ[ℂ] 𝒮 V :=
    (V.ω g ∘L .apply ℂ _ f).toLinearMap ∘ₗ V.schrodingerOp S ∘ₗ .funLeft ℂ ℂ M.mulVec
  have T_schrodingerAct (y : n → 𝔸f E) :
      T (schrodingerAct S y (boxIndicator n S)) = V.ϱ (finVec (idem S.conjClosure • y)) u := by
    obtain ⟨y, rfl⟩ : ∃ z : n → 𝔸f E, M *ᵥ z = y := mulVec_surjective_of_invertible M y
    -- The translation by the image of `y` is `g.adeleMatrix` applied to the translation by `y`.
    have h_vec : finVec (idem S.conjClosure • (M *ᵥ y)) =
        g.adeleMatrix *ᵥ finVec (idem S.conjClosure • y) := by
      rw [mulVec_finVec, map_snd_adeleMatrix, mulVec_smul]
    rw [h_vec, ← omega_rho, rho_schrodingerOp hS]
    simp [T, M, schrodingerAct, LinearMap.pi, LinearMap.funLeft, Function.comp_def, mulVec_add]
  -- Integral translations, corrected by `semichar`, fix the box function, so their mean fixes `u`.
  have h_fix_all : ∀ y ∈ stdLattice E n, V.finHeisenbergOp (idem S.conjClosure • y) u = u := by
    intro y hy
    have h_fix :
        T (semichar (idem S.conjClosure • y) • schrodingerAct S y (boxIndicator n S)) = u :=
      congrArg T (schrodingerAct_boxIndicator hS (integralBox_compl_inter.ge hy).right)
    simpa [finHeisenbergOp, T_schrodingerAct] using h_fix
  have h_fixed : V.projOn S u = u := V.map_projOn_eq_const 1 h_fix_all
  refine ⟨h_fixed, ?_⟩
  -- `T` and `· ⊗ u` agree on translates of the box function, hence on `Ψ (g⁻¹ ·)`.
  obtain ⟨c, hc⟩ : ∃ c : (n → 𝔸f E) →₀ ℂ,
      schrodingerCombination S c = fun x ↦
        Ψ (((↑(g.snd⁻¹) : GL n (𝔸f E)) : Matrix n n (𝔸f E)) *ᵥ x) :=
    mem_range_schrodingerCombination hS (hΨ.comp_mulVec g.snd⁻¹)
  calc
    _ = T (fun x ↦ Ψ (↑g.snd⁻¹ *ᵥ x)) := by simp [T, M, LinearMap.funLeft, Function.comp_def]
    _ = _ := by
      rw [← hc]
      simp [T_schrodingerAct, h_fixed, schrodingerOp_schrodingerAct_boxIndicator hS, Finsupp.sum]

/-- Let `S` be disjoint from its conjugate, `Ψ` Schwartz–Bruhat above `S`, and `g` in the finite
adelic unitary group (gᴴg = 1) supported on S ∪ S̄. Then `V.ω g` sends `V.schrodingerOp S Ψ f`, the
operator Ψ⊗ on 𝒮(V) applied to `f`, to `V.schrodingerOp S` of x ↦ Ψ(g⁻¹x) applied to `f`, times a
scalar. The scalar is the complex conjugate of `chiAdelic` (x ↦ υ(x)|x|^(−1/2), with υ the splitting
character) at the idele `detOn S g`, which equals det g at the places of `S` and 1 elsewhere. -/
lemma omega_schrodingerOp_of_mem_supportedOn {g : Gf E n} (hg : g ∈ supportedOn n S) (f : 𝒮 V) :
    V.ω g (V.schrodingerOp S Ψ f) =
      starRingEnd ℂ (chiAdelic (detOn S g.val)) •
        V.schrodingerOp S (fun x : n → 𝔸f E ↦ Ψ (↑g⁻¹ *ᵥ x)) f := by
  -- By `omega_schrodingerOp` it suffices to find `ω g v` for the vector `v` below; compute
  -- `projOn S v` twice.
  let v : 𝒮 V := V.schrodingerOp S (fun x ↦ boxIndicator n S (↑g *ᵥ x)) f
  let c : ℂ := (((‖glMultiplier (cutGL (idem_mul_self S) g.val)‖ ^ 2)⁻¹ : ℝ) : ℂ)
  obtain ⟨h_fixed, h_omega_name⟩ : V.projOn S (V.ω g v) = V.ω g v ∧
      V.ω g (V.schrodingerOp S Ψ f) = V.schrodingerOp S (fun x ↦ Ψ (↑g⁻¹ *ᵥ x)) (V.ω g v) :=
    V.omega_schrodingerOp hS (Ψ := Ψ) g f
  -- First, `projOn S v = c • projOn S f`: by `dataInner_schrodingerOp` the inner product of two
  -- named vectors has the inner product of the functions, here `c`, as a factor.
  have h_proj_v : V.projOn S v = c • V.projOn S f := by
    have h_dataInner_projOn (w : 𝒮 V) :
        V.dataInner (V.projOn S w) v = c * V.dataInner (V.projOn S w) (V.projOn S f) := by
      simp only [c, v, ← localInner_boxIndicator_mulVec, ← dataInner_schrodingerOp hS V,
        schrodingerOp_boxIndicator hS]
    have h_sub : V.projOn S (v - c • V.projOn S f) = 0 :=
      V.eq_zero_of_dataInner_self (by simp [← dataInner_projOn, h_dataInner_projOn])
    simpa [← projOn_union, sub_eq_zero] using h_sub
  -- Second, apply `projOn_omega` to `g⁻¹` and the fixed vector `ω g v`.
  have h_projOn_omega : (finMultiplier g)⁻¹ • V.ω g v = V.projOn S v := by
    simpa [rep_apply_apply, Prod.mk_one_one] using (V.projOn_omega (inv_mem hg) h_fixed).symm
  -- `finMultiplier g` is `c⁻¹` times the conjugated character (`finMultiplier_eq_of_supportedOn`).
  have h_mult : finMultiplier g * c = starRingEnd ℂ (chiAdelic (detOn S g.val)) := by
    have h_ne := finMultiplier_ne_zero g
    simp_all [c, finMultiplier_eq_of_supportedOn hS hg, chiFin, detOn, mul_right_comm]
  have h_ω_v : V.ω g v = starRingEnd ℂ (chiAdelic (detOn S g.val)) • V.projOn S f := by
    rw [← h_mult, mul_smul, ← h_proj_v, ← h_projOn_omega, smul_inv_smul₀ (finMultiplier_ne_zero g)]
  rw [h_omega_name, h_ω_v, map_smul, schrodingerOp_projOn]

end New.Space

end
