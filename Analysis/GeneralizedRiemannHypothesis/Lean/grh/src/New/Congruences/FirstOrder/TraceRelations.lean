import Lib.Cyclotomic.OddSha
import New.Congruences.FirstOrder.TateTwistCocycles
import New.Congruences.GaloisRepresentations.RowsAndColumnsFromLabels
import New.Congruences.LocalLoss.CrystallineDefect
import New.Congruences.LocalLoss.LocalLattices
import New.Congruences.LocalLoss.TateDualBound

/-!
# Constants, trace relations, lattices and local defects for Ribet's method

This file fixes the constants of Ribet's method: the bound `New.Selmer.oddClassBound` for the odd
classes, the local defect bound, the error term `New.Selmer.denominatorError` and the clearing
bound `New.Selmer.clearingBound`. It checks the trace relations and chooses block diagonal lattices
for representations with the trace of a twisted main summand plus `t` powers of the cyclotomic
character. It adds up the crystalline colengths of the summands and bounds the local defects.
Here `New.ellVal` is the valuation on `ℚ̄_ℓ` with `ellVal ℓ = 1`, with negative values replaced
by 0, and `New.inertiaAbove S` is the union of the inertia groups above `S`. The primes
`p₀ = D.levelPrime 0` and `p₁ = D.levelPrime 1` give the principal level.

## Main definitions and results

* `New.Selmer.exists_blockDiagonal_lattice`: let the trace form be non-degenerate on the span of the
  image of `R'`, let `R'` have the trace of the twisted main summand `ψ R` plus the characters
  `O(-e)`, `e < t`, and let the twisted lattice `ψ' R₀` span all matrices over `O`. Then `R'` has a
  lattice that is block diagonal with summands `ψ' R₀` and the characters.
* `New.Selmer.crystallineColength_le_sum_dualDefect`: at each place `v` above `ℓ` let the lattices
  of all `u x` and of `ρ` lie in the class `InClass (F v) (C v) (U v)`. Then the crystalline members
  have colength, among Ribet's cocycles modulo `ℓ ^ M`, at most the sum over `v` of the defects
  `dualDefect`.

Notions from other files:
* `New.CoeffRing`: rings of integers of finite Galois extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`; their
  `normLength` is length over `O`, scaled so that `O/ℓ` has length 1.
* `New.Selmer.tateTwist`: the rank-one representation `O(-e)`, given by the power `e` of the inverse
  `New.Selmer.cyclotomicInv` of the cyclotomic character.
* `New.Selmer.crystallineColength`: the length of the cocycles of a summand that obey the linear
  relations among the `u x g - 1`, modulo those that obey the crystalline relations above `ℓ`.
* `New.Selmer.IsLiftSetting`: a descent pair `V` (`New.DescentPair`) has the places of the data and
  of the twist `ϑ`, an odd rank `card r ≤ D.r` and an odd difference of ranks `V.rankDiff ≤ D.t`.
  Its type polynomials `c i` are monic squarefree polynomials of degree `card r` over the residue
  fields at the chosen places above `p₀` and `p₁`, with conditions on their roots.
* `New.Lift.InClass F C U`: the local lattices `Y` such that `Bmax ⊗ Y` is spanned by the periods
  fixed both near `1` and along the filter `F`, the Hodge–Tate jumps lie in the sets `U`, and every
  polynomial `Q` with `C s Q` kills the inertial element `s` on the periods.

## Relation to the literature

The torsion cocycles that Ribet's method produces in the summands of a lift's Galois representation
need not reduce from crystalline ones. Local duality and a case analysis on ℓ bound their total
distance from the crystalline condition, over all summands and places above ℓ, by an explicit bound.
It is known that torsion crystalline classes can miss reductions of crystalline ones by a bounded
defect that vanishes for small weights. Related work: Sweeting, Bloch–Kato conjecture for
four-dimensional symplectic representations, 2025; Chang–Diamond, Extensions of rank one
(φ,Γ)-modules, 2011; T. Liu, Torsion p-adic Galois representations and a conjecture of Fontaine,
2007.
-/

namespace New.Selmer

section RibetElement

open Matrix Polynomial Fintype Module Filter ENNReal Finset CoeffRing

open IsDiscreteValuationRing (addVal)

section Constants

variable {P : Parameters} (D : Data P) (ℓ : ℕ)

/-- A positive integer, at most `2 ^ (4 (N + t + 3) ^ 27) h_E` for the conductor `N` and the class
number `h_E`, whose valuation in large coefficient rings bounds, for each `0 < e < t`, the length of
the odd classes (`shaOdd`) in `(O/ℓ^ν)(-e)`, and for `e = 0` the length of the unramified
homomorphisms. -/
noncomputable def oddClassBound : ℕ :=
  (exists_length_shaOdd_le D.cyclotomicConductor D.t D.E D.algebraMap_mem_cycloField).choose

lemma oddClassBound_ne_zero : oddClassBound D ≠ 0 :=
  (exists_length_shaOdd_le D.cyclotomicConductor D.t D.E D.algebraMap_mem_cycloField).choose_spec.1

/-- The chosen bound for the odd classes is at most `2 ^ (4 (N + t + 3) ^ 27)` times the class
number of `E`, where `N` is the conductor of the cyclotomic field that contains `E`. -/
lemma oddClassBound_le : oddClassBound D ≤
    2 ^ (4 * (D.cyclotomicConductor + D.t + 3) ^ 27) * NumberField.classNumber D.E := by
  obtain ⟨-, h_size, -⟩ :=
    (exists_length_shaOdd_le D.cyclotomicConductor D.t D.E D.algebraMap_mem_cycloField).choose_spec
  exact h_size

/-- For every sufficiently large coefficient ring `O`, the valuation of `oddClassBound D` bounds
the length of the odd classes `shaOdd` in `(O/ℓ^ν)(-e)`, for all `e < t` and all `ν`. -/
lemma eventually_length_shaOdd_le [ThePrime ℓ] : ∀ᶠ O : CoeffRing ℓ in atTop, ∀ e < D.t, ∀ ν : ℕ,
    length O (shaOdd ℓ D.E O e ν) ≤ addVal O (oddClassBound D) := by
  obtain ⟨-, -, h_odd⟩ :=
    (exists_length_shaOdd_le D.cyclotomicConductor D.t D.E D.algebraMap_mem_cycloField).choose_spec
  exact (eventually_exists_isPrimitiveRoot _).mono fun O hO ↦ h_odd ℓ O ⟨hO, inferInstance⟩

/-- The number `loc_ℓ = 4 f defect_ℓ`: a bound, per unit of rank, for the local defect above `ℓ`.
Here `f = D.f` is the number of infinite places of `E`, and `defect_ℓ = defectBound D ℓ` is an
explicit number that depends only on `D` and `ℓ`. -/
noncomputable def localDefectBound : NNReal := 4 * D.f * defectBound D ℓ

/-- The error term `e_ℓ`, with crude constants. Its four terms pay for the class group and the odd
classes, the places above `p₀ p₁` (the principal level `D.M`), the idempotent and the automorphisms,
and the congruences between the characters `O(-e)`. Here `D.f` is the number of infinite places of
`E`, `D.halfGap = D.r ^ 8`, and `D.chosenGroupOrder` is the product of the orders of
`GL (D.r * D.t)` over the residue fields at the chosen places above `p₀` and `p₁`. -/
noncomputable def denominatorError : ℝ≥0∞ :=
  D.t * padicValNat ℓ (oddClassBound D) + 8 * D.f * D.t * padicValNat ℓ D.chosenGroupOrder +
    2 * padicValNat ℓ D.chosenGroupOrder +
    ((4 * D.t + 1) * D.halfGap ^ 22 + D.halfGap) * padicValNat ℓ D.chosenGroupOrder

/-- The error term `denominatorError D ℓ` is the cast of a natural number, a combination of the
`ℓ`-adic valuations of `oddClassBound D` and `D.chosenGroupOrder`. -/
lemma denominatorError_eq_natCast :
    denominatorError D ℓ =
      ((D.t * padicValNat ℓ (oddClassBound D) + 8 * D.f * D.t * padicValNat ℓ D.chosenGroupOrder +
        2 * padicValNat ℓ D.chosenGroupOrder +
        ((4 * D.t + 1) * D.halfGap ^ 22 + D.halfGap) * padicValNat ℓ D.chosenGroupOrder : ℕ) :
          ℝ≥0∞) := by
  simp [denominatorError]

lemma denominatorError_ne_top : denominatorError D ℓ ≠ ⊤ :=
  (denominatorError_eq_natCast D ℓ).trans_ne (ENNReal.natCast_ne_top _)

/-- The clearing bound `β_ℓ = loc_ℓ + (1 + 2 t) e'_ℓ + e_ℓ + v_ℓ(N)` per unit of rank of a main
summand at `ℓ`, where `N = D.chosenGroupOrder`. Here `loc_ℓ = localDefectBound D ℓ` bounds the local
defect, `e'_ℓ = twistError ℓ D` is the number `(4 f + 3) r v_ℓ(N) + 2 ^ (-ℓ)` allowed for the Selmer
length and for the ramification of a twist, and `e_ℓ` is the error term `denominatorError`. -/
noncomputable def clearingBound : NNReal :=
  localDefectBound D ℓ + (1 + 2 * D.t) * twistError ℓ D + (denominatorError D ℓ).toNNReal +
    padicValNat ℓ D.chosenGroupOrder

variable {D ℓ}

/-- Let `1 ≤ r' ≤ D.r` and `t' ≤ D.t`. Let `sel` and `ram` be at most the allowance
`e'_ℓ = twistError ℓ D`. Then `sel + 2 t' ram + r' loc_ℓ + e_ℓ + v_ℓ(N) ≤ r' β_ℓ`. Here
`N = D.chosenGroupOrder` is a product of orders of general linear groups over residue fields,
`loc_ℓ = localDefectBound D ℓ` bounds the local defect above `ℓ` per unit of rank,
`e_ℓ = denominatorError D ℓ` is an error term, and `β_ℓ = clearingBound D ℓ` is by definition
`loc_ℓ + (1 + 2 D.t) e'_ℓ + e_ℓ + v_ℓ(N)`. -/
lemma add_denominatorError_le_mul_clearingBound {r' t' : ℕ} (hr' : r' ∈ Set.Icc 1 D.r)
    (ht' : t' ≤ D.t) {sel ram : ℝ≥0∞} (h_sel : sel ≤ twistError ℓ D)
    (h_ram : ram ≤ twistError ℓ D) :
    sel + 2 * t' * ram + r' * localDefectBound D ℓ + denominatorError D ℓ +
      padicValNat ℓ D.chosenGroupOrder ≤ r' * clearingBound D ℓ := by
  set err : ℝ≥0∞ := ↑(twistError ℓ D)
  set loc : ℝ≥0∞ := ↑(localDefectBound D ℓ)
  set v : ℝ≥0∞ := ↑(padicValNat ℓ D.chosenGroupOrder)
  have h_one : (1 : ℝ≥0∞) ≤ r' := Nat.one_le_cast.2 hr'.1
  calc
    _ ≤ err + 2 * D.t * err + r' * loc + denominatorError D ℓ + v := by gcongr
    _ = r' * loc + 1 * ((1 + 2 * D.t) * err + denominatorError D ℓ + v) := by ring
    _ ≤ r' * loc + r' * ((1 + 2 * D.t) * err + denominatorError D ℓ + v) := by gcongr
    _ = r' * clearingBound D ℓ := by
      simp [clearingBound, err, loc, v, coe_toNNReal (denominatorError_ne_top D ℓ), mul_add,
        add_assoc]

/-- The cost of `t' ≤ D.t` characters, an inequality between numbers. Let `v` be the `ℓ`-adic
valuation of `D.chosenGroupOrder`, let `h ≤ v` and put `sep = D.halfGap * h`. Let
`(k + nTest) sep ≤ halfGap ^ 22 h` and `nDetect ≤ 2 (k + nTest)`. Let `tame ≤ 2 ram + 8 D.f v` (the
cost of the tame places, and the ramification of the twist). Each character costs the valuation of
`oddClassBound D`, `tame`, and `2 nDetect sep`; a further `(k + 1) sep` is paid once. With `2 v`
this is at most `2 t' ram` plus the error term `denominatorError D ℓ`. -/
lemma mul_padicValNat_add_le_add_denominatorError {t' h k nTest nDetect : ℕ} (ht' : t' ≤ D.t)
    (h_le : h ≤ padicValNat ℓ D.chosenGroupOrder)
    (h_points : (k + nTest) * (D.halfGap * h) ≤ D.halfGap ^ 22 * h)
    (h_detect : nDetect ≤ 2 * (k + nTest))
    {tame ram : ℝ≥0∞} (h_tame : tame ≤ 2 * ram + 8 * D.f * padicValNat ℓ D.chosenGroupOrder) :
    t' * padicValNat ℓ (oddClassBound D) + t' * (tame + 2 * nDetect * (D.halfGap * h : ℕ)) +
      (k + 1) * (D.halfGap * h : ℕ) + 2 * padicValNat ℓ D.chosenGroupOrder ≤
      2 * t' * ram + denominatorError D ℓ := by
  unfold denominatorError
  set v : ℕ := padicValNat ℓ D.chosenGroupOrder
  set odd : ℕ := padicValNat ℓ (oddClassBound D)
  -- the multiples of `sep`, counted in `ℕ`
  have h_sep : t' * (2 * nDetect * (D.halfGap * h)) + (k + 1) * (D.halfGap * h) ≤
      ((4 * D.t + 1) * D.halfGap ^ 22 + D.halfGap) * v := calc
    _ ≤ D.t * (2 * (2 * (k + nTest)) * (D.halfGap * h)) +
        (k + nTest + 1) * (D.halfGap * h) := by
      gcongr
      exact k.le_add_right nTest
    _ = (4 * D.t + 1) * ((k + nTest) * (D.halfGap * h)) + D.halfGap * h := by ring
    _ ≤ (4 * D.t + 1) * (D.halfGap ^ 22 * v) + D.halfGap * v := by grw [h_points, h_le]
    _ = _ := by ring
  calc
    _ = t' * odd + t' * tame + 2 * v +
        (t' * (2 * nDetect * (D.halfGap * h)) + (k + 1) * (D.halfGap * h) : ℕ) := by
      push_cast
      ring
    _ ≤ t' * odd + t' * (2 * ram + 8 * D.f * v) + 2 * v +
        (((4 * D.t + 1) * D.halfGap ^ 22 + D.halfGap) * v : ℕ) := by gcongr
    _ = 2 * t' * ram + (t' * odd + 8 * D.f * t' * v + 2 * v +
        ((4 * D.t + 1) * D.halfGap ^ 22 + D.halfGap) * v) := by
      push_cast
      ring
    _ ≤ _ := by gcongr

end Constants

variable {ℓ : ℕ} [ThePrime ℓ] {P : Parameters} {D : Data P}
  {K Y n r : Type} [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]
  {t ν : ℕ} {w : K → FinPlace D.E} {τ φ : K → AbsGal D} {O : CoeffRing ℓ}

/-- Ribet's cocycles vanish on the kernel of `u`: a cocycle `z` that obeys the linear relations
among the `u x g - 1` vanishes at every `g` with `u x g = 1` for all `x`. -/
lemma ribetCocycles.apply_eq_zero {u : Y → AbsGal D →* Matrix n n O}
    {ρ : AbsGal D →* Matrix r r O} {b : ↑O} {z : AbsGal D → r → QuotSpan b}
    (hz : z ∈ ribetCocycles u ρ b) {g : AbsGal D} (hg : ∀ x : Y, u x g = 1) : z g = 0 := by
  simpa using (mem_ribetCocycles.1 hz).2 (.single g 1) (by simp [funext_iff, hg])

open Ideal IsLocallyConstant in
/-- Let `z` be a cocycle for `ρ` modulo `b` that obeys the linear relations among the `u x g - 1`
(`ribetCocycles`), where the `u x` are continuous and trivial on the inertia groups outside
`S`. Then `z` is continuous and unramified outside `S`, so it lies in the Selmer module for `S`
and for every set `L` of relations that it obeys. -/
lemma ribetCocycles.mem_selmerModule [Fintype Y] {u : Y → AbsGal D →* Matrix n n O}
    (hu_cont : ∀ x : Y, Continuous (u x)) {S : Set (FinPlace D.E)}
    (h_unr : ∀ g : AbsGal D, g ∈ inertiaAbove Sᶜ → ∀ x : Y, u x g = 1)
    {ρ : AbsGal D →* Matrix r r O} {b : ↑O} [NeZero b] {z : AbsGal D → r → QuotSpan b}
    (hz : z ∈ ribetCocycles u ρ b) {L : Set (AbsGal D →₀ Matrix r r O)}
    (hzL : z ∈ obeying L (QuotSpan b)) : z ∈ selmerModule ρ S L (QuotSpan b) := by
  -- By Artin–Rees the pairs `(u g - 1 + b ^ k • v, z g)` lie in a module `W` whose elements are
  -- determined by their first coordinate.
  obtain ⟨k, W, h_inj, hW⟩ := exists_graph_subrepresentation u ρ hz
  have h_determined {g g' : AbsGal D} {v : Y → Matrix n n O}
      (h_eq : (fun x ↦ u x g' - 1) + b ^ k • 0 = (fun x ↦ u x g - 1) + b ^ k • v) : z g' = z g := by
    have h_pair : ((fun x ↦ u x g' - 1) + b ^ k • 0, z g') =
        ((fun x ↦ u x g - 1) + b ^ k • v, z g) :=
      congrArg Subtype.val (h_inj (a₁ := ⟨_, hW g' 0⟩) (a₂ := ⟨_, hW g v⟩) h_eq)
    exact congrArg Prod.snd h_pair
  have h_coc : ∀ g g' : AbsGal D, z (g * g') = z g + ρ g • z g' :=
    mem_obeying_cocycleRelations.1 hz.1
  refine mem_selmerModule_iff.2 ⟨h_coc, fun g hg ↦ apply_eq_zero hz (h_unr g hg), hzL, ?_⟩
  -- So `z g` depends only on `u g` modulo `b ^ k`, which is locally constant in `g`.
  have h_red : IsLocallyConstant fun g x ↦ (u x g).map (span {b ^ k}).mkQ := (iff_continuous _).2
    (continuous_pi fun x ↦ (hu_cont x).matrix_map (span {b ^ k}).continuous_mkQ)
  refine (iff_eventually_eq _).2 fun g ↦ (h_red.eventually_eq g).mono fun g' hg' ↦ ?_
  have h_dvd (x : Y) (i j : n) : b ^ k ∣ u x g' i j - u x g i j :=
    mk_span_eq_iff_dvd_sub.1 (congrFun₃ hg' x i j)
  choose v hv using h_dvd
  refine h_determined (v := fun x ↦ of (v x)) ?_
  ext
  simp [← hv]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let every `u x` be conjugate self-dual with twist `t`. Let `w j` be new places with tame
generators `τ j` and elements `φ j` that fix the `ℓ ^ ν`-th roots of unity. Let `𝒥` be a trace
ideal. Then `𝒥` is also a trace ideal for the doubled families `withConjInv τ`, `withConjInv φ`,
which add the inverses of the conjugates; both copies of `j` use the variable `X j`. -/
lemma isTraceIdeal_withConjInv (hw : IsTameGeneratorFamily ν w τ φ)
    {S : Subalgebra O (Y → MvPolynomial K (PadicAlgCl ℓ))}
    {𝒥 : Submodule S (Y → MvPolynomial K (PadicAlgCl ℓ))} {H : K → O[X]}
    {u : Y → GalRep ℓ D.E n} (hu : ∀ x : Y, IsConjSelfDual t (u x))
    (h𝒥 : IsTraceIdeal 𝒥 (fun (x : Y) (g : AbsGal D) ↦ (u x g).val) (ℓ ^ ν : ↑O) τ φ id H) :
    IsTraceIdeal 𝒥 (fun (x : Y) (g : AbsGal D) ↦ (u x g).val) (ℓ ^ ν : ↑O) (withConjInv τ)
      (withConjInv φ) Prod.fst H := by
  -- On the copy `(j, true)` the relation is the old one. On `(j, false)`, duality turns each trace
  -- into a power of `χ = cyclotomicInv` times a trace at `g' = (g ^ c)⁻¹`. As `χ` is `1` at
  -- `τ_j ^ (-c)` and `1` modulo `ℓ ^ ν` at `φ_j ^ (-c)`, the new relation is `χ g ^ (t - 1)` times
  -- the old one at `g'`, up to a combination of the `ℓ ^ ν • trace`.
  refine ⟨h𝒥.X_mem, h𝒥.charpoly_coeff_mem, h𝒥.smul_trace_mem, fun g ⟨j, copy⟩ ↦ ?_⟩
  cases copy
  case true => exact h𝒥.trace_relation_mem g j
  let k : K × Bool := (j, false)
  let g' : AbsGal D := (conjGal g)⁻¹
  let χ : AbsGal D →* O := cyclotomicInv ℓ D.E O
  have h_dual (f : K → AbsGal D) (i : ℕ) (x : Y) :
      (u x (withConjInv f k ^ i * g)).1.trace =
        χ (withConjInv f k ^ i * g) ^ (t - 1) • (u x (f j ^ i * g')).1.trace := by
    simpa [k, g', χ, idOrConjInv, cyclotomicInv, trace_mul_comm _⁻¹, O.1.smul_def] using
      (hu x).trace_conj ((f j)⁻¹ ^ i * conjGal g)
  obtain ⟨hχτ : χ (withConjInv τ k) = 1, hχφ⟩ := hw.cyclotomicInv_withConjInv_eq_one_and_dvd O k
  have h_cong : ∀ i : ℕ, ∃ a : ↑O, χ (withConjInv φ k) ^ i - 1 = ℓ ^ ν * a := hχφ
  choose d hd using h_cong
  have h_one (x : Y) : (u x g).1.trace = χ g ^ (t - 1) • (u x g').1.trace := by
    simpa using h_dual τ 0 x
  have h_τ (x : Y) : ((u x (withConjInv τ k)).1 * u x g).trace =
      χ g ^ (t - 1) • ((u x (τ j)).1 * u x g').trace := by
    simpa [hχτ] using h_dual τ 1 x
  have h_φ (i : ℕ) (x : Y) : ((u x (withConjInv φ k)).1 ^ i * u x g).trace =
      ((1 + ℓ ^ ν * d ((t - 1) * i)) * χ g ^ (t - 1)) • ((u x (φ j)).1 ^ i * u x g').trace := by
    simpa [mul_pow, ← pow_mul', ← hd] using h_dual φ i x
  have h_smul (c : ↑O) {f : Y → MvPolynomial K (PadicAlgCl ℓ)} (hf : f ∈ 𝒥) :
      c • f ∈ 𝒥 := by
    rw [Algebra.smul_def]
    exact 𝒥.smul_mem ⟨_, S.algebraMap_mem c⟩ hf
  -- expand `G` in powers and apply `h_φ` to each of them; `err` collects the multiples of `ℓ ^ ν`
  let G : O[X] := (X - 1) * H j
  let err (x : Y) : PadicAlgCl ℓ := ∑ i ∈ range (G.natDegree + 1),
    (d ((t - 1) * i) * G.coeff i) • (ℓ ^ ν : ↑O) • (u x (φ j ^ i * g')).1.trace
  have h_G (x : Y) : (aeval (u x (withConjInv φ k)).1 G * u x g).trace =
      χ g ^ (t - 1) • ((aeval (u x (φ j)).1 G * u x g').trace + err x) := by
    simp only [err, aeval_eq_sum_range, sum_mul, trace_sum, smul_mul_assoc, trace_smul, h_φ,
      smul_add, smul_sum, smul_smul, ← sum_add_distrib, map_mul, map_pow, Units.val_mul,
      Units.val_pow_eq_pow_val]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← add_smul]
    congr 1
    ring
  have h_err : (fun x : Y ↦ MvPolynomial.C (err x)) ∈ 𝒥 := by
    have h_expand : (fun x : Y ↦ (.C (err x) : MvPolynomial K (PadicAlgCl ℓ))) =
        ∑ i ∈ range (G.natDegree + 1), (d ((t - 1) * i) * G.coeff i) •
          fun x : Y ↦ .C ((ℓ ^ ν : ↑O) • (u x (φ j ^ i * g')).1.trace) := by
      funext x
      simp [err, Subalgebra.smul_def, MvPolynomial.smul_eq_C_mul]
    rw [h_expand]
    exact sum_mem fun i _ ↦ h_smul _ (h𝒥.smul_trace_mem (φ j ^ i * g'))
  have h_X_err : (fun x : Y ↦ MvPolynomial.X j * MvPolynomial.C (err x)) ∈ 𝒥 :=
    𝒥.smul_mem ⟨_, h𝒥.X_mem j⟩ h_err
  -- `rel a b γ`: the trace of the relation that ties `a` to `b`, multiplied by `γ`
  let rel (a b γ : AbsGal D) (x : Y) : MvPolynomial K (PadicAlgCl ℓ) :=
    .C (((u x a).1 - 1) * u x γ).trace - .X j * .C (aeval (u x b).1 G * u x γ).trace
  have h_old : rel (τ j) (φ j) g' ∈ 𝒥 := h𝒥.trace_relation_mem g' j
  have h_new : rel (withConjInv τ k) (withConjInv φ k) g =
      χ g ^ (t - 1) • (rel (τ j) (φ j) g' - fun x : Y ↦ .X j * .C (err x)) := by
    funext x
    simp only [rel, sub_mul, one_mul, trace_sub, h_one x, h_τ, h_G, Pi.smul_apply, Pi.sub_apply,
      Subalgebra.smul_def, smul_eq_mul, MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul]
    ring
  change rel (withConjInv τ k) (withConjInv φ k) g ∈ 𝒥
  rw [h_new]
  exact h_smul _ (sub_mem h_old h_X_err)

/-- A subalgebra over the integers of `ℚ̄_ℓ`, read as a subalgebra over a coefficient ring. -/
abbrev restrictToCoeffRing {A : Type} [CommRing A] [Algebra (PadicAlgCl ℓ) A]
    (S : Subalgebra (intQpBar ℓ) A) (O : CoeffRing ℓ) : Subalgebra O A :=
  ⟨S.toSubsemiring, fun a ↦ S.algebraMap_mem ⟨a, norm_le_one a⟩⟩

/-- Let `w j` be new places: `w j` is not above `ℓ`, `τ j` is a tame generator at `w j`, and `φ j`
fixes the `ℓ ^ ν`-th roots of unity. Let `u' x` be lattices over `O` in the conjugate self-dual
`u x`. Let the `S`-module `𝒥` be a trace ideal (`IsTraceIdeal`) for the `u x` over the integers of
`ℚ̄_ℓ`: it contains `ℓ ^ ν` times the traces and the traces of the relations that tie `τ j` to `φ j`
through `X j` and `H j`, and `S` contains the `X j` and the coefficients of the characteristic
polynomials. Let the polynomials `H' j` over `O` be equal to the `H j`. Then `𝒥` is a trace ideal
for the `u' x` over `O` and the doubled families `withConjInv τ`, `withConjInv φ`, which add the
inverses of the conjugates; both copies of `j` use `X j` and `H' j`. -/
lemma IsTraceIdeal.of_isLatticeIn (hw : IsTameGeneratorFamily ν w τ φ)
    {u : Y → GalRep ℓ D.E n} (hu : ∀ x : Y, IsConjSelfDual t (u x))
    {u' : Y → AbsGal D →* Matrix n n O} (hu' : ∀ x : Y, IsLatticeIn (u x) (u' x))
    {S : Subalgebra (intQpBar ℓ) (Y → MvPolynomial K (PadicAlgCl ℓ))}
    {𝒥 : Submodule S (Y → MvPolynomial K (PadicAlgCl ℓ))} {H : K → (intQpBar ℓ)[X]}
    (h𝒥 : IsTraceIdeal 𝒥 (fun (x : Y) (g : AbsGal D) ↦ (u x g).val) (ℓ ^ ν) τ φ id H)
    {H' : K → O[X]}
    (hH' : ∀ j : K, (H' j).map (algebraMap O (PadicAlgCl ℓ)) = (H j).map (intQpBar ℓ).subtype) :
    IsTraceIdeal (S := restrictToCoeffRing S O) 𝒥 (fun x : Y ↦ u' x) (ℓ ^ ν) (withConjInv τ)
      (withConjInv φ) Prod.fst H' := by
  -- first change the ring of coefficients and add the conjugates, then pass to the lattices
  have h_conj : IsTraceIdeal (S := restrictToCoeffRing S O) 𝒥
      (fun (x : Y) (g : AbsGal D) ↦ (u x g).1) (ℓ ^ ν) (withConjInv τ) (withConjInv φ)
      Prod.fst H' := by
    refine isTraceIdeal_withConjInv hw hu
      ⟨h𝒥.X_mem, h𝒥.charpoly_coeff_mem, fun g ↦ ?_, fun g j ↦ ?_⟩
    · simpa [Algebra.smul_def] using! h𝒥.smul_trace_mem g
    · simpa [hH', ← aeval_map_algebraMap (PadicAlgCl ℓ)] using! h𝒥.trace_relation_mem g j
  -- `F x` carries `u' x` to `u x` and keeps traces
  have h_algHom (x : Y) : ∃ F : Matrix n n O →ₐ[O] Matrix n n (PadicAlgCl ℓ),
      (∀ g : AbsGal D, F (u' x g) = u x g) ∧ ∀ A : Matrix n n O, (F A).trace = A.trace.val := by
    obtain ⟨F, -, hF, hF_det_trace⟩ := (hu' x).exists_algHom
    exact ⟨F, hF, fun A ↦ (hF_det_trace A).2⟩
  choose F hF hF_trace using h_algHom
  refine ⟨h_conj.X_mem, fun g k ↦ ?_, fun g ↦ ?_, fun g k ↦ ?_⟩
  · simpa [↓(hu' _).charpoly_eq_map] using h_conj.charpoly_coeff_mem g k
  · simpa [← (hu' _).trace_eq, O.1.smul_def] using h_conj.smul_trace_mem g
  · simpa [← hF, aeval_algHom_apply (F _), ← map_mul, sub_mul, hF_trace] using
      h_conj.trace_relation_mem g k

/-- The summand `e` of `summandRep T`, the family of a main summand `T` and `t` characters, is the
`1 × 1` matrix of the power `e` of the inverse cyclotomic character `cyclotomicInv`. -/
lemma summandRep_some_apply (T : AbsGal D →* Matrix r r O) (e : Fin t) (g : AbsGal D) :
    summandRep T (some e) g =
      of fun _ _ : SummandCoordIndex r (some e) ↦ cyclotomicInv ℓ D.E O g ^ (e : ℕ) :=
  rfl

/-- The index set of a main summand and `t` characters, as a sum and as a family of summands. -/
def summandCoordIndexEquiv (r : Type) (t : ℕ) :
    r ⊕ Fin t ≃ Sigma (SummandCoordIndex r (t := t)) where
  toFun := Sum.elim (fun a ↦ ⟨none, a⟩) fun e ↦ ⟨some e, ()⟩
  invFun := Sigma.rec (Option.rec .inl fun e _ ↦ .inr e)
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro ⟨_ | _, _⟩ <;> rfl

/-- The block diagonal sum of a main summand `T` and the `t` characters `cyclotomicInv ^ e` is the
matrix with `T g` and a diagonal matrix on the diagonal, reindexed by `summandCoordIndexEquiv`. -/
lemma blockDiagonal'_summandRep (T : AbsGal D →* Matrix r r O) (g : AbsGal D) :
    blockDiagonal' (fun i : Option (Fin t) ↦ summandRep T i g) =
      reindex (summandCoordIndexEquiv r t) (summandCoordIndexEquiv r t)
        (fromBlocks (T g) 0 0 (diagonal fun e : Fin t ↦ cyclotomicInv ℓ D.E O g ^ e.val)) := by
  refine (reindex _ _).symm_apply_eq.1 ?_
  ext1 (_ | _) (_ | _)
  · simp [blockDiagonal', summandCoordIndexEquiv]
    rfl
  · simp [blockDiagonal', summandCoordIndexEquiv]
  · simp [blockDiagonal', summandCoordIndexEquiv]
  · simp [blockDiagonal', summandCoordIndexEquiv, summandRep_some_apply, diagonal]
    rfl

/-- Let the trace form be non-degenerate on the span of the image of `R'` (`IsTraceNondeg`). Let
`R'` have the trace of the twisted main summand `ψ R` plus the characters `O(-e)`, `e < t`, and let
the twisted lattice `ψ' R₀` span all matrices over `O`. Then `R'` has a lattice that is block
diagonal with summands `ψ' R₀` and the characters (`summandRep`), the summands being placed by
`ϵ`. -/
lemma exists_blockDiagonal_lattice {ψ : AbsGal D →* PadicAlgCl ℓ} {R : GalRep ℓ D.E r}
    {R' : GalRep ℓ D.E n} (hR' : IsTraceNondeg R')
    (h_trace : ∀ g : AbsGal D, (R' g).val.trace =
      ψ g * (R g).val.trace + ∑ e ∈ range t, cyclotomicInv ℓ D.E (PadicAlgCl ℓ) g ^ e)
    {R₀ : AbsGal D →* Matrix r r O} (hR₀ : IsLatticeIn R R₀) {ψ' : AbsGal D →* O}
    (hψ' : ∀ g : AbsGal D, ψ' g = ψ g)
    (h_span : Submodule.span O (.range (twistRep (.id O) ψ' R₀)) = ⊤)
    (ϵ : Sigma (SummandCoordIndex r (t := t)) ≃ n) :
    ∃ v : AbsGal D →* Matrix n n O, IsLatticeIn R' v ∧ ∀ g : AbsGal D, v g = reindex ϵ ϵ
      (blockDiagonal' fun i : Option (Fin t) ↦ summandRep (twistRep (.id O) ψ' R₀) i g) := by
  set T : AbsGal D →* Matrix r r O := twistRep (.id O) ψ' R₀
  -- `Φ` puts a family of blocks along the diagonal; `ρ` is the family of summands over `ℚ̄_ℓ`
  let Φ (A : Type) [CommRing A] := (reindexAlgEquiv A A ϵ).toAlgHom.comp blockDiagonalAlgHom
  let ρ : AbsGal D →* ∀ i : Option (Fin t),
      Matrix (SummandCoordIndex r i) (SummandCoordIndex r i) (PadicAlgCl ℓ) :=
    .pi fun i ↦ O.1.val.mapMatrix.toMonoidHom.comp (summandRep T i)
  have h_semi : HasSemiprimeSpan (PadicAlgCl ℓ) ρ := by
    intro y _ hy
    ext (_ | e) a b
    · -- on `T`, `y M y = 0` extends from `M = T g` to all matrices `M`; take an elementary one
      have h_all : LinearMap.mulLeftRight O (y none, y none) ∘ₗ
          (Algebra.linearMap O (PadicAlgCl ℓ)).mapMatrix = 0 :=
        LinearMap.ext_on_range h_span fun g ↦ congrFun (hy g) none
      simpa [mul_apply, single_apply, ite_and] using
        congrFun₂ (LinearMap.congr_fun h_all (.single b a 1)) a b
    · -- on a character, `y * y = 0` is an equation between numbers
      let y_e : Matrix Unit Unit (PadicAlgCl ℓ) := y (some e)
      have h_sq_all : y * y = 0 := by simpa using hy 1
      have h_sq : y_e * y_e = 0 := congrFun h_sq_all (some e)
      have h_entry : y_e () () * y_e () () = 0 := by simpa [mul_apply] using congrFun₂ h_sq () ()
      exact mul_self_eq_zero.1 h_entry
  -- both traces are the sum of the traces of the summands
  have h_trace_main (g : AbsGal D) : (ρ g none).trace = ψ g * (R g).val.trace := by
    change ((T g).map O.1.val).trace = _
    rw [← hR₀.trace_eq, ← hψ']
    simp [T, twistRep, trace, mul_sum]
  have h_trace_char (g : AbsGal D) (e : Fin t) :
      (ρ g (some e)).trace = cyclotomicInv ℓ D.E (PadicAlgCl ℓ) g ^ e.val := by
    change ((summandRep T (some e) g).map O.1.val).trace = _
    rw [summandRep_some_apply]
    simp [trace, cyclotomicInv]
    simp! [map_pow, inv_pow]
  have h_trace_eq (g : AbsGal D) : (R' g).val.trace = (Φ (PadicAlgCl ℓ) (ρ g)).trace := calc
    _ = ∑ i : Option (Fin t), (ρ g i).trace := by
      simp only [h_trace, sum_range, Fintype.sum_option, h_trace_main, h_trace_char]
    _ = _ := by simp [Φ, trace, ← ϵ.sum_comp, Fintype.sum_sigma]
  -- equal traces make `R'` conjugate to `Φ ρ`, which has entries in `O`
  obtain ⟨Z, hZ⟩ := hR'.exists_conj_of_trace_eq ρ (Φ _) h_semi h_trace_eq
  refine ⟨(Φ O).toMonoidHom.comp (.pi (summandRep T)), ⟨Z, fun g ↦ ?_⟩, fun _ ↦ rfl⟩
  have h_map : (Φ O fun i ↦ summandRep T i g).map O.1.val = Φ (PadicAlgCl ℓ) (ρ g) := by
    change _ = Φ (PadicAlgCl ℓ) fun i ↦ (summandRep T i g).map O.1.val
    simp [Φ, ← submatrix_map, blockDiagonal'_map]
  change _ = (Φ O fun i ↦ summandRep T i g).map O.1.val
  rw [h_map]
  simp [hZ, mul_assoc]

/-- Let the representations `u x`, indexed by the type `Y`, have non-degenerate trace form
(`IsTraceNondeg`) and have lattices over `O`, and for `x ∈ 𝓧` let the trace of `u x` be that of the
twisted main summand `ψ (R x)` plus the characters `O(-e)`, `e < t`, where the twisted lattice
`ψ' x R₀ x` spans all matrices. Then there are lattices in all these representations that, for
`x ∈ 𝓧`, are block diagonal with the twisted lattice of the main summand and the characters. -/
lemma exists_blockDiagonal_lattices {u : Y → GalRep ℓ D.E n}
    (hu : ∀ x : Y, IsTraceNondeg (u x))
    (h_lat : ∀ x : Y, ∃ v : AbsGal D →* Matrix n n O, IsLatticeIn (u x) v)
    {ψ : AbsGal D →* PadicAlgCl ℓ} {𝓧 : Set Y} {R : 𝓧 → GalRep ℓ D.E r}
    (h_trace : ∀ (x : 𝓧) (g : AbsGal D), (u x g).val.trace =
      ψ g * (R x g).val.trace + ∑ e ∈ range t, cyclotomicInv ℓ D.E (PadicAlgCl ℓ) g ^ e)
    {R₀ : 𝓧 → AbsGal D →* Matrix r r O} (hR₀ : ∀ x : 𝓧, IsLatticeIn (R x) (R₀ x))
    {ψ' : 𝓧 → AbsGal D →* O} (hψ' : ∀ (x : 𝓧) (g : AbsGal D), ψ' x g = ψ g)
    (h_span : ∀ x : 𝓧, Submodule.span O (.range (twistRep (.id O) (ψ' x) (R₀ x))) = ⊤)
    (ϵ : Sigma (SummandCoordIndex r (t := t)) ≃ n) :
    ∃ u' : Y → AbsGal D →* Matrix n n O, (∀ x : Y, IsLatticeIn (u x) (u' x)) ∧
      ∀ (x : 𝓧) (g : AbsGal D), u' x g = reindex ϵ ϵ (blockDiagonal'
        fun i : Option (Fin t) ↦ summandRep (twistRep (.id O) (ψ' x) (R₀ x)) i g) := by
  classical
  have h_block (x : 𝓧) : ∃ v : AbsGal D →* Matrix n n O, IsLatticeIn (u x) v ∧
      ∀ g : AbsGal D, v g = reindex ϵ ϵ (blockDiagonal'
        fun i : Option (Fin t) ↦ summandRep (twistRep (.id O) (ψ' x) (R₀ x)) i g) :=
    exists_blockDiagonal_lattice (hu x) (h_trace x) (hR₀ x) (hψ' x) (h_span x) ϵ
  choose v hv hv_block using h_block
  choose v' hv' using h_lat
  refine ⟨fun x ↦ if hx : x ∈ 𝓧 then v ⟨x, hx⟩ else v' x, fun x ↦ ?_, by simpa using hv_block⟩
  by_cases hx : x ∈ 𝓧
  · simpa [hx] using hv ⟨x, hx⟩
  · simpa [hx] using hv' x

section Model

variable {ψ : AbsGal D →* PadicAlgCl ℓ} {R : GalRep ℓ D.E r} {Q : Finset (FinPlace D.E)}
  {γ : AbsGal D} {ζ : intQpBar ℓ} {R₀ : AbsGal D →* Matrix r r O} {ψ' : AbsGal D →* O} {ζ' : ↑O}

/-- Let `R₀`, `ψ'`, `ζ'` be a model over `O` (`IsTwistedLattice`): `R₀` is a lattice in `R`, `ψ'`
and `ζ'` are `ψ` and `ζ` with values in `O`, and `γ` acts on the twisted lattice `ψ' R₀` by the
scalar `ζ'`. Then `ψ' R₀` agrees with `R₀` at every `g` with `ψ g = 1`. -/
lemma IsTwistedLattice.twistRep_apply_eq_of_eq_one (h_model : IsTwistedLattice ψ R γ ζ R₀ ψ' ζ')
    {g : AbsGal D} (hg : ψ g = 1) : twistRep (.id O) ψ' R₀ g = R₀ g := by
  ext
  simp [twistRep, h_model.twist_eq, hg]

/-- Let `R₀`, `ψ'`, `ζ'` be a model over `O` (`IsTwistedLattice`): `R₀` is a lattice in `R`, `ψ'`
and `ζ'` are `ψ` and `ζ` with values in `O`, and the inertial element `γ` acts on the twisted
lattice `ψ' R₀` by the scalar `ζ'`. Let `ψ` come from the norm-one torus with modulus `Q`
(`IsFromU1`). Let `R` be a main summand (`IsMainSummandLike`): a conjugate self-dual representation
of twist `t` and empty level, with Hodge–Tate jumps `J` read through the isomorphism `ℂ ≃ ℚ̄_ℓ`
fixed by `PadicIso ℓ`; only that `R` is unramified outside `ℓ p₀ p₁` (`p₀ p₁ = D.M`) is used. Then
`ψ' R₀` is unramified outside `ℓ p₀ p₁`, `Q` and `Q̄`. -/
lemma IsTwistedLattice.twistRep_eq_one_of_mem_inertiaAbove [PadicIso ℓ]
    (h_model : IsTwistedLattice ψ R γ ζ R₀ ψ' ζ')
    (hψ : IsFromU1 (placesDividing D.E ℓ) Q ψ) {J : (D.E →+* ℂ) → Multiset ℤ}
    (h_summand : IsMainSummandLike D t J R) (g : AbsGal D)
    (hg : g ∈ inertiaAbove (placesDividing D.E ℓ ∪ placesAboveM D ∪ .conjClosure Q)ᶜ) :
    twistRep (.id O) ψ' R₀ g = 1 := by
  obtain ⟨v, hv, hg⟩ := hg
  rw [h_model.twistRep_apply_eq_of_eq_one (hψ.eq_one_of_mem_inertiaAbove g ⟨v, mt .inr hv, hg⟩)]
  exact h_model.isLatticeIn.eq_one
    (h_summand.eq_one_of_mem_inertiaAbove g ⟨v, by simpa using mt .inl hv, hg⟩)

end Model

/-- Let the `τ j` be tame generators at places `w j` off `ℓ`. Let `u x`, `x : Y`, be finitely many
continuous representations over `O`, unramified outside `ℓ p₀ p₁` (`p₀ p₁ = D.M`), `Q`, the `w j`
and their conjugates, and let `T` be unramified outside `ℓ p₀ p₁`, `Q` and `Q̄`. Consider the
cocycles in `T` modulo `ℓ ^ m` that obey the linear relations among the `u x g - 1`. Those that
vanish at `γ`, at the `τ j` and at the inverses of their conjugates have length at most
`crystallineColength T u m`, the length of all of them modulo those obeying the crystalline
relations above `ℓ`, plus the length of the Selmer cocycles `selmerCocycles T Q m γ`. -/
lemma length_ribetCocyclesVanishingOn_le [Fintype Y] (hw : IsTameGeneratorFamily ν w τ φ)
    {Q : Finset (FinPlace D.E)}
    {u : Y → AbsGal D →* Matrix n n O} (hu_cont : ∀ x : Y, Continuous (u x))
    (hu_unr : ∀ g ∈ inertiaAbove (placesDividing D.E ℓ ∪ placesAboveM D ∪
      (.conjClosure Q ∪ (Set.range w).conjClosure))ᶜ, ∀ x : Y, u x g = 1)
    {T : AbsGal D →* Matrix r r O}
    (hT_unr : ∀ g ∈ inertiaAbove (placesDividing D.E ℓ ∪ placesAboveM D ∪ .conjClosure Q)ᶜ, T g = 1)
    (m : ℕ) (γ : AbsGal D) :
    length O (ribetCocyclesVanishingOn u T (QuotSpan (ℓ ^ m : ↑O)) (.range (withConjInv τ)) γ) ≤
      crystallineColength T u m + length O (selmerCocycles T Q m γ) := by
  set Z : Submodule O (AbsGal D → r → QuotSpan (ℓ ^ m : ↑O)) :=
    ribetCocyclesVanishingOn u T (QuotSpan (ℓ ^ m : ↑O)) (.range (withConjInv τ)) γ
  let Zf : Submodule O (AbsGal D → r → QuotSpan (ℓ ^ m : ↑O)) :=
    obeying (crysRelations T) (QuotSpan (ℓ ^ m : ↑O))
  -- A cocycle that kills the tame generators is unramified at the places `w j`; so the members of
  -- `Z` that lie in `H¹_f` above `ℓ` are Selmer cocycles.
  have h_selmer : Z ⊓ Zf ≤ selmerCocycles T Q m γ := by
    rintro z ⟨hzZ, hz_crys⟩
    obtain ⟨hz, hzτ, hzγ⟩ := (mem_ribetCocyclesVanishingOn u).1 hzZ
    have hz_sel : z ∈ selmerModule T (placesDividing D.E ℓ ∪ placesAboveM D ∪
        (.conjClosure Q ∪ (Set.range w).conjClosure)) (crysRelations T) (QuotSpan (ℓ ^ m : ↑O)) :=
      ribetCocycles.mem_selmerModule hu_cont hu_unr hz hz_crys
    have hz_tame (k : K × Bool) : z (withConjInv τ k) = 0 := hzτ _ ⟨k, rfl⟩
    have hz_unr : z ∈ selmerModule T (placesDividing D.E ℓ ∪ placesAboveM D ∪ .conjClosure Q)
        (crysRelations T) (QuotSpan (ℓ ^ m : ↑O)) := by
      rw [← Set.union_assoc] at hz_sel
      exact hw.mem_selmerModule_of_tame_eq_zero hz_sel hz_tame .rfl fun g hg _ ↦ hT_unr g hg
    exact ⟨hz_unr, hzγ⟩
  rw [← relLength_add_length_inf Z Zf]
  exact add_le_add (relLength_mono (inf_le_left.trans inf_le_left) le_rfl) (length_mono h_selmer)

open scoped Classical in
/-- Let the places `w j` off `ℓ`, with tame generators `τ j`, elements `φ j` and monotone exponents
`0 < ty j < t`, form a triangle of primes for `g₀` up to `ℓ ^ sep`; `c` bounds `sep` times the
number of places and test points. Let the `u x` be continuous and unramified outside `ℓ p₀ p₁`
(`p₀ p₁ = D.M`), `Q`, the `w j` and their conjugates, and let `e < t`. Let `Z` consist of character
cocycles: cocycles in `O/ℓ^ν(-e)` that obey the relations among the `u x g - 1`, vanish at tame
generators `δ` of places `q` covering the remaining places prime to `ℓ` and at the inverses of their
conjugates, and, if they vanish at `γ`, have their value at `g₀` killed by every `χ g - 1`,
`χ = cyclotomicInv ^ e`. Here `γ` lies in inertia at a place not above `ℓ`. Then `HasTriangleCost`
holds along the `j` with `ty j = e`: for the members `Z₀` of `Z` that vanish on some set, agreement
at the earlier `τ i`, `φ i` and the inverses of their conjugates gives agreement at `τ j` up to
`ℓ ^ sep`, and the length of `Z / Z₀`, plus the length modulo `ℓ ^ sep`-torsion of any submodule of
`Z₀` that vanishes at the tame generators and agrees at the `φ j`, is at most the colength
`crystallineColength` of the crystalline members among Ribet's cocycles plus the length of `shaOdd`,
the cocycles unramified off `ℓ` that change sign under `conjGal`. Moreover a member of `Z` is zero
if it vanishes at the `τ j`, the inverses of their conjugates and on a set `s` that detects the
cocycles unramified outside `ℓ` (`IsDetectedBy`). -/
lemma hasTriangleCost_of_isCharacterCocycle [Fintype Y] [Fintype K] [LinearOrder K]
    {ty : K →o {e : Fin t // 0 < e.val}} {g₀ : AbsGal D} {sep c : ℕ}
    (h_tri : IsPrimeTriangle ν w τ φ g₀ t ty sep c) {u : Y → AbsGal D →* Matrix n n O}
    (hu_cont : ∀ x : Y, Continuous (u x)) {W : Type} {q : W → FinPlace D.E} {δ : W → AbsGal D}
    (hq : IsTameGeneratorFamily 0 q δ 1) {Q : Finset (FinPlace D.E)}
    (hq_cover : placesAboveM D ∪ .conjClosure Q ⊆ placesDividing D.E ℓ ∪ (Set.range q).conjClosure)
    (hu_unr : ∀ g ∈ inertiaAbove (placesDividing D.E ℓ ∪ placesAboveM D ∪
      (.conjClosure Q ∪ (Set.range w).conjClosure))ᶜ, ∀ x : Y, u x g = 1)
    (e : Fin t) {γ : AbsGal D} (hγ : γ ∈ inertiaAbove (placesDividing D.E ℓ)ᶜ)
    {s : Finset (AbsGal D)} (hs : IsDetectedBy
      (selmerModule (tateTwist ℓ D.E O e) (placesDividing D.E ℓ) ∅ (QuotSpan (ℓ ^ ν : ↑O))) s)
    {Z : Submodule O (AbsGal D → Unit → QuotSpan (ℓ ^ ν : ↑O))}
    (hZ : ∀ z ∈ Z, IsCharacterCocycle u (cyclotomicInv ℓ D.E O ^ e.val) (withConjInv δ) γ g₀ z) :
    HasTriangleCost Z τ (fun j : K ↦ (conjGal (τ j))⁻¹) φ (fun j : K ↦ (conjGal (φ j))⁻¹)
      {j : K | (ty j).val = e} (ℓ ^ sep)
      (crystallineColength (tateTwist ℓ D.E O e) u ν + length O (shaOdd ℓ D.E O e ν)) ∧
    IsDetectedBy Z (s ∪ image (withConjInv τ) univ) := by
  have h_cover : placesDividing D.E ℓ ∪ placesAboveM D ∪
      (.conjClosure Q ∪ (Set.range w).conjClosure) ⊆
      placesDividing D.E ℓ ∪ (Set.range w).conjClosure ∪ (Set.range q).conjClosure := by
    rintro v ((hv | hv) | hv | hv)
    · exact .inl (.inl hv)
    · exact (hq_cover (.inl hv)).imp_left .inl
    · exact (hq_cover (.inr hv)).imp_left .inl
    · exact .inl (.inr hv)
  have h_obey : Z ≤ ribetCocycles u (tateTwist ℓ D.E O e) (ℓ ^ ν) := fun z hz ↦ (hZ z hz).1
  have h_tame : ∀ z ∈ Z, ∀ k : W × Bool, z (withConjInv δ k) = 0 := fun z hz ↦ by
    obtain ⟨-, h_vanish, -⟩ := hZ z hz
    exact h_vanish
  -- A member of `Z` that is unramified off `ℓ` vanishes at `γ`, so `(χ g₀ - 1) z(g₀) = 0`.
  have h_g₀ : ∀ z ∈ Z,
      z ∈ selmerModule (tateTwist ℓ D.E O e) (placesDividing D.E ℓ) ∅ (QuotSpan (ℓ ^ ν : ↑O)) →
      (cyclotomicInv ℓ D.E O g₀ ^ e.1 - 1) • z g₀ = 0 := by
    intro z hz hz_sel
    obtain ⟨-, h_unram, -⟩ := mem_selmerModule_iff.1 hz_sel
    obtain ⟨-, -, h_kill⟩ := hZ z hz
    exact h_kill (h_unram γ hγ) g₀
  -- The members of `Z` are unramified off `ℓ` and the new places.
  have h_unr : Z ≤ selmerModule (tateTwist ℓ D.E O e)
      (placesDividing D.E ℓ ∪ (Set.range w).conjClosure) ∅ (QuotSpan (ℓ ^ ν : ↑O)) :=
    fun z hz ↦ hq.mem_selmerModule_of_tame_eq_zero
      (ribetCocycles.mem_selmerModule hu_cont hu_unr (h_obey hz) (by simp [obeying]))
      (h_tame z hz) h_cover (by simp +contextual [tateTwist, cyclotomicInv])
  refine ⟨hasTriangleCost_tateTwist h_tri h_unr h_g₀ ?_, fun z hz hzs ↦ hs z ?_ ?_⟩
  · exact add_le_add (relLength_mono h_obey le_rfl) le_rfl
  · -- `z` kills the tame generators at the new places, so it is unramified off `ℓ`
    exact h_tri.isTameGeneratorFamily.mem_selmerModule_of_tame_eq_zero (h_unr hz)
      (fun k ↦ hzs _ (by simp)) .rfl (by simp +contextual [tateTwist, cyclotomicInv])
  · exact fun g hg ↦ hzs g (mem_union_left _ hg)

variable [PadicIso ℓ]

open Period Lift GaloisRep in
/-- Let `V` be a descent pair of ranks `card r < card n`, with type polynomials `c i` over the
residue fields at its chosen places above `p₀` and `p₁`, forming a lift setting for the twist `ϑ`.
Let `t ≤ D.t`, and let `v` be a place above `ℓ` and above `D.levelPrime 0` or `D.levelPrime 1`. Then
`ℓ = D.levelPrime k` for some `k`. Fix any jumps `J`, any level `S` and an element `s` of inertia at
`v` (`IsWeilPair (toGp s) 0`). Consider the conjugate self-dual representations (`IsRepOfType`) with
these jumps and level on which inertia at the chosen places acts through the roots of
`scaledTypePoly V c i * (X - 1) ^ t`, where `scaledTypePoly` rescales the roots of `c i` by the
character of `V`. Let `O ⊆ ℚ̄_ℓ` be a coefficient ring (`CoeffRing ℓ`). The polynomials over `O`
whose images over `ℚ̄_ℓ` kill `s` on all these representations (`IsKilledBy`) satisfy `IsTameType`:
they include `X ^ e - 1`, with `e` the least common multiple of the `ℓ ^ i - 1` for `1 ≤ i ≤ D.r`,
and a monic polynomial over `ℤ_[ℓ]` of degree at most `(D.r + D.t) * D.r`. -/
lemma isTameType_of_mem_placesAboveM {V : DescentPair D.E r n}
    {c : ∀ i : V.ChosenIndex, (ResField (V.chosenPlace i))[X]} {ϑ : D.Twist}
    (hc : IsLiftSetting V c ϑ) (ht : t ≤ D.t)
    {J : (D.E →+* ℂ) → Multiset ℤ} {S : Set (FinPlace D.E)}
    (v : placesDividing D.E ℓ) (hv : v.1 ∈ placesAboveM D) :
    ∃ k : Fin 2, ℓ = D.levelPrime k ∧
      ∀ s : decompGroup (AbsGal D) (placeOver v.1), IsWeilPair (toGp s) 0 →
      IsTameType ℓ D.r ((D.r + D.t) * D.r) fun Q : O[X] ↦ v.1 ∈ placesAboveM D ∧
        ∀ R : GalRep ℓ D.E n,
          IsRepOfType V t J (fun i : V.ChosenIndex ↦ scaledTypePoly V c i * (X - 1) ^ t) S R →
          IsKilledBy (decompRep R (placeOver v.1)) s 0 (Q.map O.1.val) := by
  have ⟨k, hk⟩ :
      ∃ k : Fin 2, (D.levelPrime k : NumberField.RingOfIntegers D.E) ∈ v.1.asIdeal := hv
  have hℓ : D.levelPrime k = ℓ := (v.1.charP_quotient hk).eq _ (v.1.charP_quotient v.2)
  refine ⟨k, hℓ.symm, fun s hs ↦ ?_⟩
  obtain ⟨γ, -, hγ⟩ := exists_inertiaGroup_isInertiaSpectrum n hc hk v.1.isPlaceOver_placeOver t
  obtain ⟨μ, hμ, -⟩ := hγ s ((localChart ℓ D.E v).isWeilPair_zero_iff.1 hs)
  refine isTameType_of_roots (M := μ) (by grw [hμ.card_eq, hc.rank_le.1, ht])
    (by simpa only [hℓ] using hμ.exists_pow_eq_one) fun Q hQ ↦ ⟨hv, fun R hR ↦ ?_⟩
  -- `∏ (X - y)`, `y ∈ μ`, kills `s` on `R`, and `Q` vanishes on `μ`
  exact (hμ.polyKillsAt hR).isKilledBy_of_roots hs
    (by simpa [eval_multiset_prod, eval_map, sub_eq_zero] using! hQ)

omit [PadicIso ℓ] in
open Period Lift in
/-- Ribet's cocycles above `ℓ`. At each place `v` above `ℓ`, let the restrictions of all `u x` and
of `ρ` lie in the class `InClass (F v) (C v) (U v)` of local lattices. This means three things.
Their periods are admissible along the filter `F v`. Their Hodge–Tate jumps lie in the sets `U v`.
Each inertial `s` is killed by every polynomial `Q` with `C v s Q`. Take the cocycles of `ρ` modulo
`ℓ ^ M` that obey the linear relations among the `u x g - 1`. Those that also obey the crystalline
relations above `ℓ` have colength at most the sum over `v` of the `dualDefect`. This defect is the
length of the crystalline cocycles of the Tate dual of `ρ`, modulo those orthogonal under cup
product to the class. -/
lemma crystallineColength_le_sum_dualDefect [Fintype Y] {u : Y → AbsGal D →* Matrix n n O}
    {ρ : AbsGal D →* Matrix r r O}
    {F : ∀ v : placesDividing D.E ℓ, Filter (decompGroup (AbsGal D) (placeOver v.1))}
    {C : ∀ v : placesDividing D.E ℓ, decompGroup (AbsGal D) (placeOver v.1) → O[X] → Prop}
    {U : placesDividing D.E ℓ → (O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → Finset ℤ}
    (hu : ∀ (v : placesDividing D.E ℓ) (x : Y), InClass (F v) (C v) (U v) (localLattice (u x) v))
    (hρ : ∀ v : placesDividing D.E ℓ, InClass (F v) (C v) (U v) (localLattice ρ v)) (M : ℕ) :
    crystallineColength ρ u M ≤ ∑ v : placesDividing D.E ℓ,
      dualDefect (InClass (F v) (C v) (U v)) (localLattice ρ v).tateDual := by
  rw [crystallineColength, obeying_crysRelations]
  exact (relLength_iInf_le _ _).trans (sum_le_sum fun v _ ↦
    relLength_ribetCocycles_le (localChart ℓ D.E v).inducesPlace.2.1 (hu v) M (hρ v))

open Period in
/-- Let `R` be a main summand (`IsMainSummandLike`), in particular conjugate self-dual with
Hodge–Tate jumps `J`, and let `T` agree on the decomposition group at `v` with a lattice `T₀` in
`R`. An element `g` of the absolute Galois group `Gp ℓ` of `ℚ_ℓ` gives an embedding
`coefficientEmbedding O g` of `O` and, through the chart `localChart` at `v`, a complex embedding
`σ` of `E`. At this embedding of `O` the summand `T` has the jumps `J σ`, and `O(-e)` has the single
jump `e`. -/
lemma hasJumps_localLattice_summandRep {J : (D.E →+* ℂ) → Multiset ℤ} {R : GalRep ℓ D.E r}
    (h_summand : IsMainSummandLike D t J R) {T T₀ : AbsGal D →* Matrix r r O}
    (hT₀ : IsLatticeIn R T₀)
    {v : placesDividing D.E ℓ} (hTT₀ : ∀ g ∈ decompGroup (AbsGal D) (placeOver v.1), T g = T₀ g)
    (i : Option (Fin t)) (g : Gp ℓ) :
    HasJumps (localLattice (summandRep T i) v).ρ (coefficientEmbedding O g)
      (i.elim (J (complexEmbeddingOf ((localChart ℓ D.E v).e.comp (algebraMap D.E Ω)) g))
        fun e : Fin t ↦ {↑e}) := by
  rcases i with _ | e
  · let G := decompGroup (AbsGal D) (placeOver v.1)
    have h_restrict : T.comp G.subtype = T₀.comp G.subtype := MonoidHom.ext fun s ↦ hTT₀ s s.2
    change HasJumps (matrixLattice (T.comp G.subtype)).ρ _ _
    rw [h_restrict]
    exact h_summand.toIsConjSelfDualOfLevel.hasJumps_localLattice hT₀ v g
  · intro a
    rw [hasJumps_of_cyclotomicGp_zpow _ (tateTwist_smul _), finrank_pi]
    simp!

omit [DecidableEq r] in
open NumberField in
/-- At each place `v` above `ℓ`, a summand costs the local degree (the index of the decomposition
group in the absolute Galois group of `ℚ_ℓ`) times its rank times the explicit number
`defectBound D ℓ`, divided by `D.t` for a character. For a main summand of rank `r' = card r ≥ 1`
and `t ≤ D.t` characters the total is at most `r' · localDefectBound D ℓ`. -/
lemma sum_index_mul_defectBound_le (hr : 1 ≤ card r) (ht : t ≤ D.t) :
    ∑ i : Option (Fin t), ∑ v : placesDividing D.E ℓ,
      ((localChart ℓ D.E v).toGp.range.index : ℝ≥0∞) *
        (card (SummandCoordIndex r i) * (defectBound D ℓ / (if i = none then 1 else D.t : ℕ)) :
          NNReal) ≤
      card r * localDefectBound D ℓ := by
  classical
  -- The local degree at `v` counts the embeddings of `E` that belong to `v`, out of `2 f`.
  have h_degrees : ∑ v : placesDividing D.E ℓ, (localChart ℓ D.E v).toGp.range.index ≤ 2 * D.f :=
    calc
      _ = ∑ v : placesDividing D.E ℓ, ∑ σ : D.E →+* ℂ with
            ∃ g : Gp ℓ, complexEmbeddingOf ((localChart ℓ D.E v).e.comp (algebraMap D.E Ω)) g = σ,
              1 := by
        simp [(localChart ℓ D.E _).inducesPlace.2.index_eq_card_range, Fintype.card_subtype]
      _ ≤ 2 * D.f := by
        simpa [Embeddings.card, finrank_eq_two_mul_card_infinitePlace] using
          sum_complexEmbeddingOf_le fun _ : D.E →+* ℂ ↦ 1
  -- The main summand costs `r' defectBound`, and the characters together cost at most as much.
  have h_blocks : ∑ i : Option (Fin t),
      (card (SummandCoordIndex r i) * (defectBound D ℓ / (if i = none then 1 else D.t : ℕ)) :
        NNReal) ≤
      2 * card r * defectBound D ℓ :=
    calc
      _ = card r * defectBound D ℓ + t * (defectBound D ℓ / D.t) := by simp [SummandCoordIndex]
      _ ≤ card r * defectBound D ℓ + (card r * D.t : ℕ) * (defectBound D ℓ / D.t) := by
        grw [ht, ← Nat.le_mul_of_pos_left D.t hr]
      _ = 2 * card r * defectBound D ℓ := by
        push_cast
        field [Nat.cast_ne_zero.2 D.t_odd.pos.ne']
  calc
    _ = ((∑ v : placesDividing D.E ℓ, (localChart ℓ D.E v).toGp.range.index : ℕ) : ℝ≥0∞) *
          (∑ i : Option (Fin t), card (SummandCoordIndex r i) *
            (defectBound D ℓ / (if i = none then 1 else D.t : ℕ)) : NNReal) := by
      rw [Nat.cast_sum, ENNReal.ofNNReal_finsetSum, Finset.sum_mul_sum, sum_comm]
    _ ≤ ((2 * D.f : ℕ) : ℝ≥0∞) * (2 * card r * defectBound D ℓ : NNReal) := by gcongr
    _ = card r * localDefectBound D ℓ := by
      rw [localDefectBound]
      push_cast
      ring

open Period Lift Function GaloisRep in
/-- Let the descent pair `V`, with type polynomials `c i` at its chosen places, be a lift setting
for the twist `ϑ` (`IsLiftSetting`). Let `R` be a main summand of rank `r' = card r`, and let the
`ρ x` be representations of rank `card n` on which inertia at the chosen places acts through the
roots of `scaledTypePoly V c i * (X - 1) ^ t` (`IsRepOfType`). Over every sufficiently large
coefficient ring `O`, let the `u x` be lattices in the `ρ x`, and for one index `π` let `u π` be
block diagonal with summands `T` and the characters `O(-e)`, `e < t`, placed by `ϵ`, where `T`
agrees above `ℓ` with a lattice `T₀` in `R`. Then at each place `v` above `ℓ` there is a class
`InClass (F v) (C v) (U v)` of local lattices that contains the restrictions of all `u x` and of the
summands of `u π`. The defect `dualDefect` of a summand at `v` is the length of the crystalline
cocycles of its Tate dual modulo those orthogonal to the class; the defects of the `t + 1` summands
at all places above `ℓ`, scaled so that `O/ℓ` has length 1 (`normLength`), add up to at most
`r' · localDefectBound D ℓ`. -/
lemma eventually_exists_inClass_sum_dualDefect_le {V : DescentPair D.E r n}
    {c : ∀ i : V.ChosenIndex, (ResField (V.chosenPlace i))[X]} {ϑ : D.Twist}
    (hc : IsLiftSetting V c ϑ)
    {J J' : (D.E →+* ℂ) → Multiset ℤ} {S : Set (FinPlace D.E)} {R : GalRep ℓ D.E r}
    {ρ : Y → GalRep ℓ D.E n} (h_summand : IsMainSummandLike D t J R)
    (h_type : ∀ x : Y,
      IsRepOfType V t J' (fun i : V.ChosenIndex ↦ scaledTypePoly V c i * (X - 1) ^ t) S (ρ x))
    (ϵ : Sigma (SummandCoordIndex r (t := t)) ≃ n) (π : Y) :
    ∀ᶠ O : CoeffRing ℓ in atTop, ∀ (T T₀ : AbsGal D →* Matrix r r O)
      (u : Y → AbsGal D →* Matrix n n O),
      (∀ g : AbsGal D,
        u π g = reindex ϵ ϵ (blockDiagonal' fun i : Option (Fin t) ↦ summandRep T i g)) →
      (∀ x : Y, IsLatticeIn (ρ x) (u x)) → IsLatticeIn R T₀ →
      (∀ v ∈ placesDividing D.E ℓ, ∀ g ∈ decompGroup (AbsGal D) (placeOver v), T g = T₀ g) →
      ∃ (F : ∀ v : placesDividing D.E ℓ, Filter (decompGroup (AbsGal D) (placeOver v.val)))
        (C : ∀ v : placesDividing D.E ℓ, decompGroup (AbsGal D) (placeOver v.val) → O[X] → Prop)
        (U : placesDividing D.E ℓ → (O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → Finset ℤ),
        (∀ (v : placesDividing D.E ℓ) (x : Y), InClass (F v) (C v) (U v) (localLattice (u x) v)) ∧
        (∀ (v : placesDividing D.E ℓ) (i : Option (Fin t)),
          InClass (F v) (C v) (U v) (localLattice (summandRep T i) v)) ∧
        ∑ i : Option (Fin t), ∑ v : placesDividing D.E ℓ, O.normLength
          (dualDefect (InClass (F v) (C v) (U v)) (localLattice (summandRep T i) v).tateDual) ≤
          card r * localDefectBound D ℓ := by
  classical
  -- Fix a place `v` above `ℓ`. The lattices `u x` lie in a class of local lattices, and so do the
  -- summands of `u π`. Then `summand_defect_le_at_place` bounds the defect of each summand at `v`,
  -- and `sum_index_mul_defectBound_le` sums over the summands and the places.
  filter_upwards [eventually_all.2 fun v : placesDividing D.E ℓ ↦ summand_defect_le_at_place
    h_summand.toIsMainSummandWeights (localChart ℓ D.E v).inducesPlace.2]
    with O h_place T T₀ u hπ hu_lat hT₀ hTT₀
  -- `L v i`: the summands at `v`; `f`: the splitting of `u π` into its summands
  let G (v : placesDividing D.E ℓ) : Subgroup (AbsGal D) := decompGroup (AbsGal D) (placeOver v.1)
  let L (v : placesDividing D.E ℓ) (i : Option (Fin t)) : GalLattice O (G v) :=
    localLattice (summandRep T i) v
  let f : (n → ↑O) ≃ₗ[O] ∀ i : Option (Fin t), SummandCoordIndex r i → ↑O :=
    LinearEquiv.funCongrLeft O O ϵ ≪≫ₗ .piCurry O fun _ _ ↦ O
  have hf (v : placesDividing D.E ℓ) (i : Option (Fin t)) (g : G v) (x : n → ↑O) :
      f (u π g *ᵥ x) i = (L v i).ρ g (f x i) := by
    simp [L, f, funext_iff, hπ, mulVec_apply_eq_sum, ← ϵ.sum_comp, Fintype.sum_sigma,
      blockDiagonal'_apply', Sigma.curry]
  -- `σ v g`: the complex embeddings of `E` that belong to `v`. In the class at `v` the jumps are
  -- those of the representations of a type. Above `p₀ p₁` the lattices are potentially crystalline,
  -- and `C v s Q` says that `Q` kills `s` on every representation of the given type; elsewhere they
  -- are crystalline (`F v = ⊤`) and `C v` is empty.
  let σ (v : placesDividing D.E ℓ) : Gp ℓ → D.E →+* ℂ :=
    complexEmbeddingOf ((localChart ℓ D.E v).e.comp (algebraMap D.E Ω))
  let F (v : placesDividing D.E ℓ) : Filter (G v) := ⨅ _ : v.1 ∈ placesAboveM D, ⊥
  let C (v : placesDividing D.E ℓ) (s : G v) (Q : O[X]) : Prop := v.1 ∈ placesAboveM D ∧
    ∀ R₀ : GalRep ℓ D.E n,
      IsRepOfType V t J' (fun i ↦ scaledTypePoly V c i * (X - 1) ^ t) S R₀ →
      IsKilledBy (decompRep R₀ (placeOver v.1)) s 0 (Q.map O.1.val)
  let U (v : placesDividing D.E ℓ) : (O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → Finset ℤ :=
    Multiset.toFinset ∘ (fun g ↦ J' (σ v g)) ∘ surjInv coefficientEmbedding_surjective
  have hu (v : placesDividing D.E ℓ) (x : Y) :
      (∀ g : Gp ℓ, HasJumps (localLattice (u x) v).ρ (coefficientEmbedding O g) (J' (σ v g))) ∧
      InClass (F v) (C v) (U v) (localLattice (u x) v) :=
    hasJumps_and_inClass_localLattice v (h_type x).toIsConjSelfDualOfLevel (h_type x) (hu_lat x)
  -- a summand embeds equivariantly in `u π`, so it belongs to the class
  have hL (v : placesDividing D.E ℓ) (i : Option (Fin t)) : InClass (F v) (C v) (U v) (L v i) := by
    refine InClass.of_jointly_injective (fun _ ↦ (hu v π).2)
      (fun () ↦ f.symm ∘ₗ .single O (fun i ↦ L v i) i) ?_ (by simp)
    simp [f.symm_apply_eq, funext_iff, hf, fun g ↦ Pi.apply_single fun i ↦ (L v i).ρ g]
  -- every jump of `u π` is a jump of some summand
  have h_jump_from (v : placesDividing D.E ℓ) (γ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) (a : ℤ) (ha : a ∈ U v γ) :
      ∃ i : Option (Fin t), jump (L v i).ρ γ a ≠ 0 := by
    obtain ⟨g, rfl, ha'⟩ : ∃ g : Gp ℓ, coefficientEmbedding O g = γ ∧ a ∈ J' (σ v g) :=
      ⟨_, surjInv_eq coefficientEmbedding_surjective γ, by simpa [U] using ha⟩
    have h_jump : jump (localLattice (u π) v).ρ (coefficientEmbedding O g) a ≠ 0 :=
      ((hu v π).1 g a).trans_ne (by simpa using ha')
    exact exists_jump_of_jointly_injective (fun i ↦ (hL v i).isPotentiallyCrystalline)
      (fun i ↦ .proj i ∘ₗ f.toLinearMap) (hf v) (by simp [← funext_iff, ← Pi.zero_def]) h_jump
  have h_defect (i : Option (Fin t)) (v : placesDividing D.E ℓ) :
      O.normLength (dualDefect (InClass (F v) (C v) (U v)) (L v i).tateDual) ≤
      (localChart ℓ D.E v).toGp.range.index *
        (card (SummandCoordIndex r i) * (defectBound D ℓ / (if i = none then 1 else D.t : ℕ)) :
          NNReal) := by
    have h_rank (j : Option (Fin t)) : finrank O (L v j) = card (SummandCoordIndex r j) :=
      finrank_pi _
    rw [← h_rank]
    refine h_place v ?_ (h_jump_from v)
      (hasJumps_localLattice_summandRep h_summand hT₀ (hTT₀ v v.2)) (h_rank none) i (hL v i)
    -- the class is tame above `p₀ p₁` and crystalline elsewhere
    by_cases hv : v.1 ∈ placesAboveM D
    · exact .inl (isTameType_of_mem_placesAboveM hc h_summand.t_le v hv)
    · exact .inr (by simp [F, C, hv, funext_iff])
  refine ⟨F, C, U, fun v x ↦ (hu v x).2, hL, ?_⟩
  exact (sum_le_sum fun i _ ↦ sum_le_sum fun v _ ↦ h_defect i v).trans
    (sum_index_mul_defectBound_le h_summand.rank_mem.1 h_summand.t_le)

open GaloisRep in
/-- Let the descent pair `V` with type polynomials `c i` be a lift setting for `ϑ`, and let `R` be a
representation of a type on which inertia at the chosen places acts through the roots of the scaled
type polynomials times `(X - 1) ^ t`. Then each element `g` of inertia at a place above `p₀ p₁` and
prime to `ℓ` acts on `R` with order dividing `D.chosenGroupOrder`. -/
lemma pow_chosenGroupOrder_eq_one_of_mem_inertiaAbove {V : DescentPair D.E r n}
    {c : ∀ i : V.ChosenIndex, (ResField (V.chosenPlace i))[X]} {ϑ : D.Twist}
    (hc : IsLiftSetting V c ϑ)
    {J : (D.E →+* ℂ) → Multiset ℤ} {S : Set (FinPlace D.E)} {R : GalRep ℓ D.E n}
    (hR : IsRepOfType V t J (fun i : V.ChosenIndex ↦ scaledTypePoly V c i * (X - 1) ^ t) S R)
    {g : AbsGal D} (hg : g ∈ inertiaAbove (placesAboveM D \ placesDividing D.E ℓ)) :
    (R g).val ^ D.chosenGroupOrder = 1 := by
  obtain ⟨v, ⟨⟨i, hvi⟩, hvℓ⟩, A, hA : IsPlaceOver A v, hgA⟩ := hg
  -- `R g` is killed by `∏ (X - y)`, `y ∈ μ`, and the order of each `y` divides some
  -- `D.levelPrime i ^ d - 1`, which divides `chosenGroupOrder`
  obtain ⟨μ, h_roots, h_kill⟩ : ∃ μ : Multiset (PadicAlgCl ℓ),
      (∀ y ∈ μ, ∃ d ∈ Set.Icc 1 D.r, y ^ (D.levelPrime i ^ d - 1) = 1) ∧
      PolyKillsAt R A g (μ.map fun y ↦ X - C y).prod := by
    obtain ⟨γ, -, hγ⟩ := exists_inertiaGroup_isInertiaSpectrum n hc hvi hA t
    obtain ⟨μ, hμ, -⟩ := hγ g hgA
    exact ⟨μ, hμ.exists_pow_eq_one, hμ.polyKillsAt hR⟩
  have h_root (y : PadicAlgCl ℓ) (hy : y ∈ μ) : y ^ D.chosenGroupOrder = 1 := by
    obtain ⟨d, ⟨hd_pos, hd_le⟩, hyd⟩ := h_roots y hy
    obtain ⟨m, hm⟩ : D.levelPrime i ^ d - 1 ∣ D.chosenGroupOrder :=
      levelPrime_pow_sub_one_dvd_chosenGroupOrder D ⟨hd_pos, hd_le.trans D.nat_le_of_hasLogBound⟩
    rw [hm, pow_mul, hyd, one_pow]
  -- inertia acts through a finite group, so a polynomial that vanishes on `μ` kills `R g`
  have h_finite : IsFiniteTypeAt R A := (hR.local_conditions v (·.2 (.inr ⟨i, hvi⟩)) hA).1
  have h_aeval : aeval (R g).1 (X ^ D.chosenGroupOrder - 1 : (PadicAlgCl ℓ)[X]) = 0 :=
    h_finite.aeval_eq_zero_of_roots (hA.valuation_natCast_eq_one_iff.2 hvℓ) hgA h_kill _
      (by simpa [eval_multiset_prod, sub_eq_zero] using h_root)
  simpa [sub_eq_zero] using h_aeval

/-- Let `V` with type polynomials `c i` form a lift setting (`IsLiftSetting`), and let `ψ` be an
auxiliary twist (`IsAuxTwist`): it comes from the norm-one torus with modulus `Q`, the places of `Q`
avoid the places `badPlaces D ℓ` that divide `ℓ p₀ p₁` or the level `D.N`, and the valuations of
`ψ - 1` at tame generators over `Q` add up to at most `ram`. Let the `u x` be representations of a
type with the scaled type polynomials, on which inertia above `Q` and `Q̄` satisfies
`(g - ψ g) (g - 1) = 0`, and let `u' x` and `ψ'` be models over `O`. Then there are finitely many
places `q j` prime to `ℓ`, covering `Q` and the places above `p₀ p₁` prime to `ℓ` up to conjugation,
with tame generators `δ j`. For each `δ` among the `δ j` and the inverses of their conjugates
(`withConjInv δ`) there is a polynomial `o` such that `o(δ) (δ - 1)` vanishes on every `u' x`, and
the valuations of the `o(1)` add up to at most `2 ram + 8 f v_ℓ(N)`, where `f = D.f` is the number
of infinite places of `E` and `N = D.chosenGroupOrder`. -/
lemma exists_tame_relations {V : DescentPair D.E r n}
    {c : ∀ i : V.ChosenIndex, (ResField (V.chosenPlace i))[X]} {ϑ : D.Twist}
    (hc : IsLiftSetting V c ϑ) {ψ : AbsGal D →* PadicAlgCl ℓ}
    {Q : Finset (FinPlace D.E)} {ram : ℝ≥0∞} (h_twist : IsAuxTwist (badPlaces D ℓ) Q ψ ram)
    {J : (D.E →+* ℂ) → Multiset ℤ} {S : Set (FinPlace D.E)} {u : Y → GalRep ℓ D.E n}
    (h_type : ∀ x : Y,
      IsRepOfType V t J (fun i : V.ChosenIndex ↦ scaledTypePoly V c i * (X - 1) ^ t) S (u x))
    (h_quad : ∀ x : Y, ∀ g ∈ inertiaAbove (Set.conjClosure Q),
      ((u x g).val - ψ g • 1) * ((u x g).val - 1) = 0)
    {u' : Y → AbsGal D →* Matrix n n O} (hu' : ∀ x : Y, IsLatticeIn (u x) (u' x))
    {ψ' : AbsGal D →* O} (hψ' : ∀ g : AbsGal D, ψ' g = ψ g) :
    ∃ (W : Type) (_ : Fintype W) (q : W → FinPlace D.E) (δ : W → AbsGal D) (o : W × Bool → O[X]),
      IsTameGeneratorFamily 0 q δ 1 ∧
      placesAboveM D ∪ .conjClosure Q ⊆ placesDividing D.E ℓ ∪ (Set.range q).conjClosure ∧
      (∀ (k : W × Bool) (x : Y), aeval (u' x (withConjInv δ k)) (o k * (X - 1)) = 0) ∧
      O.normLength (∑ k : W × Bool, addVal O ((o k).eval 1)) ≤
        2 * ram + 8 * D.f * padicValNat ℓ D.chosenGroupOrder := by
  -- The places are those of `Q`, with `o = ψ(δ) - X`, and the set `M` of places above `p₀ p₁` prime
  -- to `ℓ`, with `o = (X ^ N - 1) / (X - 1)`.
  obtain ⟨-, hψ : IsFromU1 (placesDividing D.E ℓ) Q ψ, σ, hσ :
    IsTameGeneratorFamily 0 Subtype.val σ 1,
    h_ram : ∑ k : Q, ellVal (ψ (σ k) - 1) ≤ ram⟩ := h_twist
  have h_fin : (placesAboveM D \ placesDividing D.E ℓ).Finite :=
    (badPlaces D ℓ).finite_toSet.subset fun v hv ↦
      placesDividing_union_subset_badPlaces D ℓ (.inr hv.1)
  let M : Finset (FinPlace D.E) := h_fin.toFinset
  have hM (v : M) : v.1 ∈ placesAboveM D \ placesDividing D.E ℓ := h_fin.mem_toFinset.1 v.2
  let q : Q ⊕ M → FinPlace D.E := Sum.elim (↑) (↑)
  let δ : Q ⊕ M → AbsGal D := Sum.elim σ fun v ↦ v.1.isPlaceOver_placeOver.tameGenerator
  have hq : IsTameGeneratorFamily 0 q δ 1 := by
    rintro (v | v)
    · exact hσ v
    · exact ⟨(hM v).2, map_one _, placeOver v.1, v.1.isPlaceOver_placeOver, rfl⟩
  have h_inertia (k : (Q ⊕ M) × Bool) {S : Set (FinPlace D.E)}
      (hS : q k.1 ∈ S ∧ star (q k.1) ∈ S) : withConjInv δ k ∈ inertiaAbove S := by
    obtain ⟨-, -, A, hA : IsPlaceOver A (q k.1), hδA : hA.tameGenerator = δ k.1⟩ := hq k.1
    exact idOrConjInv_mem_inertiaAbove hA (by simp [← hδA]) hS _
  let o (k : (Q ⊕ M) × Bool) : O[X] :=
    k.1.elim (fun _ ↦ C (ψ' (withConjInv δ k)) - X) fun _ ↦ ∑ i ∈ range D.chosenGroupOrder, X ^ i
  refine ⟨Q ⊕ M, inferInstance, q, δ, o, hq, ?_, fun k x ↦ ?_, ?_⟩
  · have h_range : Set.range q = ↑Q ∪ placesAboveM D \ placesDividing D.E ℓ :=
      Set.ext (by simp [q, M])
    rw [h_range]
    rintro v (hv | hv | hv)
    · by_cases hvℓ : v ∈ placesDividing D.E ℓ
      · exact .inl hvℓ
      · exact .inr (.inl (.inr ⟨hv, hvℓ⟩))
    · exact .inr (.inl (.inl hv))
    · exact .inr (.inr (.inl hv))
  · -- it suffices to check the relation on `u x`, which is the image of `u' x` under `F`
    obtain ⟨F, hF_inj : Function.Injective F, hF : ∀ g : AbsGal D, F (u' x g) = u x g, -⟩ :=
      (hu' x).exists_algHom
    apply hF_inj
    obtain ⟨j | j, b⟩ := k
    · -- at `Q` the eigenvalues are `1` and `ψ g`
      set g : AbsGal D := withConjInv δ (.inl j, b) with hg
      have h_prod : (ψ g • 1 - (u x g).1) * ((u x g).1 - 1) = 0 := by
        rw [← neg_sub, neg_mul, h_quad x g (h_inertia _ (by simp [q])), neg_zero]
      have h_scalar : F (algebraMap O (Matrix n n O) (ψ' g)) = ψ g • 1 := by
        rw [F.commutes, ← hψ', Algebra.algebraMap_eq_smul_one, O.1.smul_def]
      simpa [o, ← hg, hF, h_scalar, -AlgHom.commutes] using h_prod
    · -- above `p₀ p₁` the order divides `N`
      have h_pow : (u x (withConjInv δ (.inr j, b))).1 ^ D.chosenGroupOrder = 1 :=
        pow_chosenGroupOrder_eq_one_of_mem_inertiaAbove hc (h_type x)
          (h_inertia _ (by simpa [q] using hM j))
      simpa [o, hF, geom_sum_mul, sub_eq_zero] using h_pow
  · have h_card : (#M : ℝ≥0∞) ≤ 4 * D.f :=
      mod_cast card_le_of_subset_placesAboveM D (T := M) (by simp [M])
    calc
      -- `o(1)` is `ψ (σ k) - 1` at both copies of `k ∈ Q`, `N` at both copies of a place of `M`
      _ = 2 * ∑ k : Q, ellVal (ψ (σ k) - 1) + 2 * #M * padicValNat ℓ D.chosenGroupOrder := by
        simp [o, δ, ellVal_natCast (NeZero.ne D.chosenGroupOrder), hψ', hψ.apply_idOrConjInv,
          sum_prod_type, two_mul, add_mul, sum_add_distrib]
        ring
      _ ≤ 2 * ram + 2 * (4 * D.f) * padicValNat ℓ D.chosenGroupOrder := by gcongr
      _ = 2 * ram + 8 * D.f * padicValNat ℓ D.chosenGroupOrder := by ring

end RibetElement

end New.Selmer
