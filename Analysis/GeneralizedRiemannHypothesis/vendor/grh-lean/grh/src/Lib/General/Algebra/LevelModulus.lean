import Lib.Adelic.AutomorphicForms.PAdicGauge
import Lib.General.LinearAlgebra.BlockEmbeddings
import Lib.Weil.DualPair.KernelDecay
import Lib.Weil.DualPair.KernelLaws

/-!
# Level moduli, residue data as Schwartz–Bruhat functions, and descent in positive degree

This file treats the modulus `M ^ c Q`, where `M` and `Q` are the products of two families of places
(the chosen places and the twist places) and `c` is a natural number. For a principal modulus
`(star g)` and a vector `x` with `g x` integral, it writes the translate of the vacuum by `x` as a
combination of the data `New.modDatum` of indicator functions of classes. Finally it proves a lemma
of algebra: if ∏ (T - a i) = 0 with all a i ≠ 0 and ∏ (S T^k - α i a i^k) = 0 for every k > 0, then
∏ (S - α i) = 0.

## Main definitions and results

* `New.Rows.places_levelModulus`: for `c ≠ 0` the places dividing `M ^ c Q` are the places of `M`
  and of `Q`.
* `New.isSchwartzBruhat_residueDatum`: the function `New.residueDatum w f` (`f` of the reductions
  at the places `w i` on matrices integral there, `0` elsewhere) is Schwartz–Bruhat
  (`New.IsSchwartzBruhat`) if no `w i` is conjugate to a `w j`.
* `New.Rows.liftFn_eq_residueDatum`, `New.exists_modulus_places_eq`: it is the lift of a function
  modulo a modulus `New.Modulus`, an ideal prime to its conjugate, with the same set of places;
  such a modulus exists if no `w i` is conjugate to a `w j`.
* `New.exists_rho_finVec_vacElem_eq_sum_modDatum`: if `𝔪 = (star g)` and `g x` is integral, the
  translate of the vacuum by `x` is a combination of the data `New.modDatum` of the indicator
  functions of classes modulo `𝔪`, with values of `New.stdLattice.selfDualAddChar` as coefficients.
* `New.GaloisRep.eval₂_prod_eq_zero_of_mul_pow`: the lemma of algebra just stated, for S and T in a
  ring that commute with the image of a ring homomorphism from a field K.

Notions from other files:
* `New.Modulus.liftFn`: A function Ψ of vectors mod 𝔪, read on finite adelic vectors: Ψ of the
  reduction if the vector is integral at the places of 𝔪 (`New.Modulus.places`), and 0 otherwise.

## Relation to the literature

Known; see `Lib.Weil.MixedModel.ZeroTerm` for sources.
-/

namespace New

/-!
## The level modulus of a set of chosen places and its places

For chosen places `S` (`New.LevelPlaces`: two finite families, with products `M` and `Q`, no place
conjugate to itself or to another), `New.LevelPlaces.levelModulus S c b` is the modulus `M ^ c Q` or
`M ^ c`, according to `b`.
-/

section LevelModulus

open Matrix NumberField Ideal IsPrime Set Finset Rows

variable {E : Type} [Field E] [NumberField E] {ι : Type*} [Fintype ι] {u : ι → FinPlace E}

/-- The product of finitely many places `u i` of `E` is contained in the prime of a place `w` if and
only if `w` is one of the `u i`. -/
lemma Rows.prod_places_le_iff {w : FinPlace E} :
    ∏ i : ι, (u i).asIdeal ≤ w.asIdeal ↔ ∃ i : ι, u i = w := by
  simp [prod_le, IsMaximal.eq_iff_le, ne_top, (u _).ext_iff]

variable [IsCMField E] (S : LevelPlaces E)

/-- The modulus M^c·Q if b is true and M^c otherwise, with M and Q the products of the places
`New.LevelPlaces.chosenPlace` and `New.LevelPlaces.twistPlace` of S. -/
noncomputable def LevelPlaces.levelModulus (c : ℕ) (b := true) : Modulus E where
  ideal :=
    (∏ i : S.ChosenIndex, (S.chosenPlace i).1) ^ c *
      if b then ∏ i : S.TwistIndex, (S.twistPlace i).1 else 1
  ne_bot := by simp [← absNorm_eq_zero_iff, prod_eq_zero_iff, ite_eq_iff]
  not_le_star := by
    -- A place that divides the modulus is a chosen place or a twist place, and none of these is
    -- conjugate to itself or to another.
    obtain ⟨-, h_conj⟩ := S.apart
    have h_place : ∀ w : FinPlace E,
        (∏ i : S.ChosenIndex, (S.chosenPlace i).1) ^ c *
          (if b then ∏ i : S.TwistIndex, (S.twistPlace i).1 else 1) ≤ w.asIdeal →
          ∃ i : S.ChosenIndex ⊕ S.TwistIndex, (S.chosenPlace ⊕ᵥ S.twistPlace) i = w := fun w hw ↦ by
      rw [Sum.exists]
      exact (w.isPrime.mul_le.1 hw).imp (fun h ↦ prod_places_le_iff.1 (w.isPrime.le_of_pow_le h))
        fun h ↦ prod_places_le_iff.1 (by cases b <;> simp_all [w.isPrime.ne_top])
    intro w hw hw'
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := And.intro (h_place w hw) (h_place (star w) hw')
    exact h_conj i j (by rw [hi, hj])

/-- The modulus M·Q is the product of the chosen places and the twist places of S. -/
lemma LevelPlaces.ideal_levelModulus_one :
    (S.levelModulus 1).ideal =
      ∏ i : S.ChosenIndex ⊕ S.TwistIndex, ((S.chosenPlace ⊕ᵥ S.twistPlace) i).asIdeal := by
  simp [LevelPlaces.levelModulus]

/-- The modulus M is the product of the chosen places of S. -/
lemma LevelPlaces.ideal_levelModulus_one_false :
    (S.levelModulus 1 false).ideal = ∏ i : S.ChosenIndex, (S.chosenPlace i).asIdeal := by
  simp [LevelPlaces.levelModulus]

variable {S}

/-- Let `S` be a choice of chosen places and twist places of `E`, with products `M` and `Q`. For
`c ≠ 0` (the instance `NeZero c`), the places that divide the modulus `S.levelModulus c = M ^ c Q`
are the chosen places and the twist places. -/
lemma Rows.places_levelModulus {c : ℕ} [NeZero c] :
    (S.levelModulus c).places = Set.range (S.chosenPlace ⊕ᵥ S.twistPlace) := by
  ext w
  -- A prime contains `M ^ c Q` iff it contains `M` or `Q`, iff it is one of their factors.
  change (∏ i : S.ChosenIndex, (S.chosenPlace i).asIdeal) ^ c *
    ∏ i : S.TwistIndex, (S.twistPlace i).asIdeal ≤ w.asIdeal ↔ _
  rw [w.isPrime.mul_le, pow_le_iff (NeZero.ne c), prod_places_le_iff, prod_places_le_iff]
  simp

/-- For c ≠ 0 and a place dividing M or Q, the reduction from the residue ring modulo M^c·Q to the
residue field at that place. -/
noncomputable abbrev Rows.levelResidueAt {c : ℕ} [NeZero c] (i : S.ChosenIndex ⊕ S.TwistIndex) :
    (S.levelModulus c).ResidueRing →+* ResField ((S.chosenPlace ⊕ᵥ S.twistPlace) i) :=
  modulusResidue (S.levelModulus c) (places_levelModulus.ge ⟨i, rfl⟩)

/-- If the ideal of 𝔪 is the product of the primes u i, then every u i divides 𝔪. -/
lemma Modulus.mem_places_of_ideal_eq_prod {𝔪 : Modulus E}
    (h𝔪 : 𝔪.ideal = ∏ i : ι, (u i).asIdeal) (i : ι) : u i ∈ 𝔪.places :=
  h𝔪.trans_le (prod_places_le_iff.2 ⟨i, rfl⟩)

/-- The injectivity in the Chinese remainder theorem: if the ideal of 𝔪 is the product of the
distinct primes u i, two matrices over O_E/𝔪 are equal if and only if their reductions at every
u i are equal. -/
lemma Modulus.matrix_eq_iff_map_modulusResidue_eq {𝔪 : Modulus E} (hu : u.Injective)
    (h𝔪 : 𝔪.ideal = ∏ i : ι, (u i).asIdeal) {a b : Type*} {x y : Matrix a b 𝔪.ResidueRing} :
    x = y ↔
      ∀ i : ι,
        x.map (modulusResidue 𝔪 (mem_places_of_ideal_eq_prod h𝔪 i)) =
          y.map (modulusResidue 𝔪 (mem_places_of_ideal_eq_prod h𝔪 i)) := by
  -- Reduce to one pair of entries, with representatives `c`, `d` in the ring of integers.
  simp only [← ext_iff, Matrix.map_apply, forall_comm (α := ι)]
  refine forall₂_congr fun i j ↦ ?_
  obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ :=
    And.intro (Ideal.Quotient.mk_surjective (x i j)) (Ideal.Quotient.mk_surjective (y i j))
  have h_red (k : ι) (hk : u k ∈ 𝔪.places) (e : 𝓞 E) :
      modulusResidue 𝔪 hk (Ideal.Quotient.mk 𝔪.ideal e) = algebraMap (𝓞 E) (ResField (u k)) e :=
    rfl
  -- `c - d` lies in the product of the distinct primes `u k` iff it lies in each of them.
  simp_rw [← hc, ← hd, h_red, Ideal.Quotient.eq, h𝔪, mem_prod_finPlace_iff hu,
    ← algebraMap_ResField_eq_zero, map_sub, sub_eq_zero]

end LevelModulus

/-! ## Residue data and translates of the vacuum -/

section ResidueDataApi

open Matrix Set Valued Rows Modulus NumberField

section

variable {n n' E : Type} [Field E] [NumberField E] [IsCMField E]
  {ι : Type*} [Fintype ι] {w : ι → FinPlace E}
  (f : ((i : ι) → Matrix n' n (ResField (w i))) → ℂ) [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {x : n' × n → 𝔸f E} {𝔪 : Modulus E}

/-- For a place `w` dividing the modulus `𝔪` and an element `k` of the integral finite adelic
unitary group `stdLevel E n`, reducing `k` modulo `𝔪` (`reductionGL`) and then modulo `w`
(`modulusResidue`) is the reduction `stdLevel.reduceAt w k` of `k` at `w`. -/
@[simp]
lemma Rows.reductionGL_map_modulusResidue (𝔪 : Modulus E) {w : FinPlace E} (h : w ∈ 𝔪.places)
    (k : stdLevel E n) :
    (reductionGL 𝔪 k).val.map (modulusResidue 𝔪 h) = (stdLevel.reduceAt w k).val := by
  ext i j
  exact modulusResidue_reduction 𝔪 h _

omit [DecidableEq n] [DecidableEq n'] in
/-- If the places of `𝔪` are the `w i`, then `New.residueDatum w f` (`f` of the reductions at the
`w i` on matrices integral there, `0` elsewhere) is the lift `New.Modulus.liftFn` to adelic vectors
of the function that sends a matrix `T` modulo `𝔪` to `f` of the reductions `modulusResidue` of `T`
at the `w i`; `vecToMatrix` reads a vector indexed by `n' × n` as a matrix. -/
lemma Rows.liftFn_eq_residueDatum {𝔪 : Modulus E} (h_places : places 𝔪 = range w)
    (f : ((i : ι) → Matrix n' n (ResField (w i))) → ℂ) :
    𝔪.liftFn
        ((fun T : Matrix n' n 𝔪.ResidueRing ↦
            f fun i : ι ↦ T.map (modulusResidue 𝔪 (h_places.ge ⟨i, rfl⟩))) ∘
          vecToMatrix (m := n) (m' := n')) =
      residueDatum w f := by
  classical
  ext x
  -- Both sides test whether the entries of `x` are integral at the places `w i`.
  have h_int : (∀ p : n' × n, idem 𝔪.places * x p ∈ Ô E) ↔
      ∀ (i : ι) (p : n' × n), x p (w i) ∈ LocInt (w i) := by
    simp only [idem_mul_mem_Ô, h_places, forall_mem_range]
    exact forall_comm
  -- Reducing modulo `𝔪` and then modulo `w i` gives the residue of the component at `w i`.
  have h_res (i : ι) (hi : w i ∈ 𝔪.places) (z : 𝔸f E) (hz : idem 𝔪.places * z ∈ Ô E) :
      modulusResidue 𝔪 hi (𝔪.reduction ⟨idem 𝔪.places * z, hz⟩) = residueOrZero (z (w i)) := by
    simp [reduceAt, ← residueOrZero_coe, RingHom.codRestrict, hi]
  simp only [liftFn_apply, residueDatum, h_int]
  split_ifs <;> simp [h_res, map, vecToMatrix]

open Space stdLattice Ideal

/-- If no `w i` is conjugate to a `w j`, there is a modulus whose places are the `w i` and which
contains the intersection of these primes. -/
lemma exists_modulus_places_eq (hw : ∀ i j : ι, star (w i) ≠ w j) :
    ∃ 𝔪 : Modulus E,
      places 𝔪 = range w ∧ (Finset.univ.inf fun i : ι ↦ (w i).asIdeal) ≤ 𝔪.ideal := by
  -- Take the intersection of the `w i`; a prime contains it exactly if it is one of them.
  let I : Ideal (𝓞 E) := Finset.univ.inf fun i : ι ↦ (w i).asIdeal
  have h_le (u : FinPlace E) : I ≤ u.asIdeal ↔ ∃ i : ι, w i = u := by
    rw [u.isPrime.inf_le', ← prod_places_le_iff, u.isPrime.prod_le]
  have h_ne : I ≠ ⊥ := fun h_bot ↦
    let ⟨i, _, hi⟩ := Ideal.isPrime_bot.inf_le'.1 h_bot.le; (w i).ne_bot (le_bot_iff.1 hi)
  -- By `hw`, a prime and its conjugate do not both contain `I`.
  refine ⟨⟨I, h_ne, fun u hu hu' ↦ ?_⟩, Set.ext h_le, le_rfl⟩
  obtain ⟨i, rfl⟩ := (h_le u).1 hu
  obtain ⟨j, hj⟩ := (h_le _).1 hu'
  exact hw i j hj.symm

end

open Space stdLattice Ideal

variable {n n' E : Type} [Field E] [CMType E] {ι : Type*} [Fintype ι] {w : ι → FinPlace E}
  (f : ((i : ι) → Matrix n' n (ResField (w i))) → ℂ) [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {x : n' × n → 𝔸f E} {𝔪 : Modulus E} [WeilData E] {s : n → ℤˣ} {s' : n' → ℤˣ}
  (V : Space E n s) (V' : Space E n' s')

omit [WeilData E] in
/-- If no `w i` is conjugate to a `w j`, then `New.residueDatum w f` (`f` of the reductions at the
`w i` on matrices integral there, `0` elsewhere) is Schwartz–Bruhat at the places `w i`: it depends
only on the components there and, as a function of these, is locally constant of compact support. -/
lemma isSchwartzBruhat_residueDatum (hw : ∀ i j : ι, star (w i) ≠ w j) :
    IsSchwartzBruhat (range w) (residueDatum w f) := by
  obtain ⟨𝔪, h𝔪, -⟩ := exists_modulus_places_eq hw
  rw [← h𝔪, ← liftFn_eq_residueDatum h𝔪 f]
  exact isSchwartzBruhat_liftFn 𝔪 _

/-- The datum `New.modDatum` of a function `Ψ` on matrices modulo `𝔪` with the Gaussian
`Fock.vacVector` as real part is what the operator `schrodingerOp` of the lift of `Ψ` (`vecToMatrix`
reads vectors as matrices) makes of the vacuum `vacElem` of `V.hom V' = Hom(V, V')`. Here
`V : Space E n s` and `V' : Space E n' s'` have signs `s`, `s'` (units ±1), and `E` carries a CM
type (`CMType E`) and Weil data (`WeilData E`). For a function `Φ` on finite adelic vectors,
`New.Space.schrodingerOp W P Φ` is the operator on `𝒮 W` (the space on which `W.ϱ` acts, which
contains the vacuum `vacElem`) that realizes `Φ` at the places `P`: the combination of Heisenberg
translations whose counterpart in the Schrödinger model at `P` carries the indicator of the integral
vectors to `Φ`, if there is one. -/
@[simp↓]
lemma modDatum_vacVector (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ) :
    modDatum V V' 𝔪 Ψ Fock.vacVector =
      schrodingerOp (V.hom V') 𝔪.places (𝔪.liftFn (Ψ ∘ vecToMatrix))
        (Space.vacElem (V.hom V')) := by
  -- The operator of the real part commutes with `schrodingerOp` and, for the Gaussian, fixes the
  -- vacuum.
  simp [modDatum, integrated_schrodingerOp]

/-- Let the ideal of the modulus `𝔪` be `(star g)`, and let `x` be a finite adelic vector of
`V.hom V' = Hom(V, V')` with `g x` in `Ô E` (integral). Apply the Heisenberg operator `ϱ` of
`New.finVec x` (finite part `α x`, where `α` is the finite idele of the Weil data; real part zero)
to the vacuum `vacElem`. The result is `∑_T New.stdLattice.selfDualAddChar E (z T) • New.modDatum V
V' 𝔪 (Pi.single T 1) Fock.vacVector` for some `z`, where `T` runs over the matrices modulo `𝔪`, and
each datum has real part the Gaussian `Fock.vacVector`, equals the lift of the indicator of `T` at
the places dividing `𝔪`, and equals the vacuum elsewhere. -/
lemma exists_rho_finVec_vacElem_eq_sum_modDatum {g : 𝓞 E} (h_ideal : 𝔪.ideal = span {star g})
    (hx : ∀ i : n' × n, algebraMap E (𝔸f E) g * x i ∈ Ô E) :
    ∃ z : Matrix n' n 𝔪.ResidueRing → 𝔸f E,
      (V.hom V').ϱ (finVec x) (Space.vacElem (V.hom V')) =
        ∑ T : Matrix n' n 𝔪.ResidueRing,
          selfDualAddChar E (z T) • modDatum V V' 𝔪 (Pi.single T 1) Fock.vacVector := by
  -- `x` differs by a lattice vector `y` from its part above the conjugates of the places of `𝔪`.
  -- The operator `finHeisenbergOp y` fixes the vacuum, and the translate of the vacuum by that part
  -- is the datum of an additive character modulo `𝔪` (`schrodingerOp_char_eq_translate_projOn`).
  -- First: for `a = c * conj g`, `c` integral, `a * conj (x q) = c * conj (g * x q)` is integral.
  have h_ker_mul (q : n' × n) (a : Ô E) (ha : 𝔪.reduction a = 0) : ↑a * star (x q) ∈ Ô E := by
    obtain ⟨c, rfl⟩ : ∃ c : Ô E, c * algebraMap (𝓞 E) (Ô E) (star g) = a := by
      simpa [𝔪.reduction_eq_zero_iff, h_ideal, map_span, mem_span_singleton'] using ha
    simpa [mul_assoc] using mul_mem c.2 (star_mem_Ô (hx q))
  let y : n' × n → 𝔸f E := star (idem 𝔪.places) • x - x
  have hy : y ∈ stdLattice E (n' × n) := fun q ↦ by
    have h_red : 𝔪.reduction (⟨idem 𝔪.places, idem_mem_Ô _⟩ - 1) = 0 := by
      simpa [sub_eq_zero] using 𝔪.reduction_idem_mul 1
    simpa [y, sub_mul] using star_mem_Ô (h_ker_mul q _ h_red)
  -- The character is `r ↦ 𝔪.primAddChar (r ⬝ᵥ 𝔪.reduction ∘ u)` for the integral vector
  -- `u = 𝔪.generator * conj x`.
  let u : n' × n → Ô E := fun q ↦ ⟨𝔪.generator * star (x q),
    h_ker_mul q ⟨𝔪.generator, 𝔪.generator_spec.1⟩ (by simp [generator_spec])⟩
  have h_part : x + y = star (idem 𝔪.places • 𝔪.generator⁻¹.val • Subtype.val ∘ u) := by
    ext; simp [y, u]
  -- The translate is a multiple of the operator of that character applied to the vacuum.
  let W := V.hom V'
  have h_translate : W.ϱ (finVec x) W.vacElem =
      semichar y • selfDualAddChar E (half * star y ⬝ᵥ x) •
        schrodingerOp W 𝔪.places (𝔪.liftFn fun r ↦ 𝔪.primAddChar (r ⬝ᵥ 𝔪.reduction ∘ u))
          W.vacElem := calc
    _ = semichar y • W.ϱ (finVec x) (W.ϱ (finVec y) W.vacElem) := by
      conv_lhs => rw [← finHeisenbergOp_vacElem hy]
      simp [W, finHeisenbergOp]
    _ = semichar y • selfDualAddChar E (half * star y ⬝ᵥ x) • W.ϱ (finVec (x + y)) W.vacElem := by
      rw [rho_finVec_rho_finVec]
    _ = _ := by rw [schrodingerOp_char_eq_translate_projOn, projOn_vacElem, h_part]
  have h_lift : (fun r : n' × n → 𝔪.ResidueRing ↦ 𝔪.primAddChar (r ⬝ᵥ 𝔪.reduction ∘ u)) =
    (fun T ↦ 𝔪.primAddChar (matrixToVec T ⬝ᵥ 𝔪.reduction ∘ u)) ∘ vecToMatrix := rfl
  rw [h_translate, h_lift, ← modDatum_vacVector, modDatum_eq_sum]
  -- The scalars `semichar y`, `selfDualAddChar E (half * star y ⬝ᵥ x)` and the values of
  -- `𝔪.primAddChar` are all values of `selfDualAddChar`.
  have h_psi : ∀ r : 𝔪.ResidueRing, ∃ a : 𝔸f E, 𝔪.primAddChar r = selfDualAddChar E a :=
    𝔪.reduction_surjective.forall.2 fun b ↦ ⟨_, 𝔪.primAddChar_reduction b⟩
  choose a ha using h_psi
  simp only [ha, Finset.smul_sum, smul_smul, semichar, ← AddChar.map_add_eq_mul]
  -- So `z T` is the sum of the arguments of the three scalars at `T`.
  exact ⟨fun T ↦ traceOneAdele * half * star y ⬝ᵥ y +
    (half * star y ⬝ᵥ x + a (matrixToVec T ⬝ᵥ 𝔪.reduction ∘ u)), rfl⟩

end ResidueDataApi

end New

/-!
## Relations for S T^k in positive degree give the relation for S
-/

section PositiveDegreeDescent

open Polynomial Finset Ideal Quotient PiTensorProduct

/-- Let `S`, `T` lie in a `K`-algebra `Z` and let `α i`, `a i` be scalars with `a i ≠ 0`. If
`∏ (T - a i) = 0`, and `∏ (S T ^ k - α i * a i ^ k) = 0` for all `k > 0`, then `∏ (S - α i) = 0`. -/
lemma New.GaloisRep.aeval_prod_eq_zero_of_mul_pow {K Z : Type*} {n : ℕ} [Field K] [Ring Z]
    [Algebra K Z] {α a : Fin n → K} (S T : Z) (hT : aeval T (∏ i : Fin n, (X - C (a i))) = 0)
    (ha : ∀ i : Fin n, a i ≠ 0)
    (hST : ∀ k > (0 : ℕ), aeval (S * T ^ k) (∏ i : Fin n, (X - C (α i * a i ^ k))) = 0) :
    aeval S (∏ i : Fin n, (X - C (α i))) = 0 := by
  -- Work in the `n`-th tensor power of `R = K[X] / (q)`, one factor for each index `i`.
  set q : K[X] := ∏ i, (X - C (a i))
  let R : Type _ := K[X] ⧸ span {q}
  have : Module.Finite K R := (monic_prod_X_sub_C a univ).finite_quotient
  -- The class `ξ` of `X` is a unit of `R`, as it divides `q - q(0)` and `q(0) ≠ 0`.
  let ξ : R := Ideal.Quotient.mk (span {q}) X
  have hX : IsUnit ξ := by
    refine isUnit_of_dvd_unit (map_dvd _ q.X_dvd_sub_C) ?_
    have hq0 : q.coeff 0 ≠ 0 := by simp [q, ha, prod_eq_zero_iff, coeff_zero_prod]
    simpa using (hq0.isUnit.map C).map (Ideal.Quotient.mk (span {q}))
  -- So `y = X ⊗ ⋯ ⊗ X` is a unit of a finite algebra: `p(y) = 0` for some `p` with `p(0) ≠ 0`.
  let y : PiTensorProduct K fun _ : Fin n ↦ R := tprodMonoidHom K (Pi.constRingHom (Fin n) R ξ)
  have hy : IsUnit y := (hX.map (Pi.constRingHom (Fin n) R)).map (tprodMonoidHom K)
  obtain ⟨p, hp0, hp⟩ : ∃ p : K[X], p.coeff 0 ≠ 0 ∧ aeval y p = 0 :=
    (IsAlgebraic.of_finite K y).exists_nonzero_coeff_and_aeval_eq_zero hy.mem_nonZeroDivisors
  -- `ev i` sends `X` to `(T, a i)`; it is well defined on `R` as `q(T) = 0` and `q(a i) = 0`.
  have h_vanish (i : Fin n) (r : K[X]) (hr : r ∈ span {q}) : aeval (T, a i) r = 0 :=
    aeval_eq_zero_of_dvd_aeval_eq_zero (mem_span_singleton.1 hr) <| by
      simp [aeval_prod_apply, hT, q, prod_eq_zero (mem_univ i)]
  let ev (i : Fin n) : R →ₐ[K] Z × K := liftₐ (span {q}) (aeval (T, a i)) (h_vanish i)
  have hev (i : Fin n) : ev i ξ = (T, a i) := aeval_X (T, a i)
  -- `L i` multiplies `ev i r` by `(S, -α i)` and adds the two components in `Z`.
  let L (i : Fin n) : R →ₗ[K] Z :=
    LinearMap.coprod LinearMap.id (Algebra.linearMap K Z) ∘ₗ
      LinearMap.mulLeft K (S, -α i) ∘ₗ (ev i).toLinearMap
  have hL (i : Fin n) (k : ℕ) : L i (ξ ^ k) = S * T ^ k - algebraMap K Z (α i * a i ^ k) := by
    simp [L, hev, sub_eq_add_neg]
  -- The product of the `L i` sends `y ^ k` to `∏ (S * T ^ k - α i * a i ^ k)`, which is zero for
  -- `k > 0`; in the image of `p(y) = 0` only `p(0) • ∏ (S - α i)` is left.
  have h_image (k : ℕ) : lift (MultilinearMap.mkPiAlgebraFin K n Z) (map L (y ^ k)) =
      aeval (S * T ^ k) (∏ i : Fin n, (X - C (α i * a i ^ k))) := by
    simp_rw [y, ← map_pow]
    simp [hL, ← List.prod_ofFn, map_list_prod, Function.comp_def]
  have h_smul : p.coeff 0 • aeval S (∏ i : Fin n, (X - C (α i))) = 0 := calc
    _ = lift (MultilinearMap.mkPiAlgebraFin K n Z) (map L (aeval y p)) := by
      rw [aeval_eq_sum_range (p := p) y, sum_range_succ']
      simp only [map_add, map_sum, map_smul, h_image, hST _ (Nat.succ_pos _)]
      simp
    _ = 0 := by simp [hp]
  simpa [hp0] using h_smul

/-- Let `g : K →+* A` be a ring map from a field `K`, let `S`, `T` in `A` commute with the image of
`g`, and let `α i`, `a i` in `K` with `a i ≠ 0`. If `∏ (T - g (a i)) = 0`, and
`∏ (S T ^ k - g (α i * a i ^ k)) = 0` for all `k > 0`, then `∏ (S - g (α i)) = 0`. -/
lemma New.GaloisRep.eval₂_prod_eq_zero_of_mul_pow {K A : Type*} {n : ℕ} [Field K] [Ring A]
    {g : K →+* A} {α a : Fin n → K} {S T : A} (hS_comm : ∀ c : K, Commute (g c) S)
    (hT_comm : ∀ c : K, Commute (g c) T) (hT : (∏ i : Fin n, (X - C (a i))).eval₂ g T = 0)
    (ha : ∀ i : Fin n, a i ≠ 0)
    (hST : ∀ k > (0 : ℕ), (∏ i : Fin n, (X - C (α i * a i ^ k))).eval₂ g (S * T ^ k) = 0) :
    (∏ i : Fin n, (X - C (α i))).eval₂ g S = 0 := by
  -- The centralizer `Z` of the image of `g` contains `S` and `T`. It is a `K`-algebra, in which
  -- `eval₂ g` is `aeval`.
  let Z : Subring A := Subring.centralizer (Set.range g)
  let S' : Z := ⟨S, Subring.mem_centralizer_iff.2 (Set.forall_mem_range.2 hS_comm)⟩
  let T' : Z := ⟨T, Subring.mem_centralizer_iff.2 (Set.forall_mem_range.2 hT_comm)⟩
  have h_mem (x : K) : g x ∈ Z := by
    simp +contextual [Z, Subring.mem_centralizer_iff, ← map_mul, mul_comm]
  let : Algebra K Z := (g.codRestrict Z h_mem).toAlgebra' fun c x ↦
    Subtype.ext (Subring.mem_centralizer_iff.1 x.2 (g c) (Set.mem_range_self c))
  have h_eval (P : K[X]) (x : Z) : eval₂ g x P = 0 ↔ aeval x P = 0 := by
    have h_coe : (aeval x P : A) = eval₂ g x P := hom_eval₂ P _ Z.subtype x
    rw [← h_coe, ZeroMemClass.coe_eq_zero]
  exact (h_eval _ S').2 <| aeval_prod_eq_zero_of_mul_pow S' T' ((h_eval _ T').1 hT) ha
    fun k hk ↦ (h_eval _ (S' * T' ^ k)).1 (hST k hk)

end PositiveDegreeDescent
