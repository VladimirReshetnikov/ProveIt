import New.Derivatives.Field.ChosenPlaces

/-!
# Tight frames in `𝔞₀`

A tight frame of length `h` is a finite family of vectors `y` of the lattice `𝔞₀`, counted with
multiplicities, such that `∑ y, (y† z) y = h z` for all `z`: a resolution of `h`.

* `New.Parameters.exists_isTightFrame_coprime`: a tight frame in `𝔞₀` of a length `h` prime to `q₁`,
  namely `New.Parameters.dualResolutionFactor`.
* `New.Parameters.exists_isTightFrame_of_coprime`: this frame and the powers of `ζ` give tight
  frames of every length `m ≥ q₁ h + R (q₁ + h)` with multiplicities at least `R`.
* `New.Data.exists_short_isTightFrame_coprime`: the length `h` is at most the weight `b`, and the
  two frames contain a vector `y` with `HasUnitLinearForm`.
* `New.Data.exists_isTightFrame`: a tight frame of length `p₀ p₁ = D.M` with large multiplicities,
  where `p₀` and `p₁` are the two primes `D.levelPrime 0` and `D.levelPrime 1` of the data.

The powers of `ζ` are a tight frame of length `q₁`. The frame of length `h` comes from the powers of
`ζ⁻¹` and the orbits `ζ ^ k * τ(e i)` of a multiple `e i` in `𝔞₀` of their dual basis for the
Hermitian form `y'† y`, by replacing some pairs of members by their sums; the cross terms add
`β ^ j + conj β ^ j` to the length, which makes it prime to `q₁`.

Notions from other files:
* `P.E s` is the field `E = K(ζ)`, where `K = ℚ(√-d)` and `ζ = P.ζ s` is a primitive root of unity
  of order `q₁ = P.q₁ s = P.q₀ * towerDeg s`; here `q₀ = P.q₀` is the fixed modulus of the
  parameters and `towerDeg s = 3 ^ (log₃ s + 5) * 2 ^ s`. `P.zetaInt s` is `ζ` as an element of
  `𝓞 E`. For admissible data `D` the exponent `s` is `D.towerExp`, so that `D.E = P.E D.towerExp`.
* `P.Φ s` is the set of infinite places of `E`, a group isomorphic to `Gal(E/K)` by
  `P.galOfPlace s`; `Φ τ` is the complex embedding of `E` chosen at the infinite place `τ`.
* `finiteImage id y ∈ Ô E` says that `y` lies in the lattice `𝔞₀ = E ∩ α Ô`, where `α` is the idele
  of the Weil data and `Ô` is the ring of integral finite adeles.
* `P.periodFactor s` is a complex number; by `norm_iota_periodFactor` its absolute value at an
  embedding `ιₚ : ℂ →+* ℂ_[p]` is given by the idele `α`.
* `β = (1 + √-d) / 2` is `quadGen d` in `ℂ`, `QuadField.betaK d` in `𝓞 K` and `P.betaKInE s` in
  `𝓞 E`.

In comments `P'(ζ)` is `P.relDifferentGen s`, the value at `ζ` of the derivative of the cyclotomic
polynomial of order `q₁`; `φ(q₁)` is the totient of `q₁`, `j` is the least integer with
`2 ^ j ≥ q₁`, and `y'† y = ∑ τ, τ(y) conj τ(y')`.
-/

open Polynomial Finset ComplexConjugate NumberField

namespace New

section Families

variable {E I J : Type} [Field E] [CMType E] [WeilData E] [Fintype I] [Fintype J]

/-- The lattice of the `x` with `finiteImage id x = α⁻¹ x` integral at every finite place, that is
`E ∩ α Ô`, is closed under addition. -/
lemma finiteImage_add_mem {x y : E} (hx : finiteImage id x ∈ Ô E) (hy : finiteImage id y ∈ Ô E) :
    finiteImage id (x + y) ∈ Ô E := by
  simpa [finiteImage, mul_add] using add_mem hx hy

/-- The lattice of the `y` with `finiteImage id y = α⁻¹ y` integral at every finite place, that is
`E ∩ α Ô`, is closed under multiplication by integers of `E`. -/
lemma finiteImage_mul_mem (a : 𝓞 E) {y : E} (hy : finiteImage id y ∈ Ô E) :
    finiteImage id (a * y) ∈ Ô E := by
  simpa [finiteImage, mul_left_comm] using mul_mem (algebraMap_mem_Ô.2 a.isIntegral_coe) hy

omit [Fintype I] in
/-- A finite sum of products `z i * conj (z i)` equals the real number `r` if and only if `r` is the
sum of the squared norms. -/
lemma sum_mul_conj_eq_ofReal_iff (t : Finset I) (z : I → ℂ) (r : ℝ) :
    ∑ i ∈ t, z i * conj (z i) = r ↔ r = ∑ i ∈ t, ‖z i‖ ^ 2 := by
  simp [Complex.mul_conj', ← Complex.ofReal_inj, eq_comm]

/-- The disjoint union of a tight frame `w` with multiplicities `m` and frame bound `M` and a tight
frame `w'` with multiplicities `m'` and frame bound `M'` is a tight frame with frame bound `M + M'`.
This disjoint union is the family `Sum.elim w w'` with multiplicities `Sum.elim m m'`. -/
lemma IsTightFrame.sumElim {w : I → E} {w' : J → E} {m : I → ℕ} {m' : J → ℕ} {M M' : ℕ}
    (hw : IsTightFrame w m M) (hw' : IsTightFrame w' m' M') :
    IsTightFrame (Sum.elim w w') (Sum.elim m m') (M + M') := by
  refine ⟨Sum.forall.2 ⟨hw.finiteImage_mem, hw'.finiteImage_mem⟩, fun σ τ ↦ ?_⟩
  simp [Fintype.sum_sum_type, hw.sum_mul_conj, hw'.sum_mul_conj, ite_add_ite]

/-- The disjoint union of finitely many tight frames `v i` of lengths `L i`, all with multiplicities
`1`, is a tight frame of length `∑ i, L i`. -/
lemma IsTightFrame.join_family {v : I → J → E} {L : I → ℕ}
    (hv : ∀ i : I, IsTightFrame (v i) 1 (L i)) :
    IsTightFrame (fun x : I × J ↦ v x.1 x.2) 1 (∑ i : I, L i) := by
  refine ⟨fun ⟨i, j⟩ ↦ (hv i).finiteImage_mem j, fun σ τ ↦ ?_⟩
  have h_sum (i : I) : ∑ j, Φ σ (v i j) * conj (Φ τ (v i j)) = if σ = τ then ↑(L i) else 0 := by
    simpa using (hv i).sum_mul_conj σ τ
  simp [Fintype.sum_prod_type, h_sum]

/-- Let `w` be a tight frame of length `M` with multiplicities `1`, meaning each member is taken
once. Let `pair` select disjoint pairs of members, indexed by `J`. Suppose the cross terms of all
pairs add up to `t` times the identity matrix for an integer `t`. Then `M + t` is a natural number
`L`, and the unpaired members together with the sums of the pairs are a tight frame of length
`L`. -/
lemma IsTightFrame.replace_pairs {w : I → E} {M : ℕ} [DecidableEq I] (hw : IsTightFrame w 1 M)
    (pair : J ⊕ J ↪ I) {t : ℤ}
    (h_cross : ∀ σ τ : InfinitePlace E,
      ∑ j : J, Φ σ (w (pair (.inl j))) * conj (Φ τ (w (pair (.inr j)))) +
        ∑ j : J, Φ σ (w (pair (.inr j))) * conj (Φ τ (w (pair (.inl j)))) =
          if σ = τ then (t : ℂ) else 0) :
    ∃ L : ℕ, (L : ℤ) = M + t ∧
      IsTightFrame (Sum.elim (fun i : ↥(univ.map pair)ᶜ ↦ w i)
        fun j : J ↦ w (pair (.inl j)) + w (pair (.inr j))) 1 L := by
  set v : ↥(univ.map pair)ᶜ ⊕ J → E :=
    Sum.elim (fun i ↦ w i) fun j : J ↦ w (pair (.inl j)) + w (pair (.inr j)) with hv
  have h_sum (σ τ : InfinitePlace E) :
      ∑ x, Φ σ (v x) * conj (Φ τ (v x)) = if σ = τ then ((M + t : ℤ) : ℂ) else 0 := by
    let g (i : I) : ℂ := Φ σ (w i) * conj (Φ τ (w i))
    have h_old : ∑ i, g i = if σ = τ then (M : ℂ) else 0 := by simpa using hw.sum_mul_conj σ τ
    calc ∑ x, Φ σ (v x) * conj (Φ τ (v x)) = ∑ i, g i + if σ = τ then (t : ℂ) else 0 := by
          rw [← h_cross, ← sum_compl_add_sum (univ.map pair) g, ← sum_coe_sort (univ.map pair)ᶜ]
          simp only [hv, g, sum_map, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, map_add,
            add_mul, mul_add, sum_add_distrib]
          ring
      _ = _ := by rw [h_old]; split_ifs <;> simp
  -- A diagonal entry is a sum of squared absolute values.
  have h_nonneg : 0 ≤ M + t := by
    obtain ⟨σ⟩ : Nonempty (InfinitePlace E) := inferInstance
    have h_real : ((M + t : ℤ) : ℝ) = ∑ x, ‖Φ σ (v x)‖ ^ 2 :=
      (sum_mul_conj_eq_ofReal_iff univ (fun x ↦ Φ σ (v x)) _).1 (by simpa using h_sum σ σ)
    have h_cast_nonneg : (0 : ℝ) ≤ (M + t : ℤ) := by
      rw [h_real]
      positivity
    exact_mod_cast h_cast_nonneg
  lift (M : ℤ) + t to ℕ using h_nonneg with L hL
  refine ⟨L, rfl, Sum.forall.2 ⟨fun i ↦ hw.finiteImage_mem i, fun j ↦ ?_⟩, fun σ τ ↦ ?_⟩
  · exact finiteImage_add_mem (hw.finiteImage_mem _) (hw.finiteImage_mem _)
  · simpa using h_sum σ τ

end Families

/-- Let `d` be a prime with `d ≡ 7 mod 8`. An element of `K = ℚ(√-d)` fixed by complex conjugation
is rational. -/
lemma QuadField.exists_algebraMap_eq_of_star_eq {d : ℕ} [PrimeSevenModEight d] {a : QuadField d}
    (ha : star a = a) : ∃ q : ℚ, algebraMap ℚ (QuadField d) q = a := by
  -- The maximal real subfield of the quadratic field `K` does not contain `√-d`, so it is `ℚ`.
  let R : IntermediateField ℚ (QuadField d) :=
    (maximalRealSubfield (QuadField d)).toIntermediateField (by simp)
  have h_mem {x : QuadField d} : x ∈ R ↔ star x = x := mem_maximalRealSubfield_iff_star_eq
  have h_prime : (Module.finrank ℚ (QuadField d)).Prime := by
    simp [QuadField.finrank_eq_two, Nat.prime_two]
  have h_sqrt : QuadField.sqrtNegD d ∉ R := by
    simp [h_mem, neg_eq_self, Subtype.ext_iff, NeZero.ne]
  rcases (IntermediateField.isSimpleOrder_of_finrank_prime ℚ (QuadField d) h_prime).eq_bot_or_eq_top
    R with h_bot | h_top
  · exact IntermediateField.mem_bot.1 (h_bot.le (h_mem.2 ha))
  · exact absurd (h_top.ge IntermediateField.mem_top) h_sqrt

/-- Let `d` be a prime with `d ≡ 7 mod 8`. If a complex number `z` lies in `quadInt d`, the ring of
integers of `K = ℚ(√-d)` as a subring of `ℂ`, and is real, then `z` is a rational integer. -/
lemma exists_eq_intCast_of_mem_quadInt_of_conj_eq {d : ℕ} [PrimeSevenModEight d] {z : ℂ}
    (hz : z ∈ quadInt d) (h_real : conj z = z) : ∃ n : ℤ, z = n := by
  obtain ⟨a, rfl⟩ : ∃ a : 𝓞 (QuadField d), ((a : QuadField d) : ℂ) = z := RingHom.mem_range.1 hz
  have ha_real : star (a : QuadField d) = a :=
    Subtype.ext ((QuadField.coe_star_eq_conj d a).trans h_real)
  obtain ⟨q, hq⟩ : ∃ q : ℚ, algebraMap ℚ (QuadField d) q = a :=
    QuadField.exists_algebraMap_eq_of_star_eq ha_real
  have h_int : IsIntegral ℤ q := by
    rw [← isIntegral_algebraMap_iff (B := QuadField d), hq]
    exact a.isIntegral_coe
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, algebraMap ℤ ℚ n = q :=
    IsIntegrallyClosed.algebraMap_eq_of_integral h_int
  exact ⟨n, by simp [← hq]⟩

namespace Parameters

variable {P : Parameters} {s : ℕ}

open scoped Classical in
/-- An element `y` of `E` lies in the lattice `𝔞₀`, that is `finiteImage id y ∈ Ô E`, if and only if
`relDifferentGen * y` is integral at the finite places dividing `betaKInE = (1 + √-d) / 2` and `y`
is integral at the other finite places. Here `relDifferentGen` generates the different of `E/K`. -/
lemma finiteImage_mem_iff {y : P.E s} :
    finiteImage id y ∈ Ô (P.E s) ↔
      ∀ w : FinPlace (P.E s), w.valuation (P.E s)
        ((if P.betaKInE s ∈ w.asIdeal then (P.relDifferentGen s : P.E s) else 1) * y) ≤ 1 := by
  refine mem_Ô.trans (forall_congr' fun w ↦ ?_)
  by_cases hw : P.betaKInE s ∈ w.asIdeal <;> simp [finiteImage, WeilData.α, α, hw]

/-- For the automorphism `galOfPlace τ` of `E/K` named by the infinite place `τ`, the valuation of
`τ(y)` at the finite place `w` is the valuation of `y` at `τ • w`, the preimage of `w` under `τ`. -/
lemma valuation_galOfPlace (τ : P.Φ s) (w : FinPlace (P.E s)) (y : P.E s) :
    w.valuation (P.E s) (P.galOfPlace s τ y) = (τ • w).valuation (P.E s) y := by
  let g : P.E s →+* P.E s := P.galOfPlace s τ
  have h_place : w.comap g = τ • w := rfl
  rw [← v_algebraMap_eq_valuation, ← v_algebraMap_eq_valuation,
    ← v_locMap_eq_of_surjective g h_place (P.galOfPlace s τ).surjective, locMap_algebraMap,
    RingHom.coe_coe]

/-- Let `P` be the parameters, `s` a natural number and `E = P.E s = K(ζ)`. The lattice
`𝔞₀ = E ∩ α Ô` of the `y` with `finiteImage id y = α⁻¹ y` integral at every finite place, `α` being
the idele of the Weil data, is stable under the automorphism `galOfPlace τ` of `E/K` named by any
infinite place `τ`. -/
lemma finiteImage_galOfPlace_mem (τ : P.Φ s) {y : P.E s} (hy : finiteImage id y ∈ Ô (P.E s)) :
    finiteImage id (P.galOfPlace s τ y) ∈ Ô (P.E s) := by
  classical
  -- The condition on `τ(y)` at `w` is the condition on `y` at `τ • w`.
  refine finiteImage_mem_iff.2 fun w ↦ ?_
  have h_fixed : galOfPlaceInt τ (P.betaKInE s) = P.betaKInE s :=
    RingOfIntegers.ext ((P.galOfPlace s τ).commutes _)
  have h_different : w.valuation (P.E s) (P.relDifferentGen s : P.E s) =
      (τ • w).valuation (P.E s) (P.relDifferentGen s : P.E s) := by
    rw [← valuation_galOfPlace, ← coe_galOfPlaceInt,
      valuation_map_relDifferentGen _ (MulAction.injective _)]
  have h_bound : (τ • w).valuation (P.E s)
      ((if P.betaKInE s ∈ w.asIdeal then (P.relDifferentGen s : P.E s) else 1) * y) ≤ 1 := by
    simpa only [mem_asIdeal_smul_iff, h_fixed] using finiteImage_mem_iff.1 hy (τ • w)
  split_ifs at h_bound ⊢ <;> simpa [valuation_galOfPlace, h_different] using h_bound

/-- Every embedding `Φ τ` of the CM type maps `betaKInE` to `quadGen d = (1 + i √d) / 2`. -/
lemma phi_betaKInE (τ : P.Φ s) : Φ τ (P.betaKInE s : P.E s) = quadGen P.d :=
  P.phi_algebraMap s τ _

/-- Take `y` in the lattice `𝔞₀ = E ∩ α Ô`, with `α` the idele of the Weil data and `Ô` the integral
finite adeles; that is, `finiteImage id y = α⁻¹ y` lies in `Ô E`. Then the sum of `‖Φ τ y‖ ^ 2` over
the infinite places `τ` of `E`, with `Φ` the CM type, is a natural number: it is an integer of `K`,
real and nonnegative. -/
lemma exists_natCast_eq_sum_norm_sq {y : P.E s} (hy : finiteImage id y ∈ Ô (P.E s)) :
    ∃ ν : ℕ, (ν : ℝ) = ∑ τ : InfinitePlace (P.E s), ‖Φ τ y‖ ^ 2 := by
  have h_real : conj (∑ τ, Φ τ y * conj (Φ τ y)) = ∑ τ, Φ τ y * conj (Φ τ y) := by
    simp [mul_comm]
  obtain ⟨n, hn⟩ : ∃ n : ℤ, ∑ τ, Φ τ y * conj (Φ τ y) = n :=
    exists_eq_intCast_of_mem_quadInt_of_conj_eq (sum_mul_conj_mem_quadInt hy hy) h_real
  have hn_real : (n : ℝ) = ∑ τ, ‖Φ τ y‖ ^ 2 :=
    (sum_mul_conj_eq_ofReal_iff univ (fun τ ↦ Φ τ y) n).1 (mod_cast hn)
  have hn_nonneg : (0 : ℝ) ≤ n := (sum_nonneg fun τ _ ↦ sq_nonneg _).trans_eq hn_real.symm
  lift n to ℕ using mod_cast hn_nonneg
  exact ⟨n, mod_cast hn_real⟩

/-- The orbit of `y`: the family of the vectors `ζ ^ i * τ(y)`, indexed by the pairs `(i, τ)` with
`0 ≤ i < q₁` and `τ` an infinite place, read as an element of `Gal(E/K)` by `galOfPlace`. -/
noncomputable def orbit (y : P.E s) (x : Fin (P.q₁ s) × P.Φ s) : P.E s :=
  P.ζ s ^ x.1.val * P.galOfPlace s x.2 y

/-- Let `y` lie in the lattice `𝔞₀ = E ∩ α Ô`, that is `finiteImage id y ∈ Ô E`, and let the natural
number `ν` be the sum of the `|τ(y)| ^ 2` over the CM type. Then the vectors `w = ζ ^ i * ρ(y)` with
`i < q₁` and `ρ` in `Gal(E/K)`, each taken once, are a tight frame of length `q₁ ν`: they lie in
`𝔞₀` and satisfy `∑ w, σ(w) conj (τ(w)) = q₁ ν δ(σ, τ)` for `σ`, `τ` in the CM type. -/
lemma isTightFrame_orbit {y : P.E s} (hy : finiteImage id y ∈ Ô (P.E s)) {ν : ℕ}
    (hν : (ν : ℝ) = ∑ τ : InfinitePlace (P.E s), ‖Φ τ y‖ ^ 2) :
    IsTightFrame (orbit y) 1 (P.q₁ s * ν) := by
  refine ⟨fun ⟨i, ρ⟩ ↦ ?_, fun σ τ ↦ ?_⟩
  · change finiteImage id ((P.zetaInt s ^ i.val : 𝓞 (P.E s)) * P.galOfPlace s ρ y) ∈ Ô (P.E s)
    exact finiteImage_mul_mem _ (finiteImage_galOfPlace_mem ρ hy)
  -- The sum over `i` leaves a diagonal matrix, by the orthogonality of the powers of `ζ`.
  obtain ⟨-, h_pow⟩ : IsTightFrame (fun i : Fin (P.q₁ s) ↦ P.ζ s ^ i.val) 1 (P.q₁ s) :=
    isTightFrame_pow isPrimitiveRoot_zeta
  have h_split : ∑ x, Φ σ (orbit y x) * conj (Φ τ (orbit y x)) =
      (if σ = τ then (P.q₁ s : ℂ) else 0) * ∑ ρ, Φ (σ * ρ) y * conj (Φ (τ * ρ) y) := by
    rw [← h_pow σ τ, sum_mul_sum, Fintype.sum_prod_type]
    simp only [orbit, map_mul, ← phi_mul, Pi.one_apply, Nat.cast_one, one_mul, mul_mul_mul_comm]
  have h_diag : ∑ ρ, Φ (τ * ρ) y * conj (Φ (τ * ρ) y) = ν :=
    calc ∑ ρ, Φ (τ * ρ) y * conj (Φ (τ * ρ) y)
        = ∑ ρ, Φ ρ y * conj (Φ ρ y) :=
          Equiv.sum_comp (Equiv.mulLeft τ) fun ρ ↦ Φ ρ y * conj (Φ ρ y)
      _ = ν := mod_cast (sum_mul_conj_eq_ofReal_iff univ (fun ρ ↦ Φ ρ y) ν).2 hν
  simp only [Pi.one_apply, Nat.cast_one, one_mul, h_split]
  split_ifs with h
  · rw [h, h_diag, Nat.cast_mul (P.q₁ s)]
  · rw [zero_mul]

/-- The least integer `j` with `2 ^ j ≥ q₁`. -/
abbrev ceilLogQ₁ (P : Parameters) (s : ℕ) : ℕ := Nat.clog 2 (P.q₁ s)

/-- The quotient of the cyclotomic polynomial of order `q₁` by `X - ζ`, over the integers of `E`. -/
noncomputable def cyclotomicQuotient (P : Parameters) (s : ℕ) : (𝓞 (P.E s))[X] :=
  cyclotomic (P.q₁ s) (𝓞 (P.E s)) /ₘ (X - C (P.zetaInt s))

/-- The vector `e i`: the `i`-th coefficient of `cyclotomicQuotient`, divided by the value
`relDifferentGen` at `ζ` of the derivative of the cyclotomic polynomial and multiplied by
`conj β ^ j`, where `β = betaKInE = (1 + √-d) / 2` and `j = ceilLogQ₁`. Without `conj β ^ j`
these are, for `i < φ(q₁)`, the basis of `E/K` dual to the powers of `ζ` under the trace
(`trace_coeff_cyclotomicQuotient_div_mul_pow`). -/
noncomputable def dualVector (P : Parameters) (s i : ℕ) : P.E s :=
  star (P.betaKInE s : P.E s) ^ P.ceilLogQ₁ s * (P.cyclotomicQuotient s).coeff i /
    P.relDifferentGen s

/-- `X - ζ`, with `ζ = P.zetaInt s` the primitive root of unity of order `q₁` in `𝓞 E`, times
`cyclotomicQuotient` is the cyclotomic polynomial of order `q₁`. -/
lemma X_sub_C_mul_cyclotomicQuotient :
    (X - C (P.zetaInt s)) * P.cyclotomicQuotient s = cyclotomic (P.q₁ s) (𝓞 (P.E s)) :=
  mul_divByMonic_eq_iff_isRoot.2 (isPrimitiveRoot_zetaInt.isRoot_cyclotomic (NeZero.pos _))

lemma natDegree_cyclotomicQuotient :
    (P.cyclotomicQuotient s).natDegree = (P.q₁ s).totient - 1 := by
  simp [cyclotomicQuotient, natDegree_divByMonic _ (monic_X_sub_C _), natDegree_cyclotomic]

lemma monic_cyclotomicQuotient : (P.cyclotomicQuotient s).Monic := by
  refine (monic_X_sub_C (P.zetaInt s)).of_mul_monic_left ?_
  simpa [X_sub_C_mul_cyclotomicQuotient] using cyclotomic.monic (P.q₁ s) (𝓞 (P.E s))

/-- Euler's formula. Let `b i` for `i < φ(q₁)` be the coefficients of `cyclotomicQuotient`, the
quotient over `𝓞 E` of the cyclotomic polynomial of order `q₁` by `X - ζ`, and let
`P'(ζ) = relDifferentGen` be the value at `ζ` of the derivative of the cyclotomic polynomial. The
elements `b i / P'(ζ)` are the basis of `E/K` dual to the powers `ζ ^ k` for the trace form. -/
lemma trace_coeff_cyclotomicQuotient_div_mul_pow (i k : Fin (P.q₁ s).totient) :
    Algebra.trace P.K (P.E s)
        ((P.cyclotomicQuotient s).coeff i / P.relDifferentGen s * P.ζ s ^ k.val) =
      if k = i then 1 else 0 := by
  -- The cyclotomic polynomial of order `q₁` is the minimal polynomial of `ζ` over `K`.
  let pb : PowerBasis P.K (P.E s) := isPrimitiveRoot_zeta.powerBasis P.K
  have h_gen : pb.gen = P.ζ s := isPrimitiveRoot_zeta.powerBasis_gen P.K
  have h_minpoly : minpoly P.K pb.gen = cyclotomic (P.q₁ s) P.K := by
    rw [h_gen, ← isPrimitiveRoot_zeta.minpoly_eq_cyclotomic_of_irreducible
      (P.irreducible_cyclotomic s)]
  have h_dim : (P.q₁ s).totient = pb.dim := by
    rw [← pb.natDegree_minpoly, h_minpoly, natDegree_cyclotomic]
  have h_quotient : minpolyDiv P.K pb.gen =
      (P.cyclotomicQuotient s).map (algebraMap (𝓞 (P.E s)) (P.E s)) := by
    rw [minpolyDiv, h_minpoly, cyclotomicQuotient, map_divByMonic _ (monic_X_sub_C _)]
    simp [h_gen]
  have h_deriv : aeval pb.gen (derivative (minpoly P.K pb.gen)) = P.relDifferentGen s := by
    rw [h_minpoly, aeval_def, eval₂_eq_eval_map, ← derivative_map]
    simp [h_gen, relDifferentGen, ← eval_map_apply, ← derivative_map]
  have h_dual : pb.basis.traceDual (i.cast h_dim) =
      (P.cyclotomicQuotient s).coeff i / P.relDifferentGen s := by
    simp [Module.Basis.traceDual_powerBasis_eq, h_quotient, h_deriv]
  simpa [h_dual, h_gen] using pb.basis.trace_traceDual_mul (i.cast h_dim) (k.cast h_dim)

/-- The vectors `e i = dualVector i` are `conj β ^ j` times the basis of `E/K` dual to the powers of
`ζ` under the trace. For `σ`, `τ` in `P.Φ s`, the infinite places of `E`, the sum of
`σ(e i) * conj τ(ζ ^ (-i))` over `i < φ(q₁)` is `conj β ^ j` for `σ = τ` and `0` otherwise. -/
lemma sum_dualVector_mul_conj (σ τ : P.Φ s) :
    ∑ i : Fin (P.q₁ s).totient, Φ σ (P.dualVector s i) * conj (Φ τ ((P.ζ s)⁻¹ ^ i.val)) =
      if σ = τ then conj (quadGen P.d) ^ P.ceilLogQ₁ s else 0 := by
  -- By Euler's formula the square matrices of the conjugates of the two dual bases have
  -- product `1` in one order, hence also in the other.
  let A : Matrix (Fin (P.q₁ s).totient) (P.Φ s) ℂ :=
    .of fun i ρ ↦ Φ ρ ((P.cyclotomicQuotient s).coeff i / P.relDifferentGen s : P.E s)
  let B : Matrix (P.Φ s) (Fin (P.q₁ s).totient) ℂ := .of fun ρ k ↦ Φ ρ (P.ζ s ^ k.val)
  have h_dual : A * B = 1 := by
    ext i k
    simp only [A, B, Matrix.mul_apply, Matrix.of_apply, ← map_mul, ← coe_trace_eq_sum,
      trace_coeff_cyclotomicQuotient_div_mul_pow, Matrix.one_apply, eq_comm (a := i)]
    split_ifs <;> simp
  have h_card : Fintype.card (Fin (P.q₁ s).totient) = Fintype.card (P.Φ s) := by
    rw [Fintype.card_fin, ← IsCyclotomicExtension.finrank (P.E s) (P.irreducible_cyclotomic s),
      ← IsGalois.card_aut_eq_finrank, ← Nat.card_congr (P.galOfPlace s).toEquiv,
      Nat.card_eq_fintype_card]
  have h_swap : B * A = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ ℂ h_card).1 h_dual
  calc ∑ i : Fin (P.q₁ s).totient, Φ σ (P.dualVector s i) * conj (Φ τ ((P.ζ s)⁻¹ ^ i.val))
      = conj (quadGen P.d) ^ P.ceilLogQ₁ s * (B * A) τ σ := by
        simp only [A, B, Matrix.mul_apply, mul_sum, Matrix.of_apply, dualVector, ← star_zeta,
          map_mul,
          map_div₀, map_pow, map_star_complex, phi_betaKInE, starRingEnd_apply, star_star]
        exact sum_congr rfl fun i _ ↦ by ring
    _ = _ := by simp [h_swap, Matrix.one_apply, eq_comm]

/-- The conjugate transpose of `sum_dualVector_mul_conj`. For the vectors `e i = dualVector i`, the
sum of `σ(ζ ^ (-i)) * conj τ(e i)` over `i < φ(q₁)` is `β ^ j` for `σ = τ` and `0` otherwise. -/
lemma sum_mul_conj_dualVector (σ τ : P.Φ s) :
    ∑ i : Fin (P.q₁ s).totient, Φ σ ((P.ζ s)⁻¹ ^ i.val) * conj (Φ τ (P.dualVector s i)) =
      if σ = τ then quadGen P.d ^ P.ceilLogQ₁ s else 0 := by
  simpa [mul_comm, apply_ite conj, eq_comm (a := τ)] using
    congrArg conj (sum_dualVector_mul_conj τ σ)

/-- `q₁` divides `((d + 1) / 4) ^ j = (β conj β) ^ j`, where `β = (1 + √-d) / 2` and
`j = ceilLogQ₁` is the least integer with `2 ^ j ≥ q₁`. -/
lemma q₁_dvd_pow_ceilLogQ₁ : P.q₁ s ∣ ((P.d + 1) / 4) ^ P.ceilLogQ₁ s := by
  -- Every prime of `q₁` divides `(d + 1) / 4` and has exponent at most `j` in `q₁`.
  refine (Nat.dvd_iff_prime_pow_dvd_dvd _ _).2 fun p k hp h_dvd ↦ ?_
  obtain rfl | hk_pos := k.eq_zero_or_pos
  · exact one_dvd _
  have hk_le : k ≤ P.ceilLogQ₁ s := (Nat.pow_le_pow_iff_right one_lt_two).1 <|
    calc 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
      _ ≤ P.q₁ s := Nat.le_of_dvd (NeZero.pos _) h_dvd
      _ ≤ 2 ^ P.ceilLogQ₁ s := Nat.le_pow_clog one_lt_two _
  exact pow_dvd_pow_of_dvd_of_le
    (P.dvd_d_add_one_div_four_of_dvd_q₁ hp ((dvd_pow_self p hk_pos.ne').trans h_dvd)) hk_le

/-- Let `β = betaKInE = (1 + √-d) / 2`, let `P'(ζ) = relDifferentGen` be the value at `ζ` of the
derivative of the cyclotomic polynomial of order `q₁`, and let `j = ceilLogQ₁` be the least integer
with `2 ^ j ≥ q₁`. The vector `e i = dualVector i` is `conj β ^ j a / P'(ζ)`, where `a` is the
`i`-th coefficient of the quotient of that polynomial by `X - ζ`. It lies in the lattice
`𝔞₀ = E ∩ α Ô`. -/
lemma finiteImage_dualVector_mem (i : ℕ) : finiteImage id (P.dualVector s i) ∈ Ô (P.E s) := by
  refine finiteImage_mem_iff.2 fun w ↦ ?_
  set j : ℕ := P.ceilLogQ₁ s
  set a : 𝓞 (P.E s) := (P.cyclotomicQuotient s).coeff i
  split_ifs with hw
  · -- At the places dividing `β = betaKInE` the factor `relDifferentGen` clears the denominator.
    have h_clear :
        P.relDifferentGen s * P.dualVector s i = (star (P.betaKInE s) ^ j * a : 𝓞 (P.E s)) := by
      rw [dualVector, mul_div_cancel₀ _ (P.relDifferentGen_ne_zero s), ← coe_star_ringOfIntegers]
      norm_cast
    rw [h_clear]
    exact w.valuation_le_one _
  · -- Elsewhere `β` is a unit, and `relDifferentGen` divides `q₁`, which divides `(β conj β) ^ j`.
    obtain ⟨b, hb⟩ : P.relDifferentGen s ∣ P.betaKInE s ^ j * star (P.betaKInE s) ^ j := by
      rw [← mul_pow, star_betaKInE, betaKInE_mul_one_sub, ← Nat.cast_pow]
      exact relDifferentGen_dvd_q₁.trans (Nat.cast_dvd_cast q₁_dvd_pow_ceilLogQ₁)
    have h_clear : (P.betaKInE s : P.E s) ^ j * P.dualVector s i = (b * a : 𝓞 (P.E s)) := by
      rw [dualVector, ← mul_div_assoc, div_eq_iff (P.relDifferentGen_ne_zero s)]
      exact_mod_cast (by linear_combination a * hb :
        P.betaKInE s ^ j * (star (P.betaKInE s) ^ j * a) = b * a * P.relDifferentGen s)
    have h_unit : w.valuation (P.E s) (P.betaKInE s : P.E s) = 1 :=
      w.valuation_eq_one_iff_notMem.2 hw
    simpa [h_unit] using (congrArg (w.valuation (P.E s)) h_clear).trans_le
      (w.valuation_le_one (b * a))

/-- Let `P` be the parameters, with prime `d = P.d`, and `s` a natural number. Let
`β = (1 + √-d) / 2` (`quadGen P.d`) and `j ≠ 0`. An integer `t` that is equal to
`β ^ j + conj β ^ j` is prime to `q₁ = P.q₁ s`, the order of the root of unity `ζ` with `E = K(ζ)`
and `K = ℚ(√-d)`. -/
lemma isCoprime_of_pow_add_conj_pow_eq {t : ℤ} {j : ℕ} (hj : j ≠ 0)
    (ht : quadGen P.d ^ j + conj (quadGen P.d) ^ j = t) : IsCoprime t (P.q₁ s) := by
  refine Int.isCoprime_iff_gcd_eq_one.2 (Nat.coprime_of_dvd fun p hp hpt hpq₁ ↦ ?_)
  -- The same equation in `𝓞 K`, where `β` is `betaK` and `conj β = 1 - β`.
  have ht_int : QuadField.betaK P.d ^ j + (1 - QuadField.betaK P.d) ^ j = t := by
    rw [← QuadField.star_betaK]
    refine RingOfIntegers.ext (Subtype.ext ?_)
    push_cast
    rwa [QuadField.coe_star_eq_conj]
  -- As `p` divides `q₁`, it divides `β conj β`. So modulo a prime of `K` above `p`, one of `β`,
  -- `1 - β` is `0` and the other is `1`.
  obtain ⟨𝔭, h𝔭, hp𝔭⟩ : ∃ 𝔭 : Ideal (𝓞 P.K), 𝔭.IsMaximal ∧ algebraMap ℤ (𝓞 P.K) p ∈ 𝔭 := by
    refine exists_max_ideal_of_mem_nonunits ?_
    rw [mem_nonunits_iff, isUnit_map_iff, Int.isUnit_iff_natAbs_eq]
    exact hp.ne_one
  have h_prod : QuadField.betaK P.d * (1 - QuadField.betaK P.d) ∈ 𝔭 := by
    rw [QuadField.betaK_mul_one_sub]
    exact 𝔭.mem_of_dvd (Nat.cast_dvd_cast (P.dvd_d_add_one_div_four_of_dvd_q₁ hp hpq₁)) hp𝔭
  have h_one : Ideal.Quotient.mk 𝔭 t = 1 := by
    rw [← ht_int]
    rcases h𝔭.isPrime.mem_or_mem h_prod with h_mem | h_mem
    · simp [Ideal.Quotient.eq_zero_iff_mem.2 h_mem, hj]
    · simp [← Ideal.Quotient.eq.2 h_mem, hj]
  have h_dvd : (p : 𝓞 P.K) ∣ t := mod_cast Int.cast_dvd_cast _ _ (Int.natCast_dvd.2 hpt)
  simp [Ideal.Quotient.eq_zero_iff_mem.2 (𝔭.mem_of_dvd h_dvd hp𝔭)] at h_one

lemma exists_pow_add_conj_pow_eq_intCast (j : ℕ) :
    ∃ t : ℤ, quadGen P.d ^ j + conj (quadGen P.d) ^ j = t :=
  exists_eq_intCast_of_mem_quadInt_of_conj_eq (add_mem (pow_mem CMLattice.quadGen_mem_quadInt j)
    (pow_mem (conj_mem_quadInt CMLattice.quadGen_mem_quadInt) j)) (by simp [add_comm])

lemma one_lt_q₁ : 1 < P.q₁ s :=
  (Nat.one_lt_two_pow s.succ_ne_zero).trans_le (Nat.le_of_dvd (NeZero.pos _) two_pow_dvd_q₁)

/-- The complex number `q₁ (1 + ∑ (e i)† (e i)) + β ^ j + conj β ^ j`. Here `e i` is `dualVector`,
for `i` below `φ(q₁)`, `y† y = ∑ |τ(y)| ^ 2` is a sum over the CM type, `β = (1 + √-d) / 2` is
`quadGen` and `j` is `ceilLogQ₁`. It is a natural number, the length of the tight frame of
`exists_isTightFrame_coprime`. -/
noncomputable def dualResolutionFactor (P : Parameters) (s : ℕ) : ℂ :=
  P.q₁ s * (1 + ∑ i : Fin (P.q₁ s).totient, ∑ τ : P.Φ s, ‖Φ τ (P.dualVector s i)‖ ^ 2 : ℝ) +
    (quadGen P.d ^ P.ceilLogQ₁ s + conj (quadGen P.d) ^ P.ceilLogQ₁ s)

/-- Let the natural number `ν i` be the sum of `|τ(e i)| ^ 2` over the CM type, where `e i` is
`dualVector` and `i < φ(q₁)`. The powers of `ζ⁻¹` together with the orbits `ζ ^ k * τ(e i)` of the
`e i` are a tight frame in the lattice `𝔞₀` of length `q₁ (1 + ∑ ν i)`. -/
lemma isTightFrame_sumElim_inv_pow_orbit {ν : Fin (P.q₁ s).totient → ℕ}
    (hν : ∀ i : Fin (P.q₁ s).totient, (ν i : ℝ) = ∑ τ : P.Φ s, ‖Φ τ (P.dualVector s i)‖ ^ 2) :
    IsTightFrame
      (Sum.elim (fun i : Fin (P.q₁ s) ↦ (P.ζ s)⁻¹ ^ i.val)
        fun x : Fin (P.q₁ s).totient × Fin (P.q₁ s) × P.Φ s ↦ orbit (P.dualVector s x.1) x.2)
      1 (P.q₁ s * (1 + ∑ i : Fin (P.q₁ s).totient, ν i)) := by
  have h_orbit (i : Fin (P.q₁ s).totient) :
      IsTightFrame (orbit (P.dualVector s i)) 1 (P.q₁ s * ν i) :=
    isTightFrame_orbit (finiteImage_dualVector_mem i.val) (hν i)
  simpa only [Sum.elim_one_one, ← mul_sum, mul_one_add] using
    (isTightFrame_pow isPrimitiveRoot_zeta.inv).sumElim (.join_family h_orbit)

/-- Put `f = φ(q₁)` and `β = quadGen d = (1 + √-d) / 2`, and let `j = ceilLogQ₁` be the least
integer with `2 ^ j ≥ q₁`. The vectors `e i = dualVector i`, `i < f`, are `conj β ^ j` times the
basis of `E/K` dual to the powers of `ζ` under the trace. Let the natural number `ν i` be the sum of
`|τ(e i)| ^ 2` over the CM type and let the integer `t` be `β ^ j + conj β ^ j`. There is a tight
frame `v` of length `h = q₁ (1 + ∑ ν i) + t` that contains the vector `ζ e (f - 1)`: the `v i` lie
in the lattice `𝔞₀ = E ∩ α Ô`, with `α` the idele of the Weil data and `Ô` the integral finite
adeles, and `∑ i, σ(v i) conj (τ(v i)) = h δ(σ, τ)` for `σ`, `τ` in the CM type. -/
lemma exists_isTightFrame_factor_eq_add {ν : Fin (P.q₁ s).totient → ℕ}
    (hν : ∀ i : Fin (P.q₁ s).totient, (ν i : ℝ) = ∑ τ : P.Φ s, ‖Φ τ (P.dualVector s i)‖ ^ 2)
    {t : ℤ} (ht : quadGen P.d ^ P.ceilLogQ₁ s + conj (quadGen P.d) ^ P.ceilLogQ₁ s = t) :
    ∃ (h : ℕ) (I : Type) (_ : Fintype I) (v : I → P.E s),
      IsTightFrame v 1 h ∧
      (h : ℤ) = P.q₁ s * (1 + ∑ i : Fin (P.q₁ s).totient, ν i : ℕ) + t ∧
      ∃ i : I, v i = P.ζ s * P.dualVector s ((P.q₁ s).totient - 1) := by
  -- In the frame of `isTightFrame_sumElim_inv_pow_orbit` replace each pair `ζ ^ (-i)`, `e i` by its
  -- sum; the cross terms add `t` to the length.
  let I : Type := Fin (P.q₁ s) ⊕ Fin (P.q₁ s).totient × Fin (P.q₁ s) × P.Φ s
  let v : I → P.E s := Sum.elim (fun i : Fin (P.q₁ s) ↦ (P.ζ s)⁻¹ ^ i.val)
    fun (i, x) ↦ orbit (P.dualVector s i) x
  have hv : IsTightFrame v 1 (P.q₁ s * (1 + ∑ i, ν i)) := isTightFrame_sumElim_inv_pow_orbit hν
  let pair : Fin (P.q₁ s).totient ⊕ Fin (P.q₁ s).totient ↪ I :=
    (Fin.castLEEmb (P.q₁ s).totient_le).sumMap (Function.Embedding.sectL _ (0, 1))
  have h_left (i : Fin (P.q₁ s).totient) : v (pair (.inl i)) = (P.ζ s)⁻¹ ^ i.val := rfl
  have h_right (i : Fin (P.q₁ s).totient) : v (pair (.inr i)) = P.dualVector s i := by
    simp [v, pair, orbit, I]
  obtain ⟨h, h_length, h_frame⟩ : ∃ h : ℕ, (h : ℤ) = (P.q₁ s * (1 + ∑ i, ν i) : ℕ) + t ∧
      IsTightFrame (Sum.elim (fun i : ↥(univ.map pair)ᶜ ↦ v i)
        fun j : Fin (P.q₁ s).totient ↦ v (pair (.inl j)) + v (pair (.inr j))) 1 h :=
    hv.replace_pairs pair fun σ τ ↦ by
      simp only [h_left, h_right, sum_dualVector_mul_conj, sum_mul_conj_dualVector, ← ht]
      split_ifs <;> simp
  -- The member `ζ e (f - 1)` of the orbit of `e (f - 1)` belongs to no pair.
  have hf : (P.q₁ s).totient - 1 < (P.q₁ s).totient :=
    Nat.sub_one_lt (Nat.totient_pos.2 (NeZero.pos _)).ne'
  let i₀ : I := .inr (⟨(P.q₁ s).totient - 1, hf⟩, ⟨1, one_lt_q₁⟩, 1)
  have hi₀_mem : i₀ ∈ (univ.map pair)ᶜ := by simp [pair, i₀, I, Fin.ext_iff]
  have hi₀ : v i₀ = P.ζ s * P.dualVector s ((P.q₁ s).totient - 1) := by simp [v, i₀, orbit]
  exact ⟨h, ↥(univ.map pair)ᶜ ⊕ Fin (P.q₁ s).totient, inferInstance, _, h_frame,
    by rw [h_length, Nat.cast_mul (P.q₁ s)], .inl ⟨i₀, hi₀_mem⟩, hi₀⟩

/-- Let `E = P.E s = K(ζ)`, where `K = ℚ(√-d)` and `ζ = P.ζ s` is a primitive root of unity of order
`q₁ = P.q₁ s`. Put `β = (1 + √-d) / 2` and let `j` be the least integer with `2 ^ j ≥ q₁`. The
vectors `e i = dualVector i`, `i < φ(q₁)`, are `conj β ^ j` times the basis of `E/K` dual to the
powers of `ζ` under the trace. A tight frame of length `h` is a finite family `v` in the lattice
`𝔞₀ = E ∩ α Ô`, with `α` the idele of the Weil data, such that
`∑ i, σ(v i) conj (τ(v i)) = h δ(σ, τ)` on the CM type. There is such a frame whose length `h` is
`dualResolutionFactor = q₁ (1 + ∑ i, ∑ τ, |τ(e i)| ^ 2) + β ^ j + conj β ^ j`, is prime to `q₁`, and
which contains the vector `ζ e (φ(q₁) - 1)`. -/
lemma exists_isTightFrame_coprime (P : Parameters) (s : ℕ) :
    ∃ (h : ℕ) (I : Type) (_ : Fintype I) (v : I → P.E s),
      IsTightFrame v 1 h ∧
      (h : ℂ) = P.dualResolutionFactor s ∧
      h.Coprime (P.q₁ s) ∧
      ∃ i : I, v i = P.ζ s * P.dualVector s ((P.q₁ s).totient - 1) := by
  choose ν hν using show ∀ i : Fin (P.q₁ s).totient,
      ∃ ν : ℕ, (ν : ℝ) = ∑ τ : P.Φ s, ‖Φ τ (P.dualVector s i)‖ ^ 2 from
    fun i ↦ exists_natCast_eq_sum_norm_sq (finiteImage_dualVector_mem i.val)
  obtain ⟨t, ht⟩ : ∃ t : ℤ,
      quadGen P.d ^ P.ceilLogQ₁ s + conj (quadGen P.d) ^ P.ceilLogQ₁ s = t :=
    exists_pow_add_conj_pow_eq_intCast _
  obtain ⟨h, I, _, v, hv, h_length, h_mem⟩ := exists_isTightFrame_factor_eq_add hν ht
  refine ⟨h, I, inferInstance, v, hv, ?_, ?_, h_mem⟩
  · rw [dualResolutionFactor, ht, ← sum_congr rfl fun i _ ↦ hν i]
    exact_mod_cast h_length
  · -- Modulo `q₁` the length `h` is `t`.
    rw [← Nat.isCoprime_iff_coprime, h_length, IsCoprime.mul_add_left_left_iff]
    exact isCoprime_of_pow_add_conj_pow_eq (Nat.clog_pos one_lt_two one_lt_q₁).ne' ht

/-- Let `φ` be a `p`-adic embedding of `E` whose prime `placeOfEmb φ` contains `β = (1 + √-d) / 2`
(`betaKInE`). Then `φ(ζ e (f - 1))` has the absolute value of `1 / φ(P'(ζ))`. Here `f` is the
totient of `q₁`, and `P'(ζ) = relDifferentGen` is the value at `ζ` of the derivative of the `q₁`-th
cyclotomic polynomial. Finally, `e = dualVector` is the trace-dual basis to the powers of `ζ`, times
`conj β ^ ceilLogQ₁`. -/
lemma norm_map_zeta_mul_dualVector {p : ℕ} [Fact p.Prime] {φ : P.E s →+* ℂ_[p]}
    (hβ : P.betaKInE s ∈ (placeOfEmb φ).asIdeal) :
    ‖φ (P.ζ s * P.dualVector s ((P.q₁ s).totient - 1))‖ = 1 / ‖φ (P.relDifferentGen s)‖ := by
  -- The vector is `ζ conj β ^ j / P'(ζ)`, and `conj β = 1 - β` is a unit.
  have h_notMem : star (P.betaKInE s) ∉ (placeOfEmb φ).asIdeal := fun h_mem ↦
    (placeOfEmb φ).isPrime.one_notMem (by simpa [star_betaKInE] using add_mem h_mem hβ)
  have h_conj : ‖φ (star (P.betaKInE s : P.E s))‖ = 1 :=
    (norm_ringOfIntegers_le φ _).eq_of_not_lt (mt (mem_placeOfEmb φ _).2 h_notMem)
  have h_zeta : ‖φ (P.ζ s)‖ = 1 :=
    ((isPrimitiveRoot_zeta.map_of_injective φ.injective).isOfFinOrder (NeZero.ne _)).norm_eq_one
  rw [dualVector, ← natDegree_cyclotomicQuotient, monic_cyclotomicQuotient.coeff_natDegree]
  simp [h_conj, h_zeta]

/-- `periodFactor * conj (Φ τ y)` has absolute value 1 at the embedding `ιₚ : ℂ →+* ℂ_[p]` (the
instance `PadicPlace p`) for all `τ` in the CM type. These numbers are the coefficients of the
linear form `z ↦ periodFactor * ∑ τ, conj (Φ τ y) * Φ τ z`. -/
def HasUnitLinearForm (P : Parameters) (s p : ℕ) [Fact p.Prime] [PadicPlace p] (y : P.E s) :
    Prop :=
  ∀ τ : InfinitePlace (P.E s), ‖(ιₚ (P.periodFactor s * conj (Φ τ y)) : ℂ_[p])‖ = 1

/-- Put `f = φ(q₁)` and `β = (1 + √-d) / 2`, and let `j` be the least integer with `2 ^ j ≥ q₁`. The
vector `e = dualVector (f - 1)` is `conj β ^ j / P'(ζ)`. For every prime `p` and embedding
`ιₚ : ℂ →+* ℂ_[p]`, one of the vectors `y = 1` and `y = ζ e` has the property that
`periodFactor * conj (τ(y))` has absolute value 1 at `ιₚ` for all `τ` in the CM type. -/
lemma exists_hasUnitLinearForm (P : Parameters) (s p : ℕ) [Fact p.Prime] [PadicPlace p] :
    ∃ y : P.E s, (y = 1 ∨ y = P.ζ s * P.dualVector s ((P.q₁ s).totient - 1)) ∧
      P.HasUnitLinearForm s p y := by
  have h_emb (τ : P.Φ s) (y : P.E s) : weightEmbedding ιₚ τ y = ιₚ (conj (Φ τ y)) :=
    congrArg ιₚ (map_star_complex _ y)
  have h_place (τ : P.Φ s) : P.betaKInE s ∈ (placeOfEmb (weightEmbedding ιₚ τ)).asIdeal ↔
      ‖ιₚ (conj (quadGen P.d))‖ < 1 := by
    rw [mem_placeOfEmb, h_emb, phi_betaKInE]
  rcases le_or_gt 1 ‖ιₚ (conj (quadGen P.d))‖ with hβ | hβ
  · -- Here `conj β` is a unit, so `periodFactor` is a unit, and `y = 1`.
    refine ⟨1, .inl rfl, fun τ ↦ ?_⟩
    have h_factor : ‖ιₚ (P.periodFactor s)‖ = 1 := by
      rw [norm_iota_periodFactor τ, adeleExtension_alpha, ite_eq_right (mt (h_place τ).1 hβ.not_gt),
        norm_one, inv_one]
    rw [map_one, map_one, mul_one, h_factor]
  · -- Otherwise the prime of each `weightEmbedding ιₚ τ` contains `β`, and `y = ζ e (f - 1)`.
    refine ⟨P.ζ s * P.dualVector s ((P.q₁ s).totient - 1), .inr rfl, fun τ ↦ ?_⟩
    let φ : P.E s →+* ℂ_[p] := weightEmbedding ιₚ τ
    have hβ_mem : P.betaKInE s ∈ (placeOfEmb φ).asIdeal := (h_place τ).2 hβ
    have h_factor : ‖ιₚ (P.periodFactor s)‖ = ‖φ (P.relDifferentGen s)‖ := by
      rw [norm_iota_periodFactor τ, adeleExtension_alpha, ite_eq_left hβ_mem, norm_inv, inv_inv]
    rw [map_mul, norm_mul, ← h_emb, h_factor, norm_map_zeta_mul_dualVector hβ_mem,
      mul_one_div_cancel (by simp)]

/-- Let `v` be a tight frame with multiplicities 1 of a length `h` prime to `q₁`. For every
`m ≥ q₁ h + R (q₁ + h)`, the powers `ζ ^ i`, `i < q₁`, and the members of `v` form a tight frame of
length `m` with suitable multiplicities, all at least `R`. -/
lemma exists_isTightFrame_of_coprime {h : ℕ} {I : Type} [Fintype I] {v : I → P.E s}
    (hv : IsTightFrame v 1 h) (h_coprime : h.Coprime (P.q₁ s)) {m R : ℕ}
    (h_large : P.q₁ s * h + R * (P.q₁ s + h) ≤ m) :
    ∃ c : Fin (P.q₁ s) ⊕ I → ℕ,
      IsTightFrame (Sum.elim (fun i : Fin (P.q₁ s) ↦ P.ζ s ^ i.val) v) c m ∧
      ∀ j : Fin (P.q₁ s) ⊕ I, R ≤ c j := by
  -- Every integer from `q₁ h` on is a sum of multiples of the coprime numbers `q₁` and `h`.
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, a * P.q₁ s + b * h = m - R * (P.q₁ s + h) :=
    Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le (P.q₁ s) h _
      (by simp [h_coprime.symm.gcd_eq_one])
      ((Nat.mul_le_mul (Nat.pred_le _) (Nat.pred_le _)).trans (Nat.le_sub_of_add_le h_large))
  have h_sum : (a + R) * P.q₁ s + (b + R) * h = m := by lia
  -- Take the powers of `ζ` `a + R` times and the frame `v` `b + R` times.
  have h_pow : IsTightFrame (fun i : Fin (P.q₁ s) ↦ P.ζ s ^ i.val) (fun _ ↦ a + R)
      ((a + R) * P.q₁ s) := by
    simpa using (isTightFrame_pow isPrimitiveRoot_zeta).mul_left (a + R)
  have hv_mul : IsTightFrame v (fun _ ↦ b + R) ((b + R) * h) := by simpa using hv.mul_left (b + R)
  exact ⟨_, by simpa only [h_sum] using h_pow.sumElim hv_mul, by simp⟩

/-- The coefficients of the cyclotomic polynomial of order `q₁ = q₀ * towerDeg s`, where `q₀` is
the fixed modulus of the parameters `P` and `towerDeg s = 3 ^ (log₃ s + 5) * 2 ^ s`, have absolute
value at most `2 ^ q₀`. -/
lemma norm_coeff_cyclotomic_le (j : ℕ) : ‖(cyclotomic (P.q₁ s) ℂ).coeff j‖ ≤ 2 ^ P.q₀ := by
  -- The cyclotomic polynomial of order `q₁` is that of order `q₀` evaluated at `X ^ (q₁ / q₀)`, so
  -- its nonzero coefficients are those of the latter, whose roots have norm 1.
  rw [← expand_towerDeg_cyclotomic, coeff_expand (NeZero.pos _)]
  split_ifs
  · have h_roots : ∀ z ∈ ((cyclotomic P.q₀ ℂ).map (.id ℂ)).roots, ‖z‖ ≤ 1 := fun z hz ↦ by
      rw [map_id, mem_roots (cyclotomic_ne_zero _ _), isRoot_cyclotomic_iff] at hz
      exact (hz.norm'_eq_one (NeZero.ne _)).le
    calc ‖(cyclotomic P.q₀ ℂ).coeff (j / towerDeg s)‖
        ≤ P.q₀.totient.choose (j / towerDeg s) := by
          simpa only [map_id, one_pow, one_mul, natDegree_cyclotomic] using
            coeff_le_of_roots_le (j / towerDeg s) (cyclotomic.monic P.q₀ ℂ)
              (IsAlgClosed.splits _) h_roots
      _ ≤ 2 ^ P.q₀.totient := mod_cast Nat.choose_le_two_pow _ _
      _ ≤ 2 ^ P.q₀ := pow_le_pow_right₀ one_le_two P.q₀.totient_le
  · simp

/-- The coefficients of `cyclotomicQuotient`, the quotient of the cyclotomic polynomial of order
`q₁` by `X - ζ`, have absolute value at most `q₁ 2 ^ q₀` under the embedding `Φ τ : E → ℂ` chosen at
any infinite place `τ`. -/
lemma norm_phi_coeff_cyclotomicQuotient_le (τ : P.Φ s) (i : ℕ) :
    ‖Φ τ ((P.cyclotomicQuotient s).coeff i : P.E s)‖ ≤ P.q₁ s * 2 ^ P.q₀ := by
  -- A coefficient of the quotient is a sum of at most `q₁` coefficients of the cyclotomic
  -- polynomial times roots of unity.
  let φ : 𝓞 (P.E s) →+* ℂ := (Φ τ).comp (algebraMap (𝓞 (P.E s)) (P.E s))
  have h_zeta : ‖φ (P.zetaInt s)‖ = 1 :=
    (isPrimitiveRoot_zeta.map_of_injective (Φ τ).injective).norm'_eq_one (NeZero.ne _)
  calc ‖φ ((P.cyclotomicQuotient s).coeff i)‖
      = ‖∑ j ∈ Icc (i + 1) (P.q₁ s).totient,
          φ (P.zetaInt s) ^ (j - (i + 1)) * (cyclotomic (P.q₁ s) ℂ).coeff j‖ := by
        simp only [cyclotomicQuotient, coeff_divByMonic_X_sub_C, natDegree_cyclotomic, map_sum,
          map_mul, map_pow, ← coeff_map, map_cyclotomic]
    _ ≤ ∑ j ∈ Icc (i + 1) (P.q₁ s).totient, (2 : ℝ) ^ P.q₀ :=
        norm_sum_le_of_le _ fun j _ ↦ by simpa [h_zeta] using norm_coeff_cyclotomic_le j
    _ ≤ P.q₁ s * 2 ^ P.q₀ := by
        rw [sum_const, nsmul_eq_mul, Nat.card_Icc]
        gcongr
        exact (Nat.sub_le_of_le_add (by lia)).trans (P.q₁ s).totient_le

/-- The number `β = quadGen d = (1 + √-d) / 2` has absolute value at most `d`. -/
lemma norm_quadGen_le : ‖quadGen P.d‖ ≤ P.d := by
  have h_one : (1 : ℝ) ≤ P.d := by exact_mod_cast Nat.one_le_of_lt P.sixty_four_lt_d
  have h_sqrt : √(P.d : ℝ) ≤ P.d := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  calc ‖quadGen P.d‖ ≤ |(quadGen P.d).re| + |(quadGen P.d).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ P.d := by
      suffices 2⁻¹ + √(P.d : ℝ) / 2 ≤ P.d by
        simpa [quadGen, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
      linarith

/-- The vector `e i = dualVector i` is `conj β ^ j b i / P'(ζ)`, with `β = (1 + √-d) / 2`, `b i` the
`i`-th coefficient of `cyclotomicQuotient` and `P'(ζ) = relDifferentGen` the generator of the
different of `E/K`. If `P'(ζ)` has absolute value at least 1 under the embedding `Φ τ`, then
`|τ(e i)| ≤ d ^ j q₁ 2 ^ q₀`. -/
lemma norm_phi_dualVector_le {τ : P.Φ s} (h_different : 1 ≤ ‖Φ τ (P.relDifferentGen s : P.E s)‖)
    (i : ℕ) : ‖Φ τ (P.dualVector s i)‖ ≤ P.d ^ P.ceilLogQ₁ s * (P.q₁ s * 2 ^ P.q₀) := by
  calc ‖Φ τ (P.dualVector s i)‖
      = ‖quadGen P.d‖ ^ P.ceilLogQ₁ s * ‖Φ τ ((P.cyclotomicQuotient s).coeff i : P.E s)‖ /
          ‖Φ τ (P.relDifferentGen s : P.E s)‖ := by
        simp only [dualVector, map_div₀, map_mul, map_pow, map_star_complex, phi_betaKInE, norm_div,
          norm_mul, norm_pow, norm_star]
    _ ≤ ‖quadGen P.d‖ ^ P.ceilLogQ₁ s * ‖Φ τ ((P.cyclotomicQuotient s).coeff i : P.E s)‖ :=
        div_le_self (by positivity) h_different
    _ ≤ P.d ^ P.ceilLogQ₁ s * (P.q₁ s * 2 ^ P.q₀) := by
        grw [norm_quadGen_le, norm_phi_coeff_cyclotomicQuotient_le]

/-- The least integer `j` with `2 ^ j ≥ q₁` is at most `q₀ + 3 s + 10`. Here `q₀` is the fixed
modulus of the parameters and `q₁ = q₀ * 3 ^ (log₃ s + 5) * 2 ^ s`. -/
lemma ceilLogQ₁_le : P.ceilLogQ₁ s ≤ P.q₀ + 3 * s + 10 := by
  refine (Nat.clog_le_iff_le_pow one_lt_two).2 ?_
  calc P.q₁ s = P.q₀ * (3 ^ (Nat.log 3 s + 5) * 2 ^ s) := rfl
    _ ≤ 2 ^ P.q₀ * (4 ^ (s + 5) * 2 ^ s) := by
        have h_log : 3 ^ (Nat.log 3 s + 5) ≤ 4 ^ (s + 5) :=
          (Nat.pow_le_pow_left (by lia) _).trans
            (Nat.pow_le_pow_right (by lia) (Nat.add_le_add_right (Nat.log_le_self 3 s) 5))
        exact Nat.mul_le_mul Nat.lt_two_pow_self.le (Nat.mul_le_mul_right _ h_log)
    _ = 2 ^ (P.q₀ + 3 * s + 10) := by
        rw [show 4 = 2 ^ 2 from rfl, ← pow_mul]
        ring

end Parameters

namespace Data

open Parameters Real

variable {P : Parameters} (D : Data P)

/-- For admissible data `D` with exponent `s = D.towerExp`, so that `D.E = P.E s`, the generator
`relDifferentGen` of the relative different of `E/K` has absolute value at least 1 under the
embedding `Φ τ` of every infinite place `τ`. -/
lemma one_le_norm_phi_relDifferentGen (τ : D.Φ) :
    1 ≤ ‖Φ τ (P.relDifferentGen D.towerExp : D.E)‖ := by
  -- `|τ(deltaE)| = |τ(relDifferentGen)| √d`, and the lower bound for `|τ(deltaE)|` exceeds `√d`.
  have h_sqrt : √P.d ≤ τ (P.relDifferentGen D.towerExp : D.E) * √P.d :=
    (D.le_of_hasLogBound : √P.d ≤ τ (P.deltaE D.towerExp)).trans_eq (infinitePlace_apply_deltaE τ)
  rw [← InfinitePlace.apply, mk_Φ]
  exact (le_mul_iff_one_le_left (by simp [NeZero.pos])).1 h_sqrt

/-- Let `D` be admissible data with weight `b = exp D.logB`. Then
`d ^ j ≤ exp (logB / 100) = b ^ (1 / 100)` for the least integer `j = ceilLogQ₁` with `2 ^ j ≥ q₁`,
where the exponent `s` in `q₁ = P.q₁ s` is `D.towerExp`; `D.HasLogUpper F l` says `|F| ≤ exp l`. -/
lemma hasLogUpper_pow_ceilLogQ₁ :
    D.HasLogUpper ((P.d : ℝ) ^ P.ceilLogQ₁ D.towerExp) (D.logB / 100) := by
  -- The ranges of the data make `logB` large against `d`, `q₀` and `s`.
  have h_exponent : ((P.q₀ + 3 * D.towerExp + 10 : ℕ) * P.d : ℝ) ≤ D.logB / 100 :=
    D.le_of_hasLogBound
  have hd : (P.d : ℝ) ≤ exp P.d := (le_add_of_nonneg_right zero_le_one).trans (add_one_le_exp _)
  rw [hasLogUpper_iff, abs_of_nonneg (by positivity)]
  calc (P.d : ℝ) ^ P.ceilLogQ₁ D.towerExp ≤ exp P.d ^ P.ceilLogQ₁ D.towerExp := by gcongr
    _ = exp (P.ceilLogQ₁ D.towerExp * P.d) := (exp_nat_mul _ _).symm
    _ ≤ exp ((P.q₀ + 3 * D.towerExp + 10 : ℕ) * P.d) := by grw [ceilLogQ₁_le]
    _ ≤ exp (D.logB / 100) := exp_le_exp.2 h_exponent

/-- Let `D` be data for the parameters `P` (a `Data P`), with weight `b = D.b` and field
`E = P.E s = K(ζ)` for `s = D.towerExp`. The vectors `e i = dualVector i`, `i < φ(q₁)`, are
`conj β ^ j` times the basis of `E/K` dual to the powers of `ζ` under the trace. A natural number
`h` equal to the complex number `dualResolutionFactor = q₁ (1 + ∑ i, ∑ τ, |τ(e i)| ^ 2) + β ^
j + conj β ^ j` is at most `b`. This number is the length of the tight frame of
`Parameters.exists_isTightFrame_coprime`. -/
lemma le_b_of_eq_dualResolutionFactor {h : ℕ}
    (h_length : (h : ℂ) = P.dualResolutionFactor D.towerExp) : (h : ℝ) ≤ D.b := by
  -- After `h_sum` the bound is a polynomial in `q₁`, `D.f`, `2 ^ q₀` and `d ^ j`. The last step
  -- compares logarithmic sizes with `logB`; it finds `h_pow` as an instance.
  have h_pow : D.HasLogUpper ((P.d : ℝ) ^ P.ceilLogQ₁ D.towerExp) (D.logB / 100) :=
    D.hasLogUpper_pow_ceilLogQ₁
  rw [dualResolutionFactor] at h_length
  set j : ℕ := P.ceilLogQ₁ D.towerExp
  have h_sum : ∑ i : Fin D.q₁.totient, ∑ τ : D.Φ, ‖Φ τ (P.dualVector D.towerExp i)‖ ^ 2 ≤
      D.q₁ * (D.f * (P.d ^ j * (D.q₁ * 2 ^ P.q₀)) ^ 2) := by
    grw [norm_phi_dualVector_le (D.one_le_norm_phi_relDifferentGen _)]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    grw [Nat.totient_le]
  calc (h : ℝ) = ‖(h : ℂ)‖ := (Complex.norm_natCast h).symm
    _ ≤ D.q₁ * (1 + ∑ i : Fin D.q₁.totient, ∑ τ : D.Φ, ‖Φ τ (P.dualVector D.towerExp i)‖ ^ 2) +
          (‖quadGen P.d‖ ^ j + ‖quadGen P.d‖ ^ j) := by
        grw [h_length, norm_add_le, norm_add_le, norm_mul, norm_pow, norm_pow, Complex.norm_conj,
          Complex.norm_natCast, Complex.norm_of_nonneg (by positivity)]
    _ ≤ D.q₁ * (1 + D.q₁ * (D.f * (P.d ^ j * (D.q₁ * 2 ^ P.q₀)) ^ 2)) + (P.d ^ j + P.d ^ j) := by
        grw [h_sum, norm_quadGen_le]
    _ ≤ D.b := D.le_of_hasLogBound

/-- Let `D` be data for the parameters `P` (a `Data P`), with weight `b = D.b` and field
`E = D.E = K(ζ)`. There are `h` prime to `q₁` with `1 ≤ h ≤ b` and a tight frame `v` of length `h`
with multiplicities 1. That is, the `v i` lie in the lattice `𝔞₀ = E ∩ α Ô`, and
`∑ i, σ(v i) conj (τ(v i)) = h δ(σ, τ)` on the CM type. Moreover, for every prime `p` and embedding
`ιₚ : ℂ →+* ℂ_[p]`, some `y` among the powers of `ζ` and the `v i` makes
`periodFactor * conj (τ(y))` a unit at `ιₚ` for all `τ` in the CM type. -/
theorem exists_short_isTightFrame_coprime :
    ∃ (h : ℕ) (I : Type) (_ : Fintype I) (v : I → D.E),
      h.Coprime D.q₁ ∧
      1 ≤ h ∧
      (h : ℝ) ≤ D.b ∧
      IsTightFrame v 1 h ∧
      ∀ (p : ℕ) [Fact p.Prime] [PadicPlace p], ∃ y : D.E,
        ((∃ i : Fin D.q₁, P.ζ D.towerExp ^ i.val = y) ∨ ∃ i : I, v i = y) ∧
        P.HasUnitLinearForm D.towerExp p y := by
  obtain ⟨h, I, _, v, hv, h_length, h_coprime, i₀, hi₀⟩ := P.exists_isTightFrame_coprime D.towerExp
  have hq₁ : 1 < D.q₁ := one_lt_q₁
  have h_pos : 1 ≤ h := by
    refine Nat.pos_of_ne_zero fun h_zero ↦ hq₁.ne' ?_
    simpa [h_zero] using h_coprime
  have h_short : (h : ℝ) ≤ D.b := D.le_b_of_eq_dualResolutionFactor h_length
  refine ⟨h, I, inferInstance, v, h_coprime, h_pos, h_short, hv, fun p _ _ ↦ ?_⟩
  -- The vector with unit coefficients is `ζ ^ 0` or the member `v i₀ = ζ e (φ(q₁) - 1)`.
  obtain ⟨y, hy_eq, hy_unit⟩ : ∃ y : D.E,
      (y = 1 ∨ y = P.ζ D.towerExp * P.dualVector D.towerExp (D.q₁.totient - 1)) ∧
        P.HasUnitLinearForm D.towerExp p y :=
    P.exists_hasUnitLinearForm D.towerExp p
  refine ⟨y, ?_, hy_unit⟩
  rcases hy_eq with rfl | rfl
  · exact .inl ⟨⟨0, zero_lt_one.trans hq₁⟩, pow_zero _⟩
  · exact .inr ⟨i₀, hi₀⟩

/-- Let `D` be data for the parameters `P` (a `Data P`), with field `E = D.E = P.E s` for the
exponent `s = D.towerExp`, weight `b = D.b`, and `f = D.f` the number of infinite places of `E`. The
principal level `M = D.M` is the product of the two distinct primes `D.levelPrime 0` and
`D.levelPrime 1` of the data, which lie in `[b ^ 10, b ^ 11]`. There is a tight frame `v` of length
`M` with multiplicities `c i ≥ 6 f b`. Moreover, for every prime `p` and embedding
`ιₚ : ℂ →+* ℂ_[p]`, some `y = v i` makes `periodFactor * conj (τ(y))` a unit at `ιₚ` for all `τ` in
the CM type. -/
theorem exists_isTightFrame :
    ∃ (I : Type) (_ : Fintype I) (v : I → D.E) (c : I → ℕ),
      IsTightFrame v c D.M ∧
      (∀ i : I, 6 * D.f * D.b ≤ c i) ∧
      ∀ (p : ℕ) [Fact p.Prime] [PadicPlace p], ∃ i : I, P.HasUnitLinearForm D.towerExp p (v i) := by
  obtain ⟨h, I, _, v, h_coprime, -, h_short, hv, h_unit⟩ := D.exists_short_isTightFrame_coprime
  -- The threshold of `exists_isTightFrame_of_coprime` for `R = ⌈6 f b⌉` is at most `D.M`.
  have h_large : D.q₁ * h + ⌈6 * D.f * D.b⌉₊ * (D.q₁ + h) ≤ D.M := by
    -- The comparison of logarithmic sizes finds `h ≤ b = exp logB` as an instance.
    have h_log : D.HasLogUpper h D.logB := ⟨by rwa [ite_eq_left rfl, Nat.abs_cast]⟩
    exact D.nat_le_of_hasLogBound
  let u : Fin D.q₁ ⊕ I → D.E := Sum.elim (fun i : Fin D.q₁ ↦ P.ζ D.towerExp ^ i.val) v
  obtain ⟨c, hu, hc⟩ : ∃ c : Fin D.q₁ ⊕ I → ℕ,
      IsTightFrame u c D.M ∧ ∀ j : Fin D.q₁ ⊕ I, ⌈6 * D.f * D.b⌉₊ ≤ c j :=
    exists_isTightFrame_of_coprime hv h_coprime h_large
  refine ⟨Fin D.q₁ ⊕ I, inferInstance, u, c, hu, fun j ↦ Nat.ceil_le.1 (hc j), fun p _ _ ↦ ?_⟩
  obtain ⟨y, ⟨i, rfl⟩ | ⟨i, rfl⟩, hy⟩ := h_unit p
  · exact ⟨.inl i, hy⟩
  · exact ⟨.inr i, hy⟩

end Data

end New
