import Lib.ClassField.GreenbergWiles.SelmerLevels
import Lib.Cyclotomic.Stickelberger

/-!
# Kolyvagin's derivative cocycles from Gauss sums, for one set of primes

The main result, `New.OddPart.exists_isKolyvaginSystem`, constructs Kolyvagin's cocycles `κ S` with
values in `O/lⁿ` from the Jacobi-type quotients `J` of `New.OddPart.exists_isJacobiFamily`. One
takes `lⁿ`-th roots `y` of `J`, forms the roots of unity `γ y / (g γ g⁻¹) y`, applies the derivative
operators at the primes of `S` and sums against `aᵉ ψ(a)`. The local properties are read modulo a
place, where roots of unity of order prime to it stay distinct.

* `New.OddPart.IsKolyvaginSystem`: the properties of the cocycles `κ S`.
* `New.OddPart.exists_isKolyvaginSystem`: a Kolyvagin system exists.
* `New.OddPart.derivativeSum`: the derivative operators followed by the character sum.

Conventions: `Ω = ℚ̄` is an algebraic closure of `ℚ`, and its places are valuation subrings
(`ClosurePlace`); `DiscreteUnits Ω` is `Ω^×` written additively, so `n • u` is `uⁿ`, and
`galUnitsRep g` is the action of `g` on it; `New.QZ.ofZMod M a` is `a/M` in `ℚ/ℤ`;
`QuotSpan (l ^ n : O)` is `O/lⁿ`; `floorDiff c x` is `⌊c ⟨x⟩⌋ - ⌊c ⟨-x⟩⌋`, where `⟨x⟩` is the
representative of `x` in `[0, 1)`.

Notions from other files:
* `New.OddPart.principalUnits B`: the units of `Ω` congruent to `1` modulo the maximal ideal of `B`,
  as an additive subgroup of `DiscreteUnits Ω`.
* `New.IsFrob B q σ`: `σ` stabilises `B`, and `σ x ≡ x ^ q` modulo the maximal ideal of `B` for
  every `x` in `B`; for `q = 1` this says that `σ` lies in the inertia group of `B`.
* `New.rootPowHom Ω m`: the map `ℤ/m → Ω^×`, `t ↦ ζᵗ`, for a fixed primitive `m`-th root of unity
  `ζ`; it is injective, and its image is the set of `m`-th roots of unity.
* `New.cyclotomicPowDirichlet l e ψ`: the character `cycᵉ ψ` of `Gal(ℚ̄/ℚ)` with values in `Oˣ`,
  where `cyc` is the `l`-adic cyclotomic character.

## Relation to the literature

Known result: Kolyvagin's derivative classes of the Euler system of Gauss sums. Here the classes
carry a Tate twist and a Dirichlet character and are cocycles over the rationals that vanish at one
fixed element. Their ramification, the relation between Frobenius and inertia, and the link between
the bottom class and the Stickelberger element are also covered. Source: K. Rubin, Kolyvagin's
system of Gauss sums, Arithmetic Algebraic Geometry (Texel 1989), Progr. Math. 89, 1991, 309-324;
with a Tate twist: G. Banaszak, W. Gajda, Euler systems for higher K-theory of number fields, J.
Number Theory 58 (1996).
-/

namespace New.OddPart

open QZ Finset MulAut Function ZMod NeZero DiscreteUnits Cohomology Representation Multiplicative
  Selmer

section

variable {O : Type} [CommRing O] {B : ClosurePlace} {g : Gal(Ω/ℚ)} {u : DiscreteUnits Ω}
  {m a M N l n e : ℕ} [NeZero m] [NeZero N] [Fact l.Prime] [Algebra ℤ_[l] O]
  {ψ : DirichletCharacter O N} [Algebra (ZMod (l ^ n)) (QuotSpan (l ^ n : O))]
  {L : ∀ q : Nat.Primes, (ZMod q)ˣ →* Multiplicative (ZMod (l ^ n))}
  {S : Finset Nat.Primes} {d f : Nat.Primes → ZMod (l ^ n)} {G G' : QZ → ZMod (l ^ n)}
  {γ : Gal(Ω/ℚ)} {q : Nat.Primes} {τ φ : Gal(Ω/ℚ)} {Y : ZMod q → DiscreteUnits Ω}
  {y : DiscreteUnits Ω} {v : (ZMod q)ˣ} {lg : (ZMod q)ˣ → ℤ}

private lemma mem_principalUnits_iff {x : DiscreteUnits Ω} :
    x ∈ principalUnits B ↔ B.valuation ((x.toMul : Ω) - 1) < 1 :=
  Iff.rfl

private lemma val_toMul_galUnitsRep : ((galUnitsRep g u).toMul : Ω) = g • (u.toMul : Ω) :=
  rfl

/-- Let `g` act as the `a`-th power modulo the maximal ideal of `B` (`IsFrob B a g`), and let
the `m`-th power of `u` be a unit at `B`, where `m ≠ 0`. Then `g u / uᵃ` is a principal unit at
`B`. -/
lemma _root_.New.IsFrob.sub_nsmul_mem_principalUnits (hg : IsFrob B a g)
    (hu : B.valuation ((m • u).toMul : Ω) = 1) :
    galUnitsRep g u - a • u ∈ principalUnits B := by
  -- `u` is a unit at `B`, so `g u / u ^ a - 1` has the valuation of `g u - u ^ a`.
  obtain ⟨-, hg_cong⟩ : g ∈ decompGroup Gal(Ω/ℚ) B ∧
      ∀ x : Ω, B.valuation x ≤ 1 → B.valuation (g • x - x ^ a) < 1 := hg
  have h_unit : B.valuation (u.toMul : Ω) = 1 := by simpa [NeZero.ne] using hu
  have h_cong : B.valuation (g • (u.toMul : Ω) - (u.toMul : Ω) ^ a) < 1 := hg_cong _ h_unit.le
  rw [mem_principalUnits_iff]
  simpa [div_sub_one, h_unit] using h_cong

/-- Roots of unity of order prime to the residue characteristic stay distinct modulo `B`. Let
`μ = New.rootPowHom Ω m` be the fixed map `t ↦ ζᵗ` from `ℤ/m` to `Ω^×`. If `m` is a unit at `B`
and `μ (a - b)` is a principal unit at `B`, then `a = b`. -/
lemma eq_of_mem_principalUnits {a b : ZMod m} (hm : B m = 1)
    (h_mem : (rootPowHom Ω m).val (a - b) ∈ principalUnits B) :
    a = b := by
  -- The image of `a - b` is an `m`-th root of unity congruent to one, and `m` is a unit at `B`.
  obtain ⟨μ_inj, μ_range⟩ : Injective (rootPowHom Ω m).val ∧
      ∀ y : DiscreteUnits Ω, y ∈ (rootPowHom Ω m).val.range ↔ m • y = 0 := (rootPowHom Ω m).prop
  have h_root : m • (rootPowHom Ω m).val (a - b) = 0 := (μ_range _).mp ⟨a - b, rfl⟩
  have h_pow : (((rootPowHom Ω m).val (a - b)).toMul : Ω) ^ m = 1 := by
    simpa using congr_arg (fun z : DiscreteUnits Ω ↦ (z.toMul : Ω)) h_root
  have h_eq_one : (((rootPowHom Ω m).val (a - b)).toMul : Ω) = 1 :=
    eq_of_val_sub_lt_one hm h_pow (one_pow m) (mem_principalUnits_iff.mp h_mem)
  exact sub_eq_zero.mp (μ_inj ((DiscreteUnits.ext h_eq_one).trans (map_zero _).symm))

/-- Let `M = m a` with `a` a unit at `B`. An element `g` of the inertia group of `B` that fixes
the `m`-th roots of unity fixes the `M`-th roots of unity. -/
lemma mem_cycloGalGroup_of_mem_inertiaGroup [NeZero M] (hg : g ∈ inertiaGroup Gal(Ω/ℚ) B)
    (ha : B a = 1) (hM : m * a = M) (hgm : g ∈ cycloGalGroup m) :
    g ∈ cycloGalGroup M := by
  -- `a • z` is an `m`-th root of unity, so it is a unit at `B` and `g` fixes it; as `a` is a unit
  -- at `B`, inertia then fixes its `a`-th root `z`.
  refine cyclotomicCharMod_eq_one_iff.mpr fun z hz ↦ DiscreteUnits.ext ?_
  have h_fix : galUnitsRep g (a • z) = a • z :=
    cyclotomicCharMod_eq_one_iff.mp hgm (a • z) (by rwa [smul_smul, hM])
  have h_fix_val : g • ((a • z).toMul : Ω) = (a • z).toMul := by rw [← val_toMul_galUnitsRep, h_fix]
  have h_unit : B.valuation ((a • z).toMul : Ω) = 1 := by
    simpa [NeZero.ne, ← hM] using congr_arg (fun w : DiscreteUnits Ω ↦ B w.toMul) hz
  rw [val_toMul_galUnitsRep]
  exact inertia_fixes_root_of_unit hg ha rfl h_unit h_fix_val

/-- If `B` lies above the prime `l` and `a` is prime to `l`, some element of the inertia group of
`B` in `Gal(Ω/ℚ)` has `l`-adic cyclotomic character `a`. -/
lemma exists_inertia_cyclotomicChar_eq (hB : B l < 1) (ha : l.Coprime a) :
    ∃ γ ∈ inertiaGroup Gal(Ω/ℚ) B, (cyclotomicChar Ω l γ).val = a := by
  -- `B` is pulled back from the integers of `ℚ̄_l` along an embedding `e`, and `res` restricts the
  -- local Galois group along `e`. It carries local inertia into inertia and keeps `cyclotomicChar`.
  obtain ⟨e, rfl⟩ := exists_comap_intQpBar_eq hB
  obtain ⟨res, h_res⟩ : ∃ res : Gp l →ₜ* Gal(Ω/ℚ), ∀ (g : Gp l) (x : Ω), e (res g • x) = g • e x :=
    exists_galois_restrict _ _ e fun g x ↦ by simp
  -- the local statement: `ℚ_l(μ_{l^∞})` is totally ramified
  have h_prime : ThePrime l := ThePrime.mk
  obtain ⟨g, hg_ine, hg_val⟩ := exists_inertia_cyclotomicGp_eq a ha
  exact ⟨res g, .map h_res hg_ine, by rwa [cyclotomicChar_eq_of_equivariant l (h_res g)]⟩

/-- If `g` raises the `(N m)`-th roots of unity to the power `a`, then on an element `x` of an
`O`-module with `m x = 0` the value `cyclotomicPowDirichlet l e ψ g` acts as the scalar
`aᵉ ψ(a)`. -/
lemma cyclotomicPowDirichlet_smul (hg : (cyclotomicCharMod Ω (N * m) g).val = a) {V : Type*}
    [AddCommGroup V] [Module O V] {x : V} (hx : m • x = 0) :
    (cyclotomicPowDirichlet l e ψ g).val • x = (a ^ e * ψ a) • x := by
  -- Up to a unit, `m` is a power of `l` in `ℤ_[l]`, and modulo that power the `l`-adic cyclotomic
  -- character of `g` is `a`.
  have hm_ne : (m : ℤ_[l]) ≠ 0 := NeZero.ne _
  have h_pow_dvd : (l : ℤ_[l]) ^ padicValNat l m ∣ (cyclotomicChar Ω l g).val - a :=
    (pow_dvd_cyclotomicChar_sub_iff _).mpr
      (cyclotomicCharMod_eq_of_dvd (.mul_left pow_padicValNat_dvd N) hg)
  have h_adic : (m : ℤ_[l]) ∣ (cyclotomicChar Ω l g).val - a :=
    (PadicInt.unitCoeff_spec hm_ne).dvd.trans (by simpa [PadicInt.valuation] using h_pow_dvd)
  obtain ⟨b, hb⟩ : (m : O) ∣ algebraMap ℤ_[l] O (cyclotomicChar Ω l g).val ^ e - a ^ e := by
    simpa using map_dvd (algebraMap ℤ_[l] O) (h_adic.trans (sub_dvd_pow_sub_pow _ _ e))
  have h_scalar : ((cyclotomicPowDirichlet l e ψ g : Oˣ) : O) =
      algebraMap ℤ_[l] O (cyclotomicChar Ω l g).val ^ e * ψ a := by
    simp [cyclotomicPowDirichlet, cyclotomicCharMod_eq_of_dvd (dvd_mul_right N m) hg]
  -- The two scalars differ by `ψ a * b * m`, and `m` kills `x`.
  rw [h_scalar]
  linear_combination (norm := module) ψ a • (hb • x + b • hx)

/-- Discrete logarithm: for a prime `q ≡ 1 mod k` there is a homomorphism `L` from `(ℤ/q)ˣ` to
`ℤ/k` (written multiplicatively) that sends some unit `g` to `1`, so `L` is onto. -/
lemma exists_monoidHom_units_zmod_eq_ofAdd_one {q : Nat.Primes} {k : ℕ} (hq : q ≡ 1 [MOD k]) :
    ∃ L : (ZMod q)ˣ →* Multiplicative (ZMod k), ∃ g : (ZMod q)ˣ, L g = ofAdd 1 := by
  obtain ⟨g, gen⟩ := (isCyclic_units_prime q.prop).exists_zpow_surjective
  have h_gen (x : (ZMod q)ˣ) : x ∈ Subgroup.zpowers g := Subgroup.mem_zpowers_iff.mpr (gen x)
  -- `1` has order `k` in `ℤ/k`, and `k` divides `q - 1`, the order of `g`.
  have h_order : orderOf (ofAdd (1 : ZMod k)) ∣ orderOf g := by
    simp [orderOf_eq_card_of_forall_mem_zpowers h_gen, Nat.totient_prime q.prop, hq.symm.dvd']
  exact ⟨monoidHomOfForallMemZpowers h_gen h_order, g,
    monoidHomOfForallMemZpowers_apply_gen h_gen h_order⟩

/-- An `m`-th root of unity `u` of `Ω` is moved alike by `γ` and by its conjugate `g γ g⁻¹`. -/
lemma galUnitsRep_conj_of_nsmul_eq_zero (γ g : Gal(Ω/ℚ)) {u : DiscreteUnits Ω} (hu : m • u = 0) :
    galUnitsRep γ u = galUnitsRep (g * γ * g⁻¹) u := by
  have h_ker : γ⁻¹ * conj g γ ∈ cycloGalGroup m := by simp [mul_comm]
  have h_fix : galUnitsRep (γ⁻¹ * conj g γ) u = u := cyclotomicCharMod_eq_one_iff.mp h_ker u hu
  calc galUnitsRep γ u = galUnitsRep γ (galUnitsRep (γ⁻¹ * conj g γ) u) := by rw [h_fix]
    _ = galUnitsRep (g * γ * g⁻¹) u := by simp

/-- Shifts do not matter. Let `Λ S d` be linear maps, for finite sets `S` of primes and shifts
`d`, such that adding a prime `q` to `S` first translates by `u/q` with weight `L q u - d q` and
sums over the units `u` mod `q` (`Λ_insert`), and `Λ S d G` reads only `G` and the shifts on `S`
when `S ⊆ I` (`Λ_congr`). If summing `F` over the translates by `b/r`, `r ∈ I ∖ S`, only changes
the shifts (`distr`), then for `S ⊆ I` the value `Λ S d F` does not depend on `d`. -/
lemma shift_indep_of_distribution {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
    {Λ : Finset Nat.Primes → (Nat.Primes → R) → (QZ → R) →ₗ[R] V}
    {L : ∀ q : Nat.Primes, (ZMod q)ˣ → R} {I : Finset Nat.Primes} {F : QZ → R}
    (Λ_insert : ∀ {q : Nat.Primes} {S : Finset Nat.Primes}, q ∉ S →
      ∀ (d : Nat.Primes → R) (G : QZ → R),
      Λ (insert q S) d G = Λ S d fun x : QZ ↦ ∑ u : (ZMod q)ˣ, (L q u - d q) * G (x + ofZMod q u))
    (Λ_congr : ∀ {S : Finset Nat.Primes} {d f : Nat.Primes → R}, S ⊆ I → (∀ q ∈ S, f q = d q) →
      ∀ {G G' : QZ → R}, (∀ x : QZ, G x = G' x) → Λ S d G = Λ S f G')
    (distr : ∀ r ∈ I, ∀ S ⊆ I, r ∉ S → ∀ d : Nat.Primes → R, ∃ f : Nat.Primes → R,
      Λ S d (fun x : QZ ↦ ∑ b : ZMod r, F (x + ofZMod r b)) = Λ S f F)
    {S : Finset Nat.Primes} (hS : S ⊆ I) {d f : Nat.Primes → R} :
    Λ S d F = Λ S f F := by
  -- Changing `d` at one `r ∈ S` changes `Λ S d F` by a multiple of
  -- `Λ (S \ r) d (∑_b F (· + b/r) - F)`, which is zero by `distr` and induction on `S`.
  revert hS d f
  refine S.strongInductionOn fun S ih hS d f ↦ ?_
  -- `step T`: the shifts may be changed from `f` to `d` on `T ⊆ S`, one prime at a time.
  have step (T : Finset Nat.Primes) (hT : T ⊆ S) : Λ S (T.piecewise d f) F = Λ S f F := by
    induction T using Finset.induction with
    | empty => rfl
    | insert r T hrT ihT =>
      obtain ⟨hr, hT⟩ := insert_subset_iff.mp hT
      refine .trans ?_ (ihT hT)
      have erase_le : S.erase r ⊆ I := (erase_subset r S).trans hS
      have r_notMem : r ∉ S.erase r := notMem_erase r S
      -- The functions that `Λ (S.erase r)` is applied to on the two sides, and the difference
      -- `H - F` with `H = ∑_b F (· + b/r)`, which it kills.
      let G₁ : QZ → R := fun x : QZ ↦
        ∑ u : (ZMod r)ˣ, (L r u - (insert r T).piecewise d f r) * F (x + ofZMod r u)
      let G₂ : QZ → R := fun x : QZ ↦
        ∑ u : (ZMod r)ˣ, (L r u - T.piecewise d f r) * F (x + ofZMod r u)
      let H : QZ → R := fun x : QZ ↦ ∑ b : ZMod r, F (x + ofZMod r b)
      have vanish {d : Nat.Primes → R} : Λ (S.erase r) d H = Λ (S.erase r) d F := by
        obtain ⟨d', hd'⟩ := distr r (hS hr) (S.erase r) erase_le r_notMem d
        exact hd'.trans (ih (S.erase r) (erase_ssubset hr) erase_le)
      have h_shift (q : Nat.Primes) (hq : q ∈ S.erase r) :
          T.piecewise d f q = (insert r T).piecewise d f q := by
        simp [ne_of_mem_erase hq]
      have h_fun (x : QZ) : (G₁ + (d r - f r) • (H - F)) x = G₂ x := by
        simp [G₁, G₂, H, hrT, mul_sum, sum_eq_add_sum_units, ← add_mul, ← sum_add_distrib]
      rw [← insert_erase hr, Λ_insert r_notMem, Λ_insert r_notMem]
      calc Λ (S.erase r) ((insert r T).piecewise d f) G₁
          = Λ (S.erase r) ((insert r T).piecewise d f) (G₁ + (d r - f r) • (H - F)) := by
            simp [vanish]
        _ = Λ (S.erase r) (T.piecewise d f) G₂ := Λ_congr erase_le h_shift h_fun
  exact (Λ_congr hS (fun q hq ↦ by simp [hq]) fun x : QZ ↦ rfl).trans (step S le_rfl)

section Derivative

variable (ψ e L S d) in
/-- Kolyvagin's derivative followed by the character sum, with values in `O/lⁿ`
(`QuotSpan (l ^ n : O)`). For each `q ∈ S`, a function on `ℚ/ℤ` is translated by `u/q` with weight
`L q u - d q` and summed over the units `u` mod `q`; the values of the result at `a / N lⁿ` are
then summed against `aᵉ ψ(a)` over the units `a` mod `N lⁿ`. -/
noncomputable def derivativeSum : (QZ → ZMod (l ^ n)) →ₗ[ZMod (l ^ n)] QuotSpan (l ^ n : O) :=
  (∑ a : (ZMod (N * l ^ n))ˣ,
      LinearMap.smulRight
        ((a : ZMod (N * l ^ n)).val ^ e • LinearMap.proj (ofZMod (N * l ^ n) a))
        (ψ (a : ZMod (N * l ^ n)).val : QuotSpan (l ^ n : O))) ∘ₗ
    asAlgebraHom (ofDistribMulAction (ZMod (l ^ n)) (Multiplicative QZ)ᵈᵐᵃ (QZ → ZMod (l ^ n)))
      (∏ q ∈ S, ∑ u : (ZMod q)ˣ,
        MonoidAlgebra.single (DomMulAct.mk (ofAdd (ofZMod q u))) ((L q u).toAdd - d q))

omit [Algebra ℤ_[l] O] in
/-- With no primes, `derivativeSum` is the character sum: the value of `G` at `a / N lⁿ` is summed
against `aᵉ ψ(a)` over the units `a` mod `N lⁿ`. -/
lemma derivativeSum_empty :
    derivativeSum e ψ L ∅ d G = ∑ a : (ZMod (N * l ^ n))ˣ,
      (((a : ZMod (N * l ^ n)).val ^ e : ℕ) * G (ofZMod (N * l ^ n) a)) •
        (ψ (a : ZMod (N * l ^ n)).val : QuotSpan (l ^ n : O)) := by
  simp [derivativeSum]

omit [Algebra ℤ_[l] O] in
/-- Adding a prime `q` to `S` applies the derivative at `q` first. -/
lemma derivativeSum_insert {q : Nat.Primes} (hq : q ∉ S) :
    derivativeSum e ψ L (insert q S) d G =
      derivativeSum e ψ L S d fun x : QZ ↦
        ∑ u : (ZMod q)ˣ, ((L q u).toAdd - d q) * G (x + ofZMod q u) := by
  -- `MonoidAlgebra.single_sub` would split the weights before the sums are matched.
  simp [derivativeSum, hq, mul_comm _ (S.prod _), sum_fn, DomMulAct.smul_apply, add_comm,
    -MonoidAlgebra.single_sub]

/-- Substituting `a u` for `u` in all the sums. Here `derivativeSum e ψ L S d G ∈ O/lⁿ` applies
Kolyvagin's derivative to `G : ℚ/ℤ → ZMod (lⁿ)`: for each `q ∈ S`, `G` is translated by `u/q` with
weight `L q u - d q` and summed over the units `u` mod `q`, and the values of the result at
`b / N lⁿ` are then summed against `bᵉ ψ(b)` over the units `b` mod `N lⁿ`. Let `M` be a multiple of
`N lⁿ` and of the primes of `S`, and let `a` be the cyclotomic character of `g` mod `N lⁿ`; if
`G x = G' (a x)` on the `M`-torsion of `ℚ/ℤ`, and `f q = L q v + d q` with `v ≡ a` mod `q` for each
`q ∈ S`, then `cycᵉ ψ (g)` (`cyclotomicPowDirichlet l e ψ g`) times `derivativeSum … d G` is
`derivativeSum … f G'`. -/
lemma cyclotomicPowDirichlet_smul_derivativeSum (hM : N * l ^ n ∣ M) (hS : ∀ q ∈ S, (q : ℕ) ∣ M)
    (hg : (cyclotomicCharMod Ω (N * l ^ n) g : ZMod (N * l ^ n)) = a)
    (hf : ∀ q ∈ S, ∃ v : (ZMod q)ˣ, f q = (L q v).toAdd + d q ∧ (v : ZMod q) = a)
    (hG : ∀ {x : QZ}, M • x = 0 → G x = G' (a • x)) :
    (cyclotomicPowDirichlet l e ψ g : O) • derivativeSum e ψ L S d G =
      derivativeSum e ψ L S f G' := by
  have killed {x : QuotSpan (l ^ n : O)} : l ^ n • x = 0 := nsmul_quot_eq_zero dvd_rfl x
  induction S using Finset.induction generalizing G G' with
  | empty =>
    -- Substitute `χ u` for `u` in the character sum, where `χ` is the character of `g` mod `N lⁿ`.
    have base_zero : (M : ZMod (N * l ^ n)) = 0 := (natCast_eq_zero_iff M (N * l ^ n)).mpr hM
    rw [derivativeSum_empty, derivativeSum_empty, smul_sum]
    refine Fintype.sum_equiv (.mulLeft (cyclotomicCharMod Ω (N * l ^ n) g)) _ _ fun u ↦ ?_
    -- Both terms become products in `O/lⁿ`, equal by `ring`.
    simp [cyclotomicPowDirichlet_smul hg killed, base_zero, Algebra.smul_def, ← map_nsmul, hG, hg]
    ring
  | insert q S hq ih =>
    obtain ⟨hqM, hS⟩ := (forall_mem_insert q S _).mp hS
    obtain ⟨⟨v, hv_shift, hv⟩, hf⟩ := (forall_mem_insert q S _).mp hf
    have q_zero : (M : ZMod q) = 0 := (natCast_eq_zero_iff M q).mpr hqM
    rw [derivativeSum_insert hq, derivativeSum_insert hq]
    -- Substitute `v u` for `u` in the sum at `q`.
    refine ih hS hf fun {x} hx ↦ sum_equiv (.mulLeft v) (fun u ↦ by simp) fun u _ ↦ ?_
    have h_tors : M • (x + ofZMod q u) = 0 := by simp [q_zero, ← map_nsmul, hx]
    have h_shift : (L q (v * u)).toAdd - f q = (L q u).toAdd - d q := by simp [hv_shift]
    have h_arg : a • (x + ofZMod q u) = a • x + ofZMod q (v * u : (ZMod q)ˣ) := by
      simp [← map_nsmul, hv]
    show ((L q u).toAdd - d q) * G (x + ofZMod q u) =
      ((L q (v * u)).toAdd - f q) * G' (a • x + ofZMod q (v * u : (ZMod q)ˣ))
    rw [hG h_tors, h_arg, h_shift]

/-- The case of a prime `r ≡ 1 mod N lⁿ` outside `S`, where `rᵉ ψ(r) = 1` in `O/lⁿ`. Let `M` be
a multiple of `N lⁿ` and of the primes of `S`. If `G x = G' (r x)` on the `M`-torsion of `ℚ/ℤ`,
then `derivativeSum` takes the same value on `d, G` as on `f, G'`, where `f q = L q r' + d q` for
the unit `r'` of `ℤ/q` that `r` gives. -/
lemma derivativeSum_eq_of_prime (hM : N * l ^ n ∣ M) (hS : ∀ q ∈ S, (q : ℕ) ∣ M) {r : Nat.Primes}
    (hr : r ≡ 1 [MOD N * l ^ n]) (hrS : r ∉ S)
    (hG : ∀ {x : QZ}, M • x = 0 → G x = G' ((r : ℕ) • x)) :
    derivativeSum e ψ L S d G =
      derivativeSum e ψ L S
        (fun q : Nat.Primes ↦ (L q (invFun Units.val ((r : ℕ) : ZMod q))).toAdd + d q) G' := by
  have h_cyc_one : (cyclotomicCharMod Ω (N * l ^ n) (1 : Gal(Ω/ℚ)) : ZMod (N * l ^ n)) =
      (r : ℕ) := by
    simpa using (natCast_eq_natCast_iff 1 r (N * l ^ n)).mpr hr.symm
  have r_unit {q : Nat.Primes} (hq : q ∈ S) : IsUnit ((r : ℕ) : ZMod q) :=
    (CharP.cast_ne_zero_of_ne_of_prime (ZMod q) r.prop
      fun h_eq ↦ ne_of_mem_of_not_mem hq hrS (Subtype.ext h_eq)).isUnit
  -- `cyclotomicPowDirichlet l e ψ` is a homomorphism, so its value at `1` acts trivially.
  simpa using cyclotomicPowDirichlet_smul_derivativeSum (e := e) (ψ := ψ) (L := L) (d := d)
    (f := fun q : Nat.Primes ↦ (L q (invFun Units.val ((r : ℕ) : ZMod q))).toAdd + d q) hM hS
    h_cyc_one (fun q hq ↦ ⟨invFun Units.val _, rfl, invFun_eq (r_unit hq)⟩) hG

/-- `derivativeSum` reads only the shifts at the primes of `S` and the values on the
`M`-torsion of `ℚ/ℤ`, where `M` is a multiple of `N lⁿ` and of the primes of `S`. -/
lemma derivativeSum_congr (hM : N * l ^ n ∣ M) (hS : ∀ q ∈ S, (q : ℕ) ∣ M)
    (hf : ∀ q ∈ S, f q = d q) (hG : ∀ {x : QZ}, M • x = 0 → G x = G' x) :
    derivativeSum e ψ L S d G = derivativeSum e ψ L S f G' := by
  -- Take `g = 1` in `cyclotomicPowDirichlet_smul_derivativeSum`.
  have h_shift : ∀ q ∈ S, ∃ v : (ZMod q)ˣ, f q = (L q v).toAdd + d q ∧ (v : ZMod q) = (1 : ℕ) :=
    fun q hq ↦ ⟨1, by simp [hf q hq], by simp⟩
  simpa using cyclotomicPowDirichlet_smul_derivativeSum (g := 1) (a := 1) (e := e) (ψ := ψ) hM hS
    (by simp) h_shift (fun {x} hx ↦ by simpa using hG hx)

/-- Equivariance of `derivativeSum` under `g`: only the shifts change. Let `M` be a multiple
of `N lⁿ` and of the primes of `S`, and let `a` be the cyclotomic character of `g` mod `M`. If
`G x = G' (a x)` on the `M`-torsion of `ℚ/ℤ`, then `cycᵉ ψ (g)` times `derivativeSum … d G` is
`derivativeSum … f G'` for some shifts `f`. -/
lemma exists_cyclotomicPowDirichlet_smul_derivativeSum [NeZero M] (hM : N * l ^ n ∣ M)
    (hS : ∀ q ∈ S, (q : ℕ) ∣ M) (hg : (cyclotomicCharMod Ω M g : ZMod M) = a)
    (hG : ∀ {x : QZ}, M • x = 0 → G x = G' (a • x)) :
    ∃ f : Nat.Primes → ZMod (l ^ n),
      (cyclotomicPowDirichlet l e ψ g : O) • derivativeSum e ψ L S d G =
        derivativeSum e ψ L S f G' := by
  have a_unit {q : Nat.Primes} (hq : q ∈ S) : IsUnit (a : ZMod q) :=
    ⟨unitsMap (hS q hq) (cyclotomicCharMod Ω M g),
      by rw [unitsMap_val, hg, cast_natCast (hS q hq) a]⟩
  -- The new shift at `q` is `L q v + d q`, where `v` is the unit of `ℤ/q` given by `a`.
  let v (q : Nat.Primes) : (ZMod q)ˣ := invFun Units.val (a : ZMod q)
  have hv (q : Nat.Primes) (hq : q ∈ S) : (v q : ZMod q) = a := invFun_eq (a_unit hq)
  exact ⟨fun q ↦ (L q (v q)).toAdd + d q, cyclotomicPowDirichlet_smul_derivativeSum hM hS
    (cyclotomicCharMod_eq_of_dvd hM hg) (fun q hq ↦ ⟨v q, rfl, hv q hq⟩) hG⟩

/-- Let `M` be a multiple of `N lⁿ`, let the natural number `a` represent the cyclotomic character
of `g ∈ Gal(ℚ̄/ℚ)` mod `N lⁿ`, and let `s : ℚ/ℤ → ℤ` and `G : ℚ/ℤ → ℤ/lⁿ` satisfy
`G x = a s(x) - s(a x)` on the `M`-torsion. Suppose that the character sum
`∑_u G(u / N lⁿ) uᵉ ψ(u)` of `G` (`derivativeSum` for no primes) vanishes in `O/lⁿ`
(`QuotSpan (l ^ n : O)`), where `u` runs over the units mod `N lⁿ`. Then `cycᵉ⁺¹ ψ (g) - 1`
(`cyclotomicPowDirichlet l (e + 1) ψ g - 1`) kills the character sum `∑_u s(u / N lⁿ) uᵉ ψ(u)` of
`s` in `O/lⁿ`. -/
lemma sub_one_smul_sum_eq_zero (hM : N * l ^ n ∣ M)
    (hg : (cyclotomicCharMod Ω (N * l ^ n) g : ZMod (N * l ^ n)) = a) {s : QZ → ℤ}
    (hG : ∀ {x : QZ}, M • x = 0 → a • (s x : ZMod (l ^ n)) - G x = s (a • x))
    (h_zero : derivativeSum e ψ L ∅ d G = 0) :
    (cyclotomicPowDirichlet l (e + 1) ψ g - 1 : O) •
        ((∑ u : (ZMod (N * l ^ n))ˣ, s (ofZMod (N * l ^ n) u) *
            ((u : ZMod (N * l ^ n)).val ^ e * ψ (u : ZMod (N * l ^ n)).val) : O) :
          QuotSpan (l ^ n : O)) =
      (0 : QuotSpan (l ^ n : O)) := by
  -- Let `Λ` be the character sum and `F` be `s` mod `lⁿ`. Equivariance gives
  -- `cycᵉ ψ (g) Λ (a F - G) = Λ F`, and the left side is `cycᵉ⁺¹ ψ (g) Λ F` since `Λ G = 0`.
  let F : QZ → ZMod (l ^ n) := fun x : QZ ↦ s x
  have killed {x : QuotSpan (l ^ n : O)} : l ^ n • x = 0 := nsmul_quot_eq_zero dvd_rfl x
  have h_sum : ((∑ u : (ZMod (N * l ^ n))ˣ, s (ofZMod (N * l ^ n) u) *
        ((u : ZMod (N * l ^ n)).val ^ e * ψ (u : ZMod (N * l ^ n)).val) : O) :
      QuotSpan (l ^ n : O)) = derivativeSum e ψ L ∅ d F := by
    rw [derivativeSum_empty, map_sum]
    refine sum_congr rfl fun u _ ↦ ?_
    simp only [F, Algebra.smul_def, map_mul, map_pow, map_natCast, map_intCast, Nat.cast_pow]
    ring
  have h_equiv : (cyclotomicPowDirichlet l e ψ g : O) • derivativeSum e ψ L ∅ d (a • F - G) =
      derivativeSum e ψ L ∅ d F :=
    cyclotomicPowDirichlet_smul_derivativeSum hM (by simp) hg (by simp) hG
  have h_sub : derivativeSum e ψ L ∅ d (a • F - G) = a • derivativeSum e ψ L ∅ d F := by
    rw [map_sub, map_nsmul, h_zero, sub_zero]
  -- On `O/lⁿ`, `cycᵉ⁺¹ ψ (g)` acts as `aᵉ⁺¹ ψ(a)` and `cycᵉ ψ (g)` as `aᵉ ψ(a)`.
  have h_scalar : (cyclotomicPowDirichlet l (e + 1) ψ g : O) • derivativeSum e ψ L ∅ d F =
      (cyclotomicPowDirichlet l e ψ g : O) • a • derivativeSum e ψ L ∅ d F := by
    rw [cyclotomicPowDirichlet_smul hg killed, cyclotomicPowDirichlet_smul hg killed]
    module
  rw [h_sum, sub_smul, one_smul, h_scalar, ← h_sub, h_equiv, sub_self]

end Derivative

section CommutatorLog

/-- The exponent `t` with `γ y / (g γ g⁻¹) y = ζᵗ`, for the fixed primitive `m`-th root of unity
`ζ` of `New.rootPowHom`, when this quotient is an `m`-th root of unity (otherwise some value that
is of no use). -/
noncomputable def commutatorLog (m : ℕ) [NeZero m] (γ : Gal(Ω/ℚ)) (y : DiscreteUnits Ω)
    (g : Gal(Ω/ℚ)) : ZMod m :=
  invFun (rootPowHom Ω m).1 (galUnitsRep γ y - galUnitsRep (g * γ * g⁻¹) y)

/-- If the commutator `γ⁻¹ (g γ g⁻¹)` moves `y` by an `m`-th root of unity, then `commutatorLog`
is the exponent of `γ y / (g γ g⁻¹) y`: `ζ ^ commutatorLog m γ y g = γ y / (g γ g⁻¹) y`. -/
lemma rootPowHom_commutatorLog (hy : m • (galUnitsRep (γ⁻¹ * conj g γ) y - y) = 0) :
    (rootPowHom Ω m).val (commutatorLog m γ y g) =
      galUnitsRep γ y - galUnitsRep (g * γ * g⁻¹) y := by
  obtain ⟨-, μ_range⟩ : Injective (rootPowHom Ω m).val ∧
      ∀ z : DiscreteUnits Ω, z ∈ (rootPowHom Ω m).val.range ↔ m • z = 0 := (rootPowHom Ω m).prop
  -- Applying `γ` to `hy` shows that `γ y / (g γ g⁻¹) y` is an `m`-th root of unity.
  have h_root : m • (galUnitsRep γ y - galUnitsRep (g * γ * g⁻¹) y) = 0 := by
    simpa [smul_sub] using congr_arg (fun z : DiscreteUnits Ω ↦ -galUnitsRep γ z) hy
  exact invFun_eq ((μ_range _).mpr h_root)

/-- `commutatorLog m γ y g` is locally constant in `g`, since the orbit map `g ↦ (g γ g⁻¹) y` is. -/
lemma isLocallyConstant_commutatorLog : IsLocallyConstant (commutatorLog m γ y) := by
  -- The orbit map of `y` under the conjugates of `γ` is locally constant, read in `Ω`.
  have h_orbit_val : IsLocallyConstant fun g : Gal(Ω/ℚ) ↦ (g * γ * g⁻¹) • (y.toMul : Ω) :=
    (isLocallyConstant_smul (y.toMul : Ω)).comp_continuous (by fun_prop)
  have orbit : IsLocallyConstant fun g : Gal(Ω/ℚ) ↦ galUnitsRep (g * γ * g⁻¹) y :=
    .desc _ (fun z : DiscreteUnits Ω ↦ (z.toMul : Ω)) h_orbit_val fun _ _ ↦ DiscreteUnits.ext
  exact orbit.comp fun z : DiscreteUnits Ω ↦ invFun (rootPowHom Ω m).val (galUnitsRep γ y - z)

/-- The cocycle rule. Let `g` act on the `m`-th roots of unity by `a`, and let `g y / y'` be an
`m`-th root of unity. If `ζᵗ = γ y / (g' γ g'⁻¹) y`, `ζˢ = γ y' / (g g' γ (g g')⁻¹) y'` and
`ζ ^ s' = γ y' / (g γ g⁻¹) y'`, where `ζ ^ t` is `rootPowHom Ω m t`, then `a t = s - s'`. -/
lemma nsmul_exponent_eq_sub {g' : Gal(Ω/ℚ)} {y' : DiscreteUnits Ω} {t s s' : ZMod m}
    (hg : (cyclotomicCharMod Ω m g : ZMod m) = a) (hgy : m • (galUnitsRep g y - y') = 0)
    (ht : (rootPowHom Ω m).val t = galUnitsRep γ y - galUnitsRep (g' * γ * g'⁻¹) y)
    (hs : (rootPowHom Ω m).val s = galUnitsRep γ y' - galUnitsRep (g * g' * γ * (g * g')⁻¹) y')
    (hs' : (rootPowHom Ω m).val s' = galUnitsRep γ y' - galUnitsRep (g * γ * g⁻¹) y') :
    a • t = s - s' := by
  obtain ⟨μ_inj, μ_range⟩ : Injective (rootPowHom Ω m).val ∧
      ∀ z : DiscreteUnits Ω, z ∈ (rootPowHom Ω m).val.range ↔ m • z = 0 := (rootPowHom Ω m).prop
  -- `g` raises the `m`-th root of unity `ζᵗ` to the power `a`.
  have g_pow : galUnitsRep g ((rootPowHom Ω m).val t) = a • (rootPowHom Ω m).val t :=
    cyclotomicCharMod_eq_iff_unitsRep.mp hg ((μ_range _).mp ⟨t, rfl⟩)
  -- Apply `g` to `ζᵗ`; conjugates of `γ` act alike on the root of unity `g y / y'`.
  apply μ_inj
  show (rootPowHom Ω m).val (a • t) = (rootPowHom Ω m).val (s - s')
  linear_combination (norm := skip) galUnitsRep_conj_of_nsmul_eq_zero γ (g * g') hgy -
    galUnitsRep_conj_of_nsmul_eq_zero γ g hgy - g_pow
  -- `-nsmul_eq_mul` keeps `a •` outside `rootPowHom`, where `abel` can match it.
  simp [ht, hs, hs', -nsmul_eq_mul]
  abel

/-- Let `B` lie above the prime `q` and let `M` be a unit at `B`. For a unit `v` mod `q` there is
an element `τ` of the inertia group of `B` whose cyclotomic character mod `q M`, acting on `ℚ/ℤ`,
sends `x + v u / q` to `x + u / q` for every `x` in the `M`-torsion and every `u` mod `q`. -/
lemma exists_inertia_smul_add_ofZMod [NeZero M] {q : Nat.Primes} (hq : B.valuation (q : Ω) < 1)
    (hM : B.valuation M = 1) (v : (ZMod q)ˣ) :
    ∃ τ ∈ inertiaGroup Gal(Ω/ℚ) B, ∀ x : QZ, M • x = 0 → ∀ u : ZMod q,
      (cyclotomicCharMod Ω (q * M) τ : ZMod (q * M)).val • (x + ofZMod q (v * u)) =
        x + ofZMod q u := by
  -- Take `τ` with `cyc_q τ = v⁻¹`; it fixes the `M`-th roots of unity, as `M` is a unit at `B`.
  obtain ⟨τ, hτ, cyc_τ⟩ := exists_inertia_cyclotomicChar_eq hq (val_coe_unit_coprime v⁻¹).symm
  refine ⟨τ, hτ, fun x hx u ↦ ?_⟩
  obtain ⟨b, rfl⟩ := exists_ofZMod hx
  -- The character of `τ` is `1` mod `M` and `v⁻¹` mod `q`.
  have cyc_M : (cyclotomicCharMod Ω M τ : ZMod M) = (1 : ℕ) := hτ.cyclotomicCharMod_eq hM
  have cyc_mod_q : (cyclotomicCharMod Ω q τ : ZMod q) = ((v⁻¹ : (ZMod q)ˣ) : ZMod q).val :=
    cyclotomicCharMod_eq_of_dvd (dvd_pow_self (q : ℕ) one_ne_zero)
      ((pow_dvd_cyclotomicChar_sub_iff 1).mp (by simp only [cyc_τ, sub_self, dvd_zero]))
  -- Without `-inv_coe_unit` this `simp` call loops.
  simp [← map_nsmul, ← cyclotomicCharMod_eq_of_dvd _ zmod_eq_natCast_val, cyc_M, cyc_mod_q,
    -inv_coe_unit]

/-- Let `g` lie in the inertia group of a place `B` at which `m` is a unit, let `γ` act on the
`m`-th roots of unity by `a`, and let `g r / r = ζᵇ`. Suppose that `g y / y` and `γ y / y'` are
`m`-th roots of unity, and that `(y / rˢ)ᵐ` and `(y' / r ^ s')ᵐ` are units at `B`. If
`γ y / (g γ g⁻¹) y = ζᵗ`, then `t = a s b - s' b`. Here `ζ ^ t` is `rootPowHom Ω m t`. -/
lemma exponent_eq_of_inertia {γ : Gal(Ω/ℚ)} {y y' r : DiscreteUnits Ω} {b t : ZMod m} {s s' : ℤ}
    (hg : IsFrob B 1 g) (hm : B.valuation m = 1) (hγ : (cyclotomicCharMod Ω m γ : ZMod m) = a)
    (hr : galUnitsRep g r - r = (rootPowHom Ω m).val b)
    (hgy : m • (galUnitsRep g y - y) = 0) (hγy : m • (galUnitsRep γ y - y') = 0)
    (hy : B.valuation ((m • (y - s • r)).toMul : Ω) = 1)
    (hy' : B.valuation ((m • (y' - s' • r)).toMul : Ω) = 1)
    (ht : (rootPowHom Ω m).val t = galUnitsRep γ y - galUnitsRep (g * γ * g⁻¹) y) :
    a • (s * b) - t = s' * b := by
  -- Reduce modulo `B`, where the `m`-th roots of unity stay distinct and `g` fixes the units.
  have g_fix : galUnitsRep g (galUnitsRep γ y - y') = 1 • (galUnitsRep γ y - y') :=
    cyclotomicCharMod_eq_iff_unitsRep.mp (hg.cyclotomicCharMod_eq hm) hγy
  have γ_pow : galUnitsRep γ (galUnitsRep g y - y) = a • (galUnitsRep g y - y) :=
    cyclotomicCharMod_eq_iff_unitsRep.mp hγ hgy
  have h_mem : galUnitsRep g (y' - s' • r) - 1 • (y' - s' • r) -
      a • (galUnitsRep g (y - s • r) - 1 • (y - s • r)) ∈ principalUnits B :=
    sub_mem (hg.sub_nsmul_mem_principalUnits hy')
      (nsmul_mem (hg.sub_nsmul_mem_principalUnits hy) a)
  have h_eq : (rootPowHom Ω m).val (a • (s * b) - t - s' * b) =
      galUnitsRep g (y' - s' • r) - 1 • (y' - s' • r) -
        a • (galUnitsRep g (y - s • r) - 1 • (y - s • r)) := by
    linear_combination (norm := skip) g_fix - γ_pow + galUnitsRep_conj_of_nsmul_eq_zero γ g hgy
    -- `-nsmul_eq_mul` keeps `a •` outside `rootPowHom`, where `abel` can match it.
    simp [ht, ← hr, ← zsmul_eq_mul, smul_sub, -nsmul_eq_mul]
    abel
  exact eq_of_mem_principalUnits hm (by rwa [h_eq])

end CommutatorLog

section Telescoping

/-- Let `τ` lie in the inertia group of `B` and let `φ` be a `q`-Frobenius at `B`. Let the `Y b`,
for `b` mod `q`, have `m`-th powers that are units at `B` and congruent to each other modulo `B`,
and let `lg (v u) ≡ lg u + 1 mod m` for the units `u` mod `q`. Then
`∏_b Y b / φ (Y 0) · ∏_u (τ Y(v u) / Y u) ^ lg u` is a principal unit at `B`. -/
lemma telescoping_mem_principalUnits (hτ : IsFrob B 1 τ) (hφ : IsFrob B q φ)
    (h_unit : ∀ b : ZMod q, B.valuation ((m • Y b).toMul : Ω) = 1)
    (h_cong : ∀ b : ZMod q, m • (Y b - Y 0) ∈ principalUnits B)
    (hlg : ∀ u : (ZMod q)ˣ, (m : ℤ) ∣ lg (v * u) - lg u - 1) :
    ∑ b : ZMod q, Y b - galUnitsRep φ (Y 0) +
        ∑ u : (ZMod q)ˣ, lg u • (galUnitsRep τ (Y (v * u)) - Y u) ∈
      principalUnits B := by
  -- Modulo `B`, `τ` acts trivially on units and `φ` as the `q`-th power; the sum over `u`
  -- telescopes.
  have h_quot : ∀ u : (ZMod q)ˣ, ∃ k : ℤ, lg (v * u) - lg u - 1 = m * k := hlg
  choose k hk using h_quot
  have inertia (b : ZMod q) : galUnitsRep τ (Y b) - 1 • Y b ∈ principalUnits B :=
    hτ.sub_nsmul_mem_principalUnits (h_unit b)
  have frobenius : galUnitsRep φ (Y 0) - (q : ℕ) • Y 0 ∈ principalUnits B :=
    hφ.sub_nsmul_mem_principalUnits (h_unit 0)
  have h_mem : ∑ u : (ZMod q)ˣ, (lg u • (galUnitsRep τ (Y (v * u)) - 1 • Y (v * u)) -
      k u • m • (Y (v * u) - Y 0)) - (galUnitsRep φ (Y 0) - (q : ℕ) • Y 0) ∈ principalUnits B :=
    sub_mem (sum_mem fun u _ ↦
      sub_mem (zsmul_mem (inertia (v * u)) (lg u)) (zsmul_mem (h_cong (v * u)) (k u))) frobenius
  -- Reindex the sum by `u ↦ v u`; the exponents telescope by `hk`.
  have h_eq : ∑ b : ZMod q, Y b - galUnitsRep φ (Y 0) +
        ∑ u : (ZMod q)ˣ, lg u • (galUnitsRep τ (Y (v * u)) - Y u) =
      ∑ u : (ZMod q)ˣ, (lg u • (galUnitsRep τ (Y (v * u)) - 1 • Y (v * u)) -
        k u • m • (Y (v * u) - Y 0)) - (galUnitsRep φ (Y 0) - (q : ℕ) • Y 0) := by
    simp_rw [← natCast_zsmul, ← mul_zsmul', ← hk]
    linear_combination (norm := skip) Equiv.sum_comp (.mulLeft v) fun u ↦ lg u • (Y u - Y 0) - Y u
    simp [sub_smul, smul_sub, sub_nsmul, q.prop.one_le, Nat.totient_prime q.prop,
      sum_eq_add_sum_units]
    abel
  rw [h_eq]
  exact h_mem

open Pointwise in
/-- The congruence behind the relation between Frobenius and inertia. Let `B` lie above `q`, let `τ`
lie in its inertia group, let `φ` be a `q`-Frobenius at `B`, and let `γ ∈ Gal(Ω/ℚ)` and `y ∈ Ωˣ`.
Let `Y : ℤ/q → Ωˣ` be such that at every place above `q`, `Y bᵐ` is a unit and `(Y b / Y 0)ᵐ` is a
principal unit. Let `v` be a unit mod `q` and `lg` satisfy `lg (v u) ≡ lg u + 1 mod m`. Suppose
`φ (Y 0) / y` and `τ Y(v u) / Y u` are `m`-th roots of unity, and `(∏_b Y b / y)ᵐ` is a root of
unity. Then `∏_u (γ Y u / τγτ⁻¹ Y u) ^ lg u ≡ γ y / φγφ⁻¹ y` modulo `B`, i.e. their quotient is a
principal unit at `B`. -/
lemma derivative_sub_frob_mem_principalUnits (γ : Gal(Ω/ℚ)) (hq : B.valuation (q : Ω) < 1)
    (hτ : IsFrob B 1 τ) (hφ : IsFrob B q φ)
    (h_unit : ∀ A : ClosurePlace, A.valuation (q : Ω) < 1 →
      ∀ b : ZMod q, A.valuation ((m • Y b).toMul : Ω) = 1)
    (h_cong : ∀ A : ClosurePlace, A.valuation (q : Ω) < 1 →
      ∀ b : ZMod q, m • (Y b - Y 0) ∈ principalUnits A)
    (hlg : ∀ u : (ZMod q)ˣ, (m : ℤ) ∣ lg (v * u) - lg u - 1)
    (hφY : m • (galUnitsRep φ (Y 0) - y) = 0)
    (hτY : ∀ u : ZMod q, m • (galUnitsRep τ (Y (v * u)) - Y u) = 0)
    (h_dist : IsOfFinAddOrder (m • (∑ b : ZMod q, Y b - y))) :
    ∑ u : (ZMod q)ˣ, lg u • (galUnitsRep γ (Y u) - galUnitsRep (τ * γ * τ⁻¹) (Y u)) -
      (galUnitsRep γ y - galUnitsRep (φ * γ * φ⁻¹) y) ∈ principalUnits B := by
  -- `W δ` is the telescoping product for `τ` and `φ` conjugated by `δ`; it is a principal unit at
  -- `δ B`. The wanted quotient is `γ (W 1) / γ (W γ⁻¹)`.
  let W (δ : Gal(Ω/ℚ)) : DiscreteUnits Ω :=
    ∑ b : ZMod q, Y b - galUnitsRep (δ * φ * δ⁻¹) (Y 0) +
      ∑ u : (ZMod q)ˣ, lg u • (galUnitsRep (δ * τ * δ⁻¹) (Y (v * u)) - Y u)
  have W_mem (δ : Gal(Ω/ℚ)) : galUnitsRep δ⁻¹ (W δ) ∈ principalUnits B := by
    have hqδ : (δ • B).valuation (q : Ω) < 1 := by simpa using (smul_apply_smul_lt_one_iff δ).mpr hq
    have W_conj : W δ ∈ principalUnits (δ • B) :=
      telescoping_mem_principalUnits (hτ.conj δ) (hφ.conj δ) (h_unit _ hqδ) (h_cong _ hqδ) hlg
    -- `δ` carries `B` to `δ B` and `δ⁻¹ (W δ)` to `W δ`.
    rw [mem_principalUnits_iff, ← smul_apply_smul_lt_one_iff δ]
    simpa [val_toMul_galUnitsRep, smul_sub] using mem_principalUnits_iff.mp W_conj
  -- `W 1` is a root of unity by the distribution relation, so `γ` acts on it by a power.
  obtain ⟨k, k_pos, hk⟩ := h_dist.exists_nsmul_eq_zero
  have hk_ne : NeZero k := NeZero.of_pos k_pos
  have h_diff : k • m • (∑ b : ZMod q, Y b - y) - k • m • (galUnitsRep φ (Y 0) - y) = 0 := by
    rw [hk, hφY, smul_zero, sub_zero]
  have root : (k * m) • W 1 = 0 := by
    simpa [W, ← smul_sub, smul_sum, smul_comm _ (lg _), hτY, mul_smul] using h_diff
  have γ_mem : galUnitsRep γ (W 1) ∈ principalUnits B := by
    rw [cyclotomicCharMod_eq_iff_unitsRep.mp zmod_eq_natCast_val root]
    exact nsmul_mem (by simpa using W_mem 1) _
  -- Conjugating by `φ` and `τ` does not change how `γ` acts on these roots of unity.
  have h_conj_τ : ∑ u : (ZMod q)ˣ, lg u • galUnitsRep γ (galUnitsRep τ (Y (v * u)) - Y u) =
      ∑ u : (ZMod q)ˣ, lg u • galUnitsRep (τ * γ * τ⁻¹) (galUnitsRep τ (Y (v * u)) - Y u) :=
    sum_congr rfl fun u _ ↦ by rw [galUnitsRep_conj_of_nsmul_eq_zero γ τ (hτY u)]
  have h_eq : ∑ u : (ZMod q)ˣ, lg u • (galUnitsRep γ (Y u) - galUnitsRep (τ * γ * τ⁻¹) (Y u)) -
        (galUnitsRep γ y - galUnitsRep (φ * γ * φ⁻¹) y) =
      galUnitsRep γ (W 1) - galUnitsRep γ⁻¹⁻¹ (W γ⁻¹) := by
    linear_combination (norm := skip) galUnitsRep_conj_of_nsmul_eq_zero γ φ hφY - h_conj_τ
    simp [W, smul_sub]
    abel
  rw [h_eq]
  exact sub_mem γ_mem (W_mem γ⁻¹)

end Telescoping

end

section Cocycles

variable {O : Type} [CommRing O] {B : ClosurePlace} {M N l n e : ℕ} [NeZero N] [Fact l.Prime]
  [Algebra ℤ_[l] O] {ψ : DirichletCharacter O N} [Algebra (ZMod (l ^ n)) (QuotSpan (l ^ n : O))]
  {L : ∀ q : Nat.Primes, (ZMod q)ˣ →* Multiplicative (ZMod (l ^ n))}
  {p : Nat.Primes} {c : ℕ} {γ : Gal(Ω/ℚ)} {y : QZ → DiscreteUnits Ω} [NeZero M]

/-- A Kolyvagin system for the character `χ`, the element `γ`, the prime `p` and the set of primes
`P`: cocycles `κ S`, one for each `S ⊆ P`, that are unramified over `ℚ(ζ_N)` away from `l`, `p` and
`S`, vanish at `γ`, and are linked by the relation between Frobenius and inertia at the primes of
`P`. -/
structure IsKolyvaginSystem {V : Type} [AddCommGroup V] [Module O V] (χ : Gal(Ω/ℚ) →* Oˣ)
    (γ : Gal(Ω/ℚ)) (N l : ℕ) [NeZero N] (p : Nat.Primes) (P : Finset Nat.Primes)
    (κ : Finset Nat.Primes → Gal(Ω/ℚ) → V) : Prop where
  /-- `κ S` is a locally constant `χ`-cocycle that vanishes on inertia over `ℚ(ζ_N)` at the places
  above neither `l`, `p` nor a prime of `S`. -/
  mem_vanishingCocycles : ∀ S ⊆ P, κ S ∈ vanishingCocycles χ V (inertiaOff N l (insert p S))
  /-- `κ S` vanishes at `γ`. -/
  apply_eq_zero : ∀ S ⊆ P, κ S γ = 0
  /-- For `q ∈ P ∖ S` and a Frobenius `φ` at a place `A` above `q`, `κ S φ` is a value of
  `κ (S ∪ {q})` on inertia at `A`. -/
  exists_mem_inertiaGroup_eq : ∀ S ⊆ P, ∀ q ∈ P, q ∉ S →
    ∀ (A : ClosurePlace) (φ : Gal(Ω/ℚ)), IsFrob A q φ → A.valuation (q : Ω) < 1 →
    ∃ τ ∈ inertiaGroup Gal(Ω/ℚ) A, κ (insert q S) τ = κ S φ

/-!
## The cocycles at one level

In this section `y : ℚ/ℤ → Ω^×` is a family whose `lⁿ`-th powers `lⁿ • y` form a Jacobi family
(`New.OddPart.IsJacobiFamily`) at a level `M` (for `x` killed by `M`: `σ J(x) = J(a x)` if `σ` acts
on `μ_M` by `a`; `J x` is a unit at places prime to `p` and has order `floorDiff c x` at `B`), and
`commutatorLog (l ^ n) γ (y x) g` is the exponent `t` with `γ y(x) / (g γ g⁻¹) y(x) = ζᵗ`, for the
fixed primitive `lⁿ`-th root of unity `ζ`.
-/

omit [Fact l.Prime] in
/-- Let `lⁿ • y` be a Jacobi family at level `M`. If `σ` raises the `M`-th roots of unity to the
power `a`, then `σ (y x) / y (a x)` is an `lⁿ`-th root of unity, for every `x` killed by `M`. -/
private lemma nsmul_galUnitsRep_sub_eq_zero_of_isJacobiFamily
    (hJ : IsJacobiFamily p B c M (l ^ n • y)) {x : QZ} (hx : M • x = 0) (σ : Gal(Ω/ℚ)) (a : ℕ)
    (ha : (cyclotomicCharMod Ω M σ).val = a) :
    l ^ n • (galUnitsRep σ (y x) - y (a • x)) = 0 := by
  rw [smul_sub, ← map_nsmul, sub_eq_zero]
  exact hJ.galUnitsRep_apply hx σ a ha

/-- Let `lⁿ • y` be a Jacobi family at level `M` and let `x` be killed by `M`. Then `commutatorLog`
names the root of unity `γ y(x) / (g γ g⁻¹) y(x)`: its image under `rootPowHom Ω (l ^ n)` is this
quotient. -/
private lemma rootPowHom_commutatorLog_of_isJacobiFamily
    (hJ : IsJacobiFamily p B c M (l ^ n • y)) {x : QZ} (hx : M • x = 0) (g : Gal(Ω/ℚ)) :
    (rootPowHom Ω (l ^ n)).val (commutatorLog (l ^ n) γ (y x) g) =
      galUnitsRep γ (y x) - galUnitsRep (g * γ * g⁻¹) (y x) := by
  -- The commutator `γ⁻¹ g γ g⁻¹` fixes the `M`-th roots of unity.
  have h_comm : (cyclotomicCharMod Ω M (γ⁻¹ * conj g γ)).val = (1 : ℕ) := by simp [mul_comm]
  have h_fixed : l ^ n • (galUnitsRep (γ⁻¹ * conj g γ) (y x) - y x) = 0 := by
    simpa using nsmul_galUnitsRep_sub_eq_zero_of_isJacobiFamily hJ hx (γ⁻¹ * conj g γ) 1 h_comm
  exact rootPowHom_commutatorLog h_fixed

/-- The distribution relation for the exponents. Let `lⁿ • y` be a Jacobi family at level `M` and
let `r ∣ M` be a prime with `r ≡ 1 mod c`. Then, for every `x` killed by `M`, the exponents
`commutatorLog (l ^ n) γ (y ·) g` at the translates `x + b / r` sum to the exponent at `r x`. -/
private lemma sum_commutatorLog_add_ofZMod_eq_of_isJacobiFamily
    (hJ : IsJacobiFamily p B c M (l ^ n • y)) {r : Nat.Primes} (hrM : (r : ℕ) ∣ M)
    (hr_one : (r : ℕ) ≡ 1 [MOD c]) (g : Gal(Ω/ℚ)) {x : QZ} (hx : M • x = 0) :
    ∑ b : ZMod r, commutatorLog (l ^ n) γ (y (x + ofZMod r b)) g =
      commutatorLog (l ^ n) γ (y ((r : ℕ) • x)) g := by
  -- The quotient `D = ∏_b y(x + b/r) / y(r x)` has finite order, so `γ` and `g γ g⁻¹` act alike on
  -- it; under `rootPowHom` the two sides differ by `γ D / (g γ g⁻¹) D`.
  have μ_inj : Injective (rootPowHom Ω (l ^ n)).val := (rootPowHom Ω (l ^ n)).property.left
  let D : DiscreteUnits Ω := ∑ b : ZMod r, y (x + ofZMod r b) - y ((r : ℕ) • x)
  have h_order : IsOfFinAddOrder (l ^ n • D) := by
    simpa [D, smul_sub, smul_sum] using
      hJ.isOfFinAddOrder_sum_sub hx r hrM hr_one.coprime_of_modEq_one.symm
  obtain ⟨k, k_pos, hk⟩ := (h_order.of_nsmul (NeZero.ne _)).exists_nsmul_eq_zero
  have hk_neZero : NeZero k := .of_pos k_pos
  have h_conj : galUnitsRep γ D = galUnitsRep (g * γ * g⁻¹) D :=
    galUnitsRep_conj_of_nsmul_eq_zero γ g hk
  have h_level (b : ZMod r) : M • (x + ofZMod r b) = 0 := by
    simp [← map_nsmul, (natCast_eq_zero_iff M r).mpr hrM, hx]
  have h_level_r : M • ((r : ℕ) • x) = 0 := by simp [smul_comm M, hx]
  apply μ_inj
  simp only [map_sum, rootPowHom_commutatorLog_of_isJacobiFamily hJ (h_level _),
    rootPowHom_commutatorLog_of_isJacobiFamily hJ h_level_r]
  simpa only [D, map_sub, map_sum, sum_sub_distrib, sub_sub_sub_comm, sub_eq_sub_iff_sub_eq_sub]
    using h_conj

/-- Let `lⁿ • y` be a Jacobi family at level `M`, with `N lⁿ ∣ M`, and let every prime of `I` divide
`M` and be `≡ 1 mod c N lⁿ`. For `S ⊆ I`, the derivative sum `derivativeSum e ψ L S d` of the
exponents `x ↦ commutatorLog (l ^ n) γ (y x) g` does not depend on the shifts `d` (the sum at
`q ∈ S` carries the weights `L q u - d q`). -/
private lemma derivativeSum_commutatorLog_eq_of_isJacobiFamily
    (hJ : IsJacobiFamily p B c M (l ^ n • y)) (hM : N * l ^ n ∣ M) {I : Finset Nat.Primes}
    (hI_dvd : ∀ q ∈ I, (q : ℕ) ∣ M) (hI_one : ∀ q ∈ I, (q : ℕ) ≡ 1 [MOD c * (N * l ^ n)])
    (g : Gal(Ω/ℚ)) {S : Finset Nat.Primes} (hS : S ⊆ I) (d f : Nat.Primes → ZMod (l ^ n)) :
    derivativeSum e ψ L S d (fun x : QZ ↦ commutatorLog (l ^ n) γ (y x) g) =
      derivativeSum e ψ L S f (fun x : QZ ↦ commutatorLog (l ^ n) γ (y x) g) := by
  -- By the distribution relation at `r ∈ I`, summing over the translates by `b / r` only changes
  -- the shifts (`derivativeSum_eq_of_prime`); `shift_indep_of_distribution` does the rest.
  refine shift_indep_of_distribution (Λ := derivativeSum e ψ L) (L := fun q u ↦ (L q u).toAdd)
    (I := I) (fun hqT _ _ ↦ derivativeSum_insert hqT) ?_ ?_ hS
  · intro T d' f' hT h_shift G G' hG
    exact derivativeSum_congr hM (fun q hq ↦ hI_dvd q (hT hq)) h_shift fun {x} _ ↦ hG x
  · intro r hr T hTI hrT d'
    exact ⟨_, derivativeSum_eq_of_prime hM (fun q hq ↦ hI_dvd q (hTI hq)) (hI_one r hr).of_mul_left
      hrT (sum_commutatorLog_add_ofZMod_eq_of_isJacobiFamily hJ (hI_dvd r hr)
        (hI_one r hr).of_mul_right g)⟩

/-- Let `lⁿ • y` be a Jacobi family at level `M` with `lⁿ ∣ M`, and let `g` lie in the inertia group
(`IsFrob A 1 g`) of a place `A` prime to `l`, fix the `M`-th roots of unity and have `g r / r = ζᵇ`.
If `y x ^ lⁿ` is a unit at `A` times `r ^ (lⁿ floorDiff c x)` for every `x` killed by `M`, then
`commutatorLog (l ^ n) γ (y x) g = (a floorDiff c x - floorDiff c (a x)) b` for such `x`, where `γ`
raises the `M`-th roots of unity to the power `a`. -/
private lemma nsmul_floorDiff_mul_sub_commutatorLog_eq_of_isFrob
    (hJ : IsJacobiFamily p B c M (l ^ n • y)) (hM : l ^ n ∣ M) {a : ℕ}
    (ha : (cyclotomicCharMod Ω M γ).val = a) {g : Gal(Ω/ℚ)} {A : ClosurePlace}
    (hg_cyc : cyclotomicCharMod Ω M g = 1) (hg_inertia : IsFrob A 1 g)
    (hl : A.valuation (l ^ n : ℕ) = 1) {b : ZMod (l ^ n)} {r : DiscreteUnits Ω}
    (hr : galUnitsRep g r - r = (rootPowHom Ω (l ^ n)).val b)
    (h_unit : ∀ {x : QZ}, M • x = 0 → A.valuation (l ^ n • (y x - floorDiff c x • r)).toMul.val = 1)
    {x : QZ} (hx : M • x = 0) :
    a • (floorDiff c x * b) - commutatorLog (l ^ n) γ (y x) g = floorDiff c (a • x) * b := by
  have h_gy : l ^ n • (galUnitsRep g (y x) - y x) = 0 := by
    simpa using nsmul_galUnitsRep_sub_eq_zero_of_isJacobiFamily hJ hx g 1 (by simp [hg_cyc])
  have h_γy : l ^ n • (galUnitsRep γ (y x) - y (a • x)) = 0 :=
    nsmul_galUnitsRep_sub_eq_zero_of_isJacobiFamily hJ hx γ a ha
  have hax : M • a • x = 0 := by simp [smul_comm M, hx]
  exact exponent_eq_of_inertia hg_inertia hl (cyclotomicCharMod_eq_of_dvd hM ha) hr h_gy h_γy
    (h_unit hx) (h_unit hax) (rootPowHom_commutatorLog_of_isJacobiFamily hJ hx g)

/-- The relation for the character sum. Let `B` lie above `p ≡ 1 mod N lⁿ`, and let `lⁿ • y` be a
Jacobi family at level `N lⁿ` for `p`, `B` and `c`. If the derivative sum over no primes of the
exponents `x ↦ commutatorLog (l ^ n) γ (y x) τ` vanishes for every `τ` in the inertia group of `B`,
then `(Υ γ - 1) ∑ floorDiff c (a / N lⁿ) aᵉ ψ(a) = 0` in `O/lⁿ`, where `Υ = cyc^(e+1) ψ` and `a`
runs over the units mod `N lⁿ`. -/
private lemma cyclotomicPowDirichlet_sub_one_smul_sum_eq_zero_of_isJacobiFamily
    (hJ : IsJacobiFamily p B c (N * l ^ n) (l ^ n • y)) (hpB : B.valuation p < 1)
    (hp_one : (p : ℕ) ≡ 1 [MOD N * l ^ n])
    (h_vanish : ∀ τ ∈ inertiaGroup Gal(Ω/ℚ) B,
      derivativeSum e ψ L ∅ 0 (fun x : QZ ↦ commutatorLog (l ^ n) γ (y x) τ) = 0) :
    (cyclotomicPowDirichlet l (e + 1) ψ γ - 1 : O) •
        ((∑ a : (ZMod (N * l ^ n))ˣ, floorDiff c (ofZMod (N * l ^ n) a) *
            ((a : ZMod (N * l ^ n)).val ^ e * ψ (a : ZMod (N * l ^ n)).val) : O) :
          QuotSpan (l ^ n : O)) =
      (0 : QuotSpan (l ^ n : O)) := by
  -- Take `τ` in the inertia group at `B` moving an `lⁿ`-th root `r` of a uniformiser by `ζ`. As
  -- `y x ^ lⁿ` is a unit times `r ^ (lⁿ floorDiff c x)`, the exponent of `y x` at `τ` is
  -- `a floorDiff c x - floorDiff c (a x)`, where `a` is the cyclotomic character of `γ`.
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (cyclotomicCharMod Ω (N * l ^ n) γ).val = a := ⟨_, zmod_eq_natCast_val⟩
  obtain ⟨v, hv, -⟩ := exists_isPlaceOver_prime hpB
  obtain ⟨τ, hτ, π, r, unif, hr, τ_r⟩ := exists_isTameGeneratorFor Gal(Ω/ℚ) (l ^ n) hv
  have h_unit {x : QZ} (hx : (N * l ^ n) • x = 0) :
      B.valuation (l ^ n • (y x - floorDiff c x • r)).toMul.val = 1 := by
    have h_ord : l ^ n • ordRat ℚ B (y x) = floorDiff c x := by simpa using hJ.ordRat_eq hx
    apply hv.ordRat_eq_zero_iff.mp
    simp [smul_sub, smul_comm, h_ord, hv.ordRat_ofBase, hv.isUniformiser_iff.mp unif, hr]
  have hτ_cyc : τ ∈ cycloGalGroup (N * l ^ n) := decompGroup_le_cycloGalGroup hpB hp_one hτ.left
  have hl : B.valuation (l ^ n : ℕ) = 1 :=
    (hp_one.of_dvd (dvd_mul_left _ _)).coprime_of_modEq_one.valuation_eq_one hpB
  have hτ_r : galUnitsRep τ r - r = (rootPowHom Ω (l ^ n)).val 1 := by simpa using τ_r
  have h_exponent {x : QZ} (hx : (N * l ^ n) • x = 0) :
      a • (floorDiff c x : ZMod (l ^ n)) - commutatorLog (l ^ n) γ (y x) τ =
        floorDiff c (a • x) := by
    simpa only [mul_one] using nsmul_floorDiff_mul_sub_commutatorLog_eq_of_isFrob hJ
      (dvd_mul_left _ _) ha hτ_cyc hτ hl hτ_r h_unit hx
  exact sub_one_smul_sum_eq_zero dvd_rfl ha h_exponent (h_vanish τ hτ)

/-- The cocycle rule. Let `lⁿ • y` be a Jacobi family at level `M`, with `N lⁿ ∣ M`, and let every
prime of `I` divide `M` and be `≡ 1 mod c N lⁿ`. Write `Λ h` for `derivativeSum e ψ L I 0` of the
exponents `x ↦ commutatorLog (l ^ n) γ (y x) h`. Then `Λ (g g') = Λ g + Υ(g) Λ g'` for
`Υ = cyc^(e+1) ψ`. -/
private lemma derivativeSum_commutatorLog_mul_eq_of_isJacobiFamily
    (hJ : IsJacobiFamily p B c M (l ^ n • y)) (hM : N * l ^ n ∣ M) {I : Finset Nat.Primes}
    (hI_dvd : ∀ q ∈ I, (q : ℕ) ∣ M) (hI_one : ∀ q ∈ I, (q : ℕ) ≡ 1 [MOD c * (N * l ^ n)])
    (g g' : Gal(Ω/ℚ)) :
    derivativeSum e ψ L I 0 (fun x : QZ ↦ commutatorLog (l ^ n) γ (y x) (g * g')) =
      derivativeSum e ψ L I 0 (fun x : QZ ↦ commutatorLog (l ^ n) γ (y x) g) +
        (cyclotomicPowDirichlet l (e + 1) ψ g).val •
          derivativeSum e ψ L I 0 (fun x : QZ ↦ commutatorLog (l ^ n) γ (y x) g') := by
  -- With `a` the cyclotomic character of `g` mod `M` and `F h x` the exponent of `y x` at `h`:
  -- `F (g g') (a x) = F g (a x) + a F g' x` (`nsmul_exponent_eq_sub`). Equivariance of the
  -- derivative sum carries this to `Λ`; it changes only the shifts, which do not matter.
  let F (h : Gal(Ω/ℚ)) (x : QZ) : ZMod (l ^ n) := commutatorLog (l ^ n) γ (y x) h
  show derivativeSum e ψ L I 0 (F (g * g')) = derivativeSum e ψ L I 0 (F g) +
    (cyclotomicPowDirichlet l (e + 1) ψ g).val • derivativeSum e ψ L I 0 (F g')
  have killed {v : QuotSpan (l ^ n : O)} : l ^ n • v = 0 := nsmul_quot_eq_zero dvd_rfl v
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (cyclotomicCharMod Ω M g).val = a := ⟨_, zmod_eq_natCast_val⟩
  have ha_N : (cyclotomicCharMod Ω (N * l ^ n) g).val = a := cyclotomicCharMod_eq_of_dvd hM ha
  have h_exponent {x : QZ} (hx : M • x = 0) : (a • F g') x = (F (g * g') - F g) (a • x) := by
    have hax : M • a • x = 0 := by simp [smul_comm M, hx]
    exact nsmul_exponent_eq_sub (cyclotomicCharMod_eq_of_dvd (dvd_of_mul_left_dvd hM) ha)
      (nsmul_galUnitsRep_sub_eq_zero_of_isJacobiFamily hJ hx g a ha)
      (rootPowHom_commutatorLog_of_isJacobiFamily hJ hx g')
      (rootPowHom_commutatorLog_of_isJacobiFamily hJ hax (g * g'))
      (rootPowHom_commutatorLog_of_isJacobiFamily hJ hax g)
  obtain ⟨f, h_equiv⟩ : ∃ f : Nat.Primes → ZMod (l ^ n),
      (cyclotomicPowDirichlet l e ψ g : O) • derivativeSum e ψ L I 0 (a • F g') =
        derivativeSum e ψ L I f (F (g * g') - F g) :=
    exists_cyclotomicPowDirichlet_smul_derivativeSum hM hI_dvd ha h_exponent
  have h_shift (h : Gal(Ω/ℚ)) : derivativeSum e ψ L I f (F h) = derivativeSum e ψ L I 0 (F h) :=
    derivativeSum_commutatorLog_eq_of_isJacobiFamily hJ hM hI_dvd hI_one h le_rfl f 0
  -- On `O/lⁿ`, `Υ(g)` acts as `aᵉ⁺¹ ψ(a)` and `cyc^e ψ (g)` as `aᵉ ψ(a)`.
  have h_scalar : (cyclotomicPowDirichlet l (e + 1) ψ g).val • derivativeSum e ψ L I 0 (F g') =
      (cyclotomicPowDirichlet l e ψ g : O) • derivativeSum e ψ L I 0 (a • F g') := by
    rw [cyclotomicPowDirichlet_smul ha_N killed, cyclotomicPowDirichlet_smul ha_N killed, map_nsmul]
    module
  rw [h_scalar, h_equiv, map_sub, h_shift, h_shift]
  abel

/-- The cocycles vanish at `γ`. Let `lⁿ • y` be a Jacobi family at level `M`, with `N lⁿ ∣ M` and
every prime of `I` dividing `M`. As `γ γ γ⁻¹ = γ`, every exponent `commutatorLog (l ^ n) γ (y x) γ`
is zero, and so is their derivative sum. -/
private lemma derivativeSum_commutatorLog_self_eq_zero_of_isJacobiFamily
    (hJ : IsJacobiFamily p B c M (l ^ n • y)) (hM : N * l ^ n ∣ M) {I : Finset Nat.Primes}
    (hI_dvd : ∀ q ∈ I, (q : ℕ) ∣ M) :
    derivativeSum e ψ L I 0 (fun x : QZ ↦ commutatorLog (l ^ n) γ (y x) γ) = 0 := by
  have μ_inj : Injective (rootPowHom Ω (l ^ n)).val := (rootPowHom Ω (l ^ n)).property.left
  have h_exponent_zero {x : QZ} (hx : M • x = 0) : commutatorLog (l ^ n) γ (y x) γ = 0 := by
    apply μ_inj
    rw [rootPowHom_commutatorLog_of_isJacobiFamily hJ hx γ, mul_inv_cancel_right, sub_self,
      map_zero]
  rw [derivativeSum_congr hM hI_dvd (fun _ _ ↦ rfl) (G' := 0) h_exponent_zero, map_zero]

/-- The cocycles at the level `M = N lⁿ ∏_{r ∈ I} r`, when `lⁿ • y` is a Jacobi family at level `M`
and the primes of `I` are `≡ 1 mod c N lⁿ`: `g ↦ derivativeSum e ψ L I 0 F_g`, where `F_g x` is the
exponent `commutatorLog (l ^ n) γ (y x) g`, is a locally constant cocycle for `Υ = cyc^(e+1) ψ` that
vanishes on inertia over `ℚ(ζ_N)` at the places above neither `l`, `p` nor a prime of `I`. -/
private lemma derivativeSum_commutatorLog_mem_vanishingCocycles_of_isJacobiFamily
    (hJ : IsJacobiFamily p B c M (l ^ n • y)) {I : Finset Nat.Primes}
    (hM_eq : N * l ^ n * ∏ q ∈ I, (q : ℕ) = M) (hM : N * l ^ n ∣ M)
    (hI_dvd : ∀ q ∈ I, (q : ℕ) ∣ M) (hI_one : ∀ q ∈ I, (q : ℕ) ≡ 1 [MOD c * (N * l ^ n)]) :
    (fun g : Gal(Ω/ℚ) ↦ derivativeSum e ψ L I 0 fun x : QZ ↦ commutatorLog (l ^ n) γ (y x) g) ∈
      vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ n : O))
        (inertiaOff N l (insert p I)) := by
  -- The derivative sum reads only the values on `M`-torsion.
  have h_congr {G G' : QZ → ZMod (l ^ n)} (hG : ∀ {x : QZ}, M • x = 0 → G x = G' x) :
      derivativeSum e ψ L I 0 G = derivativeSum e ψ L I 0 G' :=
    derivativeSum_congr hM hI_dvd (fun _ _ ↦ rfl) hG
  refine ⟨?_, fun g g' ↦
    derivativeSum_commutatorLog_mul_eq_of_isJacobiFamily hJ hM hI_dvd hI_one g g', ?_⟩
  · -- Locally constant: only the finitely many exponents at the points `b / M` are read.
    have h_orbit (b : ZMod M) :
        IsLocallyConstant fun g : Gal(Ω/ℚ) ↦ commutatorLog (l ^ n) γ (y (ofZMod M b)) g :=
      isLocallyConstant_commutatorLog
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g ↦ ?_
    filter_upwards [Filter.eventually_all.mpr fun b ↦ (h_orbit b).eventually_eq g] with g' hg'
    refine h_congr fun hx ↦ ?_
    obtain ⟨b, rfl⟩ := exists_ofZMod hx
    exact hg' b
  · -- Away from `l`, `p` and `I` the `y x` are units, and inertia fixing `μ_N` fixes `μ_M`; so
    -- every exponent is zero (`nsmul_floorDiff_mul_sub_commutatorLog_eq_of_isFrob` with `b = 0` and
    -- `r = 0`, the unit `1` of `Ω^×` written additively).
    rintro g ⟨A, ⟨hgN, hlA, hg⟩, hA⟩
    obtain ⟨hpA, hIA⟩ : A.valuation p = 1 ∧ ∀ q ∈ I, A.valuation (q : Ω) = 1 := by
      simpa [LE.le.ge_iff_eq] using hA
    have h_cofactor : A.valuation ((l ^ n * ∏ q ∈ I, (q : ℕ) : ℕ) : Ω) = 1 := by
      simp +contextual [hlA, hIA]
    have hgM : g ∈ cycloGalGroup M :=
      mem_cycloGalGroup_of_mem_inertiaGroup hg h_cofactor (by rw [← hM_eq, mul_assoc]) hgN
    obtain ⟨a, ha⟩ : ∃ a : ℕ, (cyclotomicCharMod Ω M γ).val = a := ⟨_, zmod_eq_natCast_val⟩
    have h_unit {x : QZ} (hx : M • x = 0) :
        A.valuation (l ^ n • (y x - floorDiff c x • (0 : DiscreteUnits Ω))).toMul.val = 1 := by
      simpa using hJ.valuation_eq_one hx A hpA
    have h_exponent_zero {x : QZ} (hx : M • x = 0) : commutatorLog (l ^ n) γ (y x) g = 0 := by
      simpa using nsmul_floorDiff_mul_sub_commutatorLog_eq_of_isFrob hJ (dvd_of_mul_left_dvd hM) ha
        hgM hg (by simp [hlA]) (b := 0) (by simp) h_unit hx
    exact (h_congr (G' := 0) h_exponent_zero).trans (map_zero _)

/-- Frobenius and inertia for the exponents at one `x` killed by `M`: for a Frobenius `φ` at a place
`A` above `q` and `τ` in the inertia group of `A` whose cyclotomic character mod `q M` fixes the
`M`-torsion and sends `v u / q` to `u / q` (where `L q v = 1`), the exponents of `y (x + u/q)`
at `τ`, weighted by `L q u`, sum to the exponent of `y (q x)` at `φ`. Here `lⁿ ∣ M`, `q` is prime
to `M`, `q ≡ 1 mod c`, `p ≡ 1 mod q`, and `lⁿ • y` is a Jacobi family at levels `M` and `q M`. -/
private lemma sum_mul_commutatorLog_eq_of_isJacobiFamily {q : Nat.Primes}
    (hJ : IsJacobiFamily p B c M (l ^ n • y))
    (hJ_q : IsJacobiFamily p B c ((q : ℕ) * M) (l ^ n • y)) (hM : l ^ n ∣ M)
    (hq_cop : (q : ℕ).Coprime M) (hq_one : (q : ℕ) ≡ 1 [MOD c]) (hpq : (p : ℕ) ≡ 1 [MOD q])
    {v : (ZMod q)ˣ} (hv : L q v = ofAdd 1) {A : ClosurePlace} (hqA : A.valuation (q : Ω) < 1)
    {τ φ : Gal(Ω/ℚ)} (hτ : τ ∈ inertiaGroup Gal(Ω/ℚ) A)
    (hτ_cyc : ∀ x : QZ, M • x = 0 → ∀ u : ZMod q,
      (cyclotomicCharMod Ω ((q : ℕ) * M) τ : ZMod ((q : ℕ) * M)).val • (x + ofZMod q (v * u)) =
        x + ofZMod q u)
    (hφ : IsFrob A q φ) {x : QZ} (hx : M • x = 0) :
    ∑ u : (ZMod q)ˣ, (L q u).toAdd * commutatorLog (l ^ n) γ (y (x + ofZMod q u)) τ =
      commutatorLog (l ^ n) γ (y ((q : ℕ) • x)) φ := by
  -- Put `Y b = y (x + b/q)` and lift `L q` to `lg` with values in `ℤ`. The congruence
  -- `derivative_sub_frob_mem_principalUnits` says that the image of the difference of the two sides
  -- under `rootPowHom` is a principal unit at `A`; so the two sides are equal.
  choose lg hlg using fun u : (ZMod q)ˣ ↦
    (intCast_surjective (L q u).toAdd : ∃ z : ℤ, (z : ZMod (l ^ n)) = (L q u).toAdd)
  let Y (b : ZMod q) : DiscreteUnits Ω := y (x + ofZMod q b)
  have h_level (b : ZMod q) : ((q : ℕ) * M) • (x + ofZMod q b) = 0 := by
    simp [← map_nsmul, mul_smul, hx, natCast_self]
  have hx_q : M • ((q : ℕ) • x) = 0 := by simp [smul_comm M, hx]
  have h_unit (A' : ClosurePlace) (hqA' : A'.valuation (q : Ω) < 1) (b : ZMod q) :
      A'.valuation (l ^ n • Y b).toMul.val = 1 :=
    hJ_q.valuation_eq_one (h_level b) A'
      (hpq.coprime_of_modEq_one.symm.valuation_eq_one hqA')
  have h_cong (A' : ClosurePlace) (hqA' : A'.valuation (q : Ω) < 1) (b : ZMod q) :
      l ^ n • (Y b - Y 0) ∈ principalUnits A' := by
    simpa [Y, smul_sub] using hJ.sub_mem_principalUnits hx q A' (ofZMod q b)
      (by simp [← map_nsmul, natCast_self]) hpq.symm.dvd' hqA'
  have h_lg_step (u : (ZMod q)ˣ) : ((l ^ n : ℕ) : ℤ) ∣ lg (v * u) - lg u - 1 := by
    rw [← intCast_zmod_eq_zero_iff_dvd]
    simp [hlg, hv]
  -- Up to `lⁿ`-th roots of unity, `φ` sends `Y 0 = y x` to `y (q x)`, and `τ` sends `Y (v u)` to
  -- `Y u`.
  have hφ_Y : l ^ n • (galUnitsRep φ (Y 0) - y ((q : ℕ) • x)) = 0 := by
    simpa [Y] using nsmul_galUnitsRep_sub_eq_zero_of_isJacobiFamily hJ hx φ q
      (hφ.cyclotomicCharMod_eq (hq_cop.valuation_eq_one hqA))
  have hτ_Y (u : ZMod q) : l ^ n • (galUnitsRep τ (Y (v * u)) - Y u) = 0 := by
    simpa only [hτ_cyc x hx u] using
      nsmul_galUnitsRep_sub_eq_zero_of_isJacobiFamily hJ_q (h_level (v * u)) τ _ zmod_eq_natCast_val
  have h_dist : IsOfFinAddOrder (l ^ n • (∑ b : ZMod q, Y b - y ((q : ℕ) • x))) := by
    simpa [Y, smul_sub, smul_sum] using
      hJ_q.isOfFinAddOrder_sum_sub (h_level 0) q (dvd_mul_right _ _)
        hq_one.coprime_of_modEq_one.symm
  have h_image : (rootPowHom Ω (l ^ n)).val
      (∑ u : (ZMod q)ˣ, (L q u).toAdd * commutatorLog (l ^ n) γ (y (x + ofZMod q u)) τ -
        commutatorLog (l ^ n) γ (y ((q : ℕ) • x)) φ) =
      ∑ u : (ZMod q)ˣ, lg u • (galUnitsRep γ (Y u) - galUnitsRep (τ * γ * τ⁻¹) (Y u)) -
        (galUnitsRep γ (y ((q : ℕ) • x)) - galUnitsRep (φ * γ * φ⁻¹) (y ((q : ℕ) • x))) := by
    simp [← hlg, ← zsmul_eq_mul, rootPowHom_commutatorLog_of_isJacobiFamily hJ_q (h_level _),
      rootPowHom_commutatorLog_of_isJacobiFamily hJ hx_q, Y]
  apply eq_of_mem_principalUnits ((hq_cop.of_dvd_right hM).valuation_eq_one hqA)
  rw [h_image]
  exact derivative_sub_frob_mem_principalUnits γ hqA hτ hφ h_unit h_cong h_lg_step hφ_Y hτ_Y h_dist

/-- Frobenius and inertia for the derivative sums, at the level `M = N lⁿ ∏_{r ∈ I} r`: for a prime
`q ∉ I`, a place `A` above `q` and a Frobenius `φ` at `A`, some `τ` in the inertia group of `A` has
`Λ (I ∪ {q}) τ = Λ I φ`, with `Λ S h = derivativeSum e ψ L S 0 (commutatorLog (l ^ n) γ (y ·) h)`.
Here `p ≡ 1` mod `M` and mod `q`, `lⁿ • y` is a Jacobi family at every level `M' ∣ p - 1`, `q` and
the primes of `I` are `≡ 1 mod c N lⁿ`, and `L q v = 1` for some `v`. -/
private lemma exists_mem_inertiaGroup_derivativeSum_insert_eq_of_isJacobiFamily
    (hJ : ∀ (M' : ℕ) [NeZero M'], (p : ℕ) ≡ 1 [MOD M'] → IsJacobiFamily p B c M' (l ^ n • y))
    {I : Finset Nat.Primes} (hM_eq : N * l ^ n * ∏ r ∈ I, (r : ℕ) = M) (hM : N * l ^ n ∣ M)
    (hI_dvd : ∀ r ∈ I, (r : ℕ) ∣ M) (hpM : (p : ℕ) ≡ 1 [MOD M])
    (hI_one : ∀ r ∈ I, (r : ℕ) ≡ 1 [MOD c * (N * l ^ n)])
    {q : Nat.Primes} (hq_one : (q : ℕ) ≡ 1 [MOD c * (N * l ^ n)]) (hqI : q ∉ I)
    (hpq : (p : ℕ) ≡ 1 [MOD q]) (hL : ∃ v : (ZMod q)ˣ, L q v = ofAdd 1) {A : ClosurePlace}
    {φ : Gal(Ω/ℚ)} (hφ : IsFrob A q φ) (hqA : A.valuation (q : Ω) < 1) :
    ∃ τ ∈ inertiaGroup Gal(Ω/ℚ) A,
      derivativeSum e ψ L (insert q I) 0 (fun x : QZ ↦ commutatorLog (l ^ n) γ (y x) τ) =
        derivativeSum e ψ L I 0 (fun x : QZ ↦ commutatorLog (l ^ n) γ (y x) φ) := by
  -- Take `v` with `L q v = 1` and `τ` in the inertia group at `A` with `cyc_q τ = v⁻¹`. By
  -- `derivativeSum_eq_of_prime` it suffices to compare the exponents at each `x` killed by `M`.
  obtain ⟨v, hv⟩ := hL
  have hq_cop : (q : ℕ).Coprime M := by
    rw [← hM_eq]
    refine hq_one.of_mul_left.coprime_of_modEq_one.mul_right (Nat.Coprime.prod_right fun r hr ↦
      (Nat.coprime_primes q.prop r.prop).mpr fun h_eq ↦ hqI ?_)
    rwa [Subtype.ext h_eq]
  have hpqM : (p : ℕ) ≡ 1 [MOD q * M] := (Nat.modEq_and_modEq_iff_modEq_mul hq_cop).mp ⟨hpq, hpM⟩
  obtain ⟨τ, hτ, hτ_cyc⟩ := exists_inertia_smul_add_ofZMod hqA (hq_cop.valuation_eq_one hqA) v
  have h_relation {x : QZ} (hx : M • x = 0) :
      ∑ u : (ZMod q)ˣ, (L q u).toAdd * commutatorLog (l ^ n) γ (y (x + ofZMod q u)) τ =
        commutatorLog (l ^ n) γ (y ((q : ℕ) • x)) φ :=
    sum_mul_commutatorLog_eq_of_isJacobiFamily (hJ M hpM) (hJ (q * M) hpqM)
      (dvd_of_mul_left_dvd hM) hq_cop hq_one.of_mul_right hpq hv hqA hτ hτ_cyc hφ hx
  refine ⟨τ, hτ, ?_⟩
  calc derivativeSum e ψ L (insert q I) 0 (fun x ↦ commutatorLog (l ^ n) γ (y x) τ)
      = derivativeSum e ψ L I 0 fun x ↦
          ∑ u : (ZMod q)ˣ, (L q u).toAdd * commutatorLog (l ^ n) γ (y (x + ofZMod q u)) τ := by
        simp only [derivativeSum_insert hqI, Pi.zero_apply, sub_zero]
    _ = derivativeSum e ψ L I _ (fun x ↦ commutatorLog (l ^ n) γ (y x) φ) :=
        derivativeSum_eq_of_prime hM hI_dvd hq_one.of_mul_left hqI h_relation
    _ = derivativeSum e ψ L I 0 (fun x ↦ commutatorLog (l ^ n) γ (y x) φ) :=
        derivativeSum_commutatorLog_eq_of_isJacobiFamily (hJ M hpM) hM hI_dvd hI_one φ le_rfl _ 0

end Cocycles

/-- Kolyvagin's cocycles. Let `l` be a prime, `O` a `ℤ_l`-algebra, `ψ` a Dirichlet character mod
`N ≠ 0` with values in `O`, and `Υ = cyc^(e+1) ψ` (`New.cyclotomicPowDirichlet`) the character of
`Gal(ℚ̄/ℚ)` with `cyc` the `l`-adic cyclotomic character. Let `γ ∈ Gal(ℚ̄/ℚ)`, let `P` be a finite
set of primes `≡ 1 mod c N lⁿ`, and let `B` be a place of `ℚ̄` above a prime `p ≡ 1 mod N lⁿ ∏ P`.
Then there are maps `κ S` from `Gal(ℚ̄/ℚ)` to `O/lⁿ` (`QuotSpan (l ^ n : O)`), one for each finite
set `S` of primes, with two properties.
* They form a Kolyvagin system (`New.OddPart.IsKolyvaginSystem`). For `S ⊆ P`, `κ S` is a locally
  constant `Υ`-cocycle, is unramified over `ℚ(ζ_N)` away from `l`, `p` and `S`, and vanishes at
  `γ`. For `q ∈ P ∖ S`, the value of `κ S` at a Frobenius at a place `A` above `q` is a value of
  `κ (S ∪ {q})` on the inertia group of `A`.
* If `κ ∅` vanishes on the inertia group of `B`, then `Υ γ - 1` kills the twisted Stickelberger
  sum `∑ₐ m(a / N lⁿ) aᵉ ψ(a)` in `O/lⁿ`. Here `a` runs over the units mod `N lⁿ`, read as integers
  in `[0, N lⁿ)`; `ofZMod M a` is `a / M` in `ℚ/ℤ`; and `m(x) = ⌊c ⟨x⟩⌋ - ⌊c ⟨-x⟩⌋`
  (`New.OddPart.floorDiff c x`), where `⟨x⟩` is the representative of `x` in `[0, 1)`. -/
lemma exists_isKolyvaginSystem {O : Type} [CommRing O] {B : ClosurePlace} {N l n : ℕ} [NeZero N]
    [Fact l.Prime] [Algebra ℤ_[l] O] {ψ : DirichletCharacter O N} (e c : ℕ) (γ : Gal(Ω/ℚ))
    {P : Finset Nat.Primes} (hP_one : ∀ q ∈ P, (q : ℕ) ≡ 1 [MOD c * (N * l ^ n)])
    {p : Nat.Primes} (hp_one : (p : ℕ) ≡ 1 [MOD N * l ^ n * ∏ q ∈ P, (q : ℕ)])
    (hpB : B.valuation (p : Ω) < 1) :
    ∃ κ : Finset Nat.Primes → Gal(Ω/ℚ) → QuotSpan (l ^ n : O),
      IsKolyvaginSystem (cyclotomicPowDirichlet l (e + 1) ψ) γ N l p P κ ∧
      ((∀ τ ∈ inertiaGroup Gal(Ω/ℚ) B, κ ∅ τ = 0) →
        (cyclotomicPowDirichlet l (e + 1) ψ γ - 1 : O) •
            ((∑ a : (ZMod (N * l ^ n))ˣ, floorDiff c (ofZMod (N * l ^ n) a) *
                ((a : ZMod (N * l ^ n)).val ^ e * ψ (a : ZMod (N * l ^ n)).val) : O) :
              QuotSpan (l ^ n : O)) =
          (0 : QuotSpan (l ^ n : O))) := by
  -- Let `y x` be an `lⁿ`-th root of the Jacobi-type quotient `J x` (`exists_isJacobiFamily`). Then
  -- `κ S g` is the derivative sum over `S` of the exponents of the `lⁿ`-th roots of unity
  -- `γ y(x) / (g γ g⁻¹) y(x)`; its properties are proved at the level `N lⁿ ∏ S` above.
  have killed (x : QuotSpan (l ^ n : O)) : l ^ n • x = 0 := nsmul_quot_eq_zero dvd_rfl x
  let _ : Module (ZMod (l ^ n)) (QuotSpan (l ^ n : O)) := AddCommGroup.zmodModule killed
  let _ : Algebra (ZMod (l ^ n)) (QuotSpan (l ^ n : O)) :=
    algebraOfModule (l ^ n) (QuotSpan (l ^ n : O))
  obtain ⟨J, hJ⟩ : ∃ J : QZ → DiscreteUnits Ω,
      ∀ (M : ℕ) [NeZero M], (p : ℕ) ≡ 1 [MOD M] → IsJacobiFamily p B c M J :=
    exists_isJacobiFamily hpB c
  obtain ⟨y, hy⟩ : ∃ y : QZ → DiscreteUnits Ω, ∀ x : QZ, l ^ n • y x = J x :=
    Classical.skolem.mp fun x ↦ (J x).exists_nsmul (ne _)
  obtain rfl : J = l ^ n • y := funext fun x ↦ (hy x).symm
  -- Discrete logarithms `L q` onto `ℤ/lⁿ`, for `q ∈ P`.
  have exists_log : ∀ q ∈ P, ∃ L : (ZMod q)ˣ →* Multiplicative (ZMod (l ^ n)),
      ∃ v : (ZMod q)ˣ, L v = ofAdd 1 :=
    fun q hq ↦ exists_monoidHom_units_zmod_eq_ofAdd_one (hP_one q hq).of_mul_left.of_mul_left
  choose! L hL using exists_log
  let κ (S : Finset Nat.Primes) (g : Gal(Ω/ℚ)) : QuotSpan (l ^ n : O) :=
    derivativeSum e ψ L S 0 fun x ↦ commutatorLog (l ^ n) γ (y x) g
  -- The level `M S = N lⁿ ∏ S` divides `p - 1` for `S ⊆ P`.
  let M (S : Finset Nat.Primes) : ℕ := N * l ^ n * ∏ q ∈ S, (q : ℕ)
  have M_neZero (S : Finset Nat.Primes) : NeZero (M S) := ⟨by simp [M, ne, prod_eq_zero_iff]⟩
  have base_dvd (S : Finset Nat.Primes) : N * l ^ n ∣ M S := dvd_mul_right _ _
  have prime_dvd (S : Finset Nat.Primes) (q : Nat.Primes) (hq : q ∈ S) : (q : ℕ) ∣ M S :=
    (dvd_prod_of_mem _ hq).mul_left _
  have hp_level {S : Finset Nat.Primes} (hS : S ⊆ P) : (p : ℕ) ≡ 1 [MOD M S] :=
    hp_one.of_dvd (mul_dvd_mul_left (N * l ^ n) (prod_dvd_prod_of_subset S P _ hS))
  have hJ_level {S : Finset Nat.Primes} (hS : S ⊆ P) : IsJacobiFamily p B c (M S) (l ^ n • y) :=
    hJ (M S) (hp_level hS)
  have system : IsKolyvaginSystem (cyclotomicPowDirichlet l (e + 1) ψ) γ N l p P κ :=
    { mem_vanishingCocycles := fun S hS ↦
        derivativeSum_commutatorLog_mem_vanishingCocycles_of_isJacobiFamily (hJ_level hS) rfl
          (base_dvd S) (prime_dvd S) fun q hq ↦ hP_one q (hS hq)
      apply_eq_zero := fun S hS ↦
        derivativeSum_commutatorLog_self_eq_zero_of_isJacobiFamily (hJ_level hS) (base_dvd S)
          (prime_dvd S)
      exists_mem_inertiaGroup_eq := fun S hS q hqP hqS A φ hφ hqA ↦
        exists_mem_inertiaGroup_derivativeSum_insert_eq_of_isJacobiFamily hJ rfl (base_dvd S)
          (prime_dvd S) (hp_level hS) (fun r hr ↦ hP_one r (hS hr)) (hP_one q hqP) hqS
          (hp_one.of_dvd (prime_dvd P q hqP)) (hL q hqP) hφ hqA }
  -- The relation for `κ ∅` is proved at the level `N lⁿ`.
  have hp_base : (p : ℕ) ≡ 1 [MOD N * l ^ n] := hp_one.of_dvd (base_dvd P)
  exact ⟨κ, system,
    cyclotomicPowDirichlet_sub_one_smul_sum_eq_zero_of_isJacobiFamily (hJ (N * l ^ n) hp_base) hpB
      hp_base⟩

end New.OddPart
