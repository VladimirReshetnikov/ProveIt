import Lib.PadicHodge.Kisin.PeriodMatrixBasis

/-!
# The frame theorem for a period matrix, with Frobenius and Galois action on the frame

The frame theorem `New.Lift.Chart.IsPeriodMatrix.exists_frame` for a period matrix `U`
(`New.Lift.Chart.IsPeriodMatrix`) over a chart with ring `S ⊂ A_inf`: the basis `Q`, `Z` of
`New.Lift.Chart.IsPeriodMatrix.exists_basis` is completed by partial inverses of `Q` and `Z`, a
Frobenius matrix `B` over `S`, and the Galois action on `Z`. The key point is `p ∤ det Q`; it rests
on

* `New.Lift.Chart.exists_det_ne_zero`: a nonzero determinant from a separating set of rows;
* `New.exists_mulVec_eq_zero_and_forall_comp_eq`: Artin's minimal support argument over a valuation
  ring, applied to the reduction of `Q` modulo `p` over the tilt `O^♭`.

Here `π` is `WittVector.constantCoeff`, the reduction `A_inf → O^♭` modulo `p`, `ainfToBPlus` is the
map `A_inf → B⁺`, and `(n, g)` in `New.Period.FrobGal` acts as `φ ^ n g`.

Notions from other files:
* `New.Lift.Chart.E`: The image in S of the series X^e A + p; it equals ξ times a unit of A_inf.
* `New.Lift.Chart.bicommutant`: The S-subalgebra S_B of those y in B⁺ whose multiplication commutes
  with every S-linear endomorphism of B⁺ that maps `New.Period.amaxImage` into itself.
* `New.Period.tau`: The element τ = [ε^{1/p}] − 1 of A_inf, where the brackets denote the
  Teichmüller lift.
* `New.Lift.Chart.S`: For a chart, the Λ-subalgebra S of A_inf that is the image of the chart's map
  Λ[[X]] → A_inf.
* `New.Lift.Chart`: A chart: a Λ-algebra map Λ[[X]] → A_inf, Λ = W(F_{p^f}), sending X to a non-unit
  Teichmüller lift z = [u] and a series X^e A + p, A a unit, to ξ times a unit.

## Relation to the literature

Known result: Kisin lattice (Breuil–Kisin module) of a crystalline lattice. Only existence is proved
here, of a frame over A_inf with a Frobenius matrix over S, which spans the crystalline periods up
to powers of E. Finite height is not stated, and there is no equivalence of categories. The proof
works directly by linear retractions onto the Breuil–Kisin ring, without slope theory or étale
φ-modules. Source: M. Kisin, Crystalline representations and F-crystals, Progr. Math. 253 (2006),
459–496; Bhatt–Morrow–Scholze, Integral p-adic Hodge theory, Publ. IHÉS 128 (2018), 4.26–4.34;
Cais–Liu, On F-crystalline representations, Doc. Math. 21 (2016).
-/

namespace New.Lift.Chart

open Period BPlus Algebra Matrix MulSemiringAction Function Witt RingHom Ideal Quotient PreTilt
open WittVector renaming constantCoeff → π

variable {p : ℕ} [ThePrime p] {d : Type _} {c : Chart} [Fintype d] [DecidableEq d]

/-- Let R: S → D be a homomorphism to a nontrivial semiring and X a set of vectors over S. If
R(t·x) = 0 for all x in X forces R(t) = 0, some square matrix N with rows in X has R(det N)
≠ 0. -/
lemma exists_det_ne_zero {S D : Type*} [CommRing S] [Semiring D] [Nontrivial D] (R : S →+* D)
    (X : Set (d → S)) (h_sep : ∀ t : d → S, (∀ x ∈ X, R (t ⬝ᵥ x) = 0) → ∀ i : d, R (t i) = 0) :
    ∃ N : Matrix d d S, R (det N) ≠ 0 ∧ ∀ k : d, N k ∈ X := by
  -- Among the matrices with `R (det N) ≠ 0` take one whose set of rows in `X` is maximal.
  obtain ⟨N, hN, hmax⟩ := exists_maximalFor_of_wellFoundedGT
    (fun N : Matrix d d S ↦ R (det N) ≠ 0) (fun N ↦ {k | N k ∈ X}) ⟨1, by simp⟩
  refine ⟨N, hN, fun k ↦ by_contra fun hk ↦ hN ?_⟩
  -- If row `k` is not in `X`, column `k` of the adjugate kills `X` after `R`: its product
  -- with `x` is the determinant of `N` with row `k` replaced by `x`, which has more rows in `X`.
  have hkill (x : d → S) (hx : x ∈ X) : R ((N.adjugate · k) ⬝ᵥ x) = 0 := by
    by_contra hne
    have hdet : R (det (N.updateRow k x)) ≠ 0 := by
      simpa [← cramer_transpose_apply, cramer_eq_adjugate_mulVec, ← adjugate_transpose]
    have h_rows_sub : {l | N l ∈ X} ⊆ {l | N.updateRow k x l ∈ X} := fun l hl ↦ by
      by_cases hlk : l = k <;> simp_all
    exact hk (hmax hdet h_rows_sub (show k ∈ {l | N.updateRow k x l ∈ X} by simpa using hx))
  -- So `R` kills that column, hence also `det N`, expanded along row `k`.
  have h_col : ∀ i : d, R (N.adjugate i k) = 0 := h_sep (N.adjugate · k) hkill
  simp [N.det_eq_sum_mul_adjugate_row k, h_col]

/-- A square matrix M of determinant 0 over a valuation ring R has a kernel vector a, with some
coordinate 1, such that g(a) = a for every ring endomorphism g of R with M·g(a) = 0 (Artin's
minimal support argument). -/
lemma _root_.New.exists_mulVec_eq_zero_and_forall_comp_eq {R : Type*} [CommRing R] [IsDomain R]
    [ValuationRing R] {M : Matrix d d R} (h_det : M.det = 0) :
    ∃ (a : d → R) (ν : d), a ν = 1 ∧ M *ᵥ a = 0 ∧ ∀ g : R →+* R, M *ᵥ g ∘ a = 0 → g ∘ a = a := by
  classical
  -- Take a nonzero kernel vector `w` of minimal support.
  obtain ⟨w, ⟨hw, hMw⟩, hmin⟩ := exists_minimalFor_of_wellFoundedLT
    (fun v : d → R ↦ v ≠ 0 ∧ M *ᵥ v = 0) support (exists_mulVec_eq_zero_iff.mpr h_det)
  -- Ideals of a valuation ring are totally ordered, so one coordinate `w ν` divides all others.
  have h_nonempty : Nonempty d := (ne_iff.mp hw).nonempty
  obtain ⟨ν, hν⟩ : ∃ ν : d, ∀ i : d, w ν ∣ w i := by
    simpa [mem_span_singleton] using Finite.exists_max fun i ↦ (span {w i} : Ideal R)
  -- write `w = w ν • a`
  choose a ha using hν
  generalize ht : w ν = t at ha
  obtain rfl : w = t • a := funext ha
  have ht₀ : t ≠ 0 := left_ne_zero_of_smul hw
  have haν : a ν = 1 := by simpa [ht₀] using ht
  have hMa : M *ᵥ a = 0 := by simpa [ht₀, mulVec_smul] using hMw
  refine ⟨a, ν, haν, hMa, fun g hg ↦ by_contra fun hne ↦ ?_⟩
  -- Otherwise `g ∘ a - a` is a nonzero kernel vector whose support lies in that of `t • a`
  -- but misses `ν`, against minimality.
  have hker : M *ᵥ (g ∘ a - a) = 0 := by rw [mulVec_sub, hg, hMa, sub_zero]
  have hsub : support (g ∘ a - a) ⊆ support (t • a) := by aesop
  have hν_sub : ν ∈ support (g ∘ a - a) :=
    hmin ⟨sub_ne_zero.mpr hne, hker⟩ hsub (by simp [haν, ht₀])
  -- but `(g ∘ a - a) ν = g 1 - 1 = 0`
  simp [haν] at hν_sub

/-- For a chart `c` (a Λ-algebra map Λ[[X]] → `A_inf`, Λ = `WittFq f`, sending X to z = [ϖ^♭]), let
`S = c.S` be its subring of `A_inf`, with `c.adicBasis` a (p, z)-adic topological basis of `A_inf`
over `S` whose `S`-linear coordinates are `c.adicBasis.coord i`. Let `Q` be a matrix over `A_inf`
such that, for `t` over `S`, `p` divides every entry of `Q t` only if `p` divides every entry of `t`
(`π (t i) = 0`). Then there are `N` over `S` with `p ∤ det N`, and `σ`, `τ`, such that `(N t) k` is
the coordinate `σ k` of entry `τ k` of `Q t`. -/
lemma exists_det_ne_zero_and_mulVec_eq_coord {Q : Matrix d d Ainf}
    (hsat : ∀ t : d → c.S,
      (∀ j : d, ↑p ∣ (Q *ᵥ fun i : d ↦ (t i : Ainf)) j) → ∀ i : d, π (t i).val = 0) :
    ∃ (N : Matrix d d c.S) (σ : d → c.adicBasis.Index) (τ : d → d),
      π N.det.val ≠ 0 ∧
      ∀ (k : d) (t : d → c.S),
        (N *ᵥ t) k = c.adicBasis.coord (σ k) ((Q *ᵥ fun i : d ↦ (t i : Ainf)) (τ k)) := by
  have hdot (i : c.adicBasis.Index) (j : d) (t : d → c.S) :
      t ⬝ᵥ c.adicBasis.coord i ∘ Q j = c.adicBasis.coord i ((Q *ᵥ fun l : d ↦ (t l : Ainf)) j) := by
    simp [mulVec_eq_sum, dotProduct, ← Subalgebra.smul_def]
  -- The rows `c.adicBasis.coord i ∘ Q j` separate modulo `p`, so `exists_det_ne_zero` applies to
  -- them.
  have h_sep (t : d → c.S)
      (ht : ∀ x ∈ {x : d → c.S | ∃ (i : c.adicBasis.Index) (j : d), c.adicBasis.coord i ∘ Q j = x},
        π (t ⬝ᵥ x).val = 0) : ∀ i : d, π (t i).val = 0 := by
    -- `O^♭` is separated for the `π z`-adic topology, as `z = seriesMap X` is not a unit.
    have h_haus : IsHausdorff (span {π (c.seriesMap PowerSeries.X)}) OFlat :=
      (OFlat.isHausdorff_and_shiftDiff_surjective
        (mt Ainf.isUnit_iff_isUnit_constantCoeff.mpr c.not_isUnit_z)).left
    -- All coordinates of `(Q t) j` in the adic basis lie in the kernel of `π`.
    have h_coord (j : d) (i : c.adicBasis.Index) :
        π (c.adicBasis.coord i ((Q *ᵥ fun l : d ↦ (t l : Ainf)) j)).val = 0 := by
      simpa only [hdot] using ht _ ⟨i, j, rfl⟩
    -- So `(Q t) j` lies in `maxIdeal ^ n` modulo the kernel of `π`, and its reduction is
    -- divisible by every `(π z) ^ n`, hence zero.
    refine hsat t fun j ↦ p_dvd_iff.mpr (h_haus.haus' _ fun n ↦ ?_)
    refine SModEq.zero.mpr <| mem_comap.mp <| (Submodule.restrictScalars_mem ..).mp <|
      c.adicBasis.mem_of_coord (n := n) ?_ fun i ↦ mul_mem_right _ _ (ker_le_comap π (h_coord j i))
    simp [Ideal.map_pow, ← map_le_iff_le_comap, map_span]
    rfl
  obtain ⟨N, hN, h_rows⟩ := exists_det_ne_zero (π.domRestrict c.S) _ h_sep
  -- row `k` of `N` is the functional of index `σ k` applied to row `τ k` of `Q`
  choose σ τ hστ using h_rows
  exact ⟨N, σ, τ, hN, fun k t ↦ by rw [mulVec, dotProduct_comm, ← hστ, hdot]⟩

/-- Let `ψ : S → T` be a map of commutative rings, `M` a square matrix over `S` and `s` a vector
over `S` such that `ψ` kills every entry of `M s` and `ψ (s ν) = 1` for some `ν`. Then
`ψ (det M) = 0`. -/
lemma _root_.RingHom.map_det_eq_zero_of_map_mulVec_eq_zero {S T : Type*} [CommRing S]
    [CommRing T] (ψ : S →+* T) {M : Matrix d d S} {s : d → S}
    (hMs : ∀ k : d, ψ ((M *ᵥ s) k) = 0) {ν : d} (hν : ψ (s ν) = 1) : ψ M.det = 0 := by
  -- `M.map ψ` kills the vector `ψ ∘ s`, whose entry `ν` is `1`
  have h_mulVec_zero : M.map ψ *ᵥ ψ ∘ s = 0 :=
    funext fun k ↦ (ψ.map_mulVec M s k).symm.trans (hMs k)
  exact (ψ.map_det M).trans
    (det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors h_mulVec_zero (i := ν) (by simp [hν]))

omit [DecidableEq d] in
/-- Let `m ∈ FrobGal` and `C = ρ m(Q)` for matrices over `A_inf`. Then `m` maps the kernel of the
reduction of `Q` modulo `p` into the kernel of the reduction of `C`: if `π(Q) a = 0` then
`π(C) m(a) = 0`. -/
lemma map_mulVec_comp_eq_zero_of_eq_mul_smul {Q ρ C : Matrix d d Ainf} {m : FrobGal}
    {a : d → OFlat} (hC : C = ρ * m • Q) (ha : Q.map π *ᵥ a = 0) :
    C.map π *ᵥ toRingHom FrobGal OFlat m ∘ a = 0 := by
  -- `π` commutes with the action of `m`
  have h_map_smul : (m • Q).map WittVector.constantCoeff = Q.map fun x ↦ m • x.coeff 0 := rfl
  simpa [hC, ← Pi.zero_def, comp_def, map_mulVec, h_map_smul] using
    congrArg (fun v ↦ ρ.map π *ᵥ toRingHom FrobGal OFlat m ∘ v) ha

/-- Let `Q` over `Ainf` be `p`-saturated over `S` (`p` divides every entry of `Q t`, for `t` over
`S`, only if `p` divides every entry of `t`), with `Q B` a left multiple of the Frobenius twist of
`Q`, `p ∤ det B`, and `Q` a left multiple of `(1, g) • Q` for each `g` in `Gp p` fixing `S` (`g`
acts on `A_inf` as `(1, g)` in `FrobGal`). Then `p ∤ det Q`. -/
lemma not_dvd_det_of_frobenius {Q ρ : Matrix d d Ainf} {B : Matrix d d c.S}
    (hsat : ∀ t : d → c.S,
      (∀ j : d, ↑p ∣ (Q *ᵥ fun i : d ↦ (t i : Ainf)) j) → ∀ i : d, π (t i).val = 0)
    (hφ : Q * B.map (↑) = ρ * ((Multiplicative.ofAdd 1, 1) : FrobGal) • Q) (hB : π B.det.val ≠ 0)
    (hgal : ∀ g : Gp p, (∀ s : c.S, g • s.val = s) → ∃ ρ' : Matrix d d Ainf,
       Q = ρ' * ((1, g) : FrobGal) • Q) :
    ¬↑p ∣ Q.det := by
  -- Otherwise the reduction of `Q` kills a vector `a` fixed by the fixer of `S`, so approximable
  -- from `S`. This forces every component of `K = det B · det N ≠ 0` (mod `p`) to vanish.
  intro hp
  let R : c.S →+* OFlat := π.domRestrict c.S
  have hR_apply (x : c.S) : R x = (x : Ainf).coeff 0 := rfl
  obtain ⟨N, σ, τ, hN, hNQ⟩ := exists_det_ne_zero_and_mulVec_eq_coord hsat
  -- `a`: a kernel vector of `π(Q)` with `a ν = 1`, fixed by every ring map `g` with
  -- `π(Q) (g ∘ a) = 0`
  obtain ⟨a, ν, haν, ha, hfix⟩ :=
    exists_mulVec_eq_zero_and_forall_comp_eq (M := Q.map π)
      ((π.map_det Q).symm.trans (p_dvd_iff.mp hp))
  have hga (g : Gp p) (hg : ∀ s : c.S, g • s.val = s) (i : d) : g • a i = a i := by
    obtain ⟨ρ', hρ'⟩ := hgal g hg
    exact congrFun (hfix _ (map_mulVec_comp_eq_zero_of_eq_mul_smul hρ' ha)) i
  let K : OFlat := R B.det * R N.det
  refine mul_ne_zero hB hN (Perfection.ext (f := K) fun M ↦ ?_)
  -- Component `M` of the fixed vector `a` is component `M + n` of a vector `s` over `S`.
  have h_eventually : ∀ᶠ m in Filter.atTop, ∀ i : d, ∃ s : c.S,
      coeff M (a i) = coeff m (π s.val) :=
    Filter.eventually_all.mpr fun i ↦
      c.eventually_exists_coeff_eq_of_fixed (fun g hg ↦ hga g hg i) M
  have approx : ∃ n : ℕ, ∀ i : d, ∃ s : c.S, coeff M (a i) = coeff (M + n) (π s.val) :=
    ((add_right_injective M).nat_tendsto_atTop.eventually h_eventually).exists
  choose n s hs using approx
  -- `C = B · φ B ⋯ φⁿ⁻¹ B` carries `a ^ p ^ n` to the kernel, and `K · det C ∣ K ^ p ^ n`.
  have ⟨C, hCK, hCa⟩ : ∃ C : Matrix d d c.S,
      K * R (det C) ∣ K ^ p ^ n ∧ Q.map π *ᵥ C.map R *ᵥ a ^ p ^ n = 0 := by
    clear hs
    induction n with
    | zero => exact ⟨1, by simpa⟩
    | succ n ih =>
      obtain ⟨C, hCK, hCa⟩ := ih
      -- the Frobenius `(ofAdd 1, 1)` acts on `OFlat` as `frobEnd` and commutes with `R`
      have h_frob_a (y : OFlat) : ((.ofAdd 1, 1) : FrobGal) • y = frobEnd y := rfl
      have hR_phi (x : c.S) : R (c.φ x) = frobEnd (R x) := rfl
      have hCa_succ : Q.map π *ᵥ (B * C.map c.φ).map R *ᵥ a ^ p ^ (n + 1) = 0 := by
        simpa [pow_mul, Pi.pow_def, comp_def, pow_succ, ← OFlat.frobEnd_apply, ← mul_assoc,
          map_mulVec, ← hR_apply, hR_phi, h_frob_a] using
          map_mulVec_comp_eq_zero_of_eq_mul_smul hφ hCa
      refine ⟨B * C.map c.φ, ?_, hCa_succ⟩
      grw [det_mul, map_mul, pow_succ, pow_mul, ← hCK, mul_pow,
        ← pow_dvd_pow K (Fact.out : 1 < p), Dvd.intro _ (refl K)]
      simp [map_det, comp_def, ← mul_assoc, pow_succ, ← OFlat.frobEnd_apply, hR_phi]
  -- Let `ψ` be the component `M + n` of the reduction, that is `θ ∘ φ ^ (-(M + n))` modulo `p`.
  -- This component of `Q C s` vanishes; by `exists_frobE_dvd_sub_of_dvd` the vanishing passes
  -- through `S`-linear maps `A_inf → S`, so `ψ` kills `N C s`.
  let ψ : c.S →+* ModP OC p := (coeff (M + n)).comp R
  have hNCs (k : d) : ψ (((N * C) *ᵥ s) k) = 0 := by
    have hdvd : thetaPhiInv (M + n) (p : c.S).val ∣
        thetaPhiInv (M + n) ((Q *ᵥ fun i : d ↦ (C *ᵥ s) i) (τ k)) := by
      simpa [OFlat, ← eq_zero_iff_dvd, mk_thetaPhiInv_eq_coeff, mulVec_eq_sum, hs,
        ← iterate_frobenius, hR_apply] using congrArg (coeff (M + n)) (congrFun hCa (τ k))
    obtain ⟨x, y, hx⟩ :
        ∃ x : c.S,
          c.frobE (M + n) ∣ c.adicBasis.coord (σ k) ((Q *ᵥ fun i : d ↦ (C *ᵥ s) i) (τ k)) - p * x :=
      c.exists_frobE_dvd_sub_of_dvd _ (c.adicBasis.coord (σ k)) p _ hdvd
    have hψ_apply (x : c.S) : ψ x = coeff (M + n) (π x.val) := rfl
    rw [hψ_apply, ← mulVec_mulVec, hNQ, ← mk_thetaPhiInv_eq_coeff, eq_add_of_sub_eq hx]
    simp [CharP.cast_eq_zero, frobE_dvd_iff.mp dvd_rfl]
  -- As `ψ (s ν) = 1`, it kills `det (N C)`, hence `K ^ p ^ n`, whose image is component `M` of `K`.
  have hψ_s : ψ (s ν) = 1 := by simpa [ψ, hR_apply, haν] using (hs ν).symm
  have hdet : ψ (N * C).det = 0 := ψ.map_det_eq_zero_of_map_mulVec_eq_zero hNCs hψ_s
  have h_NC : coeff (M + n) (R N.det) * coeff (M + n) (R C.det) = 0 := by simpa [ψ] using hdet
  have h_zero : coeff (M + n) (K * R C.det) = 0 := by simp [K, mul_assoc, h_NC]
  have h_pow : coeff (M + n) (K ^ p ^ n) = coeff M K := by simp [OFlat, ← iterate_frobenius]
  have h_map : coeff (M + n) (K * R C.det) ∣ coeff (M + n) (K ^ p ^ n) := map_dvd _ hCK
  rw [h_zero, zero_dvd_iff, h_pow] at h_map
  exact h_map.trans (map_zero _).symm

/-- Apply `m` to `U Z = E ^ h Q`, given `ρ m(U) = U F` and `w m(E) = E r`: then
`U w ^ h F m(Z) = E ^ h r ^ h ρ m(Q)`. Here `m` in `FrobGal` acts entrywise on matrices. -/
lemma mul_smul_mul_smul_eq_smul_map_of_mul_eq {U Z : Matrix d d BPlus} {Q : Matrix d d Ainf} {h : ℕ}
    (hUZ : U * Z = c.E.val ^ h • Q.map ainfToBPlus) (m : FrobGal) (ρ : Matrix d d Ainf)
    (F : Matrix d d BPlus) (w : BPlus) (r : Ainf) (hU : ρ.map ainfToBPlus * m • U = U * F)
    (hE : w * ainfToBPlus (m • c.E.val) = ainfToBPlus (c.E.val * r)) :
    U * w ^ h • (F * m • Z) = c.E.val ^ h • (r ^ h • ρ * m • Q).map ainfToBPlus := by
  rw [mul_smul_comm, ← mul_assoc, ← hU, mul_assoc]
  -- `m` acts on matrices entrywise, through the ring map `(toRingHom _ _ m).mapMatrix`
  change w ^ h • (ρ.map ainfToBPlus * ((toRingHom FrobGal BPlus m).mapMatrix U *
    (toRingHom FrobGal BPlus m).mapMatrix Z)) = _
  rw [← map_mul]
  ext
  simp [smul_def (A := BPlus), mul_apply, Finset.mul_sum, mul_left_comm (ainfToBPlus _), *,
    ← mul_assoc, ← mul_pow]

/-- Let `c` be a chart, let `E` be the image of its series X^e A + p (ξ times a unit),
`τ = [ε^{1/p}] - 1`, and `B⁺ = A_max[1/p]`. Let `U`, `U'` over `B⁺` satisfy `U U' = (E τ) ^ h`. If
every solution of `U Y = E ^ h X` with `X` over `A_inf` and `Y` over `B⁺` has `X = Q L` for some `L`
over `A_inf`, then `U = Q Y` for some `Y` over `B⁺`. -/
lemma map_dvd_of_forall_mul_eq_smul_map {U U' : Matrix d d BPlus} {Q : Matrix d d Ainf} {h : ℕ}
    (hUU' : U * U' = (c.E * tau) ^ h • 1)
    (hQ : ∀ {X : Matrix d d Ainf} {Y : Matrix d d BPlus},
      U * Y = c.E.val ^ h • X.map ainfToBPlus → ∃ L : Matrix d d Ainf, Q * L = X) :
    Q.map ainfToBPlus ∣ U := by
  obtain ⟨t, ht⟩ : ∃ t : Ainf, mu = c.E * tau * t := c.associated_E_mul_tau_mu.dvd
  obtain ⟨q, -, hqp⟩ : ∃ q ∈ c.bicommutant, q * p = 1 := c.exists_bicommutant_mul_p_eq_one
  have hUU'_eq : U * U' = c.E.val ^ h • (tau ^ h • (1 : Matrix d d Ainf)).map ainfToBPlus := by
    simp [-map_pow, *, map_smul', smul_smul, ← mul_pow]
  obtain ⟨L, hL⟩ := hQ hUU'_eq
  -- Approximate `p ^ n U` by a matrix over `Ainf` modulo `p ^ n μ ^ h`, where `μ = E τ t`.
  have h_approx (y : BPlus) : ∃ (m : ℕ) (a : Ainf), ∃ w ∈ amaxImage,
      (p : BPlus) ^ m * y =
        algebraMap Ainf BPlus a + (p : BPlus) ^ (m + 0) * algebraMap Ainf BPlus mu ^ h * w :=
    y.exists_Ainf_approx 0 h
  choose k a w hw_mem hka using h_approx
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ i : d × d, (k ∘ U.uncurry) i ≤ n := Finite.exists_le _
  -- With a common exponent `n`, the matrix of approximations is `U` times a matrix over `B⁺`.
  have hX : (U.map fun y : BPlus ↦ p ^ (n - k y) * a y).map ainfToBPlus =
      U * ainfToBPlus p ^ n • (1 - t ^ h • U' * U.map w) := by
    ext i j
    simp [*, ← pow_sub_mul_pow _ (hn (i, j)), mul_sub, ← mul_assoc, smul_smul, ← mul_pow]
    -- a ring identity from `hka` and `ht` alone; the other facts are cleared so grind ignores them
    clear * - hka ht
    grind [smul_def]
  have h_sol : U * (c.E.val ^ h • ainfToBPlus p ^ n • (1 - t ^ h • U' * U.map w)) =
      c.E.val ^ h • (U.map fun y : BPlus ↦ p ^ (n - k y) * a y).map ainfToBPlus := by
    rw [hX, mul_smul_comm]
  obtain ⟨γ, hγ⟩ := hQ h_sol
  -- Divide by `p ^ n` and rewrite the error term using `Q L = τ ^ h`.
  refine ⟨q ^ n • γ.map ainfToBPlus + (t * c.E) ^ h • L.map ainfToBPlus * U.map w, ?_⟩
  simp [mul_add, ← Matrix.map_mul, *, -map_pow, mul_sub, ← mul_assoc, smul_smul, ← mul_pow,
    map_smul']

/-- If `det Q ≠ 0` and `φ Q = v Q B` with `v` a unit and `B` over `S`, then `p ∤ det B`. -/
lemma constantCoeff_det_ne_zero {Q : Matrix d d Ainf} {B : Matrix d d c.S} {v : Ainfˣ}
    (hQ₀ : Q.det ≠ 0) (hB : Q.map frobEnd = v • (Q * B.map (↑))) :
    π B.det.val ≠ 0 := by
  -- If `p ∣ det B` then `p ^ n ∣ det Q` gives `p ^ (n + 1) ∣ φ (det Q)`, so `det Q = 0`.
  refine fun hB₀ ↦ hQ₀ (eq_of_forall_pow_dvd_sub p fun n ↦ ?_)
  rw [show B.det.val = (B.map (↑)).det from c.S.val.toRingHom.map_det B] at hB₀
  induction n with
  | zero => simp
  | succ n ih =>
    refine (map_dvd_iff (MulEquiv.ofBijective _ frobEnd_bijective)).mp ?_
    simpa [hB, map_det, pow_succ, Units.smul_def] using
      (mul_dvd_mul ih (p_dvd_iff.mpr hB₀)).mul_left _

/-- Frobenius step of the frame theorem. Let `U Z = E ^ h Q` with `Z` over `S_B`, let every `x`
over `A_inf` with `U y = E ^ h x` for some `y` over `S_B` be `Q s` with `s` over `S` (`hspan`), let
`φ(U) = v U F` with `F` over `S_B`, and let `u ∈ S_B` invert `φ(E)`. Then `Q B = v⁻¹ φ(Q)` for a
matrix `B` over `S`; here `(ofAdd 1, 1)` in `FrobGal` acts as the Frobenius `φ`. -/
lemma exists_mul_map_eq_frobenius_smul {U Z F : Matrix d d BPlus} {Q : Matrix d d Ainf} {h : ℕ}
    {v : Ainfˣ} {u : BPlus} (hZ : ∀ i j : d, Z i j ∈ c.bicommutant)
    (hUZ : U * Z = c.E.val ^ h • Q.map ainfToBPlus)
    (hspan : ∀ (x : d → Ainf) (y : d → BPlus), (∀ i : d, y i ∈ c.bicommutant) →
      U *ᵥ y = c.E.val ^ h • ainfToBPlus ∘ x → ∃ s : d → c.S, Q *ᵥ (↑) ∘ s = x)
    (hF : ∀ i j : d, F i j ∈ c.bicommutant) (hφU : U.map frobEnd = v • (U * F))
    (hu : u ∈ c.bicommutant) (huE : u * ainfToBPlus (c.φ c.E) = 1) :
    ∃ B : Matrix d d c.S, Q * B.map (↑) = (v⁻¹ • 1) * ((.ofAdd 1, 1) : FrobGal) • Q := by
  -- Apply the Frobenius, which acts entrywise, to `U Z = E ^ h Q`: the columns of `v⁻¹ φ(Q)`
  -- satisfy the hypothesis of `hspan`, with solutions `(E u) ^ h F φ(Z)` over `S_B`.
  let φ : FrobGal := (.ofAdd 1, 1)
  have hU_frob : (v⁻¹ • 1 : Matrix d d Ainf).map ainfToBPlus * φ • U = U * F := by
    rw [show φ • U = U.map frobEnd from rfl, hφU]
    simp [Units.smul_def, map_smul', smul_smul]
  have hE_frob : ainfToBPlus c.E.val * u * ainfToBPlus (φ • c.E.val) =
      ainfToBPlus (c.E.val * 1) := by
    rw [show φ • c.E.val = (c.φ c.E).val from rfl, mul_assoc, huE, mul_one, mul_one]
  have hact := mul_smul_mul_smul_eq_smul_map_of_mul_eq hUZ φ (v⁻¹ • 1) F (ainfToBPlus c.E.val * u) 1
    hU_frob hE_frob
  have h_mem (j i : d) : ((ainfToBPlus c.E.val * u) ^ h • (F * φ • Z)) i j ∈ c.bicommutant :=
    mul_mem (pow_mem (mul_mem (ainfToBPlus_mem_bicommutant _) hu) h)
      (sum_mem fun _ _ ↦ mul_mem (hF _ _) (c.frobEnd_mem_bicommutant (hZ _ _)))
  have h_col (j : d) : ∃ s : d → c.S,
      Q *ᵥ (↑) ∘ s = fun i : d ↦ ((1 : Ainf) ^ h • (v⁻¹ • 1) * φ • Q) i j :=
    hspan _ _ (h_mem j) (congrFun (congrArg col hact) j)
  choose b hb using h_col
  have hQb : Q * bᵀ.map (↑) = (1 : Ainf) ^ h • (v⁻¹ • 1) * φ • Q := ext_col hb
  rw [one_pow, one_smul] at hQb
  exact ⟨bᵀ, hQb⟩

/-- Galois step of the frame theorem. Let `U` be a period matrix of height `h` with `U Z = E ^ h Q`.
For `g` satisfying `c.FixesThetaZ` (this holds when `g` fixes `S` pointwise; the Frobenius factor
`v` is not used) there is `ρ` over `A_inf` with `U g(Z) = E ^ h ρ g(Q)`; here `(1, g)` in `FrobGal`
acts as `g`. -/
lemma IsPeriodMatrix.exists_mul_smul_eq_of_fixesThetaZ {U Z : Matrix d d BPlus}
    {Q : Matrix d d Ainf} {h : ℕ} {v : Ainfˣ} (hU : c.IsPeriodMatrix U h v)
    (hUZ : U * Z = c.E.val ^ h • Q.map ainfToBPlus) {g : Gp p} (hg : c.FixesThetaZ g) :
    ∃ ρ : Matrix d d Ainf,
      U * g • Z = c.E.val ^ h • (ρ * ((1, g) : FrobGal) • Q).map ainfToBPlus := by
  -- `g` acts on `U` through `ρ` (`exists_gal`) and multiplies `E` by a unit `r`
  -- (`associated_smul_E`); apply it to `U Z = E ^ h Q` with
  -- `mul_smul_mul_smul_eq_smul_map_of_mul_eq`.
  obtain ⟨ρ, hρ⟩ := hU.exists_gal g hg
  obtain ⟨r, hr⟩ := c.associated_smul_E g
  have hact : U * ((1, g) : FrobGal) • Z =
      c.E.val ^ h • ((r : Ainf) ^ h • ρ * ((1, g) : FrobGal) • Q).map ainfToBPlus := by
    simpa only [one_pow, one_smul, one_mul] using mul_smul_mul_smul_eq_smul_map_of_mul_eq hUZ (1, g)
      ρ 1 1 r
      (hρ.trans (mul_one U).symm) ((one_mul _).trans (congrArg ainfToBPlus hr.symm))
  exact ⟨(r : Ainf) ^ h • ρ, hact⟩

/-- Saturation step of the frame theorem. Let `det Q ≠ 0`, `U Z = E ^ h Q` with `Z` over `S_B`,
let `hspan` be as in `exists_basis`, and let `q ∈ S_B` invert `p`. If `p` divides every entry of
`Q s` for `s` over `S`, then `p` divides every entry of `s`: `π (s i) = 0`. -/
lemma constantCoeff_eq_zero_of_p_dvd_mulVec {U Z : Matrix d d BPlus} {Q : Matrix d d Ainf}
    {h : ℕ} {q : BPlus} (hQ₀ : Q.det ≠ 0) (hUZ : U * Z = c.E.val ^ h • Q.map ainfToBPlus)
    (hspan : ∀ (x : d → Ainf) (y : d → BPlus), (∀ i : d, y i ∈ c.bicommutant) →
      U *ᵥ y = c.E.val ^ h • ainfToBPlus ∘ x → ∃ s : d → c.S, Q *ᵥ (↑) ∘ s = x)
    (hZ : ∀ i j : d, Z i j ∈ c.bicommutant) (hq : q ∈ c.bicommutant) (hqp : q * p = 1)
    (s : d → c.S) (hs : ∀ j : d, ↑p ∣ (Q *ᵥ fun i : d ↦ (s i : Ainf)) j) (i : d) :
    π (s i).val = 0 := by
  -- If `Q s = p w` then `U (Z s / p) = E ^ h w`, so `w = Q s'` and `s = p s'`.
  obtain ⟨w, hw⟩ := pi_dvd_iff.mpr hs
  have h_mem (l : d) : (Z *ᵥ q • fun i ↦ ainfToBPlus (s i)) l ∈ c.bicommutant := by
    refine _root_.sum_mem fun j _ ↦ ?_
    simp [mul_mem, *]
  have h_sol : U *ᵥ (Z *ᵥ q • fun i ↦ ainfToBPlus (s i)) = c.E.val ^ h • ainfToBPlus ∘ w := by
    ext x
    simpa [hUZ, hqp, mulVec_smul, smul_mulVec, comp_def, map_mulVec, ← mul_assoc,
      -IsRegular.smul_right_inj, -smul_right_inj] using
      congrArg (fun y : Ainf ↦ c.E.val ^ h • (q * ainfToBPlus y)) (congrFun hw x)
  obtain ⟨s', rfl⟩ := hspan w _ h_mem h_sol
  have h_s_eq : (fun i ↦ (s i : Ainf)) = (p : Ainf) • fun i ↦ (s' i : Ainf) := by
    refine mulVec_injective_of_det_ne_zero hQ₀ ?_
    rw [hw, mulVec_smul]
    rfl
  exact p_dvd_iff.mp ⟨s' i, congrFun h_s_eq i⟩

/-- Galois step for `p ∤ det Q`. Let `U Z = E ^ h Q` with `Z` over `S_B` for a period matrix `U`.
For an element `g` of `G_p` that fixes `S` pointwise there is `ρ` over `A_inf` with `Q = ρ g(Q)`;
here `(1, g)` in `FrobGal` acts as `g`. -/
lemma IsPeriodMatrix.exists_eq_mul_smul_of_forall_smul_eq {U Z : Matrix d d BPlus}
    {Q : Matrix d d Ainf} {h : ℕ} {v : Ainfˣ} (hU : c.IsPeriodMatrix U h v)
    (hZ : ∀ i j : d, Z i j ∈ c.bicommutant) (hUZ : U * Z = c.E.val ^ h • Q.map ainfToBPlus)
    (g : Gp p) (hg : ∀ s : c.S, g • s.val = s) :
    ∃ ρ : Matrix d d Ainf, Q = ρ * ((1, g) : FrobGal) • Q := by
  -- `g` is an `S`-linear map that keeps `amaxImage`, so it commutes with `S_B` and fixes `Z`.
  have hgZ : g • Z = Z := by
    ext i j
    let gLin : BPlus →ₗ[c.S] BPlus :=
      ⟨(toRingHom _ _ g).toAddHom, by simp [c.S.smul_def, smul_def, hg]⟩
    -- evaluate at `1`: `g (Z i j) = Z i j * g 1 = Z i j`
    simpa [gLin] using LinearMap.congr_fun (hZ i j gLin smul_mem_amaxImage :
      gLin * lmul c.S BPlus (Z i j) = lmul c.S BPlus (Z i j) * gLin) 1
  -- The constants and `z` lie in `S`, so `g` satisfies `FixesThetaZ`; cancel `E ^ h` in
  -- `exists_mul_smul_eq_of_fixesThetaZ`.
  have hg_fixes : c.FixesThetaZ g := by simp [← theta_smul, FixesThetaZ, FixesLambda, hg ⟨_, _⟩]
  obtain ⟨ρ, hact⟩ := hU.exists_mul_smul_eq_of_fixesThetaZ hUZ hg_fixes
  rw [hgZ, hUZ] at hact
  -- `hact` reads `E ^ h Q = E ^ h ρ g(Q)` over `B⁺`; cancel `E ^ h ≠ 0` and the injective map
  -- `A_inf → B⁺`, entry by entry.
  refine ⟨ρ, Matrix.ext fun i j ↦ ?_⟩
  simpa [smul_def, c.E_ne_zero, -Matrix.map_mul] using congrFun (congrFun hact i) j

/-- Span step of the frame theorem. Let `p ∤ det Q`, `det Q ≠ 0`, and let `hdvd` be as in
`exists_basis`. Then every solution of `U Y = E ^ h X` with `X` over `A_inf` has `X = Q L` for
some `L` over `A_inf`. -/
lemma exists_mul_eq_of_mul_eq_smul {U : Matrix d d BPlus} {Q : Matrix d d Ainf} {h : ℕ}
    (hQ₀ : Q.det ≠ 0)
    (hdvd : ∀ (x : d → Ainf) (y : d → BPlus), U *ᵥ y = c.E.val ^ h • ainfToBPlus ∘ x →
      ∀ (δ : Ainf) (l g : d → Ainf), ¬↑p ∣ δ → l ᵥ* Q = δ • g → δ ∣ l ⬝ᵥ x)
    (hp : ¬↑p ∣ Q.det) {X : Matrix d d Ainf} {Y : Matrix d d BPlus}
    (hY : U * Y = c.E.val ^ h • X.map ainfToBPlus) :
    ∃ L : Matrix d d Ainf, Q * L = X := by
  -- `det Q` divides the entries of `adjugate Q * X`: apply `hdvd` to the columns of `Y` and the
  -- rows of `adjugate Q`, whose product with `Q` is `det Q` times a row of `1`.
  have h_dvd_entry (i j : d) : Q.det ∣ Q.adjugate i ⬝ᵥ fun l : d ↦ X l j :=
    hdvd _ _ (congrFun (congrArg col hY) j) _ _ _ hp (congrFun (adjugate_mul Q) i)
  choose L hL using h_dvd_entry
  have hadj : Q.adjugate * X = Q.det • of L := ext hL
  refine ⟨of L, (smul_right_inj hQ₀).mp ?_⟩
  simp [← mul_smul_comm, mul_adjugate, ← hadj, ← mul_assoc]

/-- The frame theorem. Let `U` be a period matrix of height `h` with Frobenius factor `v`; among
other things, `U` over `B⁺` divides `(E τ) ^ h` with τ = [ε^{1/p}] − 1, and `φ U = v U F` with `F`
over `S_B` = `c.bicommutant`. There are `Q`, `L` over `A_inf`, `Z`, `Z'` over `B⁺` and `B` over `S`
such that: (a) `Q L = τ ^ h`; (b) `Z` has entries in `S_B`; (c) `U Z = E ^ h Q`; (d) `Z' Z = E ^ h`;
(e) `φ Q = v Q B`; (f) if `g` satisfies `c.FixesThetaZ` (fixes Λ and θ(z)), then `g(Z) = Z G` for
some `G` over `A_inf`. Scalars stand for scalar matrices.

This proves the case of Kisin's theorem on the φ-module of a crystalline lattice over the
Breuil–Kisin ring that is used: it is stated for matrices, starts from a given period matrix over
`B⁺`, and says nothing on finite height. -/
lemma IsPeriodMatrix.exists_frame {U : Matrix d d BPlus} {h : ℕ} {v : Ainfˣ}
    (hU : c.IsPeriodMatrix U h v) :
    ∃ (Q L : Matrix d d Ainf) (Z Z' : Matrix d d BPlus) (B : Matrix d d c.S),
      Q * L = tau ^ h • 1 ∧
      (∀ (i : d) (j : d), Z i j ∈ c.bicommutant) ∧
      U * Z = c.E.val ^ h • Q.map ainfToBPlus ∧
      Z' * Z = c.E.val ^ h • 1 ∧
      Q.map frobEnd = v • (Q * B.map (↑)) ∧
      ∀ g : Gp p, c.FixesThetaZ g → ∃ G : Matrix d d Ainf,
        g • Z = Z * Matrix.map G ainfToBPlus := by
  -- Take the basis `Q`, `Z` of `exists_basis`. Frobenius gives `B`; the key point is `p ∤ det Q`,
  -- after which every solution of `U Y = E ^ h X` has `X` in the span of `Q` over `Ainf`.
  -- `hspan`: if `U y = E ^ h x` with `y` over `S_B`, then `x ∈ Q S ^ d`.
  -- `hdvd`: if `U y = E ^ h x`, `p ∤ δ` and `δ` divides the row `l Q`, then `δ ∣ l ⬝ᵥ x`.
  obtain ⟨Q, Z, hQ₀, hZ, hUZ, hspan, hdvd⟩ := hU.exists_basis
  obtain ⟨U', hUU'⟩ := hU.exists_mul_eq_smul_one
  -- `hφU : φ U = v U F` with `F` over `S_B`
  obtain ⟨F, -, hF, -, hφU⟩ := hU.exists_frob
  -- `φ E` and `p` have inverses `u`, `q` in `S_B`.
  obtain ⟨u, hu, huE⟩ := c.exists_bicommutant_mul_phi_E_eq_one
  obtain ⟨q, hq, hqp⟩ := c.exists_bicommutant_mul_p_eq_one
  -- `hφ : Q B = v⁻¹ φ(Q)` with `B` over `S`
  obtain ⟨B, hφ⟩ := exists_mul_map_eq_frobenius_smul hZ hUZ hspan hF hφU hu huE
  have h_smul_Q : ((.ofAdd 1, 1) : FrobGal) • Q = Q.map frobEnd := rfl
  have hB : Q.map frobEnd = v • (Q * B.map (↑)) := by simp [hφ, ← h_smul_Q]
  have hB₀ : π B.det.val ≠ 0 := constantCoeff_det_ne_zero hQ₀ hB
  have hp : ¬↑p ∣ Q.det :=
    not_dvd_det_of_frobenius
      (constantCoeff_eq_zero_of_p_dvd_mulVec hQ₀ hUZ hspan hZ hq hqp) hφ hB₀
      (hU.exists_eq_mul_smul_of_forall_smul_eq hZ hUZ)
  -- Every solution of `U Y = E ^ h X` has `X = Q L` over `Ainf`, by `hdvd` and `p ∤ det Q`.
  have hQ {X : Matrix d d Ainf} {Y : Matrix d d BPlus}
      (hY : U * Y = c.E.val ^ h • X.map ainfToBPlus) : ∃ L : Matrix d d Ainf, Q * L = X :=
    exists_mul_eq_of_mul_eq_smul hQ₀ hdvd hp hY
  have hUU'_eq : U * U' = c.E.val ^ h • (tau ^ h • (1 : Matrix d d Ainf)).map ainfToBPlus := by
    simp [-map_pow, *, map_smul', smul_smul, ← mul_pow]
  obtain ⟨L, hL⟩ := hQ hUU'_eq
  obtain ⟨Y, rfl⟩ : Q.map ainfToBPlus ∣ U := map_dvd_of_forall_mul_eq_smul_map hUU' hQ
  -- Cancel `Q` in `Q Y Z = E ^ h Q`, as `det Q ≠ 0`.
  have h_det_eq : (Q.map ainfToBPlus).det = ainfToBPlus Q.det := (ainfToBPlus.map_det Q).symm
  have h_regular : IsLeftRegular (Q.map ainfToBPlus).det := by
    rw [h_det_eq]
    exact mul_right_injective₀ (by simpa using hQ₀)
  have h_QYZ : Q.map ainfToBPlus * (Y * Z) = Q.map ainfToBPlus * (c.E.val ^ h • 1) := by
    simp [hUZ, ← mul_assoc]
  have hYZ : Y * Z = c.E.val ^ h • 1 := (isRegular_of_isLeftRegular_det h_regular).left h_QYZ
  refine ⟨Q, L, Z, Y, B, hL, hZ, hUZ, hYZ, hB, fun g hg ↦ ?_⟩
  obtain ⟨ρ, hact⟩ := hU.exists_mul_smul_eq_of_fixesThetaZ hUZ hg
  obtain ⟨G, hG⟩ := hQ hact
  -- Now `U g(Z) = E ^ h Q G = U Z G`; cancel `U`.
  have h_UgZ :
      Q.map ainfToBPlus * Y * g • Z = Q.map ainfToBPlus * Y * (Z * G.map ainfToBPlus) := by
    rw [hact, ← hG, Matrix.map_mul, ← smul_mul_assoc, ← hUZ,
      Matrix.mul_assoc (Q.map ainfToBPlus * Y) Z (G.map ainfToBPlus)]
  exact ⟨G, isLeftRegular_iff_mulVec_injective.mpr hU.mulVec_injective h_UgZ⟩

end New.Lift.Chart
