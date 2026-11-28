import Lib.General.Algebra.IntegralPowerSeries
import New.Congruences.Lifting.CutExponentBounds
import New.Congruences.Lifting.FewLowJumps
import New.Congruences.Lifting.TameCharts

/-!
# From sides to lattices: few low jumps, b-letters and tame types

Bounds for the power of p that makes the crystalline cocycles `New.Period.crysCocycles` of a lattice
L orthogonal (`New.Lift.cupOrthogonal`, under cup product) to a class of lattices
`New.Lift.InClass`. The class is given by admissibility, jump sets and polynomials that kill
inertia. The estimates themselves are proved for sides (`New.Lift.KummerChart.PairingSide`) over a
Kummer chart `New.Lift.KummerChart`. This file passes to lattices.

* `New.Lift.KummerChart.universalSide`,
  `New.Lift.KummerChart.pow_smul_mem_cupOrthogonal_of_isScaledCupCoboundary`: the side of all
  crystalline cocycles of L, and orthogonality from the relation
  `New.Lift.Pairing.IsScaledCupCoboundary` for all paired sides.
* `New.Lift.KummerChart.dualDefect_eq_zero_and_dualDefect_le`: the defect `New.Lift.dualDefect` is 0
  if there is no small negative jump, and is bounded if there are few low jumps.
* `New.Lift.KummerChart.hasCupExponent_any_pattern`,
  `New.Lift.KummerChart.hasCupExponent_sparse_thick`: explicit exponents (`New.Lift.HasCupExponent`)
  for any pattern of b-letters and for sparse b-letters.
* `New.Lift.hasCupExponent_of_isTameType`: an explicit exponent for tame inertial types
  (`New.Lift.IsTameType`).

Jumps lie in windows `New.Lift.FitsWindows` = [−η, η] ∪ ε[b, b + W]. An embedding g of O lies
over the letter i if g ζ = θ(ω(i)), where ζ is a root of unity in O and ω(i) is the Teichmüller lift
of i. The jump set `New.Lift.KummerChart.letterJumps` at i collects 0 and the sets U g for the g
over i.

Notions from other files:
* `New.Lift.KummerChart.LetterRoot`: The elements ζ of O with ζ^q = 1, where q = p^f − 1 is the
  number of letters of the chart.
* `New.Lift.KummerChart.Letter`: The letters of a Kummer chart: the multiplicative group of the
  field with p^f elements in the tilt of the ring of integers of C_p.
* `New.Period.theta`: Fontaine's ring homomorphism θ from A_inf to the ring of integers of C_p,
  sending the Teichmüller lift [x] to x^♯.

## Relation to the literature

Over Q_p, take potentially crystalline lattices of tame inertial type with weights in two windows
small against p. For these, a power of p makes Bloch–Kato classes cup to zero with those of
congruent dual lattices. The exponent, used in the Selmer bound, depends on the sizes of the types
and windows but not on the ramification index. Small ramification, the tame potentially
Barsotti–Tate case and Kisin modules with descent data for generic tame types are treated in the
literature. Related work: Iovita–Marmora, Continuity of the finite Bloch–Kato cohomology, 2015;
Nekovář, Compatibility of arithmetic and algebraic local constants II, 2018; Le–Le Hung–Levin–Morra,
Local models for Galois deformation rings, 2023.

Work over unramified p-adic fields with p ≥ 5, where p divides no non-zero integer near 0 or the
large weights. There, crystalline classes modulo those cupping to zero with congruent dual lattices
have length O(1 + large weight/p) per low weight plus O(rank × (window width + 1)), times the
residue degree and the length of O/p, and zero length absent small negative weights. This bounds the
loss above p in the Selmer bound. No loss for weights below p−1, exact Breuil–Kisin sequences for
weights of one sign, and torsion located by weights modulo p are known in the literature. Related
work: Iovita–Marmora, Continuity of the finite Bloch–Kato cohomology, 2015; Čoupek–Gazaki–Marmora,
Exactness of Breuil–Kisin functors, 2026; Gao–Liu, Integral filtered Sen theory and applications,
2024.
-/

namespace New.Lift

open Period Polynomial Module Finset KummerChart JumpLattice Function IsLocalRing Topology Selmer
  Filter

variable {p : ℕ} [l : ThePrime p] [Γ : GroupOverGp p] {O : Type} [CommRing O] {r N : ℕ}
  [PadicIntegerRing O p] {L : GalLattice O Γ}
  {U U' : (O →ₐ[ℤ_[p]] ℂ_[p]) → Finset ℤ} (k : KummerChart Γ) (ζ : k.LetterRoot O)

variable (p r N) in
/-- `K` holds for `X ^ e - 1`, with `e` the least common multiple of the `p ^ i - 1` for
`1 ≤ i ≤ r`, and for some monic polynomial over `ℤ_[p]` of degree at most `N`. -/
def IsTameType (K : O[X] → Prop) : Prop :=
  K (X ^ ((Icc 1 r).lcm fun i ↦ p ^ i - 1) - 1) ∧
  ∃ q : ℤ_[p][X], q.Monic ∧ q.natDegree ≤ N ∧ K (q.map (algebraMap ℤ_[p] O))

open scoped Classical in
/-- The jump set at the letter `i`: the union of `{0}` and the sets `U g` for the embeddings `g` of
`O` with `g ζ = θ(ω(i))`, where `ω(i)` is the Teichmüller lift `k.letterTeich i`. -/
noncomputable def KummerChart.letterJumps (U : (O →ₐ[ℤ_[p]] ℂ_[p]) → Finset ℤ) (i : k.Letter) :
    Finset ℤ :=
  insert 0 (Finset.biUnion {g : O →ₐ[ℤ_[p]] ℂ_[p] | g ζ = (theta (k.letterTeich i) : ℂ_[p])} U)

/-- Let the sets of the filter F contain the subgroup `k.subgroup` of the chart, and let L lie in
the class (`New.Lift.InClass`) along F with jump sets U. The side (a lattice with jump sets at the
letters and a parametrised module of cocycles) is formed by L, the parameter lattice Z_f(L) of all
crystalline cocycles, and the jump sets `New.Lift.KummerChart.letterJumps` of U at the letters.
Membership in the class makes L potentially crystalline, so Z_f(L) is finitely generated. -/
noncomputable abbrev KummerChart.universalSide {F : Filter Γ}
    (hF : Filter.map k.subgroup.subtype ⊤ ≤ F) (h : InClass F ⊥ U L) : PairingSide ⟨O, ζ⟩ :=
  have : Module.Finite O (crysCocycles L.ρ) := crysCocycles.fg h.isPotentiallyCrystalline
  { toGalLattice := L
    jumpSet := k.letterJumps ζ U
    embJumps := U
    inClass := ⟨h.isAdmissible.mono (by gcongr), h.mem_of_jump_ne_zero, h.isKilledBy_of_isWeilPair⟩
    embJumps_subset := fun {g} {_} hg _ hu ↦
      mem_insert_of_mem (mem_biUnion.2 ⟨g, by simpa using hg, hu⟩)
    -- the module of all crystalline cocycles, with the trivial action
    paramLattice := ⟨crysCocycles L.ρ, 1⟩
    cocycleMap := LinearMap.id
    zero_mem := by simp [letterJumps] }

/-- The jumps at the letter `i` are `0` and the elements of the sets `U g` of the embeddings `g`
with `g ζ = theta (k.letterTeich i)`, the image under `theta` of the Teichmüller lift of `i`. -/
lemma KummerChart.mem_letterJumps {i : k.Letter} {u : ℤ} :
    u ∈ k.letterJumps ζ U i ↔
      u = 0 ∨ ∃ g : O →ₐ[ℤ_[p]] ℂ_[p], g ζ = (theta (k.letterTeich i) : ℂ_[p]) ∧ u ∈ U g := by
  simp [letterJumps]

/-- If the sets `U g` of all embeddings `g` lie in a window `[-η, η] ∪ ε [b, b + W]`, then so does
the jump set `letterJumps` at each letter. -/
lemma KummerChart.fitsWindows_letterJumps {η b W : ℕ} {ε : ℤˣ}
    (hU : ∀ g : O →ₐ[ℤ_[p]] ℂ_[p], FitsWindows η ε b W (U g)) (i : k.Letter) :
    FitsWindows η ε b W (k.letterJumps ζ U i) := by
  grind [mem_letterJumps]

/-- Let the set `V` lie in `[-η, η] ∪ -ε [b, b + W]` and `V'` in `[-η, η] ∪ ε [b, b + W]`, for a
sign `ε` and `η ≤ b`. Then `-(v + v') - 1 ≤ b + W + η` for `v ∈ V` and `v' ∈ V'`, since `v` and `v'`
cannot both lie in `-[b, b + W]`. -/
lemma FitsWindows.neg_add_sub_one_le {η b W : ℕ} {ε : ℤˣ} {V V' : Finset ℤ}
    (hV : FitsWindows η (-ε) b W V) (hV' : FitsWindows η ε b W V') (hηb : η ≤ b)
    {v v' : ℤ} (hv : v ∈ V) (hv' : v' ∈ V') : -(v + v') - 1 ≤ b + (W + η : ℕ) := by
  have h_window : (-η ≤ v ∧ v ≤ η) ∨ (-(ε : ℤ) = 1 ∧ b ≤ v ∧ v ≤ b + W) ∨
      (-(ε : ℤ) = -1 ∧ b ≤ -v ∧ -v ≤ b + W) := hV v hv
  have h_window' : (-η ≤ v' ∧ v' ≤ η) ∨ ((ε : ℤ) = 1 ∧ b ≤ v' ∧ v' ≤ b + W) ∨
      ((ε : ℤ) = -1 ∧ b ≤ -v' ∧ -v' ≤ b + W) := hV' v' hv'
  omega

/-- Let `P` pair the lattices of the sides `S` and `S'`. The jumps at the letter `i` of the side
`P.tateDualSide` of the Tate dual of their tensor product are `0` and the `-(v + v') - 1`, with `v`
and `v'` jumps of `S` and `S'` at `i`; so a common bound `B ≥ 0` for these bounds its jump set. -/
lemma KummerChart.le_of_mem_jumpSet_tateDualSide {S S' : k.PairingSide ⟨O, ζ⟩}
    (P : S.SidePairing S') {i : k.Letter} {B : ℤ} (hB : 0 ≤ B)
    (h_le : ∀ v ∈ S.jumpSet i, ∀ v' ∈ S'.jumpSet i, -(v + v') - 1 ≤ B)
    (u : ℤ) (hu : u ∈ P.tateDualSide.jumpSet i) : u ≤ B := by
  simp only [mem_insert, mem_image, mem_image₂] at hu
  grind

open scoped Classical in
/-- Write `ω(i)` for the Teichmüller lift `k.letterTeich i` and `θ` for Fontaine's map `theta` from
`A_inf` to `O_C`. Let `ζ` be an element of `O` with `ζ ^ (p ^ k.f - 1) = 1`. An embedding `g` of `O`
into `ℂ_[p]` satisfies `g ζ = θ(ω(i))` for at most one letter `i`, so the numbers of such `g` for
the different letters add up to at most the rank of `O` over `ℤ_[p]`. -/
lemma KummerChart.sum_card_algHom_le_finrank (k : KummerChart Γ) (ζ : k.LetterRoot O) :
    ∑ i : k.Letter, #{g : O →ₐ[ℤ_[p]] ℂ_[p] | g ζ = (theta (k.letterTeich i) : ℂ_[p])} ≤
      finrank ℤ_[p] O := by
  -- Different letters have Teichmüller lifts that differ by a unit, so their images differ.
  have theta_ne {i i' : k.Letter} (hi : i ≠ i') :
      (theta (k.letterTeich i) : ℂ_[p]) ≠ (theta (k.letterTeich i') : ℂ_[p]) := fun h_eq ↦ by
    have h_unit : IsUnit (theta (k.letterTeich i : Ainf) - theta (k.letterTeich i' : Ainf)) := by
      simpa using ((PairingSide.isUnit_letterTeich_sub hi).map (algebraMap _ Ainf)).map theta
    exact h_unit.ne_zero (sub_eq_zero.2 (Subtype.ext h_eq))
  -- So the sets of embeddings above different letters are disjoint.
  rw [← card_biUnion fun i _ i' _ hi ↦
    disjoint_filter.2 fun g _ hg hg' ↦ theta_ne hi (hg.symm.trans hg')]
  exact (card_le_univ _).trans_eq card_algHom_eq_finrank

omit [GroupOverGp p] in
/-- The length of `O / p` over `O` times the residue degree of `O` is the rank of `O` over
`ℤ_[p]`. -/
lemma length_quotient_mul_length_residueField :
    length O (O ⧸ Ideal.span {(p : O)}) * length (ResidueField ℤ_[p]) (ResidueField O) =
      finrank ℤ_[p] O := by
  let _ : DivisionRing (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) := Ideal.Quotient.divisionRing _
  have span_eq : Ideal.span {(p : O)} = (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] O) := by
    simp [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span]
  -- Over `ℤ_[p]` the left side is the length of `O / p`, which is a vector space over `ℤ_[p] / p`.
  rw [← length_restrictScalars, span_eq,
    length_eq_of_surjective residue_surjective (R := ℤ_[p] ⧸ maximalIdeal ℤ_[p])
      (M := O ⧸ (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] O)),
    length_eq_finrank, finrank_quotient_map]

/-- For a lattice `L` in the class `InClass F K U` and an embedding `g : O →ₐ[ℤ_[p]] ℂ_[p]`, the
Hodge–Tate jumps of `L` at `g` in a finite set `J`, counted with multiplicity (`jump L.ρ g u`),
number at most `finrank O L`. -/
lemma InClass.sum_jump_le_finrank {F : Filter Γ} {K : Γ → O[X] → Prop} (hL : InClass F K U L)
    (J : Finset ℤ) (g : O →ₐ[ℤ_[p]] ℂ_[p]) : ∑ u ∈ J, jump L.ρ g u ≤ finrank O L := by
  obtain ⟨M, card_M, hM⟩ := hL.isPotentiallyCrystalline.exists_hasJumps g
  calc ∑ u ∈ J, jump L.ρ g u = ∑ u ∈ J, M.count u := sum_congr rfl fun u _ ↦ hM u
    _ ≤ ∑ u ∈ M.toFinset, M.count u := sum_le_sum_of_ne_zero (by simp)
    _ = finrank O L := M.toFinset_sum_count_eq.trans card_M

/-- For `q > 1`, the least common multiple of the `q ^ i - 1` for `1 ≤ i ≤ r` is at most
`q ^ r ^ 2`. -/
lemma lcm_pow_sub_one_le {q : ℕ} (hq : 1 < q) (r : ℕ) :
    ((Icc 1 r).lcm fun i : ℕ ↦ q ^ i - 1) ≤ q ^ r ^ 2 := by
  calc ((Icc 1 r).lcm fun i ↦ q ^ i - 1) ≤ ∏ i ∈ Icc 1 r, (q ^ i - 1) :=
        Nat.le_of_dvd (prod_pos fun i hi ↦ Nat.sub_pos_of_lt (Nat.one_lt_pow (by grind) hq))
          (lcm_dvd_prod _ _)
    _ ≤ ∏ _ ∈ Icc 1 r, q ^ r :=
        prod_le_prod fun i hi ↦ (Nat.sub_le _ _).trans (Nat.pow_le_pow_right hq.le (by grind))
    _ = q ^ r ^ 2 := by simp [← pow_mul, sq]

open scoped Classical in
/-- Let the sets of the filter `F` contain the subgroup `k.subgroup` (`hF`), and let `L` lie in the
class `InClass F ⊥ U` (`h`). Suppose that at each embedding `g` the jumps of `L` in `J`, counted
with multiplicity, number at most `n`. Then the jumps in `J` of the side `k.universalSide ζ hF h` at
the letter `i`, counted with multiplicity, number at most `n` times the number of embeddings `g`
with `g ζ = theta (k.letterTeich i)`. -/
lemma KummerChart.sum_jumpMultiplicity_le {F : Filter Γ}
    (hF : Filter.map k.subgroup.subtype ⊤ ≤ F) (h : InClass F ⊥ U L) {J : Finset ℤ} {n : ℕ}
    (hn : ∀ g : O →ₐ[ℤ_[p]] ℂ_[p], ∑ u ∈ J, jump L.ρ g u ≤ n) (i : k.Letter) :
    ∑ u ∈ J, (k.universalSide ζ hF h).jumpMultiplicity i u ≤
      #{g : O →ₐ[ℤ_[p]] ℂ_[p] | g ζ = (theta (k.letterTeich i) : ℂ_[p])} * n := by
  rw [sum_comm, ← smul_eq_mul]
  exact sum_le_card_nsmul _ _ _ fun g _ ↦ hn g

/-- Let `Γ → Gp p = Gal(ℚ̄_p / ℚ_p)` be an open embedding and `F` a filter on `Γ` whose sets contain
the subgroup `k.subgroup` of the chart. Let the lattices `Y` with property `Q` lie in
`InClass F ⊥ U` and `L` in `InClass F ⊥ U'`. Let `x` be a crystalline cocycle of `L` such that, for
all such `Y`, all pairings `P` and all crystalline cocycles `c` of `Y`, the cup product of `c` and
`p ^ e • x` is a coboundary. Then `p ^ e • x` lies in the annihilator `cupOrthogonal Q L` of these
lattices under cup products. -/
lemma KummerChart.pow_smul_mem_cupOrthogonal_of_isScaledCupCoboundary [TopologicalSpace Γ]
    (k : KummerChart Γ) (ζ : k.LetterRoot O) (ho : IsOpenEmbedding Γ.overGp.toGp)
    {F : Filter Γ} (hF : Filter.map k.subgroup.subtype ⊤ ≤ F)
    {Q : GalLattice O Γ → Prop} (hQ : Q ≤ InClass F ⊥ U) (hL : InClass F ⊥ U' L) (e : ℕ)
    (x : crysCocycles L.ρ)
    (h_cup : ∀ (Y : GalLattice O Γ) (hY : Q Y)
      (P : (k.universalSide ζ hF (hQ Y hY)).SidePairing (k.universalSide ζ hF hL))
      (c : crysCocycles Y.ρ), P.IsScaledCupCoboundary e c x) :
    (p : O) ^ e • (x : Γ → L) ∈ cupOrthogonal Q L :=
  fun Y P hY y hy ↦ mod_cast h_cup Y hY P ⟨y, hy⟩ ho

/-- Let `Γ → Gp p = Gal(ℚ̄_p / ℚ_p)` be an open embedding, let the chart `k` be unramified and
`p ≥ 5`, and at each letter `i` let `b i + W + η ≤ (p - 3) a`, `6 (a + η + W) < b i`, and let `p`
divide no nonzero integer within `6 (a + η + W)` of `0` or `± b i` (`NoMultipleNear`). Let `L` be
crystalline with Hodge–Tate jumps in `U'`, and at each letter let the jump sets of `U` and `U'` lie
in `[-η, η] ∪ ∓ε i [b i, b i + W]`, with opposite signs. If `U` and `U'` avoid `[-a, 0)`, or `U'`
lies in `[-η, 0]`, then every crystalline cocycle of `L` lies in `cupOrthogonal`: its cup product
with every crystalline cocycle of a crystalline lattice with jumps in `U` is a coboundary. -/
lemma KummerChart.crysCocycles_le_cupOrthogonal_of_no_small_neg_jump [TopologicalSpace Γ]
    (k : KummerChart Γ)
    (ζ : k.LetterRoot O) (ho : IsOpenEmbedding Γ.overGp.toGp) (hk : k.IsUnramified)
    (hp : 5 ≤ p) {a η W : ℕ} {b : k.Letter → ℕ} {ε : k.Letter → ℤˣ}
    (h_height : ∀ i : k.Letter, b i + W + η ≤ (p - 3) * a)
    (h_far : ∀ i : k.Letter, 6 * (a + η + W) < b i)
    (h_gap : ∀ i : k.Letter, NoMultipleNear p (6 * (a + η + W)) (b i)) (hL : InClass ⊤ ⊥ U' L)
    (hU : ∀ i : k.Letter, FitsWindows η (-ε i) (b i) W (k.letterJumps ζ U i))
    (hU' : ∀ i : k.Letter, FitsWindows η (ε i) (b i) W (k.letterJumps ζ U' i))
    (h_small : (∀ (g : O →ₐ[ℤ_[p]] ℂ_[p]) (u : ℤ), u ∈ U g ∨ u ∈ U' g → u ∉ Ico (-a : ℤ) 0) ∨
      ∀ g : O →ₐ[ℤ_[p]] ℂ_[p], U' g ⊆ Icc (-η : ℤ) 0) :
    crysCocycles L.ρ ≤ cupOrthogonal (InClass ⊤ ⊥ U) L := by
  -- All jumps of the three sides are at most `(p - 3) * a`, so `E ^ a` kills the cokernels, where
  -- `E = z + p` is the Eisenstein polynomial of the chart. Then
  -- `isScaledCupCoboundary_of_killsCokernel` applies, with exponent `0` since
  -- `k.differentBound = 0`.
  intro x hx
  rw [← one_smul O x, ← pow_zero (p : O)]
  refine k.pow_smul_mem_cupOrthogonal_of_isScaledCupCoboundary ζ ho le_top le_rfl hL 0 ⟨x, hx⟩
    fun Y hY P c ↦ ?_
  have height_le (i : k.Letter) : (b i : ℤ) + (W + η : ℕ) ≤ ((p - 3) * (0 + a) : ℕ) := by
    grind [h_height i]
  have kills {S : k.PairingSide ⟨O, ζ⟩} (h_le : ∀ i, ∀ u ∈ S.jumpSet i, u ≤ b i + (W + η : ℕ))
      (i : k.Letter) : S.KillsCokernel i 0 a :=
    PairingSide.killsCokernel_of_isUnramified 0 a
      (fun j u hu ↦ (h_le j u hu).trans (height_le j)) hk hp
  -- The jumps of the Tate dual side are `0` and the `-(v + v') - 1`, with `v` and `v'` in opposite
  -- windows.
  have tateDual_le (i : k.Letter) : ∀ u ∈ P.tateDualSide.jumpSet i, u ≤ b i + (W + η : ℕ) :=
    k.le_of_mem_jumpSet_tateDualSide ζ P (by positivity) fun v hv v' hv' ↦
      (hU i).neg_add_sub_one_le (hU' i) (le_trans (by omega) (h_far i).le) hv hv'
  -- The two cases of `h_small` pass from the embeddings to the letters.
  have h_small_letters :
      (∀ (i : k.Letter) (u : ℤ), u ∈ k.letterJumps ζ U i ∨ u ∈ k.letterJumps ζ U' i →
        u ∉ Ico (-a : ℤ) 0) ∨
      k.IsUnramified ∧ ∀ i : k.Letter, k.letterJumps ζ U' i ⊆ Icc (-η : ℤ) 0 := by
    refine h_small.imp (fun h_avoid i u hu ↦ ?_) fun h_low ↦ ⟨hk, fun i u hu ↦ ?_⟩
    · grind [mem_letterJumps]
    · obtain rfl | ⟨g, -, hg⟩ := (k.mem_letterJumps ζ).1 hu
      exacts [by simp, h_low g hg]
  have differentBound_eq : k.differentBound = 0 := hk.right.right
  refine P.isScaledCupCoboundary_of_killsCokernel (κ := 0) (kills tateDual_le) (kills ?_) (kills ?_)
    h_gap hU hU' h_small_letters (by simp [differentBound_eq]) c ⟨x, hx⟩
  · exact fun i _ ↦ (hU i).le_add le_rfl
  · exact fun i _ ↦ (hU' i).le_add le_rfl

/-- Few low jumps. Let `Γ → Gp p` be an open embedding, let the chart be unramified, `p ≥ 5`,
`η ≥ 1`, and at each letter `i` let `b i + W + η ≤ (p - 3) a`, `6 (a + η + W) < b i`, and let `p`
divide no nonzero integer within `6 (a + η + W)` of `0` or `± b i` (`NoMultipleNear`). Let `L` be
crystalline with jumps in `U'`, and at each letter let the jump sets of `U` and `U'` lie in
`[-η, η]` and in far windows `[b i, b i + W]` of opposite signs. If `L` has at most `m` jumps in
`[-η, η]` at each embedding, then the defect `dualDefect`, the length of the crystalline cocycles of
`L` modulo those orthogonal to the crystalline lattices with jumps in `U`, is at most
`11 f (m (a + 1) + rank L · (W + 1))` times the length of `O / p`, where `f = k.f`. -/
lemma KummerChart.dualDefect_le_of_few_low_weights [TopologicalSpace Γ] (k : KummerChart Γ)
    (ζ : k.LetterRoot O) (ho : IsOpenEmbedding Γ.overGp.toGp) (hk : k.IsUnramified) (hp : 5 ≤ p)
    {a η W m : ℕ} {b : k.Letter → ℕ} {ε : k.Letter → ℤˣ}
    (h_height : ∀ i : k.Letter, b i + W + η ≤ (p - 3) * a) (hη : 1 ≤ η)
    (h_far : ∀ i : k.Letter, 6 * (a + η + W) < b i)
    (h_gap : ∀ i : k.Letter, NoMultipleNear p (6 * (a + η + W)) (b i)) (hL : InClass ⊤ ⊥ U' L)
    (hU : ∀ i : k.Letter, FitsWindows η (-ε i) (b i) W (k.letterJumps ζ U i))
    (hU' : ∀ i : k.Letter, FitsWindows η (ε i) (b i) W (k.letterJumps ζ U' i))
    (hm : ∀ g : O →ₐ[ℤ_[p]] ℂ_[p], ∑ u ∈ Icc (-η : ℤ) η, jump L.ρ g u ≤ m) :
    dualDefect (InClass ⊤ ⊥ U) L ≤
      (11 * (k.f * (m * (a + 1) + finrank O L * (W + 1))) : ℕ) *
        length O (O ⧸ Ideal.span {(p : O)}) := by
  classical
  -- `exists_relLength_le_and_isScaledCupCoboundary` gives a `ℤ_[p]`-submodule `V` of
  -- `crysCocycles L.ρ` of small colength that satisfies `Pairing.IsScaledCupCoboundary` with
  -- exponent `0`, so `V` lies in `cupOrthogonal`. First pass to lengths over `ℤ_[p]`, where `O / p`
  -- has length `finrank ℤ_[p] O`.
  rw [dualDefect, relLength]
  refine (ENat.mul_le_mul_right_iff
    (length_pos (R := ResidueField ℤ_[p]) (M := ResidueField O)).ne' length_ne_top).1 ?_
  rw [← length_restrictScalars, mul_assoc, length_quotient_mul_length_residueField]
  let S : k.PairingSide ⟨O, ζ⟩ := k.universalSide ζ le_top hL
  -- `S.jumpMultiplicity i u` sums the multiplicities of the jump `u` over the `d i` embeddings
  -- above the letter `i`.
  let d (i : k.Letter) : ℕ := #{g : O →ₐ[ℤ_[p]] ℂ_[p] | g ζ = (theta (k.letterTeich i) : ℂ_[p])}
  have sum_le {J : Finset ℤ} {n : ℕ} (hn : ∀ g : O →ₐ[ℤ_[p]] ℂ_[p], ∑ u ∈ J, jump L.ρ g u ≤ n)
      (i : k.Letter) : ∑ u ∈ J, k.f * S.jumpMultiplicity i u ≤ k.f * (d i * n) := by
    grw [← mul_sum, k.sum_jumpMultiplicity_le ζ le_top hL hn i]
  obtain ⟨V, V_length, V_cup⟩ : ∃ V : Submodule ℤ_[p] S.paramLattice,
      relLength ⊤ V ≤ (11 * ∑ i : k.Letter,
        (k.f * (d i * m) * (a + 1) + k.f * (d i * finrank O L) * (W + 1)) : ℕ) ∧
      ∀ (S' : k.PairingSide ⟨O, ζ⟩) (P : S'.SidePairing S) (c : S'.paramLattice),
        (∀ i : k.Letter, FitsWindows η (-ε i) (b i) W (S'.jumpSet i)) →
        ∀ x ∈ V, P.IsScaledCupCoboundary 0 c x :=
    S.exists_relLength_le_and_isScaledCupCoboundary hk hp h_height h_far h_gap hU' (sum_le hm)
      (fun i ↦ sum_le (hL.sum_jump_le_finrank _) i) hη
  let T : Submodule ℤ_[p] (crysCocycles L.ρ) :=
    ((cupOrthogonal (InClass ⊤ ⊥ U) L).submoduleOf (crysCocycles L.ρ)).restrictScalars ℤ_[p]
  have V_le : V ≤ T := fun (x : crysCocycles L.ρ) hx ↦
    show (x : Γ → L) ∈ cupOrthogonal (InClass ⊤ ⊥ U) L by
      simpa using k.pow_smul_mem_cupOrthogonal_of_isScaledCupCoboundary ζ ho le_top le_rfl hL 0 x
        fun Y hY P c ↦ V_cup _ P c hU x hx
  calc length ℤ_[p] (crysCocycles L.ρ ⧸ T) = relLength ⊤ T := by
        rw [relLength_eq_length_map_mkQ, Submodule.map_top, Submodule.range_mkQ, length_top]
    _ ≤ relLength ⊤ V := relLength_mono le_rfl V_le
    _ ≤ (11 * (k.f * (m * (a + 1) + finrank O L * (W + 1)) * ∑ i : k.Letter, d i) : ℕ) := by
        refine V_length.trans_eq (congrArg _ ?_)
        simp only [mul_sum]
        exact sum_congr rfl fun i _ ↦ by ring
    _ ≤ (11 * (k.f * (m * (a + 1) + finrank O L * (W + 1))) : ℕ) * finrank ℤ_[p] O := by
        rw [← mul_assoc]
        exact_mod_cast Nat.mul_le_mul_left _ (k.sum_card_algHom_le_finrank ζ)

/-- The defect at generic primes. Let `Γ → Gp p` be an open embedding, and let the root `ζ` assign
the embeddings of `O` to the letters of the chart `k`. Let `k` be unramified, `p ≥ 5`, `η ≥ 1`, and
at each letter `i` let `b i + W + η ≤ (p - 3) a`, `6 (a + η + W) < b i`, and let `p` divide no
nonzero integer within `6 (a + η + W)` of `0` or `± b i`. Let `L` be crystalline with jumps in `U'`,
where `U` and `U'` lie at each letter in `[-η, η]` and in the opposite far windows
`∓ε i [b i, b i + W]`.

The defect `dualDefect` is the length of the crystalline cocycles of `L` modulo those orthogonal to
the crystalline lattices with jumps in `U`. It vanishes if `U` and `U'` avoid `[-a, 0)` or `U'` lies
in `[-η, 0]`. If `L` has at most `m` jumps in `[-η, η]` at each embedding, it is at most
`11 f (m (a + 1) + rank L · (W + 1))` times the length of `O / p`, where `f = k.f`. -/
lemma KummerChart.dualDefect_eq_zero_and_dualDefect_le [TopologicalSpace Γ] (k : KummerChart Γ)
    (ζ : k.LetterRoot O) (ho : IsOpenEmbedding Γ.overGp.toGp) (hk : k.IsUnramified) (hp : 5 ≤ p)
    {a η W : ℕ} {b : k.Letter → ℕ} {ε : k.Letter → ℤˣ}
    (h_height : ∀ i : k.Letter, b i + W + η ≤ (p - 3) * a) (hη : 1 ≤ η)
    (h_far : ∀ i : k.Letter, 6 * (a + η + W) < b i)
    (h_gap : ∀ i : k.Letter, NoMultipleNear p (6 * (a + η + W)) (b i)) (hL : InClass ⊤ ⊥ U' L)
    (hU : ∀ i : k.Letter, FitsWindows η (-ε i) (b i) W (k.letterJumps ζ U i))
    (hU' : ∀ i : k.Letter, FitsWindows η (ε i) (b i) W (k.letterJumps ζ U' i)) :
    -- (a) the defect vanishes, if `U` and `U'` avoid `[-a, 0)` or `U'` lies in `[-η, 0]`
    ((∀ (g : O →ₐ[ℤ_[p]] ℂ_[p]) (u : ℤ), u ∈ U g ∨ u ∈ U' g → u ∉ Ico (-a : ℤ) 0) ∨
        (∀ g : O →ₐ[ℤ_[p]] ℂ_[p], U' g ⊆ Icc (-η : ℤ) 0) →
      dualDefect (InClass ⊤ ⊥ U) L = 0) ∧
    -- (b) a bound for the defect, if at most `m` jumps lie in `[-η, η]`
    ∀ m : ℕ, (∀ g : O →ₐ[ℤ_[p]] ℂ_[p], ∑ u ∈ Icc (-η : ℤ) η, jump L.ρ g u ≤ m) →
      dualDefect (InClass ⊤ ⊥ U) L ≤
        (11 * (k.f * (m * (a + 1) + finrank O L * (W + 1))) : ℕ) *
          length O (O ⧸ Ideal.span {(p : O)}) :=
  ⟨fun h_small ↦ dualDefect_eq_zero_iff.2 (k.crysCocycles_le_cupOrthogonal_of_no_small_neg_jump
      ζ ho hk hp h_height h_far h_gap hL hU hU' h_small),
    fun _ hm ↦ k.dualDefect_le_of_few_low_weights ζ ho hk hp h_height hη h_far h_gap hL hU hU' hm⟩

/-- Let `Γ → Gp p` be an open embedding, and let the root `ζ` assign the embeddings of `O` to the
letters of the chart `k`. Let `k` be unramified, `p ≥ 7`, `η ≥ 1` and `V + 4 η ≤ M`. Let `L` be
crystalline with jumps in `U'`, where `U` and `U'` lie at each letter in `[-η, η]` and in opposite
far windows of width `V`, which start at `b` at the b-letters (those with `IsBLetter i`) and at `G`
at the others, with `0 < G ≤ b`. If `b < K p ^ 2`, `2 G < K p` and `M ≤ K`, then
`p ^ (10⁴ (K + ⌊log_p (2 (b + M))⌋))` times any crystalline cocycle of `L` is orthogonal under cup
products to the crystalline cocycles of the crystalline lattices with jumps in `U`. -/
lemma KummerChart.hasCupExponent_any_pattern [TopologicalSpace Γ] (k : KummerChart Γ)
    (ζ : k.LetterRoot O) (ho : IsOpenEmbedding Γ.overGp.toGp) (hk : k.IsUnramified) (hp : 7 ≤ p)
    {η V M G b K : ℕ} {IsBLetter : k.Letter → Prop} [DecidablePred IsBLetter] {ε : k.Letter → ℤˣ}
    (hη : 1 ≤ η) (hM : V + 4 * η ≤ M) (hL : InClass ⊤ ⊥ U' L)
    (hU : ∀ i : k.Letter,
      FitsWindows η (-ε i) (if IsBLetter i then b else G) V (k.letterJumps ζ U i))
    (hU' : ∀ i : k.Letter,
      FitsWindows η (ε i) (if IsBLetter i then b else G) V (k.letterJumps ζ U' i))
    (hG_pos : 0 < G) (hGb : G ≤ b) (hbK : b < K * p ^ 2) (hGK : 2 * G < K * p) (hMK : M ≤ K) :
    HasCupExponent (InClass ⊤ ⊥ U) L (10 ^ 4 * (K + p.log (2 * (b + M)))) :=
  fun x hx ↦ k.pow_smul_mem_cupOrthogonal_of_isScaledCupCoboundary ζ ho le_top le_rfl hL _ ⟨x, hx⟩
    fun _ _ P c ↦
    P.isScaledCupCoboundary_any_pattern hη hM hU hU' hk hp hG_pos hGb hbK hGK hMK c ⟨x, hx⟩

/-- Let `Γ → Gp p` be an open embedding, and let the root `ζ` assign the embeddings of `O` to the
letters of the chart `k`. Let `η ≥ 1`, and let `L` be crystalline with jumps in `U'`, where `U` and
`U'` lie at each letter in `[-η, η]` and in opposite far windows of width `V`, which start at `b` at
the b-letters (those with `IsBLetter i`) and at `G` at the others, with `G + V ≤ η`; so the low
window `[-η, η]` contains the far windows of the other letters. Suppose that no three b-letters
follow one another along the orbits of `letterFrob : i ↦ i ^ p` with both gaps between `1` and
`J ≥ 1`. Suppose also that either the chart is unramified with `p ≥ 7` and `10 p ^ J η ≤ b`, or the
sign `ε` is constant and `8 e ≤ p ^ (J + 1)`. Let `2 e (b + 5 η) ≤ p ^ (J + 1) δ` and
`20 (J + 1 + d) η + ⌊log_p (2 (b + 5 η))⌋ ≤ M`, where `e = k.e` is the ramification index and
`d = k.differentBound` is `0` for `e = 1` and `v_p(e) + 1` otherwise. Then
`p ^ (10³ (δ + (J + 1) M))` times any crystalline cocycle of `L` is orthogonal under cup products to
the crystalline cocycles of the crystalline lattices with jumps in `U`. -/
lemma KummerChart.hasCupExponent_sparse_thick [TopologicalSpace Γ] (k : KummerChart Γ)
    (ζ : k.LetterRoot O) (ho : IsOpenEmbedding Γ.overGp.toGp) {η V G b J M δ : ℕ}
    {IsBLetter : k.Letter → Prop} [DecidablePred IsBLetter] {ε : k.Letter → ℤˣ} (hη : 1 ≤ η)
    (hL : InClass ⊤ ⊥ U' L)
    (hU : ∀ i : k.Letter,
      FitsWindows η (-ε i) (if IsBLetter i then b else G) V (k.letterJumps ζ U i))
    (hU' : ∀ i : k.Letter,
      FitsWindows η (ε i) (if IsBLetter i then b else G) V (k.letterJumps ζ U' i))
    (hG : G + V ≤ η) (hJ : 1 ≤ J)
    (h_sparse : ∀ i : k.Letter, ∀ s ∈ Icc 1 J, ∀ t ∈ Icc 1 J,
      IsBLetter i → IsBLetter ((k.letterFrob ^ s) i) → ¬IsBLetter ((k.letterFrob ^ (s + t)) i))
    (h_unramified_or_sign : (k.IsUnramified ∧ 7 ≤ p ∧ 10 * p ^ J * η ≤ b) ∨
      ((∀ i i' : k.Letter, ε i = ε i') ∧ 8 * k.e ≤ p ^ (J + 1)))
    (h_depth : k.e * (2 * (b + 5 * η)) ≤ p ^ (J + 1) * δ)
    (hM : 20 * (J + 1 + k.differentBound) * η + p.log (2 * (b + 5 * η)) ≤ M) :
    HasCupExponent (InClass ⊤ ⊥ U) L (10 ^ 3 * (δ + (J + 1) * M)) :=
  fun x hx ↦ k.pow_smul_mem_cupOrthogonal_of_isScaledCupCoboundary ζ ho le_top le_rfl hL _ ⟨x, hx⟩
    fun _ _ P c ↦ P.isScaledCupCoboundary_sparse_thick hη hU hU' hG hJ h_sparse
      h_unramified_or_sign h_depth hM c ⟨x, hx⟩

/-- Let `Γ → Gp p` be injective. Restricting a lattice `Y` to the subgroup `k.subgroup` of a chart
does not change the operator `linearFrob` of `(s, m)` on the potentially crystalline periods. -/
lemma KummerChart.linearFrob_comp_subtype (h_inj : Injective Γ.overGp.toGp)
    (Y : GalLattice O Γ) (s : k.subgroup) (m : ℕ) :
    linearFrob (MonoidHom.comp Y.ρ k.subgroup.subtype) s m = linearFrob Y.ρ s m := by
  have Dpcris_eq : Dpcris (MonoidHom.comp Y.ρ k.subgroup.subtype) = Dpcris Y.ρ := by
    rw [Dpcris, Dpcris, ← map_nearOne k.subgroup.subtype h_inj OverGp.isOpen_range]
    rfl
  rw [linearFrob, linearFrob, Dpcris_eq]
  rfl

/-- Let `Γ → Gp p` be bijective, let `d` be a tame chart with subgroup `d.subgroup` and ramification
index `d.e`, and let `Y` be potentially crystalline. The elements `s` of inertia
(`IsWeilPair (toGp s) 0`) act on the periods of `Y` by `linearFrob Y.ρ s 0`. If `X ^ d.e - 1` kills
all these operators (`IsKilledBy`), then those of inertia elements in `d.subgroup` are trivial. -/
lemma TameChart.linearFrob_eq_one (d : TameChart Γ) (h_bij : Bijective Γ.overGp.toGp)
    {Y : GalLattice O Γ} (hY : IsPotentiallyCrystalline Y.ρ)
    (h_killed : ∀ s : Γ, IsWeilPair (toGp s) 0 → IsKilledBy Y.ρ s 0 (X ^ d.e - 1))
    (s : d.subgroup) (hs : IsWeilPair (toGp (s : Γ)) 0) : linearFrob Y.ρ s 0 = 1 := by
  -- On inertia `β = linearFrob Y.ρ · 0` is a homomorphism with open kernel that is killed by `d.e`.
  -- By tame inertia theory it is trivial on the stabiliser of the root `d.ϖ` of the uniformiser
  -- in inertia, which contains the inertia elements of `d.subgroup`.
  let J : Γ.G ≃* Gp p := .ofBijective toGp h_bij
  have toGp_symm (g : Gp p) : toGp (J.symm g) = g := J.apply_symm_apply g
  have weil (g : inertiaGroup (Gp p) (intQpBar p)) : IsWeilPair (toGp (J.symm g)) 0 := by
    simpa only [toGp_symm] using isWeilPair_zero_iff.2 g.prop
  let β : inertiaGroup (Gp p) (intQpBar p) →* End Bmax (TensorProduct ℤ_[p] Bmax Y) :=
    { toFun g := linearFrob Y.ρ (J.symm g) 0
      map_one' := by simpa using linearFrob_pow hY d.isWeilPair_tameGen 0
      map_mul' g g' := by simpa using linearFrob_mul hY (weil g) (weil g') }
  have ker_open : β.ker.IsOpen := by
    refine β.ker.isOpen_of_mem_nhds (g := 1) ?_
    filter_upwards [continuous_subtype_val.tendsto 1
      (mem_comap'.1 hY.eventually_linearFrob_eq_one)] with g hg using hg (toGp_symm g) (weil g)
  have β_pow (g : inertiaGroup (Gp p) (intQpBar p)) : β g ^ d.e = 1 := by
    simpa [β, sub_eq_zero] using (h_killed _ (weil g)).2
  have stabilizer_le : MulAction.stabilizer (inertiaGroup (Gp p) (intQpBar p)) d.ϖ ≤ β.ker :=
    (isLocalGalois_padic.tame_inertia isUniformiser_ell (valuation_natCast_eq_one d.tame)
      d.varpi_pow_eq β ker_open β_pow).left
  simpa [β] using (stabilizer_le (d.apply_varpi s) : β ⟨J s, isWeilPair_zero_iff.1 hs⟩ = 1)

/-- Descent along a tame chart. Let `Γ → Gp p` be a surjective open embedding, `F` any filter on
`Γ`, and `d` a tame chart with subgroup `d.subgroup` and ramification index `d.e`. Let the lattice
`Y` lie in `InClass F K U`: its periods fixed near `1` and on a set of `F` span, its jumps at each
embedding `g` lie in `U g`, and each polynomial allowed by `K s` kills `s` on the periods, for `s`
in inertia. If `K s` allows `X ^ d.e - 1` at every `s` in inertia, then `Y` is crystalline over
`d.subgroup` with jumps in `U`: it lies in the class of the filter of the sets containing
`d.subgroup` and the empty relation `⊥`. -/
lemma TameChart.inClass_of_pow_sub_one [TopologicalSpace Γ]
    (ho : IsOpenEmbedding Γ.overGp.toGp) {F : Filter Γ}
    (d : TameChart Γ) (h_surj : Surjective Γ.overGp.toGp)
    {K : Γ → O[X] → Prop} (hK : ∀ s : Γ, IsWeilPair (toGp s) 0 → K s (X ^ d.e - 1))
    (Y : GalLattice O Γ) (hY : InClass F K U Y) : InClass (map d.subgroup.subtype ⊤) ⊥ U Y := by
  have h_inertia (s : d.subgroup) (hs : IsWeilPair (toGp s) 0) :
      linearFrob (MonoidHom.comp Y.ρ d.subgroup.subtype) s 0 = 1 := by
    rw [d.linearFrob_comp_subtype ho.injective, d.linearFrob_eq_one ⟨ho.injective, h_surj⟩
      hY.isPotentiallyCrystalline (fun t ht ↦ hY.isKilledBy_of_isWeilPair (hK t ht) ht) s hs]
  -- A potentially crystalline lattice on which inertia acts trivially is crystalline.
  have h_adm : IsAdmissible Y.ρ (map d.subgroup.subtype ⊤) :=
    (isAdmissible_comp_iff d.subgroup.subtype OverGp.isOpen_range).1
      ((hY.isPotentiallyCrystalline.comp d.subgroup.subtype).isCrystalline_of_inertia_fixes
        h_inertia)
  exact ⟨h_adm.mono (sup_le d.nearOne_le le_rfl), hY.mem_of_jump_ne_zero, fun _ _ ↦ False.elim⟩

/-- If `Γ` maps onto `Gp p` and the number `r` is less than the prime `p`, there is a tame chart
whose ramification index is the least common multiple of the `p ^ i - 1` for `1 ≤ i ≤ r`. -/
lemma exists_tameChart_e_eq_lcm (h_surj : Surjective Γ.overGp.toGp) (hr : r < p) :
    ∃ d : TameChart Γ, d.e = (Icc 1 r).lcm fun i : ℕ ↦ p ^ i - 1 := by
  refine exists_tameChart h_surj ⟨r.factorial, r.factorial_pos⟩
    (fun h_dvd ↦ hr.not_ge (l.out.dvd_factorial.1 h_dvd)) (Finset.lcm_dvd fun i hi ↦ ?_)
  exact Nat.pow_sub_one_dvd_pow_sub_one p (Nat.dvd_factorial (by grind) (mem_Icc.1 hi).2)

/-- The number `differentBound` of a tame chart is at most `1`, since `p` does not divide the
ramification index. -/
lemma TameChart.differentBound_le_one (d : TameChart Γ) : d.differentBound ≤ 1 := by
  grind [KummerChart.differentBound, padicValNat.eq_zero_of_not_dvd d.tame]

/-- If `b + n < q`, then `q` divides no nonzero integer within distance `n` of `0`, `b` or `-b`. -/
lemma noMultipleNear_of_add_lt {q n b : ℕ} (h_lt : b + n < q) : NoMultipleNear q n b :=
  fun _ hy_ne hy_near h_dvd ↦ hy_ne (Int.eq_zero_of_abs_lt_dvd h_dvd (by grind))

/-- An element of `[-η, η] ∪ ε [b, b + W]` is at most `b + W + η`. -/
lemma FitsWindows.le_add_add {η b W : ℕ} {ε : ℤˣ} {V : Finset ℤ}
    (hV : FitsWindows η ε b W V) {u : ℤ} (hu : u ∈ V) : u ≤ b + W + η := by
  grind

/-- Let the set `V` lie in `[-η, η] ∪ -ε [b, b + W]` and `V'` in `[-η, η] ∪ ε [b, b + W]`, for a
sign `ε`. At most one of `v ∈ V` and `v' ∈ V'` is below `-η`, so `-(v + v') ≤ b + W + 2 η`. -/
lemma FitsWindows.neg_add_le_of_opposite {η b W : ℕ} {ε : ℤˣ} {V V' : Finset ℤ}
    (hV : FitsWindows η (-ε) b W V) (hV' : FitsWindows η ε b W V') {v v' : ℤ}
    (hv : v ∈ V) (hv' : v' ∈ V') : -(v + v') ≤ b + W + 2 * η := by
  have h_window : (-η ≤ v ∧ v ≤ η) ∨ (-(ε : ℤ) = 1 ∧ b ≤ v ∧ v ≤ b + W) ∨
      (-(ε : ℤ) = -1 ∧ b ≤ -v ∧ -v ≤ b + W) := hV v hv
  have h_window' : (-η ≤ v' ∧ v' ≤ η) ∨ ((ε : ℤ) = 1 ∧ b ≤ v' ∧ v' ≤ b + W) ∨
      ((ε : ℤ) = -1 ∧ b ≤ -v' ∧ -v' ≤ b + W) := hV' v' hv'
  omega

/-- Let `Γ → Gp p = Gal(ℚ̄_p / ℚ_p)` be a surjective open embedding. For each `s` in inertia let
`K s` be a tame type: it holds for `X ^ e - 1`, with `e` the least common multiple of the
`p ^ i - 1` for `1 ≤ i ≤ r`, and for a monic polynomial over `ℤ_[p]` of degree at most `N`. A
lattice lies in `InClass F K U` if its periods fixed on a neighbourhood of `1` that belongs to the
filter `F` span, its Hodge–Tate jumps at each embedding `g` of `O` lie in `U g`, and each polynomial
allowed by `K s` kills `s` on its periods, for `s` in inertia. Let `L` lie in the class for `U'` and
`s ↦ K s⁻¹`. If `U` and `U'` lie at each embedding in `[-η, η]` and in the opposite far windows
`∓ε [b, b + W]`, and `p > b + 6 (W + η) + r² (N + 1)² + 2`, then
`p ^ (3 r² (N + 1)² + 150 (η + W + 1))` times any crystalline cocycle of `L` has cup product a
coboundary with every crystalline cocycle of a lattice in `InClass F K U` paired with `L`. -/
lemma hasCupExponent_of_isTameType [TopologicalSpace Γ] (ho : IsOpenEmbedding Γ.overGp.toGp)
    (h_surj : Surjective Γ.overGp.toGp) {F : Filter Γ} {K : Γ → O[X] → Prop}
    (hL : InClass F (fun s : Γ ↦ K s⁻¹) U' L)
    (hK : ∀ s : Γ, IsWeilPair (toGp s) 0 → IsTameType p r N (K s)) {η W b : ℕ} {ε : ℤˣ}
    (hU : ∀ g : O →ₐ[ℤ_[p]] ℂ_[p], FitsWindows η (-ε) b W (U g))
    (hU' : ∀ g : O →ₐ[ℤ_[p]] ℂ_[p], FitsWindows η ε b W (U' g))
    (hp : b + 6 * (W + η) + r ^ 2 * (N + 1) ^ 2 + 2 < p) :
    HasCupExponent (InClass F K U) L (3 * (r ^ 2 * (N + 1) ^ 2) + 150 * (η + W + 1)) := by
  -- Take a tame chart `d` of ramification index `e = lcm (p ^ i - 1)`, `1 ≤ i ≤ r`, over which all
  -- lattices of the class become crystalline, and apply `isScaledCupCoboundary_of_killsCokernel`
  -- with `a = 0` and `κ = r ^ 2 * (N + 1) ^ 2`. The three cokernels are killed by `p ^ κ` thanks to
  -- `TameChart.killsCokernel_of_isKilledBy`, which asks for a monic `q` killing the tame
  -- generator, `e ≤ p ^ r ^ 2` and `r ^ 2 * (q.natDegree + 1) ≤ κ`.
  have r_le : r ≤ r ^ 2 * (N + 1) ^ 2 :=
    (Nat.le_self_pow two_ne_zero r).trans (Nat.le_mul_of_pos_right _ (by positivity))
  obtain ⟨d, he⟩ : ∃ d : TameChart Γ, d.e = (Icc 1 r).lcm fun i : ℕ ↦ p ^ i - 1 :=
    exists_tameChart_e_eq_lcm h_surj (by omega)
  have he_le : d.e ≤ p ^ r ^ 2 := he.trans_le (lcm_pow_sub_one_le l.out.one_lt r)
  have h_pow (s : Γ) (hs : IsWeilPair (toGp s) 0) : K s (X ^ d.e - 1) := by
    simpa only [he] using (hK s hs).left
  -- Monic polynomials of degree at most `N` in `K s` and `K s⁻¹`, `s` the tame generator: `q` kills
  -- `s` on the lattices `Y` of the class, `q'` kills `s` on `L`.
  obtain ⟨-, q, hq, hq_deg, hKq⟩ : IsTameType p r N (K d.tameGen) := hK _ d.isWeilPair_tameGen
  obtain ⟨-, q', hq', hq'_deg, hKq'⟩ : IsTameType p r N (K d.tameGen⁻¹) :=
    hK _ d.isWeilPair_tameGen.inv
  have class_le : InClass F K U ≤ InClass (map d.subgroup.subtype ⊤) ⊥ U :=
    d.inClass_of_pow_sub_one ho h_surj h_pow
  have hL_crys : InClass (map d.subgroup.subtype ⊤) ⊥ U' L :=
    d.inClass_of_pow_sub_one ho h_surj (fun s hs ↦ h_pow s⁻¹ hs.inv) L hL
  let ζ : d.LetterRoot O := ⟨1, one_pow _⟩
  refine fun x hx ↦ d.toKummerChart.pow_smul_mem_cupOrthogonal_of_isScaledCupCoboundary ζ ho le_rfl
    class_le hL_crys _ ⟨x, hx⟩ fun Y hY P c ↦ ?_
  -- A monic polynomial `q''` of degree at most `N ^ 2` kills the generator on the dual of `Y ⊗ L`.
  obtain ⟨q'', hq'', hq''_deg, h_killed⟩ : ∃ q'' : ℤ_[p][X], q''.Monic ∧
      q''.natDegree ≤ q'.natDegree * q.natDegree ∧
      IsKilledBy (Y.tensor L).tateDual.ρ d.tameGen 0 (q''.map (algebraMap ℤ_[p] O)) := by
    simpa only [inv_inv] using exists_isKilledBy_tateDual_tensor hY hL
      d.isWeilPair_tameGen.inv hq' hq hKq' (by rwa [inv_inv])
  have h_window (i : d.Letter) : FitsWindows η (-ε) b W (d.letterJumps ζ U i) :=
    d.fitsWindows_letterJumps ζ hU i
  have h_window' (i : d.Letter) : FitsWindows η ε b W (d.letterJumps ζ U' i) :=
    d.fitsWindows_letterJumps ζ hU' i
  -- All jumps of the three sides are at most `b + 6 (W + η)`.
  have window_le {s : ℤˣ} {V : Finset ℤ} (hV : FitsWindows η s b W V) :
      ∀ u ∈ V, u ≤ (b + 6 * (W + η) : ℕ) := fun u hu ↦ (hV.le_add_add hu).trans (by omega)
  -- The jumps of the Tate dual side are `0` and the `-(v + v') - 1`.
  have tateDual_le (i : d.Letter) :
      ∀ u ∈ P.tateDualSide.jumpSet i, u ≤ (b + 6 * (W + η) : ℕ) := by
    refine d.le_of_mem_jumpSet_tateDualSide ζ P (by positivity) fun v hv v' hv' ↦ ?_
    have neg_add_le : -(v + v') ≤ b + W + 2 * η :=
      (h_window i).neg_add_le_of_opposite (h_window' i) hv hv'
    omega
  have cost_le {n : ℕ} (hn : n ≤ N * N + N) : r ^ 2 * (n + 1) ≤ r ^ 2 * (N + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (by nlinarith)
  have h_gap : NoMultipleNear p (6 * (0 + η + W)) b := noMultipleNear_of_add_lt (by omega)
  refine P.isScaledCupCoboundary_of_killsCokernel (a := 0) (κ := r ^ 2 * (N + 1) ^ 2)
    (fun i ↦ ?_) (fun i ↦ ?_) (fun i ↦ ?_) (fun _ ↦ h_gap) h_window h_window' (.inl (by simp))
    ?_ c ⟨x, hx⟩
  · exact d.killsCokernel_of_isKilledBy h_killed tateDual_le hq'' he_le hp (cost_le (by nlinarith))
  · exact d.killsCokernel_of_isKilledBy (hY.isKilledBy_of_isWeilPair hKq d.isWeilPair_tameGen)
      (fun i ↦ window_le (h_window i)) hq he_le hp (cost_le (by omega))
  · exact d.killsCokernel_of_isKilledBy (hL.isKilledBy_of_isWeilPair hKq' d.isWeilPair_tameGen)
      (fun i ↦ window_le (h_window' i)) hq' he_le hp (cost_le (by omega))
  · show 3 * (r ^ 2 * (N + 1) ^ 2 + (8 * (6 * (0 + η + W)) + 4) * d.differentBound) ≤
      3 * (r ^ 2 * (N + 1) ^ 2) + 150 * (η + W + 1)
    grw [d.differentBound_le_one]
    lia

end New.Lift
