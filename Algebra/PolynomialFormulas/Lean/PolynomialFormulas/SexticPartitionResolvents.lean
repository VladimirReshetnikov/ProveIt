import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Polynomial.Vieta
import PolynomialFormulas.Fin6BlockSystems

/-!
# Universal partition invariants for sextics

The pair invariant is the sum of the three squarefree quadratic monomials
belonging to a perfect matching.  The triple invariant is the sum of the two
squarefree cubic monomials belonging to a `3+3` partition.  Their polynomial
stabilizers are exactly the corresponding block stabilizers.  These are the
universal roots of the degree-15 and degree-10 resolvents.
-/

open scoped BigOperators
open Equiv MvPolynomial Polynomial

namespace LeanProofs.PolynomialFormulas.SexticPartitionResolvents

open LeanProofs.PolynomialFormulas.Fin6BlockSystems

abbrev Exponent := Fin 6 → ℕ

/-- Renaming variables acts contragrediently on exponent vectors. -/
def actExponent (g : S6) (d : Exponent) : Exponent :=
  fun i ↦ d (g.symm i)

theorem actExponent_injective (g : S6) : Function.Injective (actExponent g) := by
  intro d e h
  funext i
  have hi := congrFun h (g i)
  simpa [actExponent] using hi

def permuteSupport (g : S6) (s : Finset Exponent) : Finset Exponent :=
  s.image (actExponent g)

theorem permuteSupport_mul (g h : S6) (s : Finset Exponent) :
    permuteSupport (g * h) s = permuteSupport g (permuteSupport h s) := by
  rw [permuteSupport, permuteSupport, permuteSupport, Finset.image_image]
  congr 1

@[simp] theorem permuteSupport_one (s : Finset Exponent) :
    permuteSupport 1 s = s := by
  have hact : actExponent (1 : S6) = id := by
    funext d i
    change d ((1 : S6).symm i) = d i
    rw [show (1 : S6).symm = 1 by exact inv_one]
    rfl
  simp [permuteSupport, hact]

/-- Polynomial having coefficient one at precisely the supplied exponent
vectors. -/
noncomputable def polynomialOfSupport (s : Finset Exponent) :
    MvPolynomial (Fin 6) ℤ :=
  ∑ d ∈ s, monomial (Finsupp.equivFunOnFinite.symm d) 1

theorem finsupp_actExponent (g : S6) (d : Exponent) :
    (Finsupp.equivFunOnFinite.symm d).mapDomain g =
      Finsupp.equivFunOnFinite.symm (actExponent g d) := by
  ext i
  simp [actExponent]

theorem rename_polynomialOfSupport (g : S6) (s : Finset Exponent) :
    rename g (polynomialOfSupport s) =
      polynomialOfSupport (permuteSupport g s) := by
  classical
  simp only [polynomialOfSupport, map_sum, rename_monomial,
    finsupp_actExponent, permuteSupport]
  rw [Finset.sum_image (actExponent_injective g).injOn]

theorem coeff_polynomialOfSupport (s : Finset Exponent) (d : Exponent) :
    (polynomialOfSupport s).coeff (Finsupp.equivFunOnFinite.symm d) =
      if d ∈ s then 1 else 0 := by
  classical
  simp [polynomialOfSupport, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]

theorem polynomialOfSupport_injective : Function.Injective polynomialOfSupport := by
  intro s t h
  ext d
  constructor
  · intro hds
    by_contra hdt
    have hc := congrArg
      (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm d)) h
    simp [coeff_polynomialOfSupport, hds, hdt] at hc
  · intro hdt
    by_contra hds
    have hc := congrArg
      (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm d)) h
    simp [coeff_polynomialOfSupport, hds, hdt] at hc

/-- Squarefree exponent of the unordered pair `{i,j}`. -/
def pairExponent (i j : Fin 6) : Exponent :=
  fun k ↦ if k = i ∨ k = j then 1 else 0

/-- Explicit members of the three blocks in each pair partition. -/
def pairMember : PairPartition → Fin 3 → Fin 2 → Fin 6 := ![
  ![![0, 1], ![2, 3], ![4, 5]],
  ![![0, 1], ![2, 4], ![3, 5]],
  ![![0, 1], ![2, 5], ![3, 4]],
  ![![0, 2], ![1, 3], ![4, 5]],
  ![![0, 2], ![1, 4], ![3, 5]],
  ![![0, 2], ![1, 5], ![3, 4]],
  ![![0, 3], ![1, 2], ![4, 5]],
  ![![0, 3], ![1, 4], ![2, 5]],
  ![![0, 3], ![1, 5], ![2, 4]],
  ![![0, 4], ![1, 2], ![3, 5]],
  ![![0, 4], ![1, 3], ![2, 5]],
  ![![0, 4], ![1, 5], ![2, 3]],
  ![![0, 5], ![1, 2], ![3, 4]],
  ![![0, 5], ![1, 3], ![2, 4]],
  ![![0, 5], ![1, 4], ![2, 3]]
]

/-- The three within-block edges of a pair partition. -/
def pairSupport (p : PairPartition) : Finset Exponent :=
  Finset.univ.image fun b : Fin 3 ↦
    pairExponent (pairMember p b 0) (pairMember p b 1)

/-- Squarefree exponent of the unordered triple `{i,j,k}`. -/
def tripleExponent (i j k : Fin 6) : Exponent :=
  fun n ↦ if n = i ∨ n = j ∨ n = k then 1 else 0

/-- Explicit members of the two blocks in each triple partition. -/
def tripleMember : TriplePartition → Fin 2 → Fin 3 → Fin 6 := ![
  ![![0, 1, 2], ![3, 4, 5]],
  ![![0, 1, 3], ![2, 4, 5]],
  ![![0, 1, 4], ![2, 3, 5]],
  ![![0, 1, 5], ![2, 3, 4]],
  ![![0, 2, 3], ![1, 4, 5]],
  ![![0, 2, 4], ![1, 3, 5]],
  ![![0, 2, 5], ![1, 3, 4]],
  ![![0, 3, 4], ![1, 2, 5]],
  ![![0, 3, 5], ![1, 2, 4]],
  ![![0, 4, 5], ![1, 2, 3]]
]

/-- The two blocks of a triple partition, represented by their cubic
squarefree monomials. -/
def tripleSupport (p : TriplePartition) : Finset Exponent :=
  Finset.univ.image fun b : Fin 2 ↦
    tripleExponent (tripleMember p b 0) (tripleMember p b 1)
      (tripleMember p b 2)

noncomputable def pairTheta (p : PairPartition) : MvPolynomial (Fin 6) ℤ :=
  polynomialOfSupport (pairSupport p)

noncomputable def tripleTheta (p : TriplePartition) : MvPolynomial (Fin 6) ℤ :=
  polynomialOfSupport (tripleSupport p)

theorem actExponent_pairExponent (g : S6) (i j : Fin 6) :
    actExponent g (pairExponent i j) = pairExponent (g i) (g j) := by
  funext k
  simp [actExponent, pairExponent, Equiv.symm_apply_eq]

theorem actExponent_tripleExponent (g : S6) (i j k : Fin 6) :
    actExponent g (tripleExponent i j k) =
      tripleExponent (g i) (g j) (g k) := by
  funext n
  simp [actExponent, tripleExponent, Equiv.symm_apply_eq]

theorem pairExponent_eq_iff (i j k l : Fin 6) :
    pairExponent i j = pairExponent k l ↔
      ({i, j} : Finset (Fin 6)) = {k, l} := by
  constructor
  · intro h
    ext n
    have hn := congrFun h n
    by_cases hp : n = i ∨ n = j <;>
      by_cases hq : n = k ∨ n = l <;>
      simp [pairExponent, hp, hq] at hn ⊢
  · intro h
    funext n
    have hn := Finset.ext_iff.mp h n
    by_cases hp : n = i ∨ n = j <;>
      by_cases hq : n = k ∨ n = l <;>
      simp [pairExponent, hp, hq] at hn ⊢

theorem pairExponent_comm (i j : Fin 6) :
    pairExponent i j = pairExponent j i := by
  funext n
  simp [pairExponent, or_comm]

theorem tripleExponent_eq_iff (i j k a b c : Fin 6) :
    tripleExponent i j k = tripleExponent a b c ↔
      ({i, j, k} : Finset (Fin 6)) = {a, b, c} := by
  constructor
  · intro h
    ext n
    have hn := congrFun h n
    by_cases hp : n = i ∨ n = j ∨ n = k <;>
      by_cases hq : n = a ∨ n = b ∨ n = c <;>
      simp [tripleExponent, hp, hq] at hn ⊢
  · intro h
    funext n
    have hn := Finset.ext_iff.mp h n
    by_cases hp : n = i ∨ n = j ∨ n = k <;>
      by_cases hq : n = a ∨ n = b ∨ n = c <;>
      simp [tripleExponent, hp, hq] at hn ⊢

set_option maxRecDepth 100000 in
theorem pairMember_ne (p : PairPartition) (b : Fin 3) :
    pairMember p b 0 ≠ pairMember p b 1 := by
  revert p b
  decide

set_option maxRecDepth 100000 in
theorem pairLabel_pairMember (p : PairPartition) (b : Fin 3) (s : Fin 2) :
    pairLabel p (pairMember p b s) = b := by
  revert p b s
  decide

set_option maxRecDepth 100000 in
theorem pairMember_surjective (p : PairPartition) (i : Fin 6) :
    ∃ b : Fin 3, ∃ s : Fin 2, pairMember p b s = i := by
  revert p i
  decide

set_option maxRecDepth 100000 in
theorem tripleMember_pairwise_ne (p : TriplePartition) (b : Fin 2) :
    tripleMember p b 0 ≠ tripleMember p b 1 ∧
      tripleMember p b 0 ≠ tripleMember p b 2 ∧
      tripleMember p b 1 ≠ tripleMember p b 2 := by
  revert p b
  decide

set_option maxRecDepth 100000 in
theorem tripleLabel_tripleMember (p : TriplePartition) (b : Fin 2) (s : Fin 3) :
    tripleLabel p (tripleMember p b s) = b := by
  revert p b s
  decide

set_option maxRecDepth 100000 in
theorem tripleMember_surjective (p : TriplePartition) (i : Fin 6) :
    ∃ b : Fin 2, ∃ s : Fin 3, tripleMember p b s = i := by
  revert p i
  decide

set_option maxRecDepth 100000 in
theorem pairLabel_fiberCard (p : PairPartition) (b : Fin 3) :
    fiberCard (pairLabel p) b = 2 := by
  revert p b
  decide

set_option maxRecDepth 100000 in
theorem tripleLabel_fiberCard (p : TriplePartition) (b : Fin 2) :
    fiberCard (tripleLabel p) b = 3 := by
  revert p b
  decide

set_option maxRecDepth 100000 in
theorem pairLabel_samePartition_injective (p q : PairPartition)
    (h : SamePartition (pairLabel p) (pairLabel q)) : p = q := by
  revert p q
  decide

set_option maxRecDepth 100000 in
theorem tripleLabel_samePartition_injective (p q : TriplePartition)
    (h : SamePartition (tripleLabel p) (tripleLabel q)) : p = q := by
  revert p q
  decide

theorem pairExponent_mem_pairSupport_iff (p : PairPartition) (i j : Fin 6) :
    pairExponent i j ∈ pairSupport p ↔
      i ≠ j ∧ pairLabel p i = pairLabel p j := by
  classical
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨b, -, hb⟩
    let x := pairMember p b 0
    let y := pairMember p b 1
    have hxy : x ≠ y := pairMember_ne p b
    have hsets : ({x, y} : Finset (Fin 6)) = {i, j} :=
      (pairExponent_eq_iff x y i j).mp hb
    have hij : i ≠ j := by
      intro h
      subst j
      have hc := congrArg Finset.card hsets
      simpa [hxy] using hc
    have hi : pairLabel p i = b := by
      have himem : i ∈ ({x, y} : Finset (Fin 6)) := by
        rw [hsets]
        simp
      rcases (Finset.mem_insert.mp himem) with hix | hiy
      · simpa [x, hix] using pairLabel_pairMember p b 0
      · have hiy' : i = y := Finset.mem_singleton.mp hiy
        simpa [y, hiy'] using pairLabel_pairMember p b 1
    have hj : pairLabel p j = b := by
      have hjmem : j ∈ ({x, y} : Finset (Fin 6)) := by
        rw [hsets]
        simp
      rcases (Finset.mem_insert.mp hjmem) with hjx | hjy
      · simpa [x, hjx] using pairLabel_pairMember p b 0
      · have hjy' : j = y := Finset.mem_singleton.mp hjy
        simpa [y, hjy'] using pairLabel_pairMember p b 1
    exact ⟨hij, hi.trans hj.symm⟩
  · rintro ⟨hij, hlabel⟩
    obtain ⟨b, s, hs⟩ := pairMember_surjective p i
    obtain ⟨c, t, ht⟩ := pairMember_surjective p j
    have hbc : b = c := by
      have hi : pairLabel p i = b := by
        simpa only [hs] using pairLabel_pairMember p b s
      have hj : pairLabel p j = c := by
        simpa only [ht] using pairLabel_pairMember p c t
      exact hi.symm.trans (hlabel.trans hj)
    subst c
    have hst : s ≠ t := by
      intro h
      apply hij
      rw [← hs, ← ht, h]
    apply Finset.mem_image.mpr
    refine ⟨b, Finset.mem_univ b, ?_⟩
    fin_cases s <;> fin_cases t
    · exact (hst rfl).elim
    · exact congrArg₂ pairExponent hs ht
    · exact (pairExponent_comm _ _).trans (congrArg₂ pairExponent hs ht)
    · exact (hst rfl).elim

theorem tripleExponent_mem_tripleSupport_iff
    (p : TriplePartition) (i j k : Fin 6) :
    tripleExponent i j k ∈ tripleSupport p ↔
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        tripleLabel p i = tripleLabel p j ∧
        tripleLabel p j = tripleLabel p k := by
  classical
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨d, -, hd⟩
    let x := tripleMember p d 0
    let y := tripleMember p d 1
    let z := tripleMember p d 2
    have hxyz : x ≠ y ∧ x ≠ z ∧ y ≠ z :=
      tripleMember_pairwise_ne p d
    have hsets : ({x, y, z} : Finset (Fin 6)) = {i, j, k} :=
      (tripleExponent_eq_iff x y z i j k).mp hd
    have hcard : ({i, j, k} : Finset (Fin 6)).card = 3 := by
      rw [← hsets]
      simp [hxyz.1, hxyz.2.1, hxyz.2.2]
    have hij : i ≠ j := by
      intro h; subst j
      by_cases h' : i = k <;> simp [h'] at hcard
    have hik : i ≠ k := by
      intro h; subst k
      by_cases h' : i = j
      · simp [h'] at hcard
      · have hji : j ≠ i := Ne.symm h'
        simp [hji] at hcard
    have hjk : j ≠ k := by
      intro h; subst k
      by_cases h' : i = j <;> simp [h'] at hcard
    have label_of_mem (n : Fin 6) (hn : n ∈ ({x, y, z} : Finset (Fin 6))) :
        tripleLabel p n = d := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with hn | hn | hn
      · simpa [x, hn] using tripleLabel_tripleMember p d 0
      · simpa [y, hn] using tripleLabel_tripleMember p d 1
      · simpa [z, hn] using tripleLabel_tripleMember p d 2
    have hi : tripleLabel p i = d := label_of_mem i (by rw [hsets]; simp)
    have hj : tripleLabel p j = d := label_of_mem j (by rw [hsets]; simp)
    have hk : tripleLabel p k = d := label_of_mem k (by rw [hsets]; simp)
    exact ⟨hij, hik, hjk, hi.trans hj.symm, hj.trans hk.symm⟩
  · rintro ⟨hij, hik, hjk, hijLabel, hjkLabel⟩
    obtain ⟨d, a, ha⟩ := tripleMember_surjective p i
    obtain ⟨e, b, hb⟩ := tripleMember_surjective p j
    obtain ⟨f, c, hc⟩ := tripleMember_surjective p k
    have hde : d = e := by
      have hi : tripleLabel p i = d := by
        simpa only [ha] using tripleLabel_tripleMember p d a
      have hj : tripleLabel p j = e := by
        simpa only [hb] using tripleLabel_tripleMember p e b
      exact hi.symm.trans (hijLabel.trans hj)
    have hef : e = f := by
      have hj : tripleLabel p j = e := by
        simpa only [hb] using tripleLabel_tripleMember p e b
      have hk : tripleLabel p k = f := by
        simpa only [hc] using tripleLabel_tripleMember p f c
      exact hj.symm.trans (hjkLabel.trans hk)
    subst e
    subst f
    have hab : a ≠ b := by
      intro h; apply hij; rw [← ha, ← hb, h]
    have hac : a ≠ c := by
      intro h; apply hik; rw [← ha, ← hc, h]
    have hbc : b ≠ c := by
      intro h; apply hjk; rw [← hb, ← hc, h]
    apply Finset.mem_image.mpr
    refine ⟨d, Finset.mem_univ d, ?_⟩
    fin_cases a <;> fin_cases b <;> fin_cases c
    all_goals try { exact (hab rfl).elim }
    all_goals try { exact (hac rfl).elim }
    all_goals try { exact (hbc rfl).elim }
    all_goals
      apply (tripleExponent_eq_iff _ _ _ _ _ _).2
      ext n
      simp_all only [Finset.mem_insert, Finset.mem_singleton]
      aesop

set_option maxRecDepth 100000 in
theorem exists_third_in_tripleBlock (p : TriplePartition) (i j : Fin 6)
    (hij : i ≠ j) (hlabel : tripleLabel p i = tripleLabel p j) :
    ∃ k : Fin 6, i ≠ k ∧ j ≠ k ∧
      tripleLabel p j = tripleLabel p k := by
  revert p i j
  decide

theorem pairSupport_injective : Function.Injective pairSupport := by
  intro p q hpq
  apply pairLabel_samePartition_injective p q
  intro i j
  by_cases hij : i = j
  · simp [hij]
  · constructor
    · intro h
      have hm : pairExponent i j ∈ pairSupport p :=
        (pairExponent_mem_pairSupport_iff p i j).2 ⟨hij, h⟩
      rw [hpq] at hm
      exact (pairExponent_mem_pairSupport_iff q i j).1 hm |>.2
    · intro h
      have hm : pairExponent i j ∈ pairSupport q :=
        (pairExponent_mem_pairSupport_iff q i j).2 ⟨hij, h⟩
      rw [← hpq] at hm
      exact (pairExponent_mem_pairSupport_iff p i j).1 hm |>.2

theorem tripleSupport_injective : Function.Injective tripleSupport := by
  intro p q hpq
  apply tripleLabel_samePartition_injective p q
  intro i j
  by_cases hij : i = j
  · simp [hij]
  · constructor
    · intro h
      obtain ⟨k, hik, hjk, hjkLabel⟩ :=
        exists_third_in_tripleBlock p i j hij h
      have hm : tripleExponent i j k ∈ tripleSupport p :=
        (tripleExponent_mem_tripleSupport_iff p i j k).2
          ⟨hij, hik, hjk, h, hjkLabel⟩
      rw [hpq] at hm
      exact (tripleExponent_mem_tripleSupport_iff q i j k).1 hm |>.2.2.2.1
    · intro h
      obtain ⟨k, hik, hjk, hjkLabel⟩ :=
        exists_third_in_tripleBlock q i j hij h
      have hm : tripleExponent i j k ∈ tripleSupport q :=
        (tripleExponent_mem_tripleSupport_iff q i j k).2
          ⟨hij, hik, hjk, h, hjkLabel⟩
      rw [← hpq] at hm
      exact (tripleExponent_mem_tripleSupport_iff p i j k).1 hm |>.2.2.2.1

theorem pairTheta_injective : Function.Injective pairTheta := by
  intro p q h
  apply pairSupport_injective
  exact polynomialOfSupport_injective h

theorem tripleTheta_injective : Function.Injective tripleTheta := by
  intro p q h
  apply tripleSupport_injective
  exact polynomialOfSupport_injective h

theorem pairSupport_stabilized_iff (p : PairPartition) (g : S6) :
    permuteSupport g (pairSupport p) = pairSupport p ↔
      Preserves (pairLabel p) g := by
  constructor
  · intro hs i j
    have hsInv : permuteSupport g⁻¹ (pairSupport p) = pairSupport p := by
      calc
        permuteSupport g⁻¹ (pairSupport p) =
            permuteSupport g⁻¹ (permuteSupport g (pairSupport p)) := by rw [hs]
        _ = permuteSupport (g⁻¹ * g) (pairSupport p) :=
          (permuteSupport_mul _ _ _).symm
        _ = pairSupport p := by simp
    constructor
    · intro hij
      by_cases hij' : i = j
      · simpa [hij']
      · have hback : pairExponent (g i) (g j) ∈ pairSupport p :=
          (pairExponent_mem_pairSupport_iff p (g i) (g j)).2
            ⟨g.injective.ne hij', hij⟩
        have himage : actExponent g⁻¹ (pairExponent (g i) (g j)) ∈
            permuteSupport g⁻¹ (pairSupport p) :=
          Finset.mem_image.mpr ⟨pairExponent (g i) (g j), hback, rfl⟩
        rw [hsInv] at himage
        have hpre : pairExponent i j ∈ pairSupport p := by
          simpa [actExponent_pairExponent] using himage
        exact (pairExponent_mem_pairSupport_iff p i j).1 hpre |>.2
    · intro hij
      by_cases hij' : i = j
      · simpa [hij']
      · have hmem : pairExponent i j ∈ pairSupport p :=
          (pairExponent_mem_pairSupport_iff p i j).2 ⟨hij', hij⟩
        have hmem' : actExponent g (pairExponent i j) ∈
            permuteSupport g (pairSupport p) :=
          Finset.mem_image.mpr ⟨pairExponent i j, hmem, rfl⟩
        rw [hs, actExponent_pairExponent] at hmem'
        exact (pairExponent_mem_pairSupport_iff p (g i) (g j)).1 hmem' |>.2
  · intro hg
    apply Finset.ext
    intro d
    constructor
    · intro hd
      rcases Finset.mem_image.mp hd with ⟨e, he, rfl⟩
      rcases Finset.mem_image.mp he with ⟨b, _, rfl⟩
      have hij := (pairExponent_mem_pairSupport_iff p
        (pairMember p b 0) (pairMember p b 1)).1
          (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩)
      rw [actExponent_pairExponent]
      apply (pairExponent_mem_pairSupport_iff p _ _).2
      exact ⟨g.injective.ne hij.1, (hg _ _).2 hij.2⟩
    · intro hd
      rcases Finset.mem_image.mp hd with ⟨c, _, rfl⟩
      let i := pairMember p c 0
      let j := pairMember p c 1
      have hij := (pairExponent_mem_pairSupport_iff p i j).1
        (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩)
      let a := g⁻¹ i
      let b := g⁻¹ j
      have hab : pairExponent a b ∈ pairSupport p :=
        (pairExponent_mem_pairSupport_iff p a b).2 ⟨by
          intro h
          apply hij.1
          exact g.symm.injective h, (hg a b).1 (by simpa [a, b] using hij.2)⟩
      apply Finset.mem_image.mpr
      refine ⟨pairExponent a b, hab, ?_⟩
      simp [actExponent_pairExponent, a, b, i, j]

theorem tripleSupport_stabilized_iff (p : TriplePartition) (g : S6) :
    permuteSupport g (tripleSupport p) = tripleSupport p ↔
      Preserves (tripleLabel p) g := by
  constructor
  · intro hs i j
    have hsInv : permuteSupport g⁻¹ (tripleSupport p) = tripleSupport p := by
      calc
        permuteSupport g⁻¹ (tripleSupport p) =
            permuteSupport g⁻¹ (permuteSupport g (tripleSupport p)) := by rw [hs]
        _ = permuteSupport (g⁻¹ * g) (tripleSupport p) :=
          (permuteSupport_mul _ _ _).symm
        _ = tripleSupport p := by simp
    constructor
    · intro hij
      by_cases hij' : i = j
      · simpa [hij']
      · obtain ⟨l, hil, hjl, hlabel⟩ :=
          exists_third_in_tripleBlock p (g i) (g j)
            (g.injective.ne hij') hij
        have hmem : tripleExponent (g i) (g j) l ∈ tripleSupport p :=
          (tripleExponent_mem_tripleSupport_iff p (g i) (g j) l).2
            ⟨g.injective.ne hij', hil, hjl, hij, hlabel⟩
        have himage : actExponent g⁻¹ (tripleExponent (g i) (g j) l) ∈
            permuteSupport g⁻¹ (tripleSupport p) :=
          Finset.mem_image.mpr ⟨tripleExponent (g i) (g j) l, hmem, rfl⟩
        rw [hsInv] at himage
        have hpre : tripleExponent i j (g⁻¹ l) ∈ tripleSupport p := by
          simpa [actExponent_tripleExponent] using himage
        exact (tripleExponent_mem_tripleSupport_iff p i j (g⁻¹ l)).1 hpre |>.2.2.2.1
    · intro hij
      by_cases hij' : i = j
      · simpa [hij']
      · obtain ⟨k, hik, hjk, hlabel⟩ :=
          exists_third_in_tripleBlock p i j hij' hij
        have hmem : tripleExponent i j k ∈ tripleSupport p :=
          (tripleExponent_mem_tripleSupport_iff p i j k).2
            ⟨hij', hik, hjk, hij, hlabel⟩
        have hmem' : actExponent g (tripleExponent i j k) ∈
            permuteSupport g (tripleSupport p) :=
          Finset.mem_image.mpr ⟨tripleExponent i j k, hmem, rfl⟩
        rw [hs, actExponent_tripleExponent] at hmem'
        exact (tripleExponent_mem_tripleSupport_iff p (g i) (g j) (g k)).1
          hmem' |>.2.2.2.1
  · intro hg
    apply Finset.ext
    intro d
    constructor
    · intro hd
      rcases Finset.mem_image.mp hd with ⟨e, he, rfl⟩
      rcases Finset.mem_image.mp he with ⟨b, _, rfl⟩
      have hijk := (tripleExponent_mem_tripleSupport_iff p
        (tripleMember p b 0) (tripleMember p b 1) (tripleMember p b 2)).1
          (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩)
      rw [actExponent_tripleExponent]
      apply (tripleExponent_mem_tripleSupport_iff p _ _ _).2
      exact ⟨g.injective.ne hijk.1, g.injective.ne hijk.2.1,
        g.injective.ne hijk.2.2.1,
        (hg _ _).2 hijk.2.2.2.1,
        (hg _ _).2 hijk.2.2.2.2⟩
    · intro hd
      rcases Finset.mem_image.mp hd with ⟨c, _, rfl⟩
      let i := tripleMember p c 0
      let j := tripleMember p c 1
      let k := tripleMember p c 2
      have hijk := (tripleExponent_mem_tripleSupport_iff p i j k).1
        (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩)
      let a := g⁻¹ i
      let b := g⁻¹ j
      let e := g⁻¹ k
      have hab : a ≠ b := by
        intro h
        exact hijk.1 (g.symm.injective h)
      have hae : a ≠ e := by
        intro h
        exact hijk.2.1 (g.symm.injective h)
      have hbe : b ≠ e := by
        intro h
        exact hijk.2.2.1 (g.symm.injective h)
      have habLabel : tripleLabel p a = tripleLabel p b :=
        (hg a b).1 (by simpa [a, b] using hijk.2.2.2.1)
      have hbeLabel : tripleLabel p b = tripleLabel p e :=
        (hg b e).1 (by simpa [b, e] using hijk.2.2.2.2)
      have habc : tripleExponent a b e ∈ tripleSupport p :=
        (tripleExponent_mem_tripleSupport_iff p a b e).2
          ⟨hab, hae, hbe, habLabel, hbeLabel⟩
      apply Finset.mem_image.mpr
      refine ⟨tripleExponent a b e, habc, ?_⟩
      simp [actExponent_tripleExponent, a, b, e, i, j, k]

/-- The polynomial stabilizer of a pair invariant is its block stabilizer. -/
theorem rename_pairTheta_eq_self_iff (p : PairPartition) (g : S6) :
    rename g (pairTheta p) = pairTheta p ↔ g ∈ pairStabilizer p := by
  rw [pairTheta, rename_polynomialOfSupport]
  rw [polynomialOfSupport_injective.eq_iff, pairSupport_stabilized_iff]
  rfl

/-- The polynomial stabilizer of a triple invariant is its block stabilizer. -/
theorem rename_tripleTheta_eq_self_iff (p : TriplePartition) (g : S6) :
    rename g (tripleTheta p) = tripleTheta p ↔ g ∈ tripleStabilizer p := by
  rw [tripleTheta, rename_polynomialOfSupport]
  rw [polynomialOfSupport_injective.eq_iff, tripleSupport_stabilized_iff]
  rfl

/-! ## The two finite formal orbits -/

def transportedLabel {m : ℕ} (label : Fin 6 → Fin m) (g : S6) :
    Fin 6 → Fin m := fun i ↦ label (g.symm i)

theorem fiberCard_transportedLabel {m : ℕ} (label : Fin 6 → Fin m)
    (g : S6) (b : Fin m) :
    fiberCard (transportedLabel label g) b = fiberCard label b := by
  classical
  unfold fiberCard transportedLabel
  rw [show (Finset.univ.filter fun i ↦ label (g.symm i) = b) =
      (Finset.univ.filter fun i ↦ label i = b).image g by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      exact ⟨g.symm i, hi, g.apply_symm_apply i⟩
    · rintro ⟨a, ha, hgi⟩
      rw [← hgi, g.symm_apply_apply]
      exact ha]
  exact Finset.card_image_of_injective _ g.injective

theorem exists_pairSupport_permute (g : S6) (p : PairPartition) :
    ∃ q : PairPartition,
      permuteSupport g (pairSupport p) = pairSupport q := by
  let label := transportedLabel (pairLabel p) g
  have hcard : ∀ b, fiberCard label b = 2 := by
    intro b
    rw [fiberCard_transportedLabel]
    exact pairLabel_fiberCard p b
  obtain ⟨q, hq⟩ := pairLabel_complete label hcard
  refine ⟨q, Finset.ext fun d ↦ ?_⟩
  constructor
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨e, he, rfl⟩
    rcases Finset.mem_image.mp he with ⟨b, _, rfl⟩
    have hxy := (pairExponent_mem_pairSupport_iff p
      (pairMember p b 0) (pairMember p b 1)).1
        (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩)
    rw [actExponent_pairExponent]
    apply (pairExponent_mem_pairSupport_iff q _ _).2
    refine ⟨g.injective.ne hxy.1, (hq _ _).1 ?_⟩
    simpa [label, transportedLabel] using hxy.2
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨b, _, rfl⟩
    let i := pairMember q b 0
    let j := pairMember q b 1
    have hij := (pairExponent_mem_pairSupport_iff q i j).1
      (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩)
    let a := g⁻¹ i
    let c := g⁻¹ j
    have hac : pairExponent a c ∈ pairSupport p :=
      (pairExponent_mem_pairSupport_iff p a c).2 ⟨by
        intro h
        exact hij.1 (g.symm.injective h), by
        have hl : label i = label j := (hq i j).2 hij.2
        simpa [label, transportedLabel, a, c] using hl⟩
    apply Finset.mem_image.mpr
    refine ⟨pairExponent a c, hac, ?_⟩
    simp [actExponent_pairExponent, a, c, i, j]

theorem exists_tripleSupport_permute (g : S6) (p : TriplePartition) :
    ∃ q : TriplePartition,
      permuteSupport g (tripleSupport p) = tripleSupport q := by
  let label := transportedLabel (tripleLabel p) g
  have hcard : ∀ b, fiberCard label b = 3 := by
    intro b
    rw [fiberCard_transportedLabel]
    exact tripleLabel_fiberCard p b
  obtain ⟨q, hq⟩ := tripleLabel_complete label hcard
  refine ⟨q, Finset.ext fun d ↦ ?_⟩
  constructor
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨e, he, rfl⟩
    rcases Finset.mem_image.mp he with ⟨b, _, rfl⟩
    have hxyz := (tripleExponent_mem_tripleSupport_iff p
      (tripleMember p b 0) (tripleMember p b 1) (tripleMember p b 2)).1
        (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩)
    rw [actExponent_tripleExponent]
    apply (tripleExponent_mem_tripleSupport_iff q _ _ _).2
    exact ⟨g.injective.ne hxyz.1, g.injective.ne hxyz.2.1,
      g.injective.ne hxyz.2.2.1,
      (hq _ _).1 (by simpa [label, transportedLabel] using hxyz.2.2.2.1),
      (hq _ _).1 (by simpa [label, transportedLabel] using hxyz.2.2.2.2)⟩
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨b, _, rfl⟩
    let i := tripleMember q b 0
    let j := tripleMember q b 1
    let k := tripleMember q b 2
    have hijk := (tripleExponent_mem_tripleSupport_iff q i j k).1
      (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩)
    let a := g⁻¹ i
    let c := g⁻¹ j
    let e := g⁻¹ k
    have hace : tripleExponent a c e ∈ tripleSupport p :=
      (tripleExponent_mem_tripleSupport_iff p a c e).2 ⟨by
        intro h; exact hijk.1 (g.symm.injective h), by
        intro h; exact hijk.2.1 (g.symm.injective h), by
        intro h; exact hijk.2.2.1 (g.symm.injective h), by
        have hl : label i = label j := (hq i j).2 hijk.2.2.2.1
        simpa [label, transportedLabel, a, c] using hl, by
        have hl : label j = label k := (hq j k).2 hijk.2.2.2.2
        simpa [label, transportedLabel, c, e] using hl⟩
    apply Finset.mem_image.mpr
    refine ⟨tripleExponent a c e, hace, ?_⟩
    simp [actExponent_tripleExponent, a, c, e, i, j, k]

theorem rename_pairTheta_exists (g : S6) (p : PairPartition) :
    ∃ q : PairPartition, rename g (pairTheta p) = pairTheta q := by
  obtain ⟨q, hq⟩ := exists_pairSupport_permute g p
  exact ⟨q, by simp [pairTheta, rename_polynomialOfSupport, hq]⟩

theorem rename_tripleTheta_exists (g : S6) (p : TriplePartition) :
    ∃ q : TriplePartition, rename g (tripleTheta p) = tripleTheta q := by
  obtain ⟨q, hq⟩ := exists_tripleSupport_permute g p
  exact ⟨q, by simp [tripleTheta, rename_polynomialOfSupport, hq]⟩

noncomputable def pairThetaSet : Finset (MvPolynomial (Fin 6) ℤ) :=
  Finset.univ.image pairTheta

noncomputable def tripleThetaSet : Finset (MvPolynomial (Fin 6) ℤ) :=
  Finset.univ.image tripleTheta

theorem card_pairThetaSet : pairThetaSet.card = 15 := by
  rw [pairThetaSet, Finset.card_image_of_injective _ pairTheta_injective]
  simp

theorem card_tripleThetaSet : tripleThetaSet.card = 10 := by
  rw [tripleThetaSet, Finset.card_image_of_injective _ tripleTheta_injective]
  simp

theorem image_rename_pairThetaSet (g : S6) :
    pairThetaSet.image (rename g) = pairThetaSet := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro t ht
    rcases Finset.mem_image.mp ht with ⟨u, hu, rfl⟩
    rcases Finset.mem_image.mp hu with ⟨p, _, rfl⟩
    obtain ⟨q, hq⟩ := rename_pairTheta_exists g p
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, hq.symm⟩
  · rw [Finset.card_image_of_injective _
      (MvPolynomial.rename_injective g g.injective)]

theorem image_rename_tripleThetaSet (g : S6) :
    tripleThetaSet.image (rename g) = tripleThetaSet := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro t ht
    rcases Finset.mem_image.mp ht with ⟨u, hu, rfl⟩
    rcases Finset.mem_image.mp hu with ⟨p, _, rfl⟩
    obtain ⟨q, hq⟩ := rename_tripleTheta_exists g p
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, hq.symm⟩
  · rw [Finset.card_image_of_injective _
      (MvPolynomial.rename_injective g g.injective)]

/-! ## Universal degree-15 and degree-10 resolvents -/

noncomputable def pairUniversalResolvent :
    Polynomial (MvPolynomial (Fin 6) ℤ) :=
  ∏ t ∈ pairThetaSet, (Polynomial.X - Polynomial.C t)

noncomputable def tripleUniversalResolvent :
    Polynomial (MvPolynomial (Fin 6) ℤ) :=
  ∏ t ∈ tripleThetaSet, (Polynomial.X - Polynomial.C t)

theorem pairUniversalResolvent_monic : pairUniversalResolvent.Monic := by
  exact Polynomial.monic_prod_of_monic _ _
    (fun _ _ ↦ Polynomial.monic_X_sub_C _)

theorem tripleUniversalResolvent_monic : tripleUniversalResolvent.Monic := by
  exact Polynomial.monic_prod_of_monic _ _
    (fun _ _ ↦ Polynomial.monic_X_sub_C _)

theorem pairUniversalResolvent_natDegree :
    pairUniversalResolvent.natDegree = 15 := by
  rw [pairUniversalResolvent,
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card, card_pairThetaSet]

theorem tripleUniversalResolvent_natDegree :
    tripleUniversalResolvent.natDegree = 10 := by
  rw [tripleUniversalResolvent,
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card, card_tripleThetaSet]

theorem pairUniversalResolvent_rename (g : S6) :
    pairUniversalResolvent.map (rename g).toRingHom =
      pairUniversalResolvent := by
  classical
  rw [pairUniversalResolvent, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  change (∏ t ∈ pairThetaSet,
      (Polynomial.X - Polynomial.C (rename g t))) = _
  calc
    (∏ t ∈ pairThetaSet,
        (Polynomial.X - Polynomial.C (rename g t))) =
        ∏ t ∈ pairThetaSet.image (rename g),
          (Polynomial.X - Polynomial.C t) := by
      exact (Finset.prod_image
        (f := fun t ↦ Polynomial.X - Polynomial.C t)
        (g := rename g)
        (MvPolynomial.rename_injective g g.injective).injOn).symm
    _ = ∏ t ∈ pairThetaSet,
          (Polynomial.X - Polynomial.C t) := by
      rw [image_rename_pairThetaSet]

theorem tripleUniversalResolvent_rename (g : S6) :
    tripleUniversalResolvent.map (rename g).toRingHom =
      tripleUniversalResolvent := by
  classical
  rw [tripleUniversalResolvent, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  change (∏ t ∈ tripleThetaSet,
      (Polynomial.X - Polynomial.C (rename g t))) = _
  calc
    (∏ t ∈ tripleThetaSet,
        (Polynomial.X - Polynomial.C (rename g t))) =
        ∏ t ∈ tripleThetaSet.image (rename g),
          (Polynomial.X - Polynomial.C t) := by
      exact (Finset.prod_image
        (f := fun t ↦ Polynomial.X - Polynomial.C t)
        (g := rename g)
        (MvPolynomial.rename_injective g g.injective).injOn).symm
    _ = ∏ t ∈ tripleThetaSet,
          (Polynomial.X - Polynomial.C t) := by
      rw [image_rename_tripleThetaSet]

theorem pairUniversalResolvent_coefficient_isSymmetric (n : ℕ) :
    (pairUniversalResolvent.coeff n).IsSymmetric := by
  intro g
  have h := congrArg
    (fun P : Polynomial (MvPolynomial (Fin 6) ℤ) ↦ P.coeff n)
    (pairUniversalResolvent_rename g)
  simp only [Polynomial.coeff_map] at h
  exact h

theorem tripleUniversalResolvent_coefficient_isSymmetric (n : ℕ) :
    (tripleUniversalResolvent.coeff n).IsSymmetric := by
  intro g
  have h := congrArg
    (fun P : Polynomial (MvPolynomial (Fin 6) ℤ) ↦ P.coeff n)
    (tripleUniversalResolvent_rename g)
  simp only [Polynomial.coeff_map] at h
  exact h

noncomputable def pairSymmetricResolventCoefficient (n : ℕ) :
    MvPolynomial.symmetricSubalgebra (Fin 6) ℤ :=
  ⟨pairUniversalResolvent.coeff n,
    pairUniversalResolvent_coefficient_isSymmetric n⟩

noncomputable def tripleSymmetricResolventCoefficient (n : ℕ) :
    MvPolynomial.symmetricSubalgebra (Fin 6) ℤ :=
  ⟨tripleUniversalResolvent.coeff n,
    tripleUniversalResolvent_coefficient_isSymmetric n⟩

noncomputable def pairElementaryResolventCoefficient (n : ℕ) :
    MvPolynomial (Fin 6) ℤ :=
  (MvPolynomial.esymmAlgEquiv (Fin 6) ℤ (by simp)).symm
    (pairSymmetricResolventCoefficient n)

noncomputable def tripleElementaryResolventCoefficient (n : ℕ) :
    MvPolynomial (Fin 6) ℤ :=
  (MvPolynomial.esymmAlgEquiv (Fin 6) ℤ (by simp)).symm
    (tripleSymmetricResolventCoefficient n)

theorem esymmAlgEquiv_pairElementaryResolventCoefficient (n : ℕ) :
    MvPolynomial.esymmAlgEquiv (Fin 6) ℤ (by simp)
        (pairElementaryResolventCoefficient n) =
      pairSymmetricResolventCoefficient n := by
  exact (MvPolynomial.esymmAlgEquiv (Fin 6) ℤ (by simp)).apply_symm_apply _

theorem esymmAlgEquiv_tripleElementaryResolventCoefficient (n : ℕ) :
    MvPolynomial.esymmAlgEquiv (Fin 6) ℤ (by simp)
        (tripleElementaryResolventCoefficient n) =
      tripleSymmetricResolventCoefficient n := by
  exact (MvPolynomial.esymmAlgEquiv (Fin 6) ℤ (by simp)).apply_symm_apply _

theorem pairUniversalResolvent_coefficient_eq_aeval_esymm (n : ℕ) :
    pairUniversalResolvent.coeff n =
      MvPolynomial.aeval
        (fun i : Fin 6 ↦ MvPolynomial.esymm (Fin 6) ℤ (i + 1))
        (pairElementaryResolventCoefficient n) := by
  have h := congrArg Subtype.val
    (esymmAlgEquiv_pairElementaryResolventCoefficient n)
  simpa only [MvPolynomial.esymmAlgEquiv_apply,
    MvPolynomial.esymmAlgHom_apply, pairSymmetricResolventCoefficient] using h.symm

theorem tripleUniversalResolvent_coefficient_eq_aeval_esymm (n : ℕ) :
    tripleUniversalResolvent.coeff n =
      MvPolynomial.aeval
        (fun i : Fin 6 ↦ MvPolynomial.esymm (Fin 6) ℤ (i + 1))
        (tripleElementaryResolventCoefficient n) := by
  have h := congrArg Subtype.val
    (esymmAlgEquiv_tripleElementaryResolventCoefficient n)
  simpa only [MvPolynomial.esymmAlgEquiv_apply,
    MvPolynomial.esymmAlgHom_apply, tripleSymmetricResolventCoefficient] using h.symm

/-! ## Scalar specialization -/

section Specialization

variable {K : Type*} [CommRing K]

noncomputable def pairThetaValue (r : Fin 6 → K) (p : PairPartition) : K :=
  MvPolynomial.eval₂ (Int.castRingHom K) r (pairTheta p)

noncomputable def tripleThetaValue (r : Fin 6 → K) (p : TriplePartition) : K :=
  MvPolynomial.eval₂ (Int.castRingHom K) r (tripleTheta p)

noncomputable def pairScalarResolvent (r : Fin 6 → K) : Polynomial K :=
  pairUniversalResolvent.map
    (MvPolynomial.eval₂Hom (Int.castRingHom K) r)

noncomputable def tripleScalarResolvent (r : Fin 6 → K) : Polynomial K :=
  tripleUniversalResolvent.map
    (MvPolynomial.eval₂Hom (Int.castRingHom K) r)

theorem pairScalarResolvent_permute (r : Fin 6 → K) (g : S6) :
    pairScalarResolvent (fun i ↦ r (g i)) = pairScalarResolvent r := by
  let e₁ := MvPolynomial.eval₂Hom (Int.castRingHom K) (fun i ↦ r (g i))
  let e₂ := (MvPolynomial.eval₂Hom (Int.castRingHom K) r).comp
    (rename g).toRingHom
  have heval : e₁ = e₂ := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [e₁, e₂]
    · intro i
      simp [e₁, e₂]
  change pairUniversalResolvent.map e₁ =
    pairUniversalResolvent.map
      (MvPolynomial.eval₂Hom (Int.castRingHom K) r)
  rw [heval, ← Polynomial.map_map, pairUniversalResolvent_rename]

theorem tripleScalarResolvent_permute (r : Fin 6 → K) (g : S6) :
    tripleScalarResolvent (fun i ↦ r (g i)) = tripleScalarResolvent r := by
  let e₁ := MvPolynomial.eval₂Hom (Int.castRingHom K) (fun i ↦ r (g i))
  let e₂ := (MvPolynomial.eval₂Hom (Int.castRingHom K) r).comp
    (rename g).toRingHom
  have heval : e₁ = e₂ := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [e₁, e₂]
    · intro i
      simp [e₁, e₂]
  change tripleUniversalResolvent.map e₁ =
    tripleUniversalResolvent.map
      (MvPolynomial.eval₂Hom (Int.castRingHom K) r)
  rw [heval, ← Polynomial.map_map, tripleUniversalResolvent_rename]

theorem pairScalarResolvent_eq_prod (r : Fin 6 → K) :
    pairScalarResolvent r =
      ∏ p : PairPartition,
        (Polynomial.X - Polynomial.C (pairThetaValue r p)) := by
  classical
  rw [pairScalarResolvent, pairUniversalResolvent, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    pairThetaSet, pairThetaValue]
  rw [Finset.prod_image pairTheta_injective.injOn]
  rfl

theorem tripleScalarResolvent_eq_prod (r : Fin 6 → K) :
    tripleScalarResolvent r =
      ∏ p : TriplePartition,
        (Polynomial.X - Polynomial.C (tripleThetaValue r p)) := by
  classical
  rw [tripleScalarResolvent, tripleUniversalResolvent, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    tripleThetaSet, tripleThetaValue]
  rw [Finset.prod_image tripleTheta_injective.injOn]
  rfl

theorem pairScalarResolvent_monic (r : Fin 6 → K) :
    (pairScalarResolvent r).Monic := by
  rw [pairScalarResolvent_eq_prod]
  exact Polynomial.monic_prod_of_monic _ _
    (fun _ _ ↦ Polynomial.monic_X_sub_C _)

theorem tripleScalarResolvent_monic (r : Fin 6 → K) :
    (tripleScalarResolvent r).Monic := by
  rw [tripleScalarResolvent_eq_prod]
  exact Polynomial.monic_prod_of_monic _ _
    (fun _ _ ↦ Polynomial.monic_X_sub_C _)

theorem pairScalarResolvent_natDegree [Nontrivial K] (r : Fin 6 → K) :
    (pairScalarResolvent r).natDegree = 15 := by
  rw [pairScalarResolvent_eq_prod,
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  simp

theorem tripleScalarResolvent_natDegree [Nontrivial K] (r : Fin 6 → K) :
    (tripleScalarResolvent r).natDegree = 10 := by
  rw [tripleScalarResolvent_eq_prod,
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  simp

theorem pairScalarResolvent_isRoot_iff [IsDomain K]
    (r : Fin 6 → K) (x : K) :
    (pairScalarResolvent r).IsRoot x ↔
      ∃ p : PairPartition, pairThetaValue r p = x := by
  classical
  simp only [Polynomial.IsRoot, pairScalarResolvent_eq_prod,
    Polynomial.eval_prod, Finset.prod_eq_zero_iff, Finset.mem_univ,
    true_and, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    sub_eq_zero]
  constructor <;> rintro ⟨p, hp⟩ <;> exact ⟨p, hp.symm⟩

theorem tripleScalarResolvent_isRoot_iff [IsDomain K]
    (r : Fin 6 → K) (x : K) :
    (tripleScalarResolvent r).IsRoot x ↔
      ∃ p : TriplePartition, tripleThetaValue r p = x := by
  classical
  simp only [Polynomial.IsRoot, tripleScalarResolvent_eq_prod,
    Polynomial.eval_prod, Finset.prod_eq_zero_iff, Finset.mem_univ,
    true_and, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    sub_eq_zero]
  constructor <;> rintro ⟨p, hp⟩ <;> exact ⟨p, hp.symm⟩

theorem pairScalarResolvent_coefficient_eq (r : Fin 6 → K) (n : ℕ) :
    (pairScalarResolvent r).coeff n =
      MvPolynomial.eval₂ (Int.castRingHom K) r
        (MvPolynomial.aeval
          (fun i : Fin 6 ↦ MvPolynomial.esymm (Fin 6) ℤ (i + 1))
          (pairElementaryResolventCoefficient n)) := by
  rw [pairScalarResolvent, Polynomial.coeff_map,
    pairUniversalResolvent_coefficient_eq_aeval_esymm]
  rfl

theorem tripleScalarResolvent_coefficient_eq (r : Fin 6 → K) (n : ℕ) :
    (tripleScalarResolvent r).coeff n =
      MvPolynomial.eval₂ (Int.castRingHom K) r
        (MvPolynomial.aeval
          (fun i : Fin 6 ↦ MvPolynomial.esymm (Fin 6) ℤ (i + 1))
          (tripleElementaryResolventCoefficient n)) := by
  rw [tripleScalarResolvent, Polynomial.coeff_map,
    tripleUniversalResolvent_coefficient_eq_aeval_esymm]
  rfl

end Specialization

end LeanProofs.PolynomialFormulas.SexticPartitionResolvents
