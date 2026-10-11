import GowersSzemeredi.Proofs05IntegerRuns
import GowersSzemeredi.Proofs16OrientedPartitions
import GowersSzemeredi.Proofs05SimultaneousDirichlet
import Mathlib.Data.Nat.Sqrt

/-! Genuine integer-representative refinements of modular progressions,
with an explicit budget measured by the centered modular step. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Splitting at wrap boundaries retains every point and gives a cell
budget depending on the canonical positive step, for any nonzero modulus. -/
theorem ModAP.integer_representative_partition {N : Nat} [NeZero N]
    (P : ModAP N) (hP : P.IsProper) (hd : P.step ≠ 0) :
    ∃ M : Nat, ∃ R : Fin M → ModAP N,
      IsPartition (fun j => (R j).carrier) P.carrier ∧
      (∀ j, (R j).HasIntegerRepresentatives) ∧
      M * N < 2 * N + P.length * P.step.val := by
  classical
  have hdpos : 0 < P.step.val := by
    by_contra h
    have hz : P.step.val = 0 := by omega
    have hc := ZMod.natCast_zmod_val P.step
    rw [hz, Nat.cast_zero] at hc
    exact hd hc.symm
  have heval (i : Nat) :
      ((P.start.val + i * P.step.val : Nat) : ZMod N) = section5IndexPoint P i := by
    simp [section5IndexPoint]
  have hinj : Set.InjOn
      (fun i : Nat => ((P.start.val + i * P.step.val : Nat) : ZMod N))
      (Finset.range P.length : Set Nat) := by
    simpa only [heval] using section5IndexPoint_injective_on_range P hP
  obtain ⟨M, Q, hM, hbudget, hpart, hQ⟩ :=
    integerRun_partition P.start.val P.step.val P.length hdpos hinj
  refine ⟨M, fun j => (Q j).toModAP N, ?_, fun j => (hQ j).2.2.2, ?_⟩
  · simpa only [heval, ← section5_carrier_eq_image_range] using hpart
  · have ha := ZMod.val_lt P.start
    have hlen : (P.length - 1) * P.step.val ≤ P.length * P.step.val :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    omega

/-- Either orientation has the same carrier. Choosing the smaller of the
two positive step representatives improves the wrap-boundary cell budget. -/
theorem ModAP.centered_integer_representative_partition {N : Nat} [NeZero N]
    (P : ModAP N) (hP : P.IsProper) (hd : P.step ≠ 0) :
    ∃ M : Nat, ∃ R : Fin M → ModAP N,
      IsPartition (fun j => (R j).carrier) P.carrier ∧
      (∀ j, (R j).HasIntegerRepresentatives) ∧
      M * N < 2 * N + P.length * centeredAbs P.step := by
  have hcenter : centeredAbs P.step = min P.step.val (N - P.step.val) := by
    exact ZMod.valMinAbs_natAbs_eq_min _
  by_cases hdir : P.step.val ≤ N - P.step.val
  · obtain ⟨M, R, hpart, hR, hbudget⟩ := P.integer_representative_partition hP hd
    exact ⟨M, R, hpart, hR, by simpa only [hcenter, min_eq_left hdir] using hbudget⟩
  · have hrev : P.reverse.step ≠ 0 := by simpa [ModAP.reverse] using hd
    obtain ⟨M, R, hpart, hR, hbudget⟩ :=
      P.reverse.integer_representative_partition ((P.reverse_isProper).mpr hP) hrev
    refine ⟨M, R, by simpa only [P.reverse_carrier] using hpart, hR, ?_⟩
    simpa only [ModAP.reverse, ZMod.neg_val, if_neg hd, hcenter,
      min_eq_right (Nat.le_of_not_ge hdir)] using hbudget

/-- The paper's `4 sqrt(m)` integer-representative refinement for every
injectively parameterized progression of length at least four. Dirichlet
approximation and residue classes avoid any primality assumption. -/
theorem ModAP.integer_representative_refinement_large {N : Nat} [NeZero N]
    (P : ModAP N) (hP : P.IsProper) (hL : 4 ≤ P.length) :
    ∃ M : Nat, ∃ R : Fin M → ModAP N,
      IsPartition (fun j => (R j).carrier) P.carrier ∧
      (∀ j, (R j).HasIntegerRepresentatives) ∧
      (M : Real) ≤ 4 * Real.sqrt P.length := by
  classical
  let t := Nat.sqrt P.length
  have ht2 : 2 ≤ t := Nat.le_sqrt.mpr (by simpa using hL)
  have ht0 : 0 < t := by omega
  have htSq : t * t ≤ P.length := Nat.sqrt_le _
  have htL : t < P.length := by nlinarith
  letI : NeZero t := ⟨by omega⟩
  obtain ⟨u, hu, hut, hsmall⟩ :=
    simultaneous_small_multiplier (N := N) (K := 1) (M := t) (fun _ => P.step)
  have hut' : u ≤ t := by simpa using hut
  have huL : u < P.length := hut'.trans_lt htL
  let v : ZMod N := (u : ZMod N) * P.step
  have hvt : centeredAbs v * t < N := hsmall 0
  have hv : v ≠ 0 := by
    intro hv0
    have hi := section5IndexPoint_injective_on_range P hP
      (Finset.mem_range.mpr huL) (Finset.mem_range.mpr (by omega : 0 < P.length))
      (show section5IndexPoint P u = section5IndexPoint P 0 by
        simp only [section5IndexPoint, Nat.cast_zero, zero_mul, add_zero]
        change P.start + v = P.start
        rw [hv0, add_zero])
    omega
  let A := residueNatAP P.length u
  have hApart : IsNatAPPartition A (Finset.range P.length) :=
    residueNatAP_partition hu huL.le
  let S : Fin u → ModAP N := fun r => section5Transport P (A r)
  have hSpart : IsPartition (fun r => (S r).carrier) P.carrier :=
    section5Transport_partition P A hP hApart
  have hSproper (r : Fin u) : (S r).IsProper :=
    section5Transport_isProper P (A r) hP (residueNatAP_proper hu r)
      (hApart.cell_subset r)
  have hSstep (r : Fin u) : (S r).step = v := rfl
  have hSlen : ∑ r, (S r).length = P.length := by
    calc
      ∑ r, (S r).length = ∑ r, (A r).carrier.card := by
        apply Finset.sum_congr rfl
        intro r _
        exact (residueNatAP_proper hu r).2.symm
      _ = P.length := by simpa only [Finset.card_range] using hApart.sum_card
  choose M R hRpart hRinteger hRbudget using fun r =>
    (S r).centered_integer_representative_partition (hSproper r)
      (by simpa only [hSstep] using hv)
  have hsum : (∑ r, M r) * N < 2 * u * N + P.length * centeredAbs v := by
    calc
      (∑ r, M r) * N = ∑ r, M r * N := Finset.sum_mul _ _ _
      _ < ∑ r, (2 * N + (S r).length * centeredAbs v) := by
        apply Finset.sum_lt_sum_of_nonempty
          (show (Finset.univ : Finset (Fin u)).Nonempty from
            ⟨⟨0, hu⟩, Finset.mem_univ _⟩)
        intro r _
        simpa only [hSstep] using hRbudget r
      _ = 2 * u * N + P.length * centeredAbs v := by
        rw [Finset.sum_add_distrib,
          ← Finset.sum_mul Finset.univ (fun r : Fin u => (S r).length) (centeredAbs v), hSlen]
        simp
        ring
  have hscaled : (∑ r, M r) * t < 2 * u * t + P.length := by
    apply Nat.lt_of_mul_lt_mul_right (a := N)
    calc
      (∑ r, M r) * t * N = ((∑ r, M r) * N) * t := by ring
      _ < (2 * u * N + P.length * centeredAbs v) * t :=
        Nat.mul_lt_mul_of_pos_right hsum ht0
      _ ≤ (2 * u * t + P.length) * N := by
        have h := Nat.mul_le_mul_left P.length hvt.le
        nlinarith
  have hNatCount : (∑ r, M r) ≤ 4 * t := by
    have hround : P.length ≤ t * t + t + t := Nat.sqrt_le_add _
    have humul := Nat.mul_le_mul_right t hut'
    nlinarith
  let T : Fin (∑ r, M r) → ModAP N := fun j =>
    let z := (section5NatFlattenEquiv M).symm j
    R z.1 z.2
  refine ⟨∑ r, M r, T, ?_, ?_, ?_⟩
  · exact finsetPartition_flatten M (fun r => (S r).carrier) P.carrier
      (fun r j => (R r j).carrier) hSpart hRpart
  · intro j
    let z := (section5NatFlattenEquiv M).symm j
    exact hRinteger z.1 z.2
  · have htReal : (t : Real) ≤ Real.sqrt P.length :=
      Real.le_sqrt_of_sq_le (by rw [pow_two]; exact_mod_cast htSq)
    have hcountReal : (∑ r, M r : Nat) ≤ (4 : Real) * t := by exact_mod_cast hNatCount
    exact hcountReal.trans (mul_le_mul_of_nonneg_left htReal (by norm_num))

/-- Every finite set of residues has an exact singleton partition with
integer representatives. This also handles the empty set and modulus one. -/
theorem integer_representative_singleton_partition {N : Nat} [NeZero N]
    (S : Finset (ZMod N)) :
    ∃ R : Fin S.card → ModAP N,
      IsPartition (fun j => (R j).carrier) S ∧
      ∀ j, (R j).HasIntegerRepresentatives := by
  classical
  let x : Fin S.card → ZMod N := fun j => (S.equivFin.symm j).1
  let R : Fin S.card → ModAP N := fun j => modInterval N (x j) 1
  have hR (j : Fin S.card) : (R j).carrier = {x j} := by
    simp [R, modInterval, ModAP.carrier]
  refine ⟨R, ?_, ?_⟩
  · constructor
    · intro v
      constructor
      · intro hv
        refine ⟨S.equivFin ⟨v, hv⟩, ?_⟩
        simp [hR, x]
      · rintro ⟨j, hv⟩
        simp only [hR, Finset.mem_singleton] at hv
        rw [hv]
        exact (S.equivFin.symm j).2
    · intro i j hij
      simp only [hR, Finset.disjoint_singleton]
      intro h
      have hsub : S.equivFin.symm i = S.equivFin.symm j := Subtype.ext h
      exact bne_iff_ne.mp hij (S.equivFin.symm.injective hsub)
  · intro j
    let Q : NatAP := ⟨(x j).val, 1, 1⟩
    have hQ : (Q.toModAP N).HasIntegerRepresentatives :=
      Q.toModAP_hasIntegerRepresentatives_of_bound (by simp [Q]) (by
        intro i hi
        have hi0 : i = 0 := by dsimp [Q] at hi; omega
        simpa [Q, hi0] using ZMod.val_lt (x j))
    simpa only [Q, R, modInterval, NatAP.toModAP, ZMod.natCast_zmod_val,
      Nat.cast_one] using hQ

/-- The full geometric conclusion of Lemma 5.12, strengthened to every
nonzero modulus and arbitrary modular parameterizations with repetitions. -/
theorem ModAP.integer_representative_refinement {N : Nat} [NeZero N]
    (P : ModAP N) :
    ∃ M : Nat, ∃ R : Fin M → ModAP N,
      IsPartition (fun j => (R j).carrier) P.carrier ∧
      (∀ j, (R j).HasIntegerRepresentatives) ∧
      (M : Real) ≤ 4 * Real.sqrt P.carrier.card := by
  classical
  let Q := section5Normalize P
  by_cases hlarge : 4 ≤ Q.length
  · obtain ⟨M, R, hpart, hR, hcount⟩ :=
      Q.integer_representative_refinement_large (section5Normalize_isProper P) hlarge
    exact ⟨M, R, by simpa only [Q, section5Normalize_carrier] using hpart, hR, hcount⟩
  · obtain ⟨R, hpart, hR⟩ := integer_representative_singleton_partition P.carrier
    refine ⟨P.carrier.card, R, hpart, hR, ?_⟩
    have hm : P.carrier.card ≤ 3 := by change ¬ 4 ≤ P.carrier.card at hlarge; omega
    have hmR : (P.carrier.card : Real) ≤ 3 := by exact_mod_cast hm
    have hs := Real.sq_sqrt (show (0 : Real) ≤ P.carrier.card by positivity)
    have hs0 := Real.sqrt_nonneg (P.carrier.card : Real)
    nlinarith [sq_nonneg (P.carrier.card : Real)]

/-- The paper's Lemma 5.12 with its genuine integer-representative
conclusion, rather than only injectivity of the modular parameterization. -/
def lemma_5_12_integer_representatives : Prop :=
  ∀ (N m : Nat) [NeZero N] (Q : ModAP N), Q.carrier.card = m →
    ∃ L : Nat, ∃ P : Fin L → ModAP N,
      IsPartition (fun j => (P j).carrier) Q.carrier ∧
      (∀ j, (P j).HasIntegerRepresentatives) ∧ (L : Real) ≤ 4 * Real.sqrt m

theorem lemma_5_12_integer_representatives_holds : lemma_5_12_integer_representatives := by
  intro N m _ Q hm
  obtain ⟨L, P, hpart, hP, hcount⟩ := Q.integer_representative_refinement
  exact ⟨L, P, hpart, hP, by simpa only [hm] using hcount⟩

/-- A progression partition of any finite set of residues has a genuine
integer-representative refinement with the paper's Cauchy--Schwarz budget.
The ambient modulus need not be prime, and the set need not be the whole
cyclic group. Empty cells and empty partitions are allowed. -/
theorem integer_representative_partition_refinement {N M : Nat} [NeZero N]
    (Q : Fin M → ModAP N) (S : Finset (ZMod N))
    (hQ : IsPartition (fun i => (Q i).carrier) S) :
    ∃ L : Nat, ∃ R : Fin L → ModAP N,
      IsRefinement (fun j => (R j).carrier) (fun i => (Q i).carrier) ∧
      IsPartition (fun j => (R j).carrier) S ∧
      (∀ j, (R j).HasIntegerRepresentatives) ∧
      (L : Real) ≤ 4 * Real.sqrt ((S.card : Real) * M) := by
  classical
  choose L R hRpart hRinteger hRcount using fun i =>
    (Q i).integer_representative_refinement
  let T : Fin (∑ i, L i) → ModAP N := fun j =>
    let z := (section5NatFlattenEquiv L).symm j
    R z.1 z.2
  have hTpart : IsPartition (fun j => (T j).carrier) S :=
    finsetPartition_flatten L (fun i => (Q i).carrier) S
      (fun i j => (R i j).carrier) hQ hRpart
  have hTref : IsRefinement (fun j => (T j).carrier) (fun i => (Q i).carrier) := by
    refine ⟨?_, ?_, hTpart.2⟩
    · intro x
      exact (hTpart.1 x).symm.trans (hQ.1 x)
    · intro j
      let z := (section5NatFlattenEquiv L).symm j
      exact ⟨z.1, (hRpart z.1).cell_subset z.2⟩
  have hsumCard : ∑ i, ((Q i).carrier.card : Real) = S.card := by
    exact_mod_cast hQ.sum_card
  have hroots : (∑ i, Real.sqrt ((Q i).carrier.card : Real)) ≤
      Real.sqrt ((S.card : Real) * M) := by
    have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin M))
      (f := fun i => ((Q i).carrier.card : Real)) (g := fun _ => (1 : Real))
      (fun _ => by positivity) (fun _ => by norm_num)
    simp only [Real.sqrt_one, mul_one, hsumCard, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hcs
    simpa only [Real.sqrt_mul (show (0 : Real) ≤ S.card by positivity)] using hcs
  refine ⟨∑ i, L i, T, hTref, hTpart, ?_, ?_⟩
  · intro j
    let z := (section5NatFlattenEquiv L).symm j
    exact hRinteger z.1 z.2
  · calc
      (∑ i, L i : Nat) = ∑ i, (L i : Real) := by simp
      _ ≤ ∑ i, 4 * Real.sqrt ((Q i).carrier.card : Real) :=
        Finset.sum_le_sum (fun i _ => hRcount i)
      _ = 4 * ∑ i, Real.sqrt ((Q i).carrier.card : Real) := (Finset.mul_sum _ _ _).symm
      _ ≤ 4 * Real.sqrt ((S.card : Real) * M) :=
        mul_le_mul_of_nonneg_left hroots (by norm_num)

/-- The geometric statement of Lemma 5.13, keeping its printed cell count. -/
def lemma_5_13_integer_representatives : Prop :=
  ∀ (N M : Nat) [NeZero N] (Q : Fin M → ModAP N),
    IsPartition (fun i => (Q i).carrier) Finset.univ →
      ∃ L : Nat, ∃ R : Fin L → ModAP N,
        IsRefinement (fun j => (R j).carrier) (fun i => (Q i).carrier) ∧
        (∀ j, (R j).HasIntegerRepresentatives) ∧
        (L : Real) ≤ 4 * Real.sqrt ((N : Real) * M)

theorem lemma_5_13_integer_representatives_holds : lemma_5_13_integer_representatives := by
  intro N M _ Q hQ
  obtain ⟨L, R, href, _, hR, hcount⟩ :=
    integer_representative_partition_refinement Q Finset.univ hQ
  exact ⟨L, R, href, hR, by simpa only [Finset.card_univ, ZMod.card] using hcount⟩

end LeanProofs.GowersSzemeredi
