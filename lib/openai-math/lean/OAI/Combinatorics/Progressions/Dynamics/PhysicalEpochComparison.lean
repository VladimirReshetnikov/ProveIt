import OAI.Combinatorics.Progressions.Lattices.RetainedAffineResidueEpoch
import OAI.Combinatorics.Progressions.Linear.EpochEventRank
import OAI.Combinatorics.Progressions.Polynomial.ResidueDegreeZero

namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

variable {σ L : Type*}
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

structure EpochSymbolRecord (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (T : D.Niltest (fun _ : σ => 1)) where
  fast : LieSubalgebra ℚ D.filtration.AssociatedGraded
  spanning : Fin d → D.filtration.AssociatedGraded
  budget : ℝ
  denominator : ℕ
  modulus : ℕ
  auxiliary : ℕ
  shift : σ → ℚ
  sides : σ → ℝ
  denominator_pos : 0 < denominator
  modulus_pos : 0 < modulus
  auxiliary_pos : 0 < auxiliary
  sides_pos : ∀ i, 0 < sides i
  denominator_le : (denominator : ℝ) ≤ Real.exp budget
  span_eq : Submodule.span ℚ (Set.range spanning) = fast.toSubmodule
  graded : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω fast.toSubmodule
  height_le : ∀ i j, rationalLogHeight
    ((D.filtration.associatedGradedBasis D.basis ω hF).repr (spanning i) j) ≤ budget
  factorization : D.filtration.SymbolFactorizationIn D.basis ω hF sides
    ((T.scalarAffinePullback ((modulus : ℚ) * auxiliary) shift).symbol D.basis ω hF)
    budget denominator fast

namespace EpochSymbolRecord

variable {D : RationalFilteredNilmanifold L s d} {ω : Fin d → ℕ}
  {hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i})}
  {T : D.Niltest (fun _ : σ => 1)}

def Controlled (r : EpochSymbolRecord D ω hF T) (W : σ → ℝ) (p : ℝ) : Prop :=
  r.budget ≤ p ∧ (r.auxiliary : ℝ) ≤ Real.exp p ∧
    ∀ i, Real.exp (-p) * W i ≤ ((r.modulus : ℝ) * r.auxiliary) * r.sides i

theorem transport (r : EpochSymbolRecord D ω hF T) (W : σ → ℝ) (p : ℝ)
    (hp : 0 ≤ p) (hr : r.Controlled W p)
    (M : ℕ) (hM : 0 < M) (hdiv : r.modulus ∣ M)
    (shift : σ → ℚ) (A : σ → ℝ) (hA : ∀ i, 0 < A i)
    (hcurrent : ∀ i, (M : ℝ) * A i ≤ W i) :
    D.filtration.SymbolFactorizationIn D.basis ω hF A
      ((T.scalarAffinePullback (M : ℚ) shift).symbol D.basis ω hF)
      (p + (s : ℝ) * p) (r.denominator * r.auxiliary ^ s) r.fast := by
  have h := T.scalarAffinePullback_residue_factorization D.basis ω hF
    r.modulus_pos hM r.auxiliary_pos hdiv r.shift shift r.factorization r.sides_pos hA hp hr.2.2 hcurrent
  exact h.mono D.filtration D.basis ω hF (by linarith [hr.1]) hA

end EpochSymbolRecord

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

variable {σ L : Type*}
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {ω : Fin d → ℕ}
  {hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i})}
  {T : D.Niltest (fun _ : σ => 1)}

noncomputable def epochRecordIntersection : List (EpochSymbolRecord D ω hF T) →
    LieSubalgebra ℚ D.filtration.AssociatedGraded
  | [] => ⊤
  | r :: rs => r.fast ⊓ epochRecordIntersection rs

inductive EpochRecordHistory : List (EpochSymbolRecord D ω hF T) → Prop
  | nil : EpochRecordHistory []
  | cons {r : EpochSymbolRecord D ω hF T} {rs : List (EpochSymbolRecord D ω hF T)}
      (history : EpochRecordHistory rs)
      (drop : finrank ℚ ↥(epochRecordIntersection rs ⊓ r.fast) <
        finrank ℚ (epochRecordIntersection rs)) : EpochRecordHistory (r :: rs)

theorem epochRecordIntersection_eq_iInf (rs : List (EpochSymbolRecord D ω hF T)) :
    epochRecordIntersection rs = ⨅ i : Fin rs.length, (rs.get i).fast := by
  induction rs with
  | nil => simp [epochRecordIntersection]
  | cons r rs ih =>
    change r.fast ⊓ epochRecordIntersection rs = ⨅ i : Fin (r :: rs).length, ((r :: rs).get i).fast
    apply le_antisymm
    · apply le_iInf
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact inf_le_left
      · have hle : epochRecordIntersection rs ≤ (rs.get j).fast := by rw [ih]; exact iInf_le _ j
        exact inf_le_right.trans hle
    · apply le_inf
      · exact iInf_le _ (0 : Fin (r :: rs).length)
      · rw [ih]
        exact le_iInf fun j => iInf_le _ j.succ

theorem EpochRecordHistory.length_add_finrank_le {rs : List (EpochSymbolRecord D ω hF T)}
    (h : EpochRecordHistory rs) :
    rs.length + finrank ℚ (epochRecordIntersection rs) ≤
      finrank ℚ (⊤ : LieSubalgebra ℚ D.filtration.AssociatedGraded) := by
  induction rs with
  | nil =>
    simp only [List.length_nil, epochRecordIntersection, Nat.zero_add]
    exact Nat.le_refl _
  | cons r rs ih =>
    cases h with
    | cons history drop =>
      have htail := ih history
      change rs.length + 1 + finrank ℚ ↥(r.fast ⊓ epochRecordIntersection rs) ≤ _
      rw [inf_comm r.fast]
      omega

theorem EpochRecordHistory.length_le_dimension {rs : List (EpochSymbolRecord D ω hF T)}
    (h : EpochRecordHistory rs) : rs.length ≤ d := by
  have hrank := h.length_add_finrank_le
  have htop := lie_subalgebra_finrank_le (D.filtration.associatedGradedBasis D.basis ω hF)
    (⊤ : LieSubalgebra ℚ D.filtration.AssociatedGraded)
  simp only [Fintype.card_fin] at htop
  omega

theorem EpochRecordHistory.prepend_stack_event
    {r : EpochSymbolRecord D ω hF T} {rs : List (EpochSymbolRecord D ω hF T)}
    (hdrop : finrank ℚ ↥(epochRecordIntersection rs ⊓ r.fast) <
      finrank ℚ (epochRecordIntersection rs))
    {oldTail newTail : List ℕ} (hlen : newTail.length = oldTail.length)
    (hbounded : ∀ q ∈ newTail, q ≤ d) :
    EpochStackEvent d (finrank ℚ (epochRecordIntersection rs) :: oldTail)
      (finrank ℚ (epochRecordIntersection (r :: rs)) :: newTail) := by
  apply EpochStackEvent.head _ hlen hbounded
  change finrank ℚ ↥(r.fast ⊓ epochRecordIntersection rs) < _
  rw [inf_comm r.fast]
  exact hdrop

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

universe u v

structure PhysicalEpochSource (σ : Type u) [Fintype σ] (s bound : ℕ) where
  Carrier : Type v
  [lieRing : LieRing Carrier]
  [lieAlgebra : LieAlgebra ℚ Carrier]
  [topology : TopologicalSpace (ℝ ⊗[ℚ] Carrier)]
  [topologicalAddGroup : IsTopologicalAddGroup (ℝ ⊗[ℚ] Carrier)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] Carrier)]
  [t2Space : T2Space (ℝ ⊗[ℚ] Carrier)]
  dimension : ℕ
  dimension_le : dimension ≤ bound
  model : RationalFilteredNilmanifold Carrier s dimension
  weights : Fin dimension → ℕ
  adapted : ∀ j, model.filtration.layer j = Submodule.span ℚ (model.basis '' {i | j ≤ weights i})
  fixedMap : model.Niltest (fun _ : σ => 1)
  lower : σ → ℤ
  sides : σ → ℕ
  sides_pos : ∀ i, 0 < sides i
  incomingBudget : ℝ
  recordBudget : ℝ
  incoming_nonneg : 0 ≤ incomingBudget
  incoming_le_record : incomingBudget ≤ recordBudget
  geometry : model.GeometryComplexityLE incomingBudget
  coordinates_le : (Fintype.card σ : ℝ) ≤ incomingBudget

attribute [instance] PhysicalEpochSource.lieRing PhysicalEpochSource.lieAlgebra
  PhysicalEpochSource.topology PhysicalEpochSource.topologicalAddGroup
  PhysicalEpochSource.continuousSMul PhysicalEpochSource.t2Space

structure PhysicalEpochRecords {σ : Type u} [Fintype σ] {s bound : ℕ}
    (base : PhysicalEpochSource.{u, v} σ s bound) where
  records : List (EpochSymbolRecord base.model base.weights base.adapted base.fixedMap)
  history : EpochRecordHistory records
  controlled : ∀ r ∈ records, r.Controlled (fun i => (base.sides i : ℝ)) base.recordBudget

namespace PhysicalEpochRecords

variable {σ : Type u} [Fintype σ] {s bound : ℕ} {base : PhysicalEpochSource.{u, v} σ s bound}

def empty (base : PhysicalEpochSource.{u, v} σ s bound) : PhysicalEpochRecords base where
  records := []
  history := .nil
  controlled := by simp

noncomputable def dimension (state : PhysicalEpochRecords base) : ℕ :=
  finrank ℚ (epochRecordIntersection state.records)

theorem dimension_le (state : PhysicalEpochRecords base) : state.dimension ≤ bound := by
  have h := lie_subalgebra_finrank_le
    (base.model.filtration.associatedGradedBasis base.model.basis base.weights base.adapted)
    (epochRecordIntersection state.records)
  have hdim : state.dimension ≤ base.dimension := by simpa only [dimension, Fintype.card_fin] using h
  exact hdim.trans base.dimension_le

end PhysicalEpochRecords

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

theorem exists_retained_epoch_from_records (s : ℕ) :
    ∃ C K : ℕ, 2 ≤ C ∧ 2 ≤ K ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d) (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (T : D.Niltest (fun _ : σ => 1))
      (rs : List (EpochSymbolRecord D ω hF T)), EpochRecordHistory rs →
      ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      ∀ W : σ → ℝ, (∀ r ∈ rs, r.Controlled W p) →
      ∀ M : ℕ, 0 < M → (∀ r ∈ rs, r.modulus ∣ M) →
      ∀ A : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ K) ≤ A i) →
      (∀ i, (M : ℝ) * A i ≤ W i) → ∀ shift : σ → ℚ,
      ∃ work cost : ℝ, p + 16 ≤ work ∧ work ≤ (p + 2) ^ K ∧ 0 ≤ cost ∧ cost ≤ (p + 2) ^ K ∧
        RetainedAffineResidueEpoch D ω hF (epochRecordIntersection rs)
          (T.scalarAffinePullback (M : ℚ) shift) A work cost C := by
  obtain ⟨C, K, hC, hK, hconstruct⟩ := exists_retained_affine_residue_epoch s
  refine ⟨C, K, hC, hK, ?_⟩
  intro σ L _ _ _ _ d _ _ _ _ D ω hF T rs history p hp hD hσ W hcontrolled M hM hdiv A hA hcurrent shift
  let recordAt : Fin rs.length → EpochSymbolRecord D ω hF T := fun i => rs.get i
  have hmem : ∀ i, recordAt i ∈ rs := fun i => List.get_mem rs i
  have hcontrol : ∀ i, (recordAt i).Controlled W p := fun i => hcontrolled (recordAt i) (hmem i)
  have hcount : (Fintype.card (Fin rs.length) : ℝ) ≤ p := by
    have hc : (rs.length : ℝ) ≤ d := by exact_mod_cast history.length_le_dimension
    simpa only [Fintype.card_fin] using hc.trans hD.1
  have hfactor : ∀ i, D.filtration.SymbolFactorizationIn D.basis ω hF (recordAt i).sides
      ((T.scalarAffinePullback (((recordAt i).modulus : ℚ) * (recordAt i).auxiliary) (recordAt i).shift).symbol D.basis ω hF)
      p (recordAt i).denominator (recordAt i).fast := by
    intro i
    exact (recordAt i).factorization.mono D.filtration D.basis ω hF (hcontrol i).1 (recordAt i).sides_pos
  have hresult := hconstruct D ω hF (fun i => (recordAt i).fast) (fun i => (recordAt i).spanning)
    (fun i => (recordAt i).denominator) (fun i => (recordAt i).auxiliary) (fun i => (recordAt i).modulus)
    M p hp hD hσ hcount (fun i => (recordAt i).span_eq) (fun i => (recordAt i).graded)
    (fun i j k => ((recordAt i).height_le j k).trans (hcontrol i).1)
    (fun i => (recordAt i).denominator_pos) (fun i => (recordAt i).auxiliary_pos) (fun i => (recordAt i).modulus_pos)
    hM (fun i => hdiv (recordAt i) (hmem i))
    (fun i => (recordAt i).denominator_le.trans (Real.exp_le_exp.mpr (hcontrol i).1))
    (fun i => (hcontrol i).2.1) W A hA T shift (fun i => (recordAt i).shift) (fun i => (recordAt i).sides)
    (fun i => (recordAt i).sides_pos) hcurrent (fun i => (hcontrol i).2.2) hfactor
  simpa only [epochRecordIntersection_eq_iInf] using hresult

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

theorem ResiduePairDimensionDrop.physical_record
    {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (T S : D.Niltest (fun _ : σ => 1))
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (lo : σ → ℤ) (N : σ → ℕ) (m a J : ℕ) (hm : 0 < m) (ha : 0 < a) (hJ : 0 < J)
    (u v : σ → ℤ) (B : ℝ)
    (hS : S.orbit = (T.scalarAffinePullback (m * a : ℕ) (fun i => (u i : ℚ))).orbit)
    (hv : ∀ i, v i ≡ u i [ZMOD (m * a : ℕ)])
    (hwide : ∀ i, 2 * ((m * a * J : ℕ) : ℝ) ≤ (N i : ℝ))
    (hevent : ResiduePairDimensionDrop D ω hF S W lo N (m * a) u v (fun _ => J) B) :
    ∃ r : EpochSymbolRecord D ω hF T,
      r.budget = B ∧ r.auxiliary = a ∧ r.modulus ∣ m * J ∧
      finrank ℚ ↥(W ⊓ r.fast) < finrank ℚ W ∧
      ∀ i, (N i : ℝ) / 2 ≤ ((r.modulus : ℝ) * r.auxiliary) * r.sides i := by
  have hevent' := hevent.of_orbit_eq D ω hF S
    (T.scalarAffinePullback (m * a : ℕ) (fun i => (u i : ℚ))) hS W lo N (m * a) u v (fun _ => J) B
  obtain ⟨flag, l, U, z, hl, hlB, hz, hgraded, hheight, hdrop, hfactor⟩ :=
    hevent'.scalar_record D ω hF T (m * a : ℕ) (fun i => (u i : ℚ)) W lo N (m * a) J u v B
  let f : ℕ := if flag then J else 1
  have hf : 0 < f := by cases flag <;> simp only [f, Bool.false_eq_true, ite_false, ite_true] <;> omega
  have hfJ : f ≤ J := by cases flag <;> simp only [f, Bool.false_eq_true, ite_false, ite_true] <;> omega
  have hpair : ∀ i, residuePairValue u v flag i ≡ u i [ZMOD (m * a : ℕ)] := by
    cases flag
    · exact fun i => Int.ModEq.refl _
    · exact hv
  have hshift : (fun i => ((m * a : ℕ) : ℚ) *
      (commonStrideIndex u (m * a) (residuePairValue u v flag) i : ℚ) + (u i : ℚ)) =
      (fun i => (residuePairValue u v flag i : ℚ)) :=
    funext (residue_refinement_offset_identity u (residuePairValue u v flag) (m * a) hpair)
  have hscale : ((m * a : ℕ) : ℚ) * f = ((m * f : ℕ) : ℚ) * a := by push_cast; ring
  change D.filtration.SymbolFactorizationIn D.basis ω hF
    (fun i => (residueIndexLength (lo i) (lo i + N i) (m * a * f : ℕ)
      (residuePairValue u v flag i) : ℝ))
    ((T.scalarAffinePullback (((m * a : ℕ) : ℚ) * f)
      (fun i => ((m * a : ℕ) : ℚ) * (commonStrideIndex u (m * a) (residuePairValue u v flag) i : ℚ) + (u i : ℚ))).symbol
      D.basis ω hF) B l U at hfactor
  rw [hscale, hshift] at hfactor
  have hlen : ∀ i, 0 < residueIndexLength (lo i) (lo i + N i) (m * a * f : ℕ)
        (residuePairValue u v flag i) ∧
      (N i : ℝ) / 2 ≤ ((m * a * f : ℕ) : ℝ) *
        (residueIndexLength (lo i) (lo i + N i) (m * a * f : ℕ) (residuePairValue u v flag i) : ℝ) := by
    intro i
    apply residueIndexLength_half_width (lo i) (residuePairValue u v flag i) (N i) (m * a * f)
      (Nat.mul_pos (Nat.mul_pos hm ha) hf)
    have hmf : ((m * a * f : ℕ) : ℝ) ≤ (m * a * J : ℕ) := by
      exact_mod_cast Nat.mul_le_mul_left (m * a) hfJ
    linarith [hwide i]
  let r : EpochSymbolRecord D ω hF T := {
    fast := U
    spanning := z
    budget := B
    denominator := l
    modulus := m * f
    auxiliary := a
    shift := fun i => (residuePairValue u v flag i : ℚ)
    sides := fun i => (residueIndexLength (lo i) (lo i + N i) (m * a * f : ℕ)
      (residuePairValue u v flag i) : ℝ)
    denominator_pos := hl
    modulus_pos := Nat.mul_pos hm hf
    auxiliary_pos := ha
    sides_pos := fun i => by exact_mod_cast (hlen i).1
    denominator_le := hlB
    span_eq := hz
    graded := hgraded
    height_le := hheight
    factorization := hfactor }
  refine ⟨r, rfl, rfl, ?_, hdrop, ?_⟩
  · change m * f ∣ m * J
    cases flag <;> simp [f]
  · intro i
    change (N i : ℝ) / 2 ≤ (((m * f : ℕ) : ℝ) * a) * _
    have heq : ((m * f : ℕ) : ℝ) * a = (m * a * f : ℕ) := by push_cast; ring
    rw [heq]
    exact (hlen i).2

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

theorem EpochRecordHistory.extend_of_event
    {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (T S : D.Niltest (fun _ : σ => 1)) (W : σ → ℝ) (p B : ℝ)
    (rs : List (EpochSymbolRecord D ω hF T)) (history : EpochRecordHistory rs)
    (hcontrolled : ∀ r ∈ rs, r.Controlled W p)
    (lo : σ → ℤ) (N : σ → ℕ) (m a J : ℕ) (hm : 0 < m) (ha : 0 < a) (hJ : 0 < J)
    (hdiv : ∀ r ∈ rs, r.modulus ∣ m) (hB : B ≤ p) (haB : (a : ℝ) ≤ Real.exp p)
    (u v : σ → ℤ)
    (hS : S.orbit = (T.scalarAffinePullback (m * a : ℕ) (fun i => (u i : ℚ))).orbit)
    (hv : ∀ i, v i ≡ u i [ZMOD (m * a : ℕ)])
    (hwide : ∀ i, 2 * ((m * a * J : ℕ) : ℝ) ≤ (N i : ℝ))
    (hphysical : ∀ i, 2 * (Real.exp (-p) * W i) ≤ (N i : ℝ))
    (hevent : ResiduePairDimensionDrop D ω hF S (epochRecordIntersection rs)
      lo N (m * a) u v (fun _ => J) B) :
    ∃ r : EpochSymbolRecord D ω hF T,
      EpochRecordHistory (r :: rs) ∧
      (∀ t ∈ r :: rs, t.Controlled W p) ∧
      (∀ t ∈ r :: rs, t.modulus ∣ m * J) ∧
      finrank ℚ (epochRecordIntersection (r :: rs)) < finrank ℚ (epochRecordIntersection rs) := by
  obtain ⟨r, hrB, hra, hrdiv, hdrop, hspan⟩ := hevent.physical_record D ω hF T S
    (epochRecordIntersection rs) lo N m a J hm ha hJ u v B hS hv hwide
  have hr : r.Controlled W p := ⟨by simpa only [hrB] using hB,
    by simpa only [hra] using haB, fun i => by linarith [hspan i, hphysical i]⟩
  refine ⟨r, .cons history hdrop, ?_, ?_, ?_⟩
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hr
    · exact hcontrolled t ht
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hrdiv
    · exact (hdiv t ht).trans (dvd_mul_right m J)
  · change finrank ℚ ↥(r.fast ⊓ epochRecordIntersection rs) < _
    rw [inf_comm]
    exact hdrop

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v

structure PhysicalEpochComparison {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound : ℕ}
    (base : PhysicalEpochSource.{u, v} σ s bound) (m a J : ℕ) (gap : ℝ) where
  selected_pos : 0 < m
  auxiliary_pos : 0 < a
  pending_pos : 0 < J
  lower : σ → ℤ
  sides : σ → ℕ
  sides_pos : ∀ i, 0 < sides i
  contained : ∀ i, base.lower i ≤ lower i ∧ lower i + sides i ≤ base.lower i + base.sides i
  anchor : σ → ℤ
  refined : σ → ℤ
  anchor_inside : ∀ i, lower i ≤ anchor i ∧ anchor i < lower i + sides i
  refined_inside : ∀ i, lower i ≤ refined i ∧ refined i < lower i + sides i
  compatible : ∀ i, refined i ≡ anchor i [ZMOD (m * a : ℕ)]
  test : base.model.Niltest (fun _ : σ => 1)
  orbit : test.orbit = (base.fixedMap.scalarAffinePullback (m * a : ℕ) (fun i => (anchor i : ℚ))).orbit
  positive : test.UnitIntervalValued
  complexity : test.ComplexityLE base.incomingBudget
  gap_pos : 0 < gap
  gap_le_one : gap ≤ 1
  gap_inverse : gap⁻¹ ≤ Real.exp base.incomingBudget
  discrepancy : gap ≤ ‖residuePairMean test.eval lower sides (m * a) anchor refined (fun _ => J) false -
    residuePairMean test.eval lower sides (m * a) anchor refined (fun _ => J) true‖

namespace PhysicalEpochComparison

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap : ℝ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

theorem base_nonempty (c : PhysicalEpochComparison base m a J gap) :
    Nonempty (IntegerResidueBox c.lower (fun i => c.lower i + c.sides i) (fun _ => (m * a : ℕ)) c.anchor) :=
  ⟨fun i => ⟨c.anchor i, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (c.anchor_inside i), Int.ModEq.refl _⟩⟩⟩

theorem refined_nonempty (c : PhysicalEpochComparison base m a J gap) :
    Nonempty (IntegerResidueBox c.lower (fun i => c.lower i + c.sides i) (fun _ => (m * a * J : ℕ)) c.refined) :=
  ⟨fun i => ⟨c.refined i, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (c.refined_inside i), Int.ModEq.refl _⟩⟩⟩

theorem impossible_at_zero {base : PhysicalEpochSource.{u, v} σ 0 bound}
    (c : PhysicalEpochComparison base m a J gap) : False := by
  have hzero := residue_pair_discrepancy_step_zero base.model c.test c.lower c.sides (m * a)
    c.anchor c.refined (fun _ => J) c.base_nonempty c.refined_nonempty
  have hgap := c.discrepancy
  rw [hzero] at hgap
  linarith [c.gap_pos]

end PhysicalEpochComparison

end Erdos3

end

end OAI
