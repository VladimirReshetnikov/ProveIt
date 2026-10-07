import OAI.Combinatorics.Progressions.Lattices.AffineAmbientPrimitiveBudget
import OAI.Combinatorics.Progressions.Sampling.AllocatedSlicedGridGeometryBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

structure PreparedModularCanonicalDetectorResourceConstants where
  m : ℕ
  Cperiod : ℕ
  Cgrid : ℕ
  Acover : ℕ
  Asample : ℕ
  Cpref : ℕ
  Apert : ℕ
  AmassWindow : ℕ
  Aproj : ℕ
  Aside : ℕ
  Cnative : ℕ
  Anorm : ℕ
  Amarginal : ℕ

structure PreparedModularCanonicalDetectorResources (α : Type*) where
  Q : α
  v : α
  w : α
  Dg : α
  Pproj : α
  coverLog : α
  Pmass : α
  Vlog : α
  Nlog : α
  Pbox : α
  Banalytic : α
  baseAmbient : α
  tq : α
  pq : α
  gridlog : α
  Fpref : α
  sumlog : α
  idealQ : α
  ambient : α
  Psample : α
  Pside : α
  Pnative : α
  nativeBudget : α
  E : α
  full : α
  required : α

namespace PreparedModularCanonicalDetectorResources

def toList {α : Type*} (r : PreparedModularCanonicalDetectorResources α) : List α :=
  [r.Q, r.v, r.w, r.Dg, r.Pproj, r.coverLog, r.Pmass, r.Vlog, r.Nlog, r.Pbox, r.Banalytic, r.baseAmbient, r.tq, r.pq, r.gridlog, r.Fpref, r.sumlog, r.idealQ, r.ambient, r.Psample, r.Pside, r.Pnative, r.nativeBudget, r.E, r.full, r.required]

def total {α : Type*} [AddMonoid α] (r : PreparedModularCanonicalDetectorResources α) : α :=
  r.toList.sum

def map {α β : Type*} (f : α → β) (r : PreparedModularCanonicalDetectorResources α) :
    PreparedModularCanonicalDetectorResources β :=
  { Q := f r.Q,
    v := f r.v,
    w := f r.w,
    Dg := f r.Dg,
    Pproj := f r.Pproj,
    coverLog := f r.coverLog,
    Pmass := f r.Pmass,
    Vlog := f r.Vlog,
    Nlog := f r.Nlog,
    Pbox := f r.Pbox,
    Banalytic := f r.Banalytic,
    baseAmbient := f r.baseAmbient,
    tq := f r.tq,
    pq := f r.pq,
    gridlog := f r.gridlog,
    Fpref := f r.Fpref,
    sumlog := f r.sumlog,
    idealQ := f r.idealQ,
    ambient := f r.ambient,
    Psample := f r.Psample,
    Pside := f r.Pside,
    Pnative := f r.Pnative,
    nativeBudget := f r.nativeBudget,
    E := f r.E,
    full := f r.full,
    required := f r.required }

structure Bounds (r : PreparedModularCanonicalDetectorResources ℝ) (budget : ℝ) : Prop where
  Q : r.Q ∈ Set.Icc 0 budget
  v : r.v ∈ Set.Icc 0 budget
  w : r.w ∈ Set.Icc 0 budget
  Dg : r.Dg ∈ Set.Icc 0 budget
  Pproj : r.Pproj ∈ Set.Icc 0 budget
  coverLog : r.coverLog ∈ Set.Icc 0 budget
  Pmass : r.Pmass ∈ Set.Icc 0 budget
  Vlog : r.Vlog ∈ Set.Icc 0 budget
  Nlog : r.Nlog ∈ Set.Icc 0 budget
  Pbox : r.Pbox ∈ Set.Icc 0 budget
  Banalytic : r.Banalytic ∈ Set.Icc 0 budget
  baseAmbient : r.baseAmbient ∈ Set.Icc 0 budget
  tq : r.tq ∈ Set.Icc 0 budget
  pq : r.pq ∈ Set.Icc 0 budget
  gridlog : r.gridlog ∈ Set.Icc 0 budget
  Fpref : r.Fpref ∈ Set.Icc 0 budget
  sumlog : r.sumlog ∈ Set.Icc 0 budget
  idealQ : r.idealQ ∈ Set.Icc 0 budget
  ambient : r.ambient ∈ Set.Icc 0 budget
  Psample : r.Psample ∈ Set.Icc 0 budget
  Pside : r.Pside ∈ Set.Icc 0 budget
  Pnative : r.Pnative ∈ Set.Icc 0 budget
  nativeBudget : r.nativeBudget ∈ Set.Icc 0 budget
  E : r.E ∈ Set.Icc 0 budget
  full : r.full ∈ Set.Icc 0 budget
  required : r.required ∈ Set.Icc 0 budget

private theorem bounds_of_list {r : PreparedModularCanonicalDetectorResources ℝ} {budget : ℝ}
    (h : ∀ x ∈ r.toList, x ∈ Set.Icc 0 budget) : r.Bounds budget := by
  constructor <;> apply h <;> simp only [toList, List.mem_cons] <;> tauto

private theorem total_map {α β : Type*} [Semiring α] [Semiring β]
    (f : α →+* β) (r : PreparedModularCanonicalDetectorResources α) :
    (r.map f).total = f r.total := by
  simp [total, toList, map]

end PreparedModularCanonicalDetectorResources

noncomputable def preparedModularCanonicalDetectorResources {α : Type*} [Semiring α]
    (K : PreparedModularCanonicalDetectorResourceConstants) (P : α) :
    PreparedModularCanonicalDetectorResources α :=
  let Q : α := (P + K.Cperiod) ^ K.Cperiod
  let v : α := P + 8
  let w : α := P + 1
  let Dg : α := 2 * P + K.m * P + (layerTailDegree K.m + 1 : ℕ) + K.m + comparisonProfileBound + 8
  let Pproj : α := 4 * (P + 8) ^ 2
  let coverLog : α := (Pproj + 3 + K.Acover) ^ K.Acover
  let Pmass : α := (Pproj + K.Asample) ^ K.Asample
  let Vlog : α := P ^ 2 * ((layerTailDegree K.m + 1 : ℕ) * P + 1)
  let Nlog : α := (2 * K.m : ℕ) * (2 * P + 16) * (1 + 4 * (2 * P + 8))
  let Pbox : α := 2 * P + 8
  let Banalytic : α := Dg + 4 * P + 32
  let baseAmbient : α := Pproj + coverLog + Vlog + Nlog + Q + (layerTailDegree K.m + 1 : ℕ) * P + 3 * P + comparisonProfileBound + 32
  let tq : α := 1 + Q + (P + 1) + 1
  let pq : α := K.Cgrid + 2 * Q + (P + 1) + 4
  let gridlog : α := slicedGridGeometryLog Dg v w tq + pq
  let Fpref : α := (P + K.Cpref) ^ K.Cpref
  let sumlog : α := Pbox + P + Vlog + Nlog + Q + P
  let idealQ : α := 1 + P * sumlog + (P + comparisonProfileBound + (P + 1) * sumlog) + sumlog + 1
  let ambient : α := affineAmbientPrimitiveBudget baseAmbient idealQ
  let Psample : α := Pmass + ambient + Pproj + 2 * P + K.m * (K.m + 2 : ℕ) + 8
  let Pside : α := Psample + Pproj + Pmass + 2 * P
  let Pnative : α := Dg + gridlog + v + Fpref + 6 * P + Banalytic
  let nativeBudget : α := ((Pnative + K.Cnative) ^ K.Cnative + K.Anorm) ^ K.Anorm
  let E : α := 3 * P + nativeBudget + 30
  let full : α := 4 * (P + 8) ^ 2
  let required : α := (Psample + K.Apert) ^ K.Apert + (Pmass + K.AmassWindow) ^ K.AmassWindow + (Pproj + K.Aproj) ^ K.Aproj + (Pside + K.Aside) ^ K.Aside + (full + E + K.Amarginal) ^ K.Amarginal
  { Q, v, w, Dg, Pproj, coverLog, Pmass, Vlog, Nlog, Pbox, Banalytic, baseAmbient, tq, pq, gridlog, Fpref, sumlog, idealQ, ambient, Psample, Pside, Pnative, nativeBudget, E, full, required }

private theorem preparedModularCanonicalDetectorResources_map
    {α β : Type*} [Semiring α] [Semiring β] (f : α →+* β)
    (K : PreparedModularCanonicalDetectorResourceConstants) (P : α) :
    (preparedModularCanonicalDetectorResources K P).map f =
      preparedModularCanonicalDetectorResources K (f P) := by
  simp [preparedModularCanonicalDetectorResources,
    PreparedModularCanonicalDetectorResources.map, slicedGridGeometryLog,
    affineAmbientPrimitiveBudget, affineAmbientMassLog, map_ofNat]

theorem exists_preparedModularCanonicalDetector_resource_budget
    (K : PreparedModularCanonicalDetectorResourceConstants) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ P : ℝ, 0 ≤ P →
      let resources := preparedModularCanonicalDetectorResources K P
      resources.Bounds ((P + C) ^ C) ∧ resources.total ≤ (P + C) ^ C := by
  let polynomials := preparedModularCanonicalDetectorResources K (Polynomial.X : Polynomial ℕ)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget polynomials.total
  refine ⟨C, hC, ?_⟩
  intro P hP resources
  let ev : Polynomial ℕ →+* ℝ := Polynomial.eval₂RingHom (Nat.castRingHom ℝ) P
  have hmap : polynomials.map ev = resources := by
    simpa only [polynomials, resources, ev, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      using preparedModularCanonicalDetectorResources_map ev K Polynomial.X
  have htotal : resources.total ≤ (P + C) ^ C := by
    rw [← hmap, PreparedModularCanonicalDetectorResources.total_map]
    exact hbound P hP
  have hnonneg : ∀ x ∈ resources.toList, 0 ≤ x := by
    rw [← hmap]
    change ∀ x ∈ polynomials.toList.map ev, 0 ≤ x
    intro x hx
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
    exact natPolynomial_eval_nonneg q hP
  refine ⟨PreparedModularCanonicalDetectorResources.bounds_of_list ?_, htotal⟩
  intro x hx
  exact ⟨hnonneg x hx, (List.single_le_sum hnonneg x hx).trans htotal⟩

end Erdos3.VectorPolynomial

end

end OAI
