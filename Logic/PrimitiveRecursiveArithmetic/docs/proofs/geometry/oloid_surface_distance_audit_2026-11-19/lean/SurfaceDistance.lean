import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-!
# Intrinsic distance on an oloid and its planar broken-line bounds

Scaffold for the proof in the accompanying paper. The lemmas below are
generic and have proof terms/tactics. Euclidean development, convexity,
and realization of the lifted paths are proof obligations described in
the roadmap. No theorem about the concrete oloid is assumed here.
Imported from the supplied distance archive, with imports and proofs adjusted for Lean 4.32.
-/

noncomputable section
open Set
open scoped ENNReal

namespace OloidDistance

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 3)

def diskA : Set Space :=
  {p | p.ofLp 2 = 0 ∧ (p.ofLp 0 + 1/2)^2 + (p.ofLp 1)^2 ≤ 1}

def diskB : Set Space :=
  {p | p.ofLp 1 = 0 ∧ (p.ofLp 0 - 1/2)^2 + (p.ofLp 2)^2 ≤ 1}

def surface : Set Space := frontier (convexHull ℝ (diskA ∪ diskB))

def fold (p : Space) : Space :=
  WithLp.toLp 2 ![p.ofLp 0, |p.ofLp 1|, |p.ofLp 2|]

/-- Values outside [0,1] carry no conditions and do not enter lengths. -/
structure CurveOn {E : Type*} [PseudoMetricSpace E] (S : Set E) (p q : E) where
  point : ℝ → E
  cont : ContinuousOn point (Icc 0 1)
  onSurface : MapsTo point (Icc 0 1) S
  start : point 0 = p
  finish : point 1 = q

def variation {E : Type*} [PseudoMetricSpace E] (g : ℝ → E) (a b : ℝ) : ℝ≥0∞ :=
  eVariationOn g (Icc a b)

def intrinsic {E : Type*} [PseudoMetricSpace E] (S : Set E) (p q : E) : ℝ≥0∞ :=
  ⨅ g : CurveOn S p q, variation g.point 0 1

theorem attained_intrinsic {E : Type*} [PseudoMetricSpace E] {S : Set E} {p q : E}
    {d : ℝ≥0∞} (lower : ∀ g : CurveOn S p q, d ≤ variation g.point 0 1)
    (g : CurveOn S p q) (upper : variation g.point 0 1 ≤ d) :
    intrinsic S p q = d := by
  apply le_antisymm
  · exact (iInf_le (fun c : CurveOn S p q => variation c.point 0 1) g).trans upper
  · exact le_iInf lower

theorem split_variation {E : Type*} [PseudoMetricSpace E] (g : ℝ → E)
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    variation g a b + variation g b c = variation g a c := by
  simpa [variation] using
    (eVariationOn.Icc_add_Icc (s := (univ : Set ℝ)) g hab hbc (mem_univ b))

theorem endpoint_bound {E : Type*} [PseudoMetricSpace E] (g : ℝ → E)
    {a b : ℝ} (hab : a ≤ b) :
    edist (g a) (g b) ≤ variation g a b :=
  eVariationOn.edist_le g (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)

/-- The planar chord lower bound needed on every subarc of a competitor.
Here f is the developed folded competitor, while g is the original path. -/
def BoundsChords {E : Type*} [PseudoMetricSpace E] (g : ℝ → E) (f : ℝ → Plane) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → edist (f a) (f b) ≤ variation g a b

def viaOne (p q : Plane) (A : Set Plane) : ℝ≥0∞ :=
  ⨅ a : A, edist p a.val + edist a.val q

def viaOrdered (p q : Plane) (A B : Set Plane) : ℝ≥0∞ :=
  ⨅ a : A, ⨅ b : B, edist p a.val + edist a.val b.val + edist b.val q

def viaBoth (p q : Plane) (A B : Set Plane) : ℝ≥0∞ :=
  min (viaOrdered p q A B) (viaOrdered p q B A)

theorem one_hit {E : Type*} [PseudoMetricSpace E] {g : ℝ → E} {f : ℝ → Plane}
    (h : BoundsChords g f) {A : Set Plane} {a : ℝ}
    (ha : a ∈ Icc 0 1) (hit : f a ∈ A) :
    viaOne (f 0) (f 1) A ≤ variation g 0 1 := by
  calc
    _ ≤ edist (f 0) (f a) + edist (f a) (f 1) :=
      iInf_le (fun x : A => edist (f 0) x.val + edist x.val (f 1)) ⟨f a, hit⟩
    _ ≤ variation g 0 a + variation g a 1 :=
      add_le_add (h 0 a le_rfl ha.1 ha.2) (h a 1 ha.1 ha.2 le_rfl)
    _ = _ := split_variation g ha.1 ha.2

theorem hits_in_order {E : Type*} [PseudoMetricSpace E] {g : ℝ → E} {f : ℝ → Plane}
    (h : BoundsChords g f) {A B : Set Plane} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hitA : f a ∈ A) (hitB : f b ∈ B) :
    viaOrdered (f 0) (f 1) A B ≤ variation g 0 1 := by
  let F (x : A) (y : B) :=
    edist (f 0) x.val + edist x.val y.val + edist y.val (f 1)
  calc
    _ ≤ ⨅ y : B, F ⟨f a, hitA⟩ y :=
      iInf_le (fun x : A => ⨅ y : B, F x y) ⟨f a, hitA⟩
    _ ≤ F ⟨f a, hitA⟩ ⟨f b, hitB⟩ := iInf_le _ _
    _ ≤ variation g 0 a + variation g a b + variation g b 1 :=
      add_le_add
        (add_le_add (h 0 a le_rfl ha (hab.trans hb)) (h a b ha hab hb))
        (h b 1 (ha.trans hab) hb le_rfl)
    _ = _ := by rw [split_variation g ha hab, split_variation g (ha.trans hab) hb]

theorem two_hits {E : Type*} [PseudoMetricSpace E] {g : ℝ → E} {f : ℝ → Plane}
    (h : BoundsChords g f) {A B : Set Plane} {a b : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hitA : f a ∈ A) (hitB : f b ∈ B) :
    viaBoth (f 0) (f 1) A B ≤ variation g 0 1 := by
  rcases le_total a b with hab | hba
  · exact (min_le_left _ _).trans (hits_in_order h ha.1 hab hb.2 hitA hitB)
  · exact (min_le_right _ _).trans (hits_in_order h hb.1 hba ha.2 hitB hitA)

/-- Exact geometric data and the proposition to prove for the concrete table. -/
def endA (c : ℝ) : Space :=
  WithLp.toLp 2 ![-1/2-c, Real.sqrt (1-c^2), 0]

def endB (c : ℝ) : Space :=
  WithLp.toLp 2 ![1/2-c/(1+c), 0, Real.sqrt (1+2*c)/(1+c)]

def opposite (c : ℝ) : ℝ := -c/(1+c)
def width : ℝ := 2*Real.pi*Real.sqrt 3/9

def flatA (c : ℝ) : Plane :=
  WithLp.toLp 2 ![
    2*Real.sqrt 3/9 *
      (Real.sqrt (2*(1-c)*(1+2*c)) + Real.arccos (Real.sqrt 2*c/Real.sqrt (1+c))),
    Real.sqrt 3/9 * (4*(1-c) + Real.log (2/(1+c)))]

def rise : ℝ := (flatA (-(1/2))).ofLp 1
def centerTwice : Plane := WithLp.toLp 2 ![width, rise+Real.sqrt 3]
def flatB (c : ℝ) : Plane := centerTwice - flatA (opposite c)

def mix {E : Type*} [AddCommMonoid E] [Module ℝ E] (s : ℝ) (a b : E) : E :=
  (1-s) • a + s • b

def chart (s c : ℝ) : Space := mix s (endA c) (endB c)

def flat (s c : ℝ) : Plane := mix s (flatA c) (flatB c)

def cRange : Set ℝ := Icc (-(1/2)) 1

def leftSide : Set Plane :=
  (fun s : ℝ => flat s 1) '' Icc 0 1

def rightSide : Set Plane :=
  (fun s : ℝ => flat s (-(1/2))) '' Icc 0 1

def gateY : Set Plane := (flatB '' cRange) ∪ leftSide
def gateZ : Set Plane := (flatA '' cRange) ∪ rightSide

structure Sample where
  h : ℚ
  s : ℚ
  posY : Bool
  posZ : Bool

def samples : Fin 10 → Sample := ![
  ⟨1/5, 1/6, true, true⟩, ⟨9/10, 7/10, true, true⟩,
  ⟨3/2, 2/5, true, false⟩, ⟨1/2, 3/11, true, false⟩,
  ⟨7/6, 1/8, false, true⟩, ⟨2/3, 11/13, false, true⟩,
  ⟨4/3, 8/11, false, false⟩, ⟨1/3, 4/7, false, false⟩,
  ⟨1, 5/9, true, true⟩, ⟨7/8, 19/20, false, true⟩]

def cosParam (p : Sample) : ℝ :=
  let h := (p.h : ℝ)
  (1-h^2)/(1+h^2)

def spatial (p : Sample) : Space :=
  let v := chart (p.s : ℝ) (cosParam p)
  WithLp.toLp 2 ![v.ofLp 0,
    (if p.posY then v.ofLp 1 else -v.ofLp 1),
    (if p.posZ then v.ofLp 2 else -v.ofLp 2)]

def planar (p : Sample) : Plane := flat (p.s : ℝ) (cosParam p)

def exactRoute (p q : Sample) : ℝ≥0∞ :=
  let x := planar p
  let y := planar q
  if p.posY = q.posY then
    if p.posZ = q.posZ then edist x y else viaOne x y gateZ
  else if p.posZ = q.posZ then viaOne x y gateY
  else viaBoth x y gateY gateZ

/-- Target proposition for the geometric part of the distance table. -/
def ExactTable : Prop :=
  ∀ i j : Fin 10, intrinsic surface (spatial (samples i)) (spatial (samples j))
    = exactRoute (samples i) (samples j)

structure Enclosure where
  i : Fin 10
  j : Fin 10
  lowerNumerator : ℕ
  upperNumerator : ℕ

/-- Bounds in units of 10^(-14), with zero-based point indices. -/
def enclosures : List Enclosure := [
  ⟨0, 1, 140395034929643, 140395034929654⟩,
  ⟨0, 2, 197325849823889, 197325849832406⟩,
  ⟨0, 3, 92702902355135, 92702902358675⟩,
  ⟨0, 4, 162834578466949, 162834578467239⟩,
  ⟨0, 5, 148636183756528, 148636183757715⟩,
  ⟨0, 6, 261515425801455, 261515425810344⟩,
  ⟨0, 7, 150716628468502, 150716628477229⟩,
  ⟨0, 8, 132216021712579, 132216021712589⟩,
  ⟨0, 9, 176807374469869, 176807374474756⟩,
  ⟨1, 2, 118320928176609, 118320928182238⟩,
  ⟨1, 3, 171767353059474, 171767353066592⟩,
  ⟨1, 4, 150668470611741, 150668470612382⟩,
  ⟨1, 5, 52103438241980, 52103438249435⟩,
  ⟨1, 6, 233498283153450, 233498283163014⟩,
  ⟨1, 7, 240894154635863, 240894154645303⟩,
  ⟨1, 8, 20848796288107, 20848796288116⟩,
  ⟨1, 9, 52404658055227, 52404658058405⟩,
  ⟨2, 3, 117353638366591, 117353638366602⟩,
  ⟨2, 4, 234682808163980, 234682808173088⟩,
  ⟨2, 5, 170080248438387, 170080248447848⟩,
  ⟨2, 6, 132189752560755, 132189752564317⟩,
  ⟨2, 7, 140067594894098, 140067594897909⟩,
  ⟨2, 8, 102222247941573, 102222247947413⟩,
  ⟨2, 9, 158620860250383, 158620860258564⟩,
  ⟨3, 4, 200717594832632, 200717594841732⟩,
  ⟨3, 5, 209454911715760, 209454911725688⟩,
  ⟨3, 6, 182342855003462, 182342855005295⟩,
  ⟨3, 7, 93031308413962, 93031308418200⟩,
  ⟨3, 8, 151880495852691, 151880495862444⟩,
  ⟨3, 9, 223856238329356, 223856238339352⟩,
  ⟨4, 5, 103605755069158, 103605755069169⟩,
  ⟨4, 6, 132979193596843, 132979193606635⟩,
  ⟨4, 7, 109710172493133, 109710172498945⟩,
  ⟨4, 8, 165061953093836, 165061953098986⟩,
  ⟨4, 9, 128107537902724, 128107537902735⟩,
  ⟨5, 6, 182927567706345, 182927567708361⟩,
  ⟨5, 7, 210068207163787, 210068207169970⟩,
  ⟨5, 8, 71145000013345, 71145000014262⟩,
  ⟨5, 9, 32265348486011, 32265348486020⟩,
  ⟨6, 7, 114520125294038, 114520125294048⟩,
  ⟨6, 8, 233116968684967, 233116968690417⟩,
  ⟨6, 9, 184799847588426, 184799847597818⟩,
  ⟨7, 8, 220626260741877, 220626260750107⟩,
  ⟨7, 9, 228483235629964, 228483235632833⟩,
  ⟨8, 9, 72981893724036, 72981893728478⟩]

def scaledLength (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((n : ℝ) / 10^14)

/-- Target for certified evaluation, independent of proving ExactTable. -/
def NumericalTable : Prop :=
  ∀ e ∈ enclosures,
    let d := exactRoute (samples e.i) (samples e.j)
    scaledLength e.lowerNumerator ≤ d ∧ d ≤ scaledLength e.upperNumerator


/-- The physical sign-fold contracts every Euclidean chord, including
chords whose ends lie in different sheets. -/
theorem fold_dist_le (p q : Space) : dist (fold p) (fold q) ≤ dist p q := by
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  apply pow_le_pow_left₀ dist_nonneg _ 2
  fin_cases i
  · exact le_rfl
  · exact abs_abs_sub_abs_le_abs_sub _ _
  · exact abs_abs_sub_abs_le_abs_sub _ _

theorem fold_lipschitz : LipschitzWith 1 fold := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa using fold_dist_le x y

/-- Folding all of an arbitrary continuous or discontinuous competitor
does not increase variation, even for paths of infinite length. -/
theorem fold_variation_le (g : ℝ → Space) (a b : ℝ) :
    variation (fold ∘ g) a b ≤ variation g a b := by
  simpa [variation] using
    (fold_lipschitz.lipschitzOnWith (s := (Set.univ : Set Space))).comp_eVariationOn_le
       (Set.mapsTo_univ g (Icc a b))

/-- A coordinate whose endpoint signs straddle zero meets its physical
gate. Both chronological sign orders are permitted. -/
theorem coordinate_hit {S : Set Space} {p q : Space} (g : CurveOn S p q) (i : Fin 3)
    (opposite : (p i ≤ 0 ∧ 0 ≤ q i) ∨ (q i ≤ 0 ∧ 0 ≤ p i)) :
    ∃ t ∈ Icc (0 : ℝ) 1, g.point t i = 0 := by
  let f := fun t => g.point t i
  have hc : ContinuousOn f (Icc 0 1) :=
    (PiLp.continuous_apply 2 _ i).comp_continuousOn g.cont
  have hp : f 0 = p i := congrArg (fun v : Space => v i) g.start
  have hq : f 1 = q i := congrArg (fun v : Space => v i) g.finish
  rcases opposite with h | h
  · exact intermediate_value_Icc zero_le_one hc (hp ▸ hq ▸ h)
  · exact intermediate_value_Icc' zero_le_one hc (hq ▸ hp ▸ h)


/-- Reduction of the global lower bound for a concrete pair to the
chamber development and gate identifications. Competitors are arbitrary
continuous maps into the *physical* convex-hull boundary. -/
theorem route_le_curve (p q : Sample)
    (g : CurveOn surface (spatial p) (spatial q)) (f : ℝ → Plane)
    (h : BoundsChords g.point f) (fp : f 0 = planar p) (fq : f 1 = planar q)
    (yflip : p.posY ≠ q.posY →
      ((spatial p 1 ≤ 0 ∧ 0 ≤ spatial q 1) ∨ (spatial q 1 ≤ 0 ∧ 0 ≤ spatial p 1)))
    (zflip : p.posZ ≠ q.posZ →
      ((spatial p 2 ≤ 0 ∧ 0 ≤ spatial q 2) ∨ (spatial q 2 ≤ 0 ∧ 0 ≤ spatial p 2)))
    (hy : ∀ t ∈ Icc (0 : ℝ) 1, g.point t 1 = 0 → f t ∈ gateY)
    (hz : ∀ t ∈ Icc (0 : ℝ) 1, g.point t 2 = 0 → f t ∈ gateZ) :
    exactRoute p q ≤ variation g.point 0 1 := by
  unfold exactRoute
  simp only [← fp, ← fq]
  by_cases ey : p.posY = q.posY <;> by_cases ez : p.posZ = q.posZ
  · simpa [ey, ez] using h 0 1 le_rfl zero_le_one le_rfl
  · obtain ⟨t, ht, he⟩ := coordinate_hit g 2 (zflip ez)
    simpa [ey, ez] using one_hit h ht (hz t ht he)
  · obtain ⟨t, ht, he⟩ := coordinate_hit g 1 (yflip ey)
    simpa [ey, ez] using one_hit h ht (hy t ht he)
  · obtain ⟨s, hs, hse⟩ := coordinate_hit g 1 (yflip ey)
    obtain ⟨t, ht, hte⟩ := coordinate_hit g 2 (zflip ez)
    simpa [ey, ez] using two_hits h hs ht (hy s hs hse) (hz t ht hte)

end OloidDistance
