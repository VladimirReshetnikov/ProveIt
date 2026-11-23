import Std

/- Semantic Lean theorems for the rational Seifert and Borromean chapters.
   The diagrammatic input-output correspondence and the iPRA derivations
   are addressed separately in the report. -/

namespace KnotSurface

structure StrandColors where
  a : Int
  b : Int
  c : Int
deriving DecidableEq, Repr

def positiveFirst (r : StrandColors) : StrandColors :=
  ⟨2 * r.a - r.b, r.a, r.c⟩

def negativeSecond (r : StrandColors) : StrandColors :=
  ⟨r.a, r.c, 2 * r.c - r.b⟩

def braidBlock (r : StrandColors) : StrandColors :=
  negativeSecond (positiveFirst r)

def borromean (r : StrandColors) : StrandColors :=
  braidBlock (braidBlock (braidBlock r))

def fixedModulo (q : Int) (r : StrandColors) : Prop :=
  q ∣ (borromean r).a - r.a ∧ q ∣ (borromean r).b - r.b ∧ q ∣ (borromean r).c - r.c

theorem borromeanFixed (q : Int) (r : StrandColors) :
    fixedModulo q r ↔ q ∣ 4 * (r.b - r.a) ∧ q ∣ 4 * (r.c - r.a) := by
  let u := 4 * (r.b - r.a)
  let v := 4 * (r.c - r.a)
  have h₁ : (borromean r).a - r.a = -(u + v) := by
    dsimp [u, v, borromean, braidBlock, positiveFirst, negativeSecond]
    omega
  have h₂ : (borromean r).b - r.b = v := by
    dsimp [v, borromean, braidBlock, positiveFirst, negativeSecond]
    omega
  have h₃ : (borromean r).c - r.c = (u + v) + v := by
    dsimp [u, v, borromean, braidBlock, positiveFirst, negativeSecond]
    omega
  change fixedModulo q r ↔ q ∣ u ∧ q ∣ v
  rw [fixedModulo, h₁, h₂, h₃, Int.dvd_neg]
  constructor
  · rintro ⟨huv, hv, _⟩
    exact ⟨by simpa using Int.dvd_sub huv hv, hv⟩
  · rintro ⟨hu, hv⟩
    exact ⟨Int.dvd_add hu hv, hv, Int.dvd_add (Int.dvd_add hu hv) hv⟩

theorem borromeanThreeColors (r : StrandColors) :
    fixedModulo 3 r ↔ 3 ∣ (r.b - r.a) ∧ 3 ∣ (r.c - r.a) := by
  rw [borromeanFixed]
  omega

/-- Which incidence relation holds between the attaching intervals just
    before a band is added to an oriented disk-and-band surface? -/
inductive BandCase where
  | sameBoundary
  | distinctBoundariesSameComponent
  | distinctComponents
deriving DecidableEq, Repr

structure SurfaceCounts where
  components : Int
  boundary : Int
  euler : Int
  handles : Int
deriving DecidableEq, Repr

def initialDisks (s : Nat) : SurfaceCounts := ⟨s, s, s, 0⟩

def attach (c : SurfaceCounts) : BandCase → SurfaceCounts
  | .sameBoundary =>
      {c with boundary := c.boundary + 1, euler := c.euler - 1}
  | .distinctBoundariesSameComponent =>
      {c with boundary := c.boundary - 1, euler := c.euler - 1, handles := c.handles + 1}
  | .distinctComponents =>
      {c with components := c.components - 1, boundary := c.boundary - 1, euler := c.euler - 1}

def genusEquation (c : SurfaceCounts) : Prop :=
  2 * c.handles = 2 * c.components - c.boundary - c.euler

theorem equationDisks (s : Nat) : genusEquation (initialDisks s) := by
  simp [genusEquation, initialDisks]
  omega

theorem equationAttach (c : SurfaceCounts) (k : BandCase) (h : genusEquation c) :
    genusEquation (attach c k) := by
  cases k <;> simp_all [genusEquation, attach] <;> omega

theorem equationMovie (c : SurfaceCounts) (ks : List BandCase) (h : genusEquation c) :
    genusEquation (ks.foldl attach c) := by
  induction ks generalizing c with
  | nil => exact h
  | cons k rest ih => exact ih (attach c k) (equationAttach c k h)

theorem eulerMovie (c : SurfaceCounts) (ks : List BandCase) :
    (ks.foldl attach c).euler = c.euler - ks.length := by
  induction ks generalizing c with
  | nil => simp
  | cons k rest ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    cases k <;> simp [attach] <;> omega

theorem seifertEquation (s : Nat) (ks : List BandCase) :
    let finalCounts := ks.foldl attach (initialDisks s)
    2 * finalCounts.handles =
      2 * finalCounts.components - finalCounts.boundary - s + ks.length := by
  have h := equationMovie (initialDisks s) ks (equationDisks s)
  unfold genusEquation at h
  rw [eulerMovie] at h
  simp only [initialDisks] at h ⊢
  omega

end KnotSurface
