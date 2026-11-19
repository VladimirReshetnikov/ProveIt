import Std
import Init.Data.Nat.Sqrt.Lemmas

/-!
Arithmetic and combinatorial components for a parallelepiped surface.
This file uses only the Lean distribution. The analytic interpretation and
the extraction of first-order iPRA proofs are described in the report.
-/

namespace Parallelepiped

inductive Axis where
  | x | y | z
  deriving Repr, DecidableEq, BEq

structure Face where
  axis : Axis
  high : Bool
  deriving Repr, DecidableEq, BEq

def faces : List Face := [.x, .y, .z].flatMap fun a : Axis =>
  [⟨a, false⟩, ⟨a, true⟩]

def opposite (f : Face) : Face := ⟨f.axis, !f.high⟩

theorem opposite_twice (f : Face) : opposite (opposite f) = f := by
  cases f with | mk a b => cases b <;> rfl

def adjacent (f g : Face) : Bool := !(f.axis == g.axis)

/-- The revFaces is in reverse order. Length of the revFaces plus fuel is six
when called from 'wordsFrom'. Each recursive call consumes one unit. -/
def extendWords : Nat → Face → List Face → List (List Face)
  | 0, _, revFaces => [revFaces.reverse]
  | fuel + 1, f, revFaces =>
    revFaces.reverse :: ((faces.filter fun g => adjacent f g && !revFaces.contains g).flatMap
      fun g => extendWords fuel g (g :: revFaces))

def wordsFrom (f : Face) := extendWords 5 f [f]

def wordsTo (f g : Face) :=
  (wordsFrom f).filter fun w => w.getLast? == some g

theorem mem_faces (f : Face) : f ∈ faces := by
  cases f with | mk a b => cases a <;> cases b <;> simp [faces]

/-- The unvisited suffix follows edges, and never selects a previously used face. -/
def LegalFrom : Face → List Face → List Face → Prop
  | _, _, [] => True
  | f, seen, g :: rest =>
      adjacent f g = true ∧ seen.contains g = false ∧ LegalFrom g (g :: seen) rest

/-- Completeness for every legal continuation of an arbitrary reversed prefix. -/
theorem extend_complete (fuel : Nat) (f : Face) (seen rest : List Face)
    (hlegal : LegalFrom f seen rest) (hlen : rest.length ≤ fuel) :
    seen.reverse ++ rest ∈ extendWords fuel f seen := by
  induction fuel generalizing f seen rest with
  | zero =>
    cases rest with
    | nil => simp [extendWords]
    | cons g tail => simp at hlen
  | succ k ih =>
    cases rest with
    | nil => simp [extendWords]
    | cons g tail =>
      rcases hlegal with ⟨hadj, hnew, htail⟩
      have hlen' : tail.length ≤ k := by simpa using hlen
      have hgood : g ∈ faces.filter (fun v => adjacent f v && !seen.contains v) := by
        simp [mem_faces, hadj, hnew]
      have hrec := ih g (g :: seen) tail htail hlen'
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      refine ⟨g, hgood, ?_⟩
      simpa using hrec

theorem wordsFrom_complete (f : Face) (rest : List Face)
    (hlegal : LegalFrom f [f] rest) (hlen : rest.length ≤ 5) :
    f :: rest ∈ wordsFrom f := by
  simpa [wordsFrom] using extend_complete 5 f [f] rest hlegal hlen

def goodSteps : List Face → Bool
  | a :: b :: tail => adjacent a b && goodSteps (b :: tail)
  | _ => true

def goodWord (f : Face) (w : List Face) : Bool :=
  w.head? == some f && w.length ≤ 6 && w.eraseDups == w && goodSteps w

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem allGeneratedWordsValid :
    (faces.all fun f => (wordsFrom f).all (goodWord f)) = true := by decide

-- All 36 ordered choices of starting and ending charts are checked.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem countsForEveryPair :
    (faces.all fun f => faces.all fun g =>
      (wordsTo f g).length == (if f == g then 1 else if adjacent f g then 26 else 28)) = true := by
  decide

structure Vec where
  x : Int
  y : Int
  z : Int
  deriving Repr, DecidableEq, BEq

def Vec.get (p : Vec) : Axis → Int
  | .x => p.x
  | .y => p.y
  | .z => p.z

def sub (p q : Vec) : Vec := ⟨p.x-q.x, p.y-q.y, p.z-q.z⟩
def neg (v : Vec) : Vec := ⟨-v.x, -v.y, -v.z⟩
def reflect (m : Int) (p : Vec) : Vec := ⟨m-p.x, m-p.y, m-p.z⟩

theorem reflect_twice (m : Int) (p : Vec) : reflect m (reflect m p) = p := by
  cases p
  simp [reflect, Int.sub_sub_self]

theorem reflected_difference (m : Int) (p q : Vec) :
    sub (reflect m p) (reflect m q) = neg (sub p q) := by
  have h (x y : Int) : m-x-(m-y) = -(x-y) := by
    rw [@Int.sub_eq_add_neg (m-x) (m-y), Int.neg_sub, Int.neg_sub,
      @Int.sub_eq_add_neg m x, @Int.sub_eq_add_neg y m, @Int.sub_eq_add_neg y x]
    calc
      m + -x + (y + -m) = m + -m + (y + -x) := by ac_rfl
      _ = y + -x := by rw [Int.add_right_neg, Int.zero_add]
  simp only [sub, reflect, neg, Vec.mk.injEq]
  exact ⟨h _ _, h _ _, h _ _⟩

structure Gram where
  xx : Int
  yy : Int
  zz : Int
  xy : Int
  xz : Int
  yz : Int
  deriving Repr

/-- Common numerator matrix for a rational Gram matrix. -/
def Gram.quadratic (g : Gram) (v : Vec) : Int :=
  g.xx*v.x*v.x + g.yy*v.y*v.y + g.zz*v.z*v.z +
    2*(g.xy*v.x*v.y + g.xz*v.x*v.z + g.yz*v.y*v.z)

def Gram.valid (g : Gram) : Bool :=
  let minor := g.xx*g.yy - g.xy*g.xy
  let det := g.zz*minor + 2*g.xy*g.xz*g.yz - g.xx*g.yz*g.yz - g.yy*g.xz*g.xz
  decide (0 < g.xx ∧ 0 < minor ∧ 0 < det)

theorem quadratic_neg (g : Gram) (v : Vec) : g.quadratic (neg v) = g.quadratic v := by
  simp [Gram.quadratic, neg, Int.mul_neg, Int.neg_mul]

theorem reflected_squared_chord (g : Gram) (m : Int) (p q : Vec) :
    g.quadratic (sub (reflect m p) (reflect m q)) = g.quadratic (sub p q) := by
  rw [reflected_difference, quadratic_neg]

def OnFace (m : Int) (p : Vec) (f : Face) : Prop :=
  0 ≤ p.x ∧ p.x ≤ m ∧ 0 ≤ p.y ∧ p.y ≤ m ∧ 0 ≤ p.z ∧ p.z ≤ m ∧
  p.get f.axis = (if f.high then m else 0)

instance (m : Int) (p : Vec) (f : Face) : Decidable (OnFace m p f) := by
  unfold OnFace
  infer_instance

theorem reflect_on_opposite (m : Int) (p : Vec) (f : Face) (h : OnFace m p f) :
    OnFace m (reflect m p) (opposite f) := by
  cases f with
  | mk a b =>
    cases a <;> cases b <;> simp [OnFace, reflect, opposite, Vec.get] at * <;> omega

/-- A list of (support face, successor point), interpreted from the supplied
start. Every accepted step is a face chord, including steps of length zero. -/
def checkWalk (m : Int) : Vec → List (Face × Vec) → Bool
  | _, [] => true
  | p, (f, q) :: tail =>
    decide (OnFace m p f ∧ OnFace m q f) && checkWalk m q tail

/-- A tiny checker for an individual rational square-root enclosure. It can
also verify an externally proposed enclosure independently of its generator. -/
def checkRootInterval (n den lo hi : Nat) : Bool :=
  decide (0 < den ∧ lo*lo*den ≤ n ∧ n ≤ hi*hi*den ∧ hi ≤ lo+1)

theorem checkRootInterval_sound (n den lo hi : Nat)
    (h : checkRootInterval n den lo hi = true) :
    0 < den ∧ lo*lo*den ≤ n ∧ n ≤ hi*hi*den ∧ hi ≤ lo+1 :=
  of_decide_eq_true h

/-- A transparent bounded scan, used for a short independent correctness
proof. The separate implementation using Nat.sqrt is faster. -/
def lastPassing (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k+1 => if p (k+1) then k+1 else lastPassing p k

theorem lastPassing_passes (p : Nat → Bool) (h₀ : p 0 = true) (k : Nat) :
    p (lastPassing p k) = true := by
  induction k with
  | zero => exact h₀
  | succ k ih =>
    by_cases h : p (k+1) = true
    · simp [lastPassing, h]
    · simpa [lastPassing, h] using ih

theorem lastPassing_le (p : Nat → Bool) (k : Nat) : lastPassing p k ≤ k := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    by_cases h : p (k+1) = true
    · simp [lastPassing, h]
    · simpa [lastPassing, h] using Nat.le_succ_of_le ih

theorem le_lastPassing (p : Nat → Bool) (k r : Nat) (hr : r ≤ k) (hp : p r = true) :
    r ≤ lastPassing p k := by
  induction k with
  | zero => exact hr
  | succ k ih =>
    by_cases h : p (k+1) = true
    · simpa [lastPassing, h] using hr
    · have hne : r ≠ k+1 := fun eq => h (eq ▸ hp)
      have hr' : r ≤ k := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hr hne)
      simpa [lastPassing, h] using ih hr'

def scanFloorRoot (n den : Nat) : Nat :=
  lastPassing (fun r => decide (r*r*den ≤ n)) (n+1)

theorem scanFloorRootBounds (n den : Nat) (hd : 0 < den) :
    let r := scanFloorRoot n den
    r*r*den ≤ n ∧ n < (r+1)*(r+1)*den := by
  let p := fun r => decide (r*r*den ≤ n)
  let r := lastPassing p (n+1)
  have pass := lastPassing_passes p (by simp [p]) (n+1)
  have hlow : r*r*den ≤ n := of_decide_eq_true pass
  have hbig : n < (n+1)*(n+1)*den := Nat.lt_of_lt_of_le (Nat.lt_succ_self n)
    (Nat.le_trans (Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ n)) (Nat.le_mul_of_pos_right _ hd))
  have hne : r ≠ n+1 := fun eq => Nat.not_le_of_gt hbig (eq ▸ hlow)
  have hlt : r < n+1 := Nat.lt_of_le_of_ne (lastPassing_le p _) hne
  refine ⟨hlow, Nat.lt_of_not_ge (fun hr' => ?_)⟩
  have hp : p (r+1) = true := decide_eq_true hr'
  exact Nat.not_succ_le_self r (le_lastPassing p (n+1) (r+1) (Nat.succ_le_of_lt hlt) hp)

def scanCeilRoot (n den : Nat) : Nat :=
  let r := scanFloorRoot n den
  if r*r*den = n then r else r+1

theorem scanCeilRootCovers (n den : Nat) (hd : 0 < den) :
    n ≤ scanCeilRoot n den * scanCeilRoot n den * den := by
  have h := (scanFloorRootBounds n den hd).2
  by_cases eq : scanFloorRoot n den * scanFloorRoot n den * den = n
  · simp [scanCeilRoot, eq]
  · simpa [scanCeilRoot, eq] using Nat.le_of_lt h

def floorRootRatio (n den : Nat) : Nat := Nat.sqrt (n / den)

def ceilRootRatio (n den : Nat) : Nat :=
  let r := floorRootRatio n den
  if r*r*den = n then r else r+1

theorem floorRootBounds (n den : Nat) (hd : 0 < den) :
    let r := floorRootRatio n den
    r*r*den ≤ n ∧ n < (r+1)*(r+1)*den := by
  dsimp only [floorRootRatio]
  exact ⟨(Nat.le_div_iff_mul_le hd).mp (Nat.sqrt_le _),
    (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_sqrt _)⟩

theorem ceilRootCovers (n den : Nat) (hd : 0 < den) :
    n ≤ ceilRootRatio n den * ceilRootRatio n den * den := by
  have h := (floorRootBounds n den hd).2
  by_cases eq : floorRootRatio n den * floorRootRatio n den * den = n
  · simp [ceilRootRatio, eq]
  · simpa [ceilRootRatio, eq] using Nat.le_of_lt h

/-- Squared physical chord = g.quadratic (sub p q) / (gramDen * mesh^2).
Use on a valid positive definite numerator matrix and positive denominators. -/
def chordUnits (g : Gram) (gramDen mesh scale : Nat) (p q : Vec) : Nat :=
  ceilRootRatio ((g.quadratic (sub p q)).toNat * scale * scale) (gramDen * mesh * mesh)

def walkUnits (g : Gram) (gramDen mesh scale : Nat) : Vec → List (Face × Vec) → Nat
  | _, [] => 0
  | p, (_, q) :: tail => chordUnits g gramDen mesh scale p q + walkUnits g gramDen mesh scale q tail

/-- Integer form of the last inequality in the antipodal crossing argument.
The geometric argument proves the hypothesis; comparison has this short
first-order arithmetic proof. -/
theorem bound_by_antipodal_pair (d a b : Int) (h : 2*d ≤ a+b) : d ≤ max a b := by
  omega

end Parallelepiped
