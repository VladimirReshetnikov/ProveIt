import Std

/-!
Finite constructive Helly for rational vectors. Fraction-free elimination,
signed hull-tree assembly, and the deletion recursion are proved below.
Only Lean's standard library is used.
-/

namespace ConstructiveHelly

universe u v

/-- `blend a b x y` uses the positive integer weights `a+1` and `b+1`. -/
structure Geometry (X : Type u) where
  blend : Nat → Nat → X → X → X
  equiv : X → X → Prop

structure ConvexSet {X : Type u} (G : Geometry X) where
  mem : X → Prop
  transport : ∀ {x y}, G.equiv x y → mem y → mem x
  closed : ∀ a b {x y}, mem x → mem y → mem (G.blend a b x y)

/-- A hull certificate is a binary tree with indexed leaves and positive weights. -/
inductive HullTree (k : Nat) where
  | leaf (j : Fin k)
  | node (a b : Nat) (left right : HullTree k)
  deriving Repr

namespace HullTree

def eval {X : Type u} {k : Nat} (G : Geometry X) (p : Fin k → X) : HullTree k → X
  | .leaf j => p j
  | .node a b l r => G.blend a b (eval G p l) (eval G p r)

def uses {k : Nat} (j : Fin k) : HullTree k → Bool
  | .leaf i => decide (i = j)
  | .node _ _ l r => uses j l || uses j r

theorem eval_mem {X : Type u} {k : Nat} {G : Geometry X} {p : Fin k → X}
    (C : ConvexSet G) (t : HullTree k) (h : ∀ j, uses j t = true → C.mem (p j)) :
    C.mem (eval G p t) := by
  induction t with
  | leaf i => exact h i (by simp [uses])
  | node a b l r hl hr =>
    apply C.closed
    · exact hl (fun j hj => h j (by simp [uses, hj]))
    · exact hr (fun j hj => h j (by simp [uses, hj]))

end HullTree

/-- Two nonempty, disjointly supported trees with the same evaluation. -/
structure RadonCertificate {X : Type u} {k : Nat}
    (G : Geometry X) (p : Fin k → X) where
  left : HullTree k
  right : HullTree k
  disjoint : ∀ j, left.uses j = true → right.uses j = false
  agree : G.equiv (left.eval G p) (right.eval G p)

namespace RadonCertificate

/-- If all leaves except possibly `bad` lie in C, the Radon point lies in C. -/
theorem avoid {X : Type u} {k : Nat} {G : Geometry X} {p : Fin k → X}
    (r : RadonCertificate G p) (C : ConvexSet G) (bad : Fin k)
    (good : ∀ j, j ≠ bad → C.mem (p j)) : C.mem (r.left.eval G p) := by
  by_cases occurs : r.left.uses bad = true
  · apply C.transport r.agree
    apply HullTree.eval_mem C r.right
    intro j hj
    apply good j
    intro heq
    subst j
    simp [r.disjoint bad occurs] at hj
  · apply HullTree.eval_mem C r.left
    intro j hj
    apply good j
    intro heq
    exact occurs (heq ▸ hj)

end RadonCertificate

/-- Embed a list of m positions into m+1 positions by omitting j. -/
def skip {m : Nat} (j : Fin (m+1)) (i : Fin m) : Fin (m+1) :=
  if i.val < j.val then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩

/-- Every position different from j survives deletion of j. -/
theorem skip_hit {m : Nat} (j t : Fin (m+1)) (h : t ≠ j) : ∃ i, skip j i = t := by
  have hne : t.val ≠ j.val := fun e => h (Fin.ext e)
  by_cases hj : t.val < j.val
  · exact ⟨⟨t.val, by omega⟩, by apply Fin.ext; simp [skip, hj]⟩
  · refine ⟨⟨t.val - 1, by omega⟩, ?_⟩
    have hg : ¬t.val - 1 < j.val := by omega
    apply Fin.ext
    simp [skip, hg]
    omega

abbrev Witness {X : Type u} {I : Type v} {m : Nat} {G : Geometry X}
    (C : I → ConvexSet G) (f : Fin m → I) := {x : X // ∀ i, (C (f i)).mem x}

/-- A small-family oracle returns actual points; a Radon oracle returns trees.
    The recursion is structural on the family size, even when f repeats labels. -/
def solve {X : Type u} {I : Type v} {G : Geometry X} (d : Nat) (C : I → ConvexSet G)
    (small : ∀ m, m ≤ d+1 → (f : Fin m → I) → Witness C f)
    (radon : (p : Fin (d+2) → X) → RadonCertificate G p) :
    (m : Nat) → (f : Fin m → I) → Witness C f
  | 0, f => small 0 (by omega) f
  | m+1, f =>
    if hs : m+1 ≤ d+1 then small (m+1) hs f else
    let pick (j : Fin (d+2)) : Fin (m+1) := ⟨j.val, by omega⟩
    let child (j : Fin (d+2)) := solve d C small radon m (fun i => f (skip (pick j) i))
    let p (j : Fin (d+2)) := (child j).val
    let r := radon p
    ⟨r.left.eval G p, by
      intro t
      let bad : Fin (d+2) := if h : t.val < d+2 then ⟨t.val, h⟩ else ⟨0, by omega⟩
      apply r.avoid (C (f t)) bad
      intro j hj
      have hne : t ≠ pick j := by
        intro heq
        have hv : t.val = j.val := congrArg Fin.val heq
        have hb : t.val < d+2 := hv ▸ j.isLt
        apply hj
        apply Fin.ext
        simp [bad, hb, hv]
      obtain ⟨i, hi⟩ := skip_hit (pick j) t hne
      exact hi ▸ (child j).property i⟩

/-- Rational vectors in common positive-denominator representation. -/
structure QPoint (d : Nat) where
  num : Fin d → Int
  den : Nat
  pos : 0 < den

namespace QPoint

def equiv {d : Nat} (x y : QPoint d) : Prop :=
  ∀ i, x.num i * (y.den : Int) = y.num i * (x.den : Int)

def blend {d : Nat} (a b : Nat) (x y : QPoint d) : QPoint d where
  num i := ((a+1 : Nat) : Int) * x.num i * (y.den : Int) +
           ((b+1 : Nat) : Int) * y.num i * (x.den : Int)
  den := (a+b+2) * x.den * y.den
  pos := Nat.mul_pos (Nat.mul_pos (by omega) x.pos) y.pos

def geometry (d : Nat) : Geometry (QPoint d) := ⟨blend, equiv⟩

/-- A decidable checker can validate candidate trees supplied by a generator. -/
def check {d k : Nat} (p : Fin k → QPoint d) (l r : HullTree k) : Bool :=
  decide (∀ j, l.uses j = true → r.uses j = false) &&
  decide (∀ i : Fin d,
    (l.eval (geometry d) p).num i * ((r.eval (geometry d) p).den : Int) =
    (r.eval (geometry d) p).num i * ((l.eval (geometry d) p).den : Int))

theorem sound {d k : Nat} (p : Fin k → QPoint d) (l r : HullTree k)
    (h : check p l r = true) :
    (∀ j, l.uses j = true → r.uses j = false) ∧
    equiv (l.eval (geometry d) p) (r.eval (geometry d) p) := by
  simpa [check, equiv] using h

def certify {d k : Nat} (p : Fin k → QPoint d) (l r : HullTree k)
    (h : check p l r = true) : RadonCertificate (geometry d) p :=
  ⟨l, r, (sound p l r h).1, (sound p l r h).2⟩

/-- A column in the pool is a coefficient vector indexed by the input points. -/
abbrev Col (k : Nat) := Fin k → Int

def dot {k : Nat} (r v : Col k) : Int :=
  ((List.finRange k).map (fun j => r j * v j)).sum

/-- Remove the first column on which row r has nonzero value. -/
def pivot {k : Nat} (r : Col k) : List (Col k) → Option (Col k × List (Col k))
  | [] => none
  | v :: vs => if dot r v ≠ 0 then some (v, vs) else
    (pivot r vs).map (fun z => (z.1, v :: z.2))

/-- Fraction-free elimination. After a pivot step, every remaining column
    annihilates r as well as all rows previously processed. -/
def eliminate {k : Nat} (r : Col k) (B : List (Col k)) : List (Col k) :=
  match pivot r B with
  | none => B
  | some (v, rest) => rest.map fun w =>
    let a := dot r v
    let b := dot r w
    fun j => a * w j - b * v j

/-- Homogeneous column j is (den_j, num_j[0], ..., num_j[d-1]). -/
def kernelPool {d k : Nat} (p : Fin k → QPoint d) : List (Col k) :=
  let units : List (Col k) := (List.finRange k).map fun i j => if j = i then 1 else 0
  let rows : List (Col k) := (fun j => ((p j).den : Int)) ::
    (List.finRange d).map (fun i j => (p j).num i)
  rows.foldl (fun B r => eliminate r B) units

/-- Bookkeeping for one pivot. These lemmas support the arithmetic completion. -/
theorem pivot_split {k : Nat} (r : Col k) {B : List (Col k)}
    {v : Col k} {rest : List (Col k)} (h : pivot r B = some (v, rest)) :
    v ∈ B ∧ (∀ w ∈ rest, w ∈ B) ∧ rest.length + 1 = B.length ∧ dot r v ≠ 0 := by
  induction B generalizing v rest with
  | nil => simp [pivot] at h
  | cons x xs ih =>
    by_cases hx : dot r x ≠ 0
    · simp [pivot, hx] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp, fun _ hw => List.mem_cons_of_mem _ hw, by simp, hx⟩
    · cases hp : pivot r xs with
      | none => simp [pivot, hx, hp] at h
      | some pair =>
        obtain ⟨v', ys⟩ := pair
        simp [pivot, hx, hp] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hv, hs, hlen, hdot⟩ := ih hp
        refine ⟨List.mem_cons_of_mem _ hv, ?_, by simp [hlen], hdot⟩
        intro w hw
        rcases List.mem_cons.mp hw with hw | hw
        · simp [hw]
        · exact List.mem_cons_of_mem _ (hs w hw)

theorem pivot_none {k : Nat} (r : Col k) {B : List (Col k)}
    (h : pivot r B = none) : ∀ w ∈ B, dot r w = 0 := by
  induction B with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : dot r x = 0
    · have hp : pivot r xs = none := by
        cases he : pivot r xs with
        | none => rfl
        | some z => simp [pivot, hx, he] at h
      intro w hw
      rcases List.mem_cons.mp hw with hw | hw
      · exact hw ▸ hx
      · exact ih hp w hw
    · simp [pivot, hx] at h

theorem eliminate_length {k : Nat} (r : Col k) (B : List (Col k)) :
    B.length ≤ (eliminate r B).length + 1 := by
  cases hp : pivot r B with
  | none => simp [eliminate, hp]
  | some pair =>
    obtain ⟨v, rest⟩ := pair
    simp [eliminate, hp, (pivot_split r hp).2.2.1]

theorem surviving_length {k : Nat} (rows B : List (Col k)) :
    B.length ≤ (rows.foldl (fun Bs r => eliminate r Bs) B).length + rows.length := by
  induction rows generalizing B with
  | nil => simp
  | cons r rs ih =>
    have h := ih (eliminate r B)
    have h' := eliminate_length r B
    simp only [List.foldl_cons, List.length_cons]
    omega

theorem kernelPool_positive {d : Nat} (p : Fin (d+2) → QPoint d) :
    0 < (kernelPool p).length := by
  unfold kernelPool
  generalize hB : (List.finRange (d+2)).map _ = B
  generalize hrows : (fun j => ((p j).den : Int)) :: (List.finRange d).map _ = rows
  have h := surviving_length rows B
  have hlenB := congrArg List.length hB
  have hlenR := congrArg List.length hrows
  simp at hlenB hlenR
  dsimp only
  omega

private theorem sum_combine {k : Nat} (s : List (Fin k)) (r w v : Col k) (a b : Int) :
    (s.map (fun j => r j * (a * w j - b * v j))).sum =
    a * (s.map (fun j => r j * w j)).sum - b * (s.map (fun j => r j * v j)).sum := by
  induction s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, Int.mul_sub, Int.mul_add, Int.mul_add]
    rw [Int.mul_left_comm (r x) a, Int.mul_left_comm (r x) b]
    omega

theorem dot_combine {k : Nat} (r w v : Col k) (a b : Int) :
    dot r (fun j => a * w j - b * v j) = a * dot r w - b * dot r v :=
  sum_combine (List.finRange k) r w v a b

theorem eliminate_annihilates {k : Nat} (r : Col k) (B : List (Col k)) :
    ∀ w ∈ eliminate r B, dot r w = 0 := by
  intro w hw
  cases hp : pivot r B with
  | none =>
    simp [eliminate, hp] at hw
    exact pivot_none r hp w hw
  | some pair =>
    obtain ⟨v, rest⟩ := pair
    simp [eliminate, hp] at hw
    obtain ⟨x, _, rfl⟩ := hw
    rw [dot_combine, Int.mul_comm (dot r v), Int.sub_self]

theorem eliminate_preserves {k : Nat} (q r : Col k) (B : List (Col k))
    (prev : ∀ w ∈ B, dot q w = 0) : ∀ w ∈ eliminate r B, dot q w = 0 := by
  intro w hw
  cases hp : pivot r B with
  | none => exact prev _ (by simpa [eliminate, hp] using hw)
  | some pair =>
    obtain ⟨v, rest⟩ := pair
    simp [eliminate, hp] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    obtain ⟨hv, hs, _, _⟩ := pivot_split r hp
    simp [dot_combine, prev v hv, prev x (hs x hx)]

theorem fold_preserves {k : Nat} (q : Col k) (rows B : List (Col k))
    (prev : ∀ w ∈ B, dot q w = 0) :
    ∀ w ∈ rows.foldl (fun Bs r => eliminate r Bs) B, dot q w = 0 := by
  induction rows generalizing B with
  | nil => exact prev
  | cons r rs ih => exact ih _ (eliminate_preserves q r B prev)

theorem fold_annihilates {k : Nat} (q : Col k) (rows B : List (Col k))
    (hq : q ∈ rows) : ∀ w ∈ rows.foldl (fun Bs r => eliminate r Bs) B, dot q w = 0 := by
  induction rows generalizing B with
  | nil => simp at hq
  | cons r rs ih =>
    rcases List.mem_cons.mp hq with h | h
    · subst r
      exact fold_preserves q rs _ (eliminate_annihilates q B)
    · exact ih _ h

theorem kernelPool_equations {d k : Nat} (p : Fin k → QPoint d) {v : Col k}
    (hv : v ∈ kernelPool p) : dot (fun j => ((p j).den : Int)) v = 0 ∧
      ∀ i, dot (fun j => (p j).num i) v = 0 := by
  unfold kernelPool at hv
  constructor
  · exact fold_annihilates _ _ _ (List.Mem.head _) v hv
  · intro i
    apply fold_annihilates _ _ _ _ v hv
    have hi : i.val < (List.finRange d).length := by simp
    have hm : i ∈ List.finRange d := List.mem_of_getElem (i := i.val) (h := hi) (by simp)
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, hm, rfl⟩)

/-- The pivot is moved to the front and the order of the rest is preserved. -/
theorem pivot_perm {k : Nat} (r : Col k) {B : List (Col k)}
    {v : Col k} {rest : List (Col k)} (h : pivot r B = some (v, rest)) :
    B.Perm (v :: rest) := by
  induction B generalizing v rest with
  | nil => simp [pivot] at h
  | cons x xs ih =>
    by_cases hx : dot r x ≠ 0
    · simp [pivot, hx] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .refl _
    · cases hp : pivot r xs with
      | none => simp [pivot, hx, hp] at h
      | some pair =>
        obtain ⟨v', ys⟩ := pair
        simp [pivot, hx, hp] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ((ih hp).cons x).trans (.swap _ _ _)

/-- Each column owns a coordinate at which every other surviving column vanishes. -/
structure Marked {k : Nat} (B : List (Col k)) : Prop where
  nodup : B.Nodup
  mark : ∀ x ∈ B, ∃ j, x j ≠ 0 ∧ ∀ z ∈ B, z ≠ x → z j = 0

private theorem nodup_map_on {A B : Type} {l : List A} (h : l.Nodup) (f : A → B)
    (inj : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → f x ≠ f y) : (l.map f).Nodup :=
  List.pairwise_map.mpr (h.imp_of_mem (fun hx hy hne => inj _ hx _ hy hne))

private theorem allFin_nodup (k : Nat) : (List.finRange k).Nodup := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [List.finRange_succ, List.nodup_cons]
    constructor
    · intro h
      obtain ⟨i, _, eq⟩ := List.mem_map.mp h
      have := congrArg Fin.val eq
      simp at this
    · apply nodup_map_on ih
      intro x _ y _ hne heq
      exact hne (Fin.ext (Nat.succ.inj (congrArg Fin.val heq)))

private def unitCol {k : Nat} (i : Fin k) : Col k := fun j => if j = i then 1 else 0

private theorem unit_neq {k : Nat} {i j : Fin k} (h : i ≠ j) : unitCol i ≠ unitCol j := by
  intro heq
  have := congrFun heq i
  simp [unitCol, h] at this

private theorem units_marked (k : Nat) : Marked ((List.finRange k).map unitCol) := by
  constructor
  · exact nodup_map_on (allFin_nodup k) unitCol (fun _ _ _ _ hne => unit_neq hne)
  · intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    refine ⟨i, by simp [unitCol], ?_⟩
    intro z hz hne
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz
    have hij : i ≠ j := fun e => hne (congrArg unitCol e.symm)
    simp [unitCol, hij]

theorem eliminate_marked {k : Nat} (r : Col k) (B : List (Col k))
    (hB : Marked B) : Marked (eliminate r B) := by
  cases hp : pivot r B with
  | none => simpa [eliminate, hp] using hB
  | some pair =>
    obtain ⟨v, rest⟩ := pair
    obtain ⟨hv, sub, _, ha⟩ := pivot_split r hp
    obtain ⟨hvout, nd⟩ := List.nodup_cons.mp ((pivot_perm r hp).nodup_iff.mp hB.nodup)
    let T (x : Col k) : Col k := fun j => dot r v * x j - dot r x * v j
    have ht (x) (hx : x ∈ rest) :
        ∃ j, T x j ≠ 0 ∧ ∀ z ∈ rest, z ≠ x → T z j = 0 := by
      obtain ⟨j, h1, h2⟩ := hB.mark x (sub x hx)
      have hvx : v ≠ x := fun e => hvout (e ▸ hx)
      have hz := h2 v hv hvx
      refine ⟨j, ?_, ?_⟩
      · simpa [T, hz] using Int.mul_ne_zero ha h1
      · intro z hzin hne
        simp [T, hz, h2 z (sub z hzin) hne]
    rw [eliminate, hp]
    change Marked (rest.map T)
    constructor
    · apply nodup_map_on nd
      intro x hx y hy hne heq
      obtain ⟨j, hj, hother⟩ := ht x hx
      exact hj ((congrFun heq j).trans (hother y hy (Ne.symm hne)))
    · intro tx htx
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp htx
      obtain ⟨j, hj, hother⟩ := ht x hx
      refine ⟨j, hj, ?_⟩
      intro ty hty hne
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hty
      exact hother y hy (fun e => hne (congrArg T e))

theorem fold_marked {k : Nat} (rows B : List (Col k)) (hB : Marked B) :
    Marked (rows.foldl (fun Bs r => eliminate r Bs) B) := by
  induction rows generalizing B with
  | nil => exact hB
  | cons r rs ih => exact ih _ (eliminate_marked r B hB)

theorem kernelPool_nonzero {d k : Nat} (p : Fin k → QPoint d) {v : Col k}
    (hv : v ∈ kernelPool p) : ∃ j, v j ≠ 0 := by
  have marked : Marked (kernelPool p) := fold_marked _ _ (units_marked k)
  obtain ⟨j, hj, _⟩ := marked.mark v hv
  exact ⟨j, hj⟩

private def massSum {k : Nat} (w : Fin k → Nat) (s : List (Fin k)) := (s.map w).sum
private def intSum {k : Nat} (s : List (Fin k)) (f : Fin k → Int) := (s.map f).sum

/-- Combine all positive masses in the given finite list. -/
def buildMass {k : Nat} (w : Fin k → Nat) : List (Fin k) → Option (HullTree k)
  | [] => none
  | i :: s => if w i = 0 then buildMass w s else
    match buildMass w s with
    | none => some (.leaf i)
    | some t => some (.node (w i-1) (massSum w s-1) (.leaf i) t)

def treeOfMass {k : Nat} (w : Fin k → Nat) := buildMass w (List.finRange k)

private theorem build_none {k : Nat} (w : Fin k → Nat) (s : List (Fin k)) :
    buildMass w s = none ↔ massSum w s = 0 := by
  induction s with
  | nil => simp [buildMass, massSum]
  | cons i s ih =>
    by_cases h : w i = 0
    · simpa [buildMass, h, massSum] using ih
    · cases hTail : buildMass w s <;> simp [buildMass, h, hTail, massSum]

private theorem build_uses {k : Nat} (w : Fin k → Nat) (s : List (Fin k))
    {t : HullTree k} (ht : buildMass w s = some t) (j : Fin k)
    (hj : t.uses j = true) : w j ≠ 0 := by
  induction s generalizing t with
  | nil => simp [buildMass] at ht
  | cons i s ih =>
    by_cases h : w i = 0
    · exact ih (by simpa [buildMass, h] using ht) hj
    · cases e : buildMass w s with
      | none =>
        simp [buildMass, h, e] at ht
        subst t
        simpa [HullTree.uses] using (fun he : i = j => he ▸ h) (by simpa [HullTree.uses] using hj)
      | some v =>
        simp [buildMass, h, e] at ht
        subst t
        rcases (by simpa [HullTree.uses] using hj : i=j ∨ v.uses j = true) with h' | h'
        · exact h' ▸ h
        · exact ih e h'

private theorem scalar_zero {k d : Nat} (f : Fin k → Nat) (p : Fin k → QPoint d)
    (s : List (Fin k)) (h : massSum (fun j => f j*(p j).den) s = 0) (c : Fin d) :
    intSum s (fun j => (f j : Int)*(p j).num c) = 0 := by
  induction s with
  | nil => rfl
  | cons i s ih =>
    simp [massSum, Nat.mul_eq_zero] at h
    have hi : f i = 0 := h.1.resolve_right (by have := (p i).pos; omega)
    have hs := ih h.2
    simp [intSum, hi] at hs ⊢
    exact hs

private theorem blend_eq {d : Nat} (x y : QPoint d) (a b : Nat) (A B : Int) (c : Fin d)
    (ha : 0<a) (hb : 0<b)
    (h1 : (a : Int)*x.num c = A*x.den) (h2 : (b : Int)*y.num c = B*y.den) :
    ((a+b : Nat) : Int)*(blend (a-1) (b-1) x y).num c =
    (A+B)*((blend (a-1) (b-1) x y).den : Int) := by
  have e : a-1+1 = a := by omega
  have e' : b-1+1 = b := by omega
  have e'' : a-1 + (b-1) + 2 = a+b := by omega
  simp only [blend, e, e', e'', h1, h2, Int.natCast_mul]
  simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

private theorem build_eval {k d : Nat} (f : Fin k → Nat) (p : Fin k → QPoint d)
    (s : List (Fin k)) {t : HullTree k}
    (ht : buildMass (fun j => f j*(p j).den) s = some t) (c : Fin d) :
    (massSum (fun j => f j*(p j).den) s : Int) * (t.eval (geometry d) p).num c =
    intSum s (fun j => (f j : Int)*(p j).num c) * ((t.eval (geometry d) p).den : Int) := by
  let w (j : Fin k) := f j * (p j).den
  change buildMass w s = some t at ht
  change (massSum w s : Int) * _ = _
  induction s generalizing t with
  | nil => simp [buildMass] at ht
  | cons i s ih =>
    by_cases h : w i = 0
    · have hi : f i = 0 := (Nat.mul_eq_zero.mp h).resolve_right (by have := (p i).pos; omega)
      have H := ih (by simpa [buildMass, h] using ht : buildMass w s = some t)
      simpa [massSum, intSum, h, hi] using H
    · have hi : 0 < w i := by omega
      have single : (w i : Int)*(p i).num c = ((f i : Int)*(p i).num c)*(p i).den := by
        simp only [w, Int.natCast_mul, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
      cases e : buildMass w s with
      | none =>
        have hs := (build_none w s).mp e
        have hn := scalar_zero f p s hs c
        simp [buildMass, h, e] at ht
        subst t
        change ((w i + massSum w s : Nat) : Int)*(p i).num c =
          ((f i : Int)*(p i).num c + intSum s _)*(p i).den
        simpa [hs, hn] using single
      | some v =>
        have hs : 0 < massSum w s := by
          have hn : buildMass w s ≠ none := by simp [e]
          have hpos : massSum w s ≠ 0 := fun hz => hn ((build_none w s).mpr hz)
          omega
        simp [buildMass, h, e] at ht
        subst t
        exact blend_eq (p i) (v.eval (geometry d) p) (w i) (massSum w s) _ _ c hi hs single (ih e)
/-- Executable generator. Every `some` result carries a checked proof. -/
def radon? {d : Nat} (p : Fin (d+2) → QPoint d) : Option (RadonCertificate (geometry d) p) := do
  let v ← (kernelPool p).head?
  let l ← treeOfMass (fun j => (v j).toNat * (p j).den)
  let r ← treeOfMass (fun j => (-v j).toNat * (p j).den)
  if h : check p l r = true then some (certify p l r h) else none

/-- Universal success of the rational Radon generator. -/
def RadonComplete (d : Nat) : Prop :=
  ∀ p : Fin (d+2) → QPoint d, (radon? p).isSome = true

/-- If the arithmetic completeness lemma is supplied, the constructor returns
    an actual point in the requested family, proved to lie in every member. -/
def solveRational {I : Type v} (d : Nat) (complete : RadonComplete d)
    (C : I → ConvexSet (geometry d))
    (small : ∀ m, m ≤ d+1 → (f : Fin m → I) → Witness C f)
    (m : Nat) (f : Fin m → I) : Witness C f :=
  solve d C small (fun p => (radon? p).get (complete p)) m f

private theorem signed_sum {k : Nat} (s : List (Fin k)) (v g : Col k) :
    intSum s (fun j => g j * v j) =
    intSum s (fun j => ((v j).toNat : Int)*g j) - intSum s (fun j => ((-v j).toNat : Int)*g j) := by
  induction s with
  | nil => rfl
  | cons i s ih =>
    have h : v i = ((v i).toNat : Int) - ((-v i).toNat : Int) := by omega
    have e := congrArg (fun z => z * g i) h
    change v i * g i = (((v i).toNat : Int) - ((-v i).toNat : Int)) * g i at e
    rw [Int.sub_mul, Int.mul_comm (v i)] at e
    change g i * v i + intSum s _ = (_ + intSum s _) - (_ + intSum s _)
    dsimp only
    omega

private theorem cast_mass {k : Nat} (s : List (Fin k)) (f g : Fin k → Nat) :
    (massSum (fun j => f j*g j) s : Int) = intSum s (fun j => (f j : Int)*(g j : Int)) := by
  induction s with
  | nil => rfl
  | cons i s ih => simpa [massSum, intSum, Int.natCast_add, Int.natCast_mul] using congrArg (fun z : Int => (f i : Int)*(g i : Int)+z) ih

private theorem mass_le {k : Nat} (w : Fin k → Nat) (s : List (Fin k)) (i : Fin k)
    (hi : i ∈ s) : w i ≤ massSum w s := by
  induction s with
  | nil => simp at hi
  | cons a s ih =>
    change w i ≤ w a + massSum w s
    rcases List.mem_cons.mp hi with h | h
    · subst a; omega
    · have := ih h; omega

private theorem fin_mem {k : Nat} (i : Fin k) : i ∈ List.finRange k := by
  have h : i.val < (List.finRange k).length := by simp
  exact List.mem_of_getElem (i := i.val) (h := h) (by simp)

/-- Every proposed family of d+2 rational points produces a Radon certificate. -/
theorem radon_complete (d : Nat) : RadonComplete d := by
  intro p
  cases he : (kernelPool p).head? with
  | none =>
    have e := List.head?_eq_none_iff.mp he
    have h := kernelPool_positive p
    simp [e] at h
  | some v =>
    have hv : v ∈ kernelPool p := List.mem_of_mem_head? (by simp [he])
    obtain ⟨eqD, eqN⟩ := kernelPool_equations p hv
    obtain ⟨j, hj⟩ := kernelPool_nonzero p hv
    let s := List.finRange (d+2)
    let f (i : Fin (d+2)) := (v i).toNat
    let g (i : Fin (d+2)) := (-v i).toNat
    let D (i : Fin (d+2)) := (p i).den
    let u i := f i * D i
    let w i := g i * D i
    have ew : massSum u s = massSum w s := by
      have h := signed_sum s v (fun i => (D i : Int))
      change intSum s (fun i => (D i : Int)*v i) = 0 at eqD
      rw [eqD] at h
      have h1 := cast_mass s f D
      have h2 := cast_mass s g D
      change (massSum u s : Int) = _ at h1
      change (massSum w s : Int) = _ at h2
      change 0 = intSum s (fun j => (f j : Int)*(D j : Int)) -
        intSum s (fun j => (g j : Int)*(D j : Int)) at h
      omega
    have pos : 0 < massSum u s := by
      have h1 := mass_le u s j (fin_mem j)
      have h2 := mass_le w s j (fin_mem j)
      have hD : 0 < D j := (p j).pos
      by_cases h : 0 < v j
      · have hj' : 0 < f j := by dsimp [f]; omega
        exact Nat.lt_of_lt_of_le (Nat.mul_pos hj' hD) h1
      · have hj' : 0 < g j := by dsimp [g]; omega
        rw [ew]
        exact Nat.lt_of_lt_of_le (Nat.mul_pos hj' hD) h2
    cases hl : buildMass u s with
    | none => have := (build_none u s).mp hl; omega
    | some l =>
      cases hr : buildMass w s with
      | none => have := (build_none w s).mp hr; omega
      | some r =>
        have dis : ∀ i, l.uses i = true → r.uses i = false := by
          intro i hi
          have hL := build_uses u s hl i hi
          cases hh : r.uses i with
          | false => rfl
          | true =>
            have hR := build_uses w s hr i hh
            have L : f i ≠ 0 := fun e => hL (by simp [u, e])
            have R : g i ≠ 0 := fun e => hR (by simp [w, e])
            dsimp [f, g] at L R
            omega
        have same : equiv (l.eval (geometry d) p) (r.eval (geometry d) p) := by
          intro c
          have L := build_eval f p s hl c
          have R := build_eval g p s hr c
          have hnum := signed_sum s v (fun i => (p i).num c)
          have hzero := eqN c
          change intSum s (fun i => (p i).num c*v i) = 0 at hzero
          rw [hzero] at hnum
          let A := intSum s (fun i => (f i : Int)*(p i).num c)
          let B := intSum s (fun i => (g i : Int)*(p i).num c)
          change 0 = A-B at hnum
          have ab : A=B := by omega
          let x := l.eval (geometry d) p
          let y := r.eval (geometry d) p
          change (massSum u s : Int)*x.num c = A*(x.den : Int) at L
          change (massSum w s : Int)*y.num c = B*(y.den : Int) at R
          rw [← ew, ← ab] at R
          apply Int.eq_of_mul_eq_mul_left (a := (massSum u s : Int)) (by omega)
          change (massSum u s : Int)*(x.num c*y.den) = (massSum u s : Int)*(y.num c*x.den)
          rw [← Int.mul_assoc, ← Int.mul_assoc, L, R]
          ac_rfl
        have hc : check p l r = true := by simpa [check, equiv] using And.intro dis same
        have hL : buildMass (fun i => (v i).toNat * (p i).den) (List.finRange (d+2)) = some l := hl
        have hR : buildMass (fun i => (-v i).toNat * (p i).den) (List.finRange (d+2)) = some r := hr
        simp [radon?, he, treeOfMass, hL, hR, hc]

/-- Total constructive finite Helly theorem over rational vector codes. -/
def helly {I : Type v} (d : Nat) (C : I → ConvexSet (geometry d))
    (small : ∀ m, m ≤ d+1 → (f : Fin m → I) → Witness C f)
    (m : Nat) (f : Fin m → I) : Witness C f :=
  solveRational d (radon_complete d) C small m f

/-- Promote each requested label into a duplicate-free initial block of the
    finite universe, retaining all remaining labels for padding. -/
private structure SplitLabels {n : Nat} (requested : List (Fin n)) where
  front : List (Fin n)
  rest : List (Fin n)
  perm : (front ++ rest).Perm (List.finRange n)
  cover : ∀ i ∈ requested, i ∈ front
  bound : front.length ≤ requested.length

private theorem cons_erase {n : Nat} {a : Fin n} {l : List (Fin n)} (h : a ∈ l) :
    (a :: l.erase a).Perm l := by
  induction l with
  | nil => simp at h
  | cons b s ih =>
    by_cases h' : b=a
    · subst b; simp
    · have hs := (List.mem_cons.mp h).resolve_left (Ne.symm h')
      have hneg : (b == a) = false := beq_eq_false_iff_ne.mpr h'
      simpa [List.erase, hneg] using (List.Perm.swap b a (s.erase a)).trans ((ih hs).cons b)

private def splitLabels {n : Nat} : (s : List (Fin n)) → SplitLabels s
  | [] => ⟨[], List.finRange n, .refl _, by simp, by simp⟩
  | a :: s =>
    let z := splitLabels s
    if h : a ∈ z.front then
      ⟨z.front, z.rest, z.perm, by
        intro i hi
        rcases List.mem_cons.mp hi with e | e
        · exact e ▸ h
        · exact z.cover i e, by have := z.bound; simp; omega⟩
    else
      have hrest : a ∈ z.rest :=
        (List.mem_append.mp (z.perm.mem_iff.mpr (fin_mem a))).resolve_left h
      ⟨a :: z.front, z.rest.erase a,
       List.perm_middle.symm.trans (((cons_erase hrest).append_left z.front).trans z.perm), by
        intro i hi
        rcases List.mem_cons.mp hi with e | e
        · simp [e]
        · exact List.mem_cons_of_mem _ (z.cover i e), by simpa using z.bound⟩

/-- A table on distinct labels of the exact size `min n (d+1)` supplies all
    calls made by the general solver, including repeated labels and m=0. -/
def hellyExact (d n : Nat) (C : Fin n → ConvexSet (geometry d))
    (table : (s : List (Fin n)) → s.Nodup → s.length = min n (d+1) →
      { x : QPoint d // ∀ i ∈ s, (C i).mem x }) :
    {x : QPoint d // ∀ i, (C i).mem x} := by
  apply helly d C _ n (fun i => i)
  intro m hm f
  let z := splitLabels (List.ofFn f)
  let k := min n (d+1)
  let total := z.front ++ z.rest
  have hlen : total.length = n := by simpa [total] using z.perm.length_eq
  have h1 : z.front.length ≤ d+1 := by
    have h := z.bound
    change z.front.length ≤ (List.ofFn f).length at h
    simp at h
    omega
  have h2 : z.front.length ≤ n := by simp [total] at hlen; omega
  have hk : z.front.length ≤ k := by dsimp [k]; omega
  let s := total.take k
  have nd : s.Nodup := (List.take_sublist k total).nodup (z.perm.nodup_iff.mpr (allFin_nodup n))
  have hsize : s.length = k := by simp [s, hlen, k, Nat.min_le_left]
  let x := table s nd hsize
  refine ⟨x.val, fun j => x.property (f j) ?_⟩
  have hj : f j ∈ z.front := z.cover _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
  simp only [s, total, List.take_append_eq_append_take, List.take_of_length_le hk]
  exact List.mem_append_left _ hj

private def origin (d : Nat) : QPoint d := ⟨fun _ => 0, 1, by decide⟩

-- Complete collapse of rank, including zero-dimensional space.
example : (radon? (d := 0) (fun _ => origin 0)).isSome = true := by decide
example : (radon? (d := 2) (fun _ => origin 2)).isSome = true := by decide

-- Four corners (0,0), (1,0), (0,1), (1,1) with distinct homogeneous scalings.
private def square (j : Fin 4) : QPoint 2 where
  num i := (if i.val = 0 then j.val % 2 else j.val / 2) * (j.val + 1 : Nat)
  den := j.val+1
  pos := by omega

example : (radon? square).isSome = true := by decide

end QPoint
end ConstructiveHelly
