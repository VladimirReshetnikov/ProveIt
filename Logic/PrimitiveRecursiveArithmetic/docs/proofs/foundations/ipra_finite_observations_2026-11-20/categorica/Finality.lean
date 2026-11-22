import Merge

/- The semantic cocone proof. All equalities are pointwise. To internalize for
finite tables, materialize the center/paths by the bounded graph algorithm. -/
namespace EffectiveFinality

structure Cat where
  Ob : Type
  Hom : Ob → Ob → Type
  id (d) : Hom d d
  comp {a b c} : Hom b c → Hom a b → Hom a c
  right_id {a b} (g : Hom a b) : comp g (id a) = g
  left_id {a b} (g : Hom a b) : comp (id b) g = g
  assoc {a b c d} (h : Hom c d) (g : Hom b c) (f : Hom a b) :
    comp (comp h g) f = comp h (comp g f)

structure Func (J K : Cat) where
  obj : J.Ob → K.Ob
  arr {a b} : J.Hom a b → K.Hom (obj a) (obj b)
  map_id (a) : arr (J.id a) = K.id (obj a)
  map_comp {a b c} (v : J.Hom b c) (u : J.Hom a b) :
    arr (J.comp v u) = K.comp (arr v) (arr u)

structure Diagram (K : Cat) where
  obj : K.Ob → Type
  act {a b} : K.Hom a b → obj a → obj b
  act_id {d} (x : obj d) : act (K.id d) x = x
  act_comp {a b c} (g : K.Hom b c) (f : K.Hom a b) (x : obj a) :
    act (K.comp g f) x = act g (act f x)

variable {J K : Cat} (F : Func J K)

structure Vertex (d : K.Ob) where
  j : J.Ob
  h : K.Hom d (F.obj j)

def CommaEdge {d} (v w : Vertex F d) :=
  ∃ e : J.Hom v.j w.j, w.h = K.comp (F.arr e) v.h

structure Connected where
  base (d : K.Ob) : Vertex F d
  path {d} (v : Vertex F d) : Walk (CommaEdge F) (base d) v

variable (D : Diagram K) (Z : Type)

structure ConeOnRestriction where
  val (j : J.Ob) : D.obj (F.obj j) → Z
  eqn {a b} (u : J.Hom a b) (x : D.obj (F.obj a)) :
    val b (D.act (F.arr u) x) = val a x

structure Cone where
  val (d : K.Ob) : D.obj d → Z
  eqn {a b} (u : K.Hom a b) (x : D.obj a) :
    val b (D.act u x) = val a x

variable {F D Z}

def restrict (F : Func J K) (c : Cone D Z) : ConeOnRestriction F D Z where
  val j := c.val (F.obj j)
  eqn u x := c.eqn (F.arr u) x

def via (c : ConeOnRestriction F D Z) {d} (x : D.obj d) (v : Vertex F d) :=
  c.val v.j (D.act v.h x)

theorem via_edge (c : ConeOnRestriction F D Z) {d} (x : D.obj d)
    (v w : Vertex F d) (e : CommaEdge F v w) : via c x v = via c x w := by
  obtain ⟨u, hu⟩ := e
  unfold via
  rw [hu, D.act_comp]
  exact (c.eqn u _).symm

theorem via_base (t : Connected F) (c : ConeOnRestriction F D Z)
    {d} (x : D.obj d) (v : Vertex F d) : via c x (t.base d) = via c x v :=
  (t.path v).equalValues (via c x) (via_edge c x)

def extend (t : Connected F) (c : ConeOnRestriction F D Z) : Cone D Z where
  val d x := via c x (t.base d)
  eqn := by
    intro d e u x
    let w := t.base e
    let v : Vertex F d := ⟨w.j, K.comp w.h u⟩
    have h := via_base t c x v
    change via c (D.act u x) w = via c x (t.base d)
    rw [h]
    exact (congrArg (c.val w.j) (D.act_comp w.h u x)).symm

theorem restrict_extend (t : Connected F) (c : ConeOnRestriction F D Z)
    (j : J.Ob) (x : D.obj (F.obj j)) :
    (restrict F (extend t c)).val j x = c.val j x := by
  let v : Vertex F (F.obj j) := ⟨j, K.id (F.obj j)⟩
  change via c x (t.base (F.obj j)) = c.val j x
  rw [via_base t c x v]
  exact congrArg (c.val j) (D.act_id x)

theorem extend_restrict (t : Connected F) (c : Cone D Z) (d : K.Ob) (x : D.obj d) :
    (extend t (restrict F c)).val d x = c.val d x := c.eqn (t.base d).h x

end EffectiveFinality

namespace EffectiveFinality

/- The tagged elements of the restriction of K(d,-) are literally pairs
(j,h), i.e. Vertex F d. In the full colimit the analogous functor is idK. -/
def idK (K : Cat) : Func K K where
  obj a := a
  arr f := f
  map_id _ := rfl
  map_comp _ _ := rfl

def representable (K : Cat) (d : K.Ob) : Diagram K where
  obj e := K.Hom d e
  act k h := K.comp k h
  act_id h := K.left_id h
  act_comp g f h := K.assoc g f h

variable {J K : Cat} (F : Func J K) (d : K.Ob)

def repVertexMap (v : Vertex F d) : Vertex (idK K) d := ⟨F.obj v.j, v.h⟩

theorem repEdgeMap {v w : Vertex F d} (e : CommaEdge F v w) :
    CommaEdge (idK K) (repVertexMap F d v) (repVertexMap F d w) := by
  obtain ⟨u, h⟩ := e
  exact ⟨F.arr u, h⟩

theorem fullComponent (v w : Vertex (idK K) d) : Walk (CommaEdge (idK K)) v w := by
  let b : Vertex (idK K) d := ⟨d, K.id d⟩
  have toVertex (z : Vertex (idK K) d) : Walk (CommaEdge (idK K)) b z :=
    .edge ⟨z.h, (K.right_id z.h).symm⟩
  exact (toVertex v).reverse.join (toVertex w)

/-- Surjectivity and injectivity of the map on components, written on
representatives. This avoids choice and a host quotient construction. -/
def repSurj :=
  ∀ w : Vertex (idK K) d, ∃ v : Vertex F d,
    Walk (CommaEdge (idK K)) (repVertexMap F d v) w

def repInj :=
  ∀ v w : Vertex F d,
    Walk (CommaEdge (idK K)) (repVertexMap F d v) (repVertexMap F d w) →
      Walk (CommaEdge F) v w

/-- Bijectivity on the single representable K(d,-) detects its entire comma
graph. Failure can be tested independently at each object d. -/
theorem representable_test : repSurj F d ∧ repInj F d ↔
    ∃ v : Vertex F d, ∀ w : Vertex F d, Walk (CommaEdge F) v w := by
  constructor
  · rintro ⟨s, i⟩
    obtain ⟨v, _⟩ := s ⟨d, K.id d⟩
    exact ⟨v, fun w => i v w (fullComponent d _ _)⟩
  · rintro ⟨v, hv⟩
    exact ⟨fun w => ⟨v, fullComponent d _ w⟩, fun x y _ => (hv x).reverse.join (hv y)⟩

end EffectiveFinality
