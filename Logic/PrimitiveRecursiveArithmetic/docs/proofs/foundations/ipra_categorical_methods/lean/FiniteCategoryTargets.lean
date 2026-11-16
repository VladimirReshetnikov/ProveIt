import Std

/-!
Uncompiled semantic specification of finite table category theory.
All `...Spec` declarations below DEFINE desired propositions. They do not
assert proofs. ObjectCategory.lean separately gives uncompiled expressions
in the actual ConciseIPRA.Prf calculus. Numerical coding, PR syntax, Boolean
reflection, and object-theory proofs remain the stages in FORMALIZATION.md.

List/function notation here belongs to host Lean. It does not grant iPRA
function quantification or a universal program evaluator. The final numerical
version uses the list coding and bounded scans in the paper.
-/
namespace IPRACategories

abbrev Table := List Nat

def entry (t : Table) (i : Nat) : Nat := (t[i]?).getD 0

def IsMap (n m : Nat) (t : Table) : Prop :=
  t.length = n ∧ ∀ i, i < n → entry t i < m

structure RawCategory where
  objects : Nat
  arrows : Nat
  source : Table
  target : Table
  identity : Table
  composition : Table

def src (c : RawCategory) (f : Nat) : Nat := entry c.source f
def tgt (c : RawCategory) (f : Nat) : Nat := entry c.target f
def ident (c : RawCategory) (x : Nat) : Nat := entry c.identity x
def comp (c : RawCategory) (g f : Nat) : Nat :=
  entry c.composition (g * c.arrows + f)

def IsHom (c : RawCategory) (x y f : Nat) : Prop :=
  x < c.objects ∧ y < c.objects ∧ f < c.arrows ∧ src c f = x ∧ tgt c f = y

def IsCategory (c : RawCategory) : Prop :=
  IsMap c.arrows c.objects c.source ∧
  IsMap c.arrows c.objects c.target ∧
  IsMap c.objects c.arrows c.identity ∧
  c.composition.length = c.arrows * c.arrows ∧
  (∀ x, x < c.objects → IsHom c x x (ident c x)) ∧
  (∀ f g, f < c.arrows → g < c.arrows → tgt c f = src c g →
    IsHom c (src c f) (tgt c g) (comp c g f)) ∧
  (∀ f, f < c.arrows → comp c (ident c (tgt c f)) f = f ∧
    comp c f (ident c (src c f)) = f) ∧
  (∀ f g h, f < c.arrows → g < c.arrows → h < c.arrows →
    tgt c f = src c g → tgt c g = src c h →
    comp c h (comp c g f) = comp c (comp c h g) f)

structure RawFunctor where
  objects : Table
  arrows : Table

def IsFunctor (c d : RawCategory) (f : RawFunctor) : Prop :=
  IsMap c.objects d.objects f.objects ∧ IsMap c.arrows d.arrows f.arrows ∧
  (∀ a, a < c.arrows →
    IsHom d (entry f.objects (src c a)) (entry f.objects (tgt c a)) (entry f.arrows a)) ∧
  (∀ x, x < c.objects → entry f.arrows (ident c x) = ident d (entry f.objects x)) ∧
  (∀ a b, a < c.arrows → b < c.arrows → tgt c a = src c b →
    entry f.arrows (comp c b a) = comp d (entry f.arrows b) (entry f.arrows a))

def IsNatural (c d : RawCategory) (f g : RawFunctor) (eta : Table) : Prop :=
  eta.length = c.objects ∧
  (∀ x, x < c.objects → IsHom d (entry f.objects x) (entry g.objects x) (entry eta x)) ∧
  (∀ a, a < c.arrows →
    comp d (entry eta (tgt c a)) (entry f.arrows a) =
    comp d (entry g.arrows a) (entry eta (src c a)))

structure RawDiagram where
  category : RawCategory
  sizes : Table
  maps : List Table

def size (d : RawDiagram) (x : Nat) : Nat := entry d.sizes x
def act (d : RawDiagram) (f x : Nat) : Nat := entry ((d.maps[f]?).getD []) x

def IsDiagram (d : RawDiagram) : Prop :=
  IsCategory d.category ∧ d.sizes.length = d.category.objects ∧
  d.maps.length = d.category.arrows ∧
  (∀ f, f < d.category.arrows →
    IsMap (size d (src d.category f)) (size d (tgt d.category f))
      ((d.maps[f]?).getD [])) ∧
  (∀ j x, j < d.category.objects → x < size d j → act d (ident d.category j) x = x) ∧
  (∀ f g x, f < d.category.arrows → g < d.category.arrows →
    tgt d.category f = src d.category g → x < size d (src d.category f) →
    act d (comp d.category g f) x = act d g (act d f x))

def IsCone (d : RawDiagram) (n : Nat) (p : List Table) : Prop :=
  p.length = d.category.objects ∧
  (∀ j, j < d.category.objects → IsMap n (size d j) ((p[j]?).getD [])) ∧
  (∀ f x, f < d.category.arrows → x < n →
    act d f (entry ((p[src d.category f]?).getD []) x) =
    entry ((p[tgt d.category f]?).getD []) x)

def FactorsCone (d : RawDiagram) (n ell : Nat) (p q : List Table) (u : Table) : Prop :=
  IsMap n ell u ∧ ∀ j x, j < d.category.objects → x < n →
    entry ((p[j]?).getD []) (entry u x) = entry ((q[j]?).getD []) x

def LimitSpec (d : RawDiagram) (ell : Nat) (p : List Table) : Prop :=
  IsCone d ell p ∧ ∀ n q, IsCone d n q →
    ∃ u, FactorsCone d n ell p q u ∧
      ∀ v, FactorsCone d n ell p q v → v = u

def IsCocone (d : RawDiagram) (n : Nat) (p : List Table) : Prop :=
  p.length = d.category.objects ∧
  (∀ j, j < d.category.objects → IsMap (size d j) n ((p[j]?).getD [])) ∧
  (∀ f x, f < d.category.arrows → x < size d (src d.category f) →
    entry ((p[tgt d.category f]?).getD []) (act d f x) =
    entry ((p[src d.category f]?).getD []) x)

def FactorsCocone (d : RawDiagram) (ell n : Nat) (p q : List Table) (u : Table) : Prop :=
  IsMap ell n u ∧ ∀ j x, j < d.category.objects → x < size d j →
    entry u (entry ((p[j]?).getD []) x) = entry ((q[j]?).getD []) x

def ColimitSpec (d : RawDiagram) (ell : Nat) (p : List Table) : Prop :=
  IsCocone d ell p ∧ ∀ n q, IsCocone d n q →
    ∃ u, FactorsCocone d ell n p q u ∧
      ∀ v, FactorsCocone d ell n p q v → v = u

def IsPresheaf (d : RawDiagram) : Prop :=
  IsCategory d.category ∧ d.sizes.length = d.category.objects ∧
  d.maps.length = d.category.arrows ∧
  (∀ f, f < d.category.arrows →
    IsMap (size d (tgt d.category f)) (size d (src d.category f))
      ((d.maps[f]?).getD [])) ∧
  (∀ j x, j < d.category.objects → x < size d j → act d (ident d.category j) x = x) ∧
  (∀ f g x, f < d.category.arrows → g < d.category.arrows →
    tgt d.category f = src d.category g → x < size d (tgt d.category g) →
    act d (comp d.category g f) x = act d f (act d g x))

/-- A representable transformation uses actual arrow codes as inputs.
    Its total table has c.objects * c.arrows entries; invalid entries ignored. -/
def alpha (c : RawCategory) (eta : Table) (x f : Nat) : Nat :=
  entry eta (x * c.arrows + f)

def IsRepresentableTransformation (d : RawDiagram) (a : Nat) (eta : Table) : Prop :=
  a < d.category.objects ∧ eta.length = d.category.objects * d.category.arrows ∧
  (∀ x f, IsHom d.category x a f → alpha d.category eta x f < size d x) ∧
  (∀ x y f k, IsHom d.category x a f → IsHom d.category y x k →
    alpha d.category eta y (comp d.category f k) =
      act d k (alpha d.category eta x f))

def YonedaDeterminationSpec : Prop :=
  ∀ d a eta, IsPresheaf d → IsRepresentableTransformation d a eta →
    ∀ x f, IsHom d.category x a f →
      alpha d.category eta x f =
        act d f (alpha d.category eta a (ident d.category a))

def FiniteLimitProducerSpec (produce : RawDiagram → Nat × List Table) : Prop :=
  ∀ d, IsDiagram d → LimitSpec d (produce d).1 (produce d).2

def FiniteColimitProducerSpec (produce : RawDiagram → Nat × List Table) : Prop :=
  ∀ d, IsDiagram d → ColimitSpec d (produce d).1 (produce d).2

/- Completion route:
1. Implement Boolean counterparts of the bounded guarded predicates.
2. Prove their correspondence to the above predicates using prefix invariants.
3. Implement filtered mixed-radix tuples and Warshall/least representatives.
4. Prove the producer specifications by the paper's explicit mediators.
5. Prove YonedaDeterminationSpec from naturality at identity; then implement
   the inverse finite table and prove both inverse equations.
6. Reify each fixed algorithm as PR syntax and construct the corresponding
   object-calculus derivations. Those are NOT consequences of merely defining
   these host propositions or proving them in ambient Lean.
-/
end IPRACategories
