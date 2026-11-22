import Std

/-!
Semantic verification of the minimal-neighborhood sheafification. This file
uses types and functions in the ambient Lean theory. The finite arithmetic
encoding, bounded realization of glue, and its object-calculus targets are in
category.tex. Opens are upward-closed subsets of a preorder. In a finite
topology, the relation is y ∈ N_x, including topologically indistinguishable
points. SheafGluing gives the gluing and separatedness laws on principal
covers, equivalent here to the ordinary cover definition.
-/
universe u v w

namespace IPRAReport.SheafCase

structure Site (P : Type u) where
  rel : P → P → Prop
  refl : ∀ x, rel x x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

variable {P : Type u} {S : Site P}

structure Open (S : Site P) where
  has : P → Prop
  up : ∀ {x y}, has x → S.rel x y → has y

def Sub (V U : Open S) := ∀ x, V.has x → U.has x

theorem incId (U : Open S) : Sub U U := fun _ h => h

theorem incComp {U V W : Open S} (i : Sub V U) (j : Sub W V) : Sub W U :=
  fun x h => i x (j x h)

def basic (S : Site P) (x : P) : Open S := ⟨S.rel x, S.trans⟩

theorem basicInc {U : Open S} {x : P} (h : U.has x) : Sub (basic S x) U :=
  fun _ hxy => U.up h hxy

structure Presheaf (S : Site P) where
  sections : Open S → Type v
  res : {U V : Open S} → Sub V U → sections U → sections V
  idres : ∀ {U} (a : sections U), res (incId U) a = a
  compres : ∀ {U V W} (i : Sub V U) (j : Sub W V) (a : sections U),
    res j (res i a) = res (incComp i j) a

structure Tuple (F : Presheaf S) (U : Open S) where
  val : ∀ x, U.has x → F.sections (basic S x)
  compat : ∀ x hx y (hxy : S.rel x y),
    F.res (basicInc (U := basic S x) hxy) (val x hx) = val y (U.up hx hxy)

theorem tuple_ext {F : Presheaf S} {U : Open S} {a b : Tuple F U}
    (h : ∀ x hx, a.val x hx = b.val x hx) : a = b := by
  cases a with
  | mk av ac =>
    cases b with
    | mk bv bc =>
      have hv : av = bv := funext (fun x => funext (h x))
      cases hv
      rfl

def tupleRes {F : Presheaf S} {U V : Open S} (i : Sub V U)
    (a : Tuple F U) : Tuple F V where
  val x hx := a.val x (i x hx)
  compat x hx y hxy := a.compat x (i x hx) y hxy

def sheafify (F : Presheaf S) : Presheaf S where
  sections := Tuple F
  res := tupleRes
  idres _ := tuple_ext (fun _ _ => rfl)
  compres _ _ _ := tuple_ext (fun _ _ => rfl)

structure Hom (F : Presheaf.{u,v} S) (G : Presheaf.{u,w} S) where
  app : (U : Open S) → F.sections U → G.sections U
  nat : ∀ {U V} (i : Sub V U) (a : F.sections U),
    G.res i (app U a) = app V (F.res i a)

theorem hom_ext {F : Presheaf.{u,v} S} {G : Presheaf.{u,w} S}
    {f g : Hom F G} (h : ∀ U a, f.app U a = g.app U a) : f = g := by
  cases f with
  | mk fa fnat =>
    cases g with
    | mk ga gnat =>
      have he : fa = ga := funext (fun U => funext (h U))
      cases he
      rfl

def unit (F : Presheaf S) : Hom F (sheafify F) where
  app _ a := {
    val := fun _ hx => F.res (basicInc hx) a
    compat := fun _ hx _ hxy => F.compres (basicInc hx) (basicInc hxy) a }
  nat i a := tuple_ext (fun _ hx => (F.compres i (basicInc hx) a).symm)

def mapTuple {F : Presheaf.{u,v} S} {G : Presheaf.{u,w} S} (h : Hom F G)
    {U : Open S} (a : Tuple F U) : Tuple G U where
  val x hx := h.app (basic S x) (a.val x hx)
  compat x hx y hxy := (h.nat (basicInc (U := basic S x) hxy) (a.val x hx)).trans
    (congrArg (h.app (basic S y)) (a.compat x hx y hxy))

/-- Sheaf gluing on the cover of each open by its minimal neighborhoods. -/
structure SheafGluing (G : Presheaf S) where
  glue : (U : Open S) → Tuple G U → G.sections U
  restrictGlue : ∀ U a x (hx : U.has x),
    G.res (basicInc hx) (glue U a) = a.val x hx
  separated : ∀ U (a b : G.sections U),
    (∀ x (hx : U.has x), G.res (basicInc hx) a = G.res (basicInc hx) b) → a = b

def flatten {F : Presheaf S} {U : Open S} (a : Tuple (sheafify F) U) :
    Tuple F U where
  val x hx := (a.val x hx).val x (S.refl x)
  compat x hx y hxy := by
    have h₁ := (a.val x hx).compat x (S.refl x) y hxy
    have h₂ := congrArg (fun (b : Tuple F (basic S y)) => b.val y (S.refl y))
      (a.compat x hx y hxy)
    exact h₁.trans h₂

def sheafifyGlue (F : Presheaf S) : SheafGluing (sheafify F) where
  glue _ a := flatten a
  restrictGlue U a x hx := by
    apply tuple_ext
    intro y hy
    exact (congrArg (fun (b : Tuple F (basic S y)) => b.val y (S.refl y))
      (a.compat x hx y hy)).symm
  separated U a b h := tuple_ext (fun x hx =>
    congrArg (fun (c : Tuple F (basic S x)) => c.val x (S.refl x)) (h x hx))

def alongUnit {F : Presheaf.{u,v} S} {G : Presheaf.{u,w} S}
    (k : Hom (sheafify F) G) : Hom F G where
  app U a := k.app U ((unit F).app U a)
  nat i a := (k.nat i _).trans (congrArg (k.app _) ((unit F).nat i a))

def extendHom {F : Presheaf.{u,v} S} {G : Presheaf.{u,w} S}
    (g : SheafGluing G) (h : Hom F G) : Hom (sheafify F) G where
  app U a := g.glue U (mapTuple h a)
  nat i a := by
    apply g.separated
    intro x hx
    have e := G.compres i (basicInc hx) (g.glue _ (mapTuple h a))
    exact (e.trans (g.restrictGlue _ (mapTuple h a) x (i x hx))).trans
      (g.restrictGlue _ (mapTuple h (tupleRes i a)) x hx).symm

theorem along_extend {F : Presheaf.{u,v} S} {G : Presheaf.{u,w} S}
    (g : SheafGluing G) (h : Hom F G) : alongUnit (extendHom g h) = h := by
  apply hom_ext
  intro U a
  apply g.separated
  intro x hx
  exact (g.restrictGlue U (mapTuple h ((unit F).app U a)) x hx).trans
    (h.nat (basicInc hx) a).symm

theorem extend_along {F : Presheaf.{u,v} S} {G : Presheaf.{u,w} S}
    (g : SheafGluing G) (k : Hom (sheafify F) G) :
    extendHom g (alongUnit k) = k := by
  apply hom_ext
  intro U a
  apply g.separated
  intro x hx
  have eb : (unit F).app (basic S x) (a.val x hx) = tupleRes (basicInc hx) a := by
    apply tuple_ext
    intro y hxy
    exact a.compat x hx y hxy
  exact ((g.restrictGlue U (mapTuple (alongUnit k) a) x hx).trans
    (congrArg (k.app (basic S x)) eb)).trans (k.nat (basicInc hx) a).symm

end IPRAReport.SheafCase

#print axioms IPRAReport.SheafCase.along_extend
#print axioms IPRAReport.SheafCase.extend_along
