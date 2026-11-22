import Init

/-! Semantic transport on one connected component. Finite graph codes instantiate
the types by finite ordinals. Signed generators are separate directed labels.
The data include a selected root path for each vertex (the forest algorithm).
This file does not use a quotient of words or assume proof-irrelevance of paths. -/

namespace IPRAForest

structure Bij (A B : Type) where
  fwd : A → B
  rev : B → A
  leftInv : ∀ x, rev (fwd x) = x
  rightInv : ∀ y, fwd (rev y) = y

def Bij.id (A : Type) : Bij A A :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩

def Bij.thenDo {A B C : Type} (p : Bij A B) (q : Bij B C) : Bij A C where
  fwd x := q.fwd (p.fwd x)
  rev y := p.rev (q.rev y)
  leftInv x := by rw [q.leftInv, p.leftInv]
  rightInv y := by rw [p.rightInv, q.rightInv]

structure Graph where
  Vertex : Type
  Edge : Type
  src : Edge → Vertex
  dst : Edge → Vertex

inductive Path (G : Graph) (r : G.Vertex) : G.Vertex → Type where
  | nil : Path G r r
  | snoc (e : G.Edge) (p : Path G r (G.src e)) : Path G r (G.dst e)

structure Sys (G : Graph) where
  fibre : G.Vertex → Type
  edge : (e : G.Edge) → Bij (fibre (G.src e)) (fibre (G.dst e))

variable {G : Graph}

def transport (A : Sys G) {r v : G.Vertex} (p : Path G r v) :
    Bij (A.fibre r) (A.fibre v) :=
  match p with
  | .nil => Bij.id _
  | .snoc e q => (transport A q).thenDo (A.edge e)

structure Mor (A B : Sys G) where
  app : (v : G.Vertex) → A.fibre v → B.fibre v
  edgeLaw : ∀ e x, app (G.dst e) ((A.edge e).fwd x) =
    (B.edge e).fwd (app (G.src e) x)

theorem pathLaw {A B : Sys G} (h : Mor A B) {r v} (p : Path G r v)
    (x : A.fibre r) :
    h.app v ((transport A p).fwd x) = (transport B p).fwd (h.app r x) := by
  induction p with
  | nil => rfl
  | snoc e q ih => exact (h.edgeLaw e _).trans (congrArg (B.edge e).fwd ih)

structure Chart (G : Graph) (r : G.Vertex) where
  path : (v : G.Vertex) → Path G r v
  root : path r = .nil

variable {r : G.Vertex}

def chart (A : Sys G) (c : Chart G r) (v : G.Vertex) := transport A (c.path v)

def loopMap (A : Sys G) (c : Chart G r) (e : G.Edge)
    (x : A.fibre r) : A.fibre r :=
  (chart A c (G.dst e)).rev ((A.edge e).fwd ((chart A c (G.src e)).fwd x))

def RootLaw (A B : Sys G) (c : Chart G r) (k : A.fibre r → B.fibre r) : Prop :=
  ∀ e x, k (loopMap A c e x) = loopMap B c e (k x)

theorem chartLaw {A B : Sys G} (h : Mor A B) (c : Chart G r) (v) (x) :
    h.app v ((chart A c v).fwd x) = (chart B c v).fwd (h.app r x) :=
  pathLaw h (c.path v) x

theorem reverseChartLaw {A B : Sys G} (h : Mor A B) (c : Chart G r)
    (v) (x : A.fibre v) :
    h.app r ((chart A c v).rev x) = (chart B c v).rev (h.app v x) := by
  have eq := congrArg (chart B c v).rev
    (chartLaw h c v ((chart A c v).rev x))
  rw [(chart A c v).rightInv, (chart B c v).leftInv] at eq
  exact eq.symm

theorem restrictLaw {A B : Sys G} (h : Mor A B) (c : Chart G r) :
    RootLaw A B c (h.app r) := by
  intro e x
  unfold loopMap
  rw [reverseChartLaw, h.edgeLaw, chartLaw]

def extend {A B : Sys G} (c : Chart G r) (k : A.fibre r → B.fibre r)
    (hk : RootLaw A B c k) : Mor A B where
  app v x := (chart B c v).fwd (k ((chart A c v).rev x))
  edgeLaw e x := by
    have eq := congrArg (chart B c (G.dst e)).fwd
      (hk e ((chart A c (G.src e)).rev x))
    unfold loopMap at eq
    rw [(chart A c (G.src e)).rightInv, (chart B c (G.dst e)).rightInv] at eq
    exact eq

theorem extend_restrict {A B : Sys G} (h : Mor A B) (c : Chart G r) (v x) :
    (extend c (h.app r) (restrictLaw h c)).app v x = h.app v x := by
  change (chart B c v).fwd (h.app r ((chart A c v).rev x)) = _
  rw [reverseChartLaw, (chart B c v).rightInv]

theorem restrict_extend {A B : Sys G} (c : Chart G r) (k : A.fibre r → B.fibre r)
    (hk : RootLaw A B c k) (x) : (extend c k hk).app r x = k x := by
  change (transport B (c.path r)).fwd (k ((transport A (c.path r)).rev x)) = _
  rw [c.root]
  rfl

end IPRAForest
