# Primary-source excerpts for the late overlap decision

## w_report

Source: https://github.com/VladimirReshetnikov/ProveIt/blob/09d65a93c9df8684c1a226341d6a5120623d1cdb/Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26w/report.tex

Git blob: `5285e24f0ba6a5c3385c0ff1079e965c46de8bd9`; full source SHA-256: `bb5f39821dd66d500817d5fb847ef1644d76dd0e238b16e209dddf4220c21ecf`.

Lines 480–507:

```text
For a time-index type \(\sigma\) with successor \(s:\sigma\to\sigma\),
choose \(E,V:\sigma\to\mathbb Z\to\mathbb N\) and define
\[
 T(k,x)=\langle E(k,x),V(k,x),E(k,x+1),V(s(k),x)\rangle.
\]
Now both horizontal and temporal matching are definitional:
\[
 T(k,x+1).\mathrm{west}=T(k,x).\mathrm{east},\qquad
 T(s(k),x).\mathrm{north}=T(k,x).\mathrm{south}.
\]
The time type may be finite cyclic. In particular, the reset-to-initializer
edge can be represented by the same cyclic boundary function as every
other temporal edge.

\subsection{Where the current proofs repeat this work}

\src{WangTiles942StepConstruction}{117} proves west and east signal formulas
separately, then proves horizontal matching by analyzing the move direction.
\src{WangTiles942FinishConstruction}{119} proves initializer matching by
five spatial cases. \src{WangTiles942TraceCycle}{29} repeats the live/halted
state split across four row properties and later proves the finite cycle's
temporal matching by initialization, finish and last-row cases.

The matching parts of these arguments express equality of shared edges. Giving the shared
edge a single definition changes the representation so that the equality
no longer needs to be proved independently in every client. The genuine
remaining work is that each resulting four-tuple is an allowed literal
tile and has the required machine interpretation.
```

Lines 571–583:

```text
The supplied \code{grid_eq_of_matching} theorem says that an already
matching grid admits an edge-field representation. It is a completeness
and transport fact, not evidence that the old matching proof can be deleted.
Using it to define the new grid would simply hide the original proof in
the construction.

For an actual simplification, define \(E,V\) independently, prove literal
allowedness and exact equality to the intended row data, and then use
\code{rfl} for matching. The independent initializer and step-pattern
bridges are included precisely to demonstrate this noncircular route.
Halt persistence, the actual decoded action, finite-table membership and
\(H\ge3\) separation of initializer/finish/reset still need their proofs.
The new representation does not certify any of those facts for free.
```

## w_edge_core

Source: https://github.com/VladimirReshetnikov/ProveIt/blob/09d65a93c9df8684c1a226341d6a5120623d1cdb/Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26w/lean/EdgeFieldsCore.lean

Git blob: `515234e833fdf739d9861a685c117e6c35ae46ec`; full source SHA-256: `05bef686b6d7650c1c833685dc2707b82b1a8e5180b2f8c2d1d2c213be45cad0`.

Lines 1–6:

```text

/-!
Constructing rows from shared edge fields.
The four projections have the exact west/north/east/south order of the
production Wang tile. This generic module deliberately does not import the
942-tile table, and proves no new allowedness fact for that table.
```

Lines 47–60:

```text
/-- An arbitrary time index and successor suffice, including a finite cyclic one. -/
def gridOfEdges {C σ : Type} (next : σ → σ)
    (E V : σ → Int → C) (k : σ) (x : Int) : Tile C :=
  ⟨E k x, V k x, E k (x + 1), V (next k) x⟩

theorem grid_horizontal {C σ : Type} (next : σ → σ)
    (E V : σ → Int → C) (k : σ) (x : Int) :
    (gridOfEdges next E V k (x + 1)).west =
      (gridOfEdges next E V k x).east := rfl

theorem grid_temporal {C σ : Type} (next : σ → σ)
    (E V : σ → Int → C) (k : σ) (x : Int) :
    (gridOfEdges next E V (next k) x).north =
      (gridOfEdges next E V k x).south := rfl
```

## v_readme

Source: https://github.com/VladimirReshetnikov/ProveIt/blob/09d65a93c9df8684c1a226341d6a5120623d1cdb/Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26v/README.md

Git blob: `8cabadada23fdcd0719908aa16f237d243bb0a82`; full source SHA-256: `e8fc5788c2f3c093853c6b37e981980886158cb0fefe0ff0cf21beb09bf5cae0`.

Lines 22–33:

```text

## Proposed work

- `machine/`: equality reflection for halt encoding, a write-location-only
  proof split, and the existing sharp absolute-value interval view.
- `encoding/`: the standard last-slot Option–Fin equivalence for the unchanged
  terminal-state encoding.
- `rows/`: guarded translated integer induction and an optional shared bond
  signal for west/east edge proofs.

Five proposals preserve the old theorem interfaces. The bond-signal variant
normalizes two intermediate edge statements and is a structural tradeoff,
```
