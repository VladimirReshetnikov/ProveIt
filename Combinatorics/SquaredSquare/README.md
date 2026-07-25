# Squaring the square

Machine-checked proofs, in Lean 4 and Rocq/Coq independently, that a square
can be cut into finitely many pairwise non-congruent squares (a *perfect
squared square*), realized by A. J. W. Duijvestijn's order-21 dissection of
the side-112 square, together with the elementary half of the minimality
statement: **every perfect squared square has at least 7 pieces**, so the
minimum possible order lies in `[7, 21]`.

## Statement and definitions

A *placed square* is an axis-parallel closed square `[x, x+s] × [y, y+s]` in
the real plane. A *dissection* of `[0, S]²` is a finite list of placed
squares with positive sides, pairwise disjoint open interiors, and closed
pieces covering `[0, S]²` exactly. In Lean the open box is proved to be the
topological interior of the closed piece (`Sq.interior_toSet`), so the
explicit definition matches the topological one.

Two plane sets are *congruent* when some bijection between them preserves
squared Euclidean distances. Every plane isometry restricts to such a
bijection, so the negations proved here rule out congruence by arbitrary
isometries. The key invariant is the squared diameter: a closed square of
side `s > 0` has maximal squared point distance `2s²`, attained by opposite
corners, so congruent squares have equal sides — and conversely translation
makes equal-sided squares congruent.

A dissection with at least two pieces, pairwise non-congruent, is a
*perfect squared square* (`IsPerfectSquaredSquare`).

## Results

**Existence** (Lean `SquaredSquare/Duijvestijn.lean`,
Coq `Coq/Duijvestijn.v`): the square of side 112 is cut into 21 pairwise
non-congruent squares with sides

```
2, 4, 6, 7, 8, 9, 11, 15, 16, 17, 18, 19, 24, 25, 27, 29, 33, 35, 37, 42, 50
```

placed according to Duijvestijn's Bouwkamp code
`(50,35,27)(8,19)(15,17,11)(6,24)(29,25,9,2)(7,18)(16)(42)(4,37)(33)`.
Main theorems: `duijvestijn_perfect`, `exists_perfect_squared_square`.
The scaling modules (`Scaling.lean`, `Coq/Scaling.v`) add dilation closure,
so **every** square of positive side admits such a 21-piece perfect
dissection (`exists_perfect_squared_square_of_side`, in both provers).

All combinatorial content — in-bounds placement, pairwise separation of the
open pieces, distinct sides, and exact coverage of every unit grid cell of
`[0,112]²` — is stated over integers and checked computationally: by the
Lean kernel via `decide +kernel` (no `native_decide`), and by `vm_compute`
in Rocq. Elementary floor/`Int_part` lemmas lift the integer certificates
to the real plane.

**Minimality, elementary half** (Lean `SquaredSquare/Minimality.lean`,
Coq `Coq/Minimality.v`): no perfect squared square has 6 or fewer pieces
(`seven_le_length`, with `four_le_length` and `length_ne_four/five/six`).
The proof is the classical corner/edge argument:

- each corner of the big square is covered by a unique corner tile, no
  piece can have full side `S`, and the four corner tiles are pairwise
  distinct — so at least 4 pieces;
- the tiles touching a fixed edge partition it, so their sides sum to `S`
  (via the reusable 1-D lemma `interval_cover_sum` in
  `Intervals.lean`/`Intervals.v`);
- a non-corner piece touches at most one edge; with at most two non-corner
  pieces, either some two adjacent edges are touched by corner tiles only —
  forcing two opposite corner tiles to share a side, contradicting pairwise
  non-congruence — or the two extras sit on opposite edges, forcing their
  sides to sum to `0`.

**The minimality statement, reduced** (Lean
`SquaredSquare/MinimalOrder.lean`, Coq `Coq/MinimalOrder.v`): the
proposition "the minimal number of pieces of a perfect squared square is
21" is formalized (`IsLeast perfectOrders 21`, resp. the achieved/lower
bound conjunction `minimal_order_21_iff`) and proved **equivalent** to the
single named open proposition `DuijvestijnSearchClaim` — every perfect
squared square has at least 21 pieces.  The forward inputs are proved
(`mem_perfectOrders_21` from the existence certificate; every achievable
order is at least 7); `DuijvestijnSearchClaim` itself is the exact content
of Duijvestijn's exhaustive search and remains unproved, with no axiom
introduced for it.

**Status of the sharp bound 21.** The true minimality statement — no
perfect squared square of order `7..20`, making Duijvestijn's dissection
optimal — is A. J. W. Duijvestijn's 1978 exhaustive computer search over
3-connected planar networks (with I. Gambini's 1999 independent search as a
later check). No human-scale case proof is known: even for perfect squared
*rectangles* the sharp lower bound (order 9) already requires substantial
case analysis, and the square case adds Kirchhoff-style network theory plus
an enumeration of c-nets whose completeness proof is the hard part. A full
formalization would need, in proof-obligation terms: commensurability of
squared rectangles (Dehn's argument), a proved-complete enumeration of the
combinatorial structures of order ≤ 20 (planar-graph or placement-order
based), and a verified per-structure linear-algebra check — a development
comparable in scale to this repository's larger certificate projects.
It is intentionally **not** formalized here, and no axiom standing in for
the search result is introduced; the formal bracket proved on both sides is
`7 ≤ minimum order ≤ 21`.

## Layout

```
Combinatorics/SquaredSquare/
├── Lean/SquaredSquare.lean          -- facade
├── Lean/SquaredSquare/Basic.lean    -- dissections, congruence, diameter
├── Lean/SquaredSquare/Duijvestijn.lean -- order-21 existence certificate
├── Lean/SquaredSquare/Scaling.lean  -- dilation closure, any side
├── Lean/SquaredSquare/Intervals.lean-- 1-D interval partition sum
├── Lean/SquaredSquare/Minimality.lean -- no perfect squared square ≤ 6 pieces
├── Lean/SquaredSquare/MinimalOrder.lean -- minimality reduced to the search claim
├── Coq/Defs.v                       -- definitions and congruence lemmas
├── Coq/Duijvestijn.v                -- existence certificate (vm_compute)
├── Coq/Intervals.v                  -- 1-D interval partition sum
├── Coq/Minimality.v                 -- no perfect squared square ≤ 6 pieces
├── Coq/Scaling.v                    -- dilation closure, any side
├── Coq/MinimalOrder.v               -- minimality reduced to the search claim
├── Coq/Audit.v                      -- Print Assumptions for main theorems
└── Support/bouwkamp_decode.py       -- Bouwkamp-code decoder / data check
```

## Building

Lean (root workspace, serial as per local guidance):

```powershell
cd C:\Proofs
lake build +SquaredSquare
```

Rocq/Coq (sequential, from the repository root):

```powershell
coqc -Q Combinatorics/SquaredSquare/Coq SquaredSquare Combinatorics/SquaredSquare/Coq/Defs.v
coqc -Q Combinatorics/SquaredSquare/Coq SquaredSquare Combinatorics/SquaredSquare/Coq/Duijvestijn.v
coqc -Q Combinatorics/SquaredSquare/Coq SquaredSquare Combinatorics/SquaredSquare/Coq/Intervals.v
coqc -Q Combinatorics/SquaredSquare/Coq SquaredSquare Combinatorics/SquaredSquare/Coq/Minimality.v
coqc -Q Combinatorics/SquaredSquare/Coq SquaredSquare Combinatorics/SquaredSquare/Coq/Scaling.v
coqc -Q Combinatorics/SquaredSquare/Coq SquaredSquare Combinatorics/SquaredSquare/Coq/MinimalOrder.v
coqc -Q Combinatorics/SquaredSquare/Coq SquaredSquare Combinatorics/SquaredSquare/Coq/Audit.v
```

## Trust boundary

- Lean: every theorem's axiom footprint is `propext`, `Classical.choice`,
  `Quot.sound` (checked with `#print axioms`); the integer certificates are
  discharged by the kernel (`decide +kernel`), not `native_decide`.
- Rocq: `Print Assumptions` (see `Coq/Audit.v`) reports only the standard
  library's classical-real axioms `sig_forall_dec` and
  `functional_extensionality_dep`; the integer certificates use
  `vm_compute`.
- The Python decoder in `Support/` is proof support only; the placement
  data it produced is re-verified inside both proof assistants.
