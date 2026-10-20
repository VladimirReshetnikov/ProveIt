# A 219-state binary Turing machine for Con(ZFC)

This construction replaces the 220-state machine's equality routine with a
smaller routine that shares an open subtree between cancellation and cleanup.
Two compiler repairs turn that source saving into **219 working states and
438 transition rows**, including initialization. Its ordinary mathematical
proof gives blank-tape nonhalting equivalent to Con(ZFC), formalizable in ZFC.
**The exact 219-state Lean theorem and internal PA equivalence remain open.**

The complete public table is [k219.tm](k219.tm). It uses two symbols, blank 0,
a two-way infinite single tape, L/R moves, initial state 0 and head at cell 0.
Working states are 0–218; halt label 219 has no outgoing transitions and is
not counted. Each noncomment row is `state read write direction next`.
Canonical SHA-256:
`02079501e6255951cbc1c31d2c3cab076574d3d61c892f0e5a541cd1789442ec`.
The [native table](k219.native.tm) retains predecessor labels and halt 254;
[canonicalization.json](canonicalization.json) records their bijection.

## The new idea

The old equality routine computes an absolute difference before clearing it.
The new routine cancels the counters and reuses an open control subtree in
its cleanup loop. A continue instruction serves a different surrounding loop
in each occurrence. Both routines terminate for **all natural inputs**, clear
registers 5 and 6, preserve every other register, and return normally exactly
on equality; otherwise they return one break. Replacing all four occurrences
therefore preserves the complete proof-search program.

This reduces distinct source subtrees from 208 to 206, with the same 4,744
primitive occurrences. The compiler then shares native state 108 between 86
break leaves ending in `001` and eight continue leaves ending in `101`.
A new return routine supports right-child zero decrements; a three-step
bypass preserves the increment routine's original spare-one convention.
Three states disappear and two are added: **220 − 3 + 2 = 219**.

## Fresh verification

Seven selected jobs passed during intake on 20 October 2026:

| Check | Result |
| --- | --- |
| Source replacement and literal construction | Four exact macro replacements; delivered source/native/canonical bytes reproduced |
| Complete symbolic runtime | 6,167 cases; 1,515,040 rules; all 438 rows; positive durations |
| Sparse and dense blank startup | 312,617 steps; exact whole tape and head |
| Independent runtime audit | Ordered case coverage, literal block schemas and positive durations |
| Independent decoder/startup audit | All 94 state-108 contexts and complete startup |
| Separate theory matrix check | Finite part of the restricted-calculus countermodel passes |

The source contract was independently reviewed as an all-natural mathematical
argument; the source builder checks its literal substitution, not that theorem.
The runtime uses symbolic induction over arbitrary natural register values,
gaps and nonempty finite spare lists. Initialization enters canonical dispatcher 23
(native 84), head −5, with logical registers `[3,0,0,0,3,0,0,0,0]`, gap 80,
130 value-one spares and exactly 277 one-cells. Every other cell is zero.
Graph reachability and symbolic row coverage are distinct from blank-run usage.

The unchanged calculus retains the predecessor's consistency calibration.
No proof assistant, recursive ancestor suite or exhaustive discovery search
was run for this intake. No unconditional nonhalting or minimality is claimed.

## Combining the earlier continuation ideas

The earlier row103 rewrite conflicts with the required new `103/1 → 302`
return and cannot simply be applied. The row157 rewrite **does** carry over:
`157/1: 1 L 148 → 1 L 187`. The intake's
[alternative table](variant-row157/k219-row157.tm) still has 219 states.
An unchanged independent window checker proves its halting equivalence from
state 0 on every initial tape, over 92,895 contexts; sparse and dense startup
checks recover the identical 312,617-step complete frame. See the
[result](variant-row157/result.json) and [reconstruction script](code/stack_row157.py).
This is a second 219-state layout, not a 218-state construction.

## Further minimization work

Follow-up work on 20 October keeps this 219-state machine as the accepted
construction. The following research results distinguish logical
equivalence, source size, raw allocation and complete machine verification:

- [Independent-pivot fusion](../k219-pivot-fusion/README.md) preserves the
  calculus by finite proof transformations and saves 123 primitive
  occurrences, but increases distinct source subtrees from 206 to 241.
- [Code-dependent fourth parameters](../k219-fourth-parameter/README.md)
  give a new three-input proposal, `U=R(A,B)`. Eight Lean lemmas check the
  algebraic obstruction to simpler replacements and conditional routes to
  recovering the old axiom. Full equiconsistency remains open. Three
  measured membership layouts have 205 distinct subtrees, but the checked
  allocations so far are larger and lack runtime certificates.
- [Source transformations](../k219-source-search/README.md) include exact
  control-flow comparisons, bounded sharing searches, and all-natural
  proofs of five alternate equality routines. The left-decrement hit2
  trades the right-decrement issue for a new increment entry; its measured
  raw allocation has not improved the state count.
- [Extended equality discovery](../k219-equality-extension/README.md)
  reconstructs 263 additional finite-search hits. Of these, 242 pass the
  larger finite diagnostic; none improves the 206-node source, and the
  smallest measured raw allocation uses 220 states. Their all-natural
  contracts remain unproved.
- [Decoder and helper sharing](../k219-continuation-search/README.md)
  searched 352,384 distinct candidate specifications without finding an
  accepted reduction. Follow-up families include 190,092 attempts to
  eliminate a single-entry state by longer transition blocks, also without
  a survivor. These families overlap; the finite-window failures are not
  a lower bound.

The merged [221-state Lean endpoint](../candidate-k221/README.md) is now
closed upstream. That formal result is specific to its own table; the
exact 219-state Lean and internal PA endpoints remain open.

Upstream commit `17af6847e8` adds Lean proof sources for the 219 equality
routine and structured program, including `L2Q.dag219_seed_iff`, the patched
engine's register contracts, 24 kernel bootstrap blocks totaling 312,617
steps, and the literal table's 438-action relabelling. The literal-source
equivalence and complete decoder-site coverage have generators, but their
219 theorem files and the final blank-tape composition are not yet committed.
The [source review](lean-source-review/review.md) checks this scope and the
literal table data without claiming a fresh local Lean build.

## Provenance and reproduction

Source 140, `K219_Construction_2026-10-20.zip`, arrived in `26d5de6d21` and was
imported in `24c7e68de7`. It pins the exact K220 package inspected at
`5c5d7611a9`. The [intake reconciliation](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-186.md)
contains the exact transition changes, source proof, theory findings and
limitations. The [recovery/replay guide](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-186-reproduction.md)
restores the full package and runs the selected checks on copies.

The equality macro, compiler repair and research are the submitted package's
contributions. The continuation composition is an intake finding using the
earlier alternatives' checker. See the delivered [attribution](ATTRIBUTION.md),
[parent notice](NOTICE-parent220.md), [licenses](licenses/), and
[provenance](provenance.json). Inherited credits include Elliot Glazer, Mira,
Jeff's busy-beaver development, Andrew James Wade, BusyCoq, the Coq Library
of Undecidability and ProveIt's accumulated reductions.
