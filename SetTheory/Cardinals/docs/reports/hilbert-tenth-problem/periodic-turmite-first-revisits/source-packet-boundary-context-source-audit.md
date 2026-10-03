# Targeted read-only overlap check

Checked 2026-10-03. No upstream code was executed, no repository was cloned, and no external write was made.

## Primary literature

- Maldonado–Gajardo–Hellouin de Menibus–Moreira, *Nontrivial Turmites are Turing-universal*, arXiv:1702.05547v1 (2017): https://arxiv.org/html/1702.05547. Section 1 gives the rotate/increment/move convention and periodic-background/finite-input contract; Theorems 2.1/3.1 provide simulation; Section 5 states the at-most-two-visits property. This supports context, not a proved literal head-port loader or priority claim for the lower theorem.
- D. C. Cooper, *Theorem Proving in Arithmetic without Multiplication*, Machine Intelligence 7 (1972), 91–99: https://www21.in.tum.de/teaching/logik/SS16/Exercises/Cooper.pdf. Explicit Presburger decision procedure; used as the algorithmic reference.
- Marcus Kracht, *A New Proof of a Theorem by Ginsburg and Spanier*, dated 2002-12-18: https://wwwhomes.uni-bielefeld.de/~mkracht/html/presburger.pdf. Theorem 2.9 presents quantifier elimination with fixed-modulus congruences. Independent visual review found reversed bounds in the final bounded-interval display on p.8 and a related prose typo. These do not challenge standard Presburger decidability, but this source is not used as an executable algorithm specification; Cooper is preferred.

## Repository

Repository: VladimirReshetnikov/ProveIt. Purpose-built GitHub read APIs were used after web-rendered GitHub file pages failed.

- Read `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_ANT_CHECKERBOARD_HISTORY.md`, lines 305–401. Content blob SHA: `2e762cc5f31ec21902d676956670470f49dec9f7`. Sections 9–10 distinguish the 174-operation bounded-history interface, periodic-background generation, uncharged input placement and the missing halt observable.
- Read `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_TOGGLE_ROUTER_UNIVERSALITY.md`, lines 1–95. Content blob SHA: `a70af5ccd954a1776567ff1747e040ed20a1cb13`. It distinguishes bounded prediction, periodic-background universality and physical halting.
- Scoped GitHub searches `one-visit`, `first revisit`, `self-avoiding`. First and third returned no results; the second returned unrelated token matches, not this first-revisit theorem. Search result URLs were pinned to repository commit `5883b08b7af362077f13bb4afa97a23a90ae4cf8`.

General-web queries for turmite one-visit decidability and Langton self-avoiding periodicity did not surface this exact theorem. These are limited negative searches; no exhaustive literature search, novelty claim, or priority assertion follows.
