# Source audit

Access date: 30 September 2026.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `e8bb0931d67f80d9fce87a8cddb0f661ff19f956`.

The GitHub connector was used to inspect the live tree and fetch relevant files at the
pinned revision. The search index also returned an older revision, which was not used
as the version authority for the cited source files.

### Files inspected

1. `Computability/HilbertTenthProblem/README.md`
   - MRDP and exact-iteration context, Jones/coauthor paper catalogue, reported universal
     certificate bound, distinction between formalized and nonformalized satellite work.
2. `Computability/HilbertTenthProblem/Lean/STATUS.md`
   - The relevant current status portion: shared Diophantine interfaces, no-new-axiom
     policy, remaining formalization obligations. This is not an independent build audit.
3. `Computability/HilbertTenthProblem/Lean/Diophantine/Common/DiophantineTrace.lean`
   - Actual source definitions for `boundedForall_dioph`, `exactIter_dioph`, and
     `existsExactIter_dioph`; these export Diophantineness, not witness uniqueness.
4. `Computability/CombinatoryLogic/README.md`
   - Local SK/SKI/Iota simulations, source/runtime distinction, limits of forward
     simulation, and the difference between the scoped contextual and weak-CBV models.

This was a relevant-source audit, not an exhaustive novelty review of every repository
file. No repository file was changed and no existing formalization was rebuilt.

## Literature used

- Jones and Matiyasevich (1984), register-machine exponential Diophantine representation;
  bibliographic identification from the repository's corrected-edition catalogue.
- Larchey-Wendling and Forster, *Hilbert's Tenth Problem in Coq (Extended Version)*,
  LMCS 18(1:35), 2022; primary author version https://arxiv.org/abs/2003.04604.
- Matiyasevich, *Towards finite-fold Diophantine representations*, Journal of Mathematical
  Sciences 171, 745-752, 2010; https://doi.org/10.1007/s10958-010-0179-4.
- Cantone, Casagrande, Fabris, Omodeo, *Does Every Recursively Enumerable Set Admit a
  Finite-Fold Diophantine Representation?*, 2019;
  https://ceur-ws.org/Vol-2396/paper11.pdf.
- Cartier and Foata, *Problemes combinatoires de commutation et rearrangements*,
  Lecture Notes in Mathematics 85, 1969; historical primary work cited through the
  normal-form/heap literature.
- Krattenthaler, *The theory of heaps and the Cartier-Foata monoid*, author-hosted text,
  https://www.mat.univie.ac.at/~kratt/artikel/heaps.pdf.

The new report reproduces no third-party article or repository source file. Its normal-form
proof and other mathematical arguments are written independently. Literature attribution
does not establish priority for the particular combined constructions presented here.
