# Transferable ideas from ZFC and ConciseIPRA

**Scope.** This is a targeted reading of the two directory indexes and the concrete documents cited below at ProveIt commit `2a88cb6a3f823e0de5addf19d725bf8373860c71`. It is not an exhaustive audit of the much larger ZFC development. The question is whether an idea reduces the **complete blank-input, binary, left/right PA machine**, with its initializer and proof calibration included. A shorter checker, formula, or source tree is a different measurement.

## 1. Zero-valued spares require a new blank-start argument

The ZFC `zero-spare` alternative changes one write bit and the initial state of the 215-state parent. It appends `B(0)=01` instead of `B(1)=011`; the published result remains **215 states**. The new blank run reaches a stack consisting of two truth heads above an unsafe tail. Its debt-two theorem shows that the particular candidate scheduler never exposes that tail. The related `zero-spare-transfer` construction has a different startup, eight safe heads, and scheduler debt three. These are substantial, reusable proof ideas: an initializer need not produce an entirely clean stack if a quantitative invariant permanently protects its unsafe suffix. They are not a license to treat an unsafe formula as a theorem. [Z1, Z2]

For PA, the incoming DHS report already attempted the direct append-zero transplantation and classified every possible initial control: four halt, and 190 run along blank rays. Our corpus audit identified that prior obstruction; we did not independently discover it or redesign the spare allocator. A future PA implementation would have to find a new complete startup and prove a debt bound for its exact command order. Physical spare blocks and logical stack heads are different resources. Their counts cannot be substituted for one another. [P1]

## 2. Remove an MP stack effect, then repair the proof compiler

Section “Removing the successful MP zero push” of `zero-spare-transfer/report.tex` already gives the important no-push transformation. Its repaired major-first MP compiler reserves a zero explicitly before compiling the premises. The argument handles `p(0,0)=0` by projection identities over an explicit wrapper list, without assuming an injective stack-length encoding. The PA194N/HS/NS branches already incorporate this idea; it must not be advertised as a new reduction here. The ZFC packet itself prices that companion language at **216**, despite its source-level simplification. [Z2]

Our additional experiment moves contradiction detection into **successful MP**. An initial positive-target variant cost 201 states, reduced to 199 by a reused copy block and a reachable invariant. The final **196-state** variant keeps the original target `d+x`, copies a successful target into the accumulator and a scratch, then reuses the inherited comparison against 1. Its proof compiler handles zero-target aliasing and normalizes the successful offset. The original Shift guard remains present and is unreachable at initialized command boundaries. This is a new implementation experiment, but its measured cost does not meet the requested sub-194 target. Exact tables and proof boundaries are recorded separately.

## 3. Distinguish exact quotients, contextual folds, and arithmetic representation

The ZFC exact-quotient theorem requires equality of write bit, direction, and mapped successor for **both** read symbols. Its `NoQuotient254` certificate proves that every such quotient of that particular 254-state table is injective. It explicitly leaves open tape-dependent folds, variable-length simulations, and different source programs. Thus it is useful as a narrowly scoped rejection test, not as a lower bound for a consistency problem. [Z3]

We extended the inherited PA contextual search rather than transferring that ZFC no-quotient conclusion. Across eight accepted 194-state variants, three encodings—head displacement, one-bit phase change, and both together—received complete radius-six, 128-step local screens: **1,195,148,640 patch trials**, with no survivor. Those are bounded trials of specific templates, not distinct machines and not a proof that 193 states are impossible. The portable scripts, exact counts, and positive/adverse controls are in `inventory_work/search/SEARCH_REPORT.md`.

The ZFC arithmetic representation of a tape by two naturals gives an exact way to express and verify a run, including the final halting write and move and the entire tape exterior. This can strengthen the PA proof infrastructure; it does not itself remove physical controls. [Z4]

## 4. Sequence coding and subformula economy need complete cost accounting

ConciseIPRA's native scalar core uses one numerical sort, iterator terms, and unary formula constructors `Q` and `D`. Its sorted arity codec reuses one raw-tree grammar for terms and formulas: arity identifies the constructor, while depth parity identifies the sort. These devices can reduce independent dispatch cases and unify substitution routines. The article also proves a whole-domain surjective pairing

\[
  \operatorname{cp}(a,b)=2^a(2b+1)-1
\]

with total inverse projections. That offers an alternative sequence/environment codec to Cantor pairing; it still has the zero alias `cp(0,0)=0`. Any TM transfer must price parity, halving, projections, source sharing, and initialization together. No such complete PA recompilation was implemented in this work. [C1–C3]

The one-subformula syntax makes binder depth equal to the number of binder occurrences; it does not bound the size of iterator terms, proof certificates, or decoded machine source. The corpus measures standalone Python checkers by normalized tokens, AST nodes, and bytes. A reduction in any of those quantities does not imply a reduction in this compiler's number of distinct instruction-reader subtrees. We investigated sharing and local controller folds in the existing Cantor-coded architecture; an arity-coded PA verifier remains future work. [C1, C3, C4]

## 5. Preserve the theory and the proof base

ConciseIPRA establishes presentations bi-interpretable with **iPRA**. It does not, by that fact, calibrate a contradiction search to **PA**. Replacing the existing PA validator with one of these checkers would require an explicit PA-refutation translation in both directions, including whatever additional induction is needed. Syntax economy alone supplies neither that theorem nor the compiled state count. [C1]

The ZFC index illustrates a second distinction: it reports closed external Lean/Rocq correctness for the exact K215 table, but keeps that table's internal PA endpoint open; the exact 240-state table has a separate internal PA theorem. One cannot borrow an endpoint for a different literal table or proof base. Our work reuses the attributed ordinary PA calibration of the PA numerical calculus, and supplies executable runtime evidence plus ordinary mathematical arguments. It does not claim a new end-to-end Lean/Rocq theorem or iPRA internalization. [Z5]

## Pinned sources

- **Z1.** [`ZFC/candidate-k215/alternatives/zero-spare/README.md`](https://github.com/VladimirReshetnikov/ProveIt/blob/2a88cb6a3f823e0de5addf19d725bf8373860c71/Computability/BusyBeaver/Research/ZFC/candidate-k215/alternatives/zero-spare/README.md), “Exact construction” and “Complete verification and the new proof idea.”
- **Z2.** [`ZFC/candidate-k215/alternatives/zero-spare-transfer/report.tex`](https://github.com/VladimirReshetnikov/ProveIt/blob/2a88cb6a3f823e0de5addf19d725bf8373860c71/Computability/BusyBeaver/Research/ZFC/candidate-k215/alternatives/zero-spare-transfer/report.tex), protected startup and “Removing the successful MP zero push”; see also its [README](https://github.com/VladimirReshetnikov/ProveIt/blob/2a88cb6a3f823e0de5addf19d725bf8373860c71/Computability/BusyBeaver/Research/ZFC/candidate-k215/alternatives/zero-spare-transfer/README.md).
- **Z3.** [`ZFC/no_quotient254.md`](https://github.com/VladimirReshetnikov/ProveIt/blob/2a88cb6a3f823e0de5addf19d725bf8373860c71/Computability/BusyBeaver/Research/ZFC/no_quotient254.md).
- **Z4.** [`ZFC/arithmetic_machine_perm252.md`](https://github.com/VladimirReshetnikov/ProveIt/blob/2a88cb6a3f823e0de5addf19d725bf8373860c71/Computability/BusyBeaver/Research/ZFC/arithmetic_machine_perm252.md). Its historical status statements concern that 252-state checkpoint; the directory index records later endpoints.
- **Z5.** [`ZFC/README.md`](https://github.com/VladimirReshetnikov/ProveIt/blob/2a88cb6a3f823e0de5addf19d725bf8373860c71/Computability/BusyBeaver/Research/ZFC/README.md), opening status, K215 paragraph, and “Executable experiments and reusable repository ideas.”
- **C1.** [`ConciseIPRA/README.md`](https://github.com/VladimirReshetnikov/ProveIt/blob/2a88cb6a3f823e0de5addf19d725bf8373860c71/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md), “The question,” “The native scalar core,” and “Ordinary realization.”
- **C2.** [`ConciseIPRA/docs/Article/chapters/ch01_base.tex`](https://github.com/VladimirReshetnikov/ProveIt/blob/2a88cb6a3f823e0de5addf19d725bf8373860c71/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/Article/chapters/ch01_base.tex), `base:sec:cp` and `base:lem:cp`.
- **C3.** [`ConciseIPRA/docs/Article/chapters/ch11_cert.tex`](https://github.com/VladimirReshetnikov/ProveIt/blob/2a88cb6a3f823e0de5addf19d725bf8373860c71/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/Article/chapters/ch11_cert.tex), `cert:sec:codec`, raw trees, sorted reading, and canonical encoding.
- **C4.** [`ConciseIPRA/docs/Article/chapters/ch02_kern.tex`](https://github.com/VladimirReshetnikov/ProveIt/blob/2a88cb6a3f823e0de5addf19d725bf8373860c71/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/Article/chapters/ch02_kern.tex), `kern:sec:depth` and `kern:sec:depthclass`.
- **P1.** [`docs/incoming/pa194dhs_conpa_2026-11-13.zip`](https://github.com/VladimirReshetnikov/ProveIt/blob/2a88cb6a3f823e0de5addf19d725bf8373860c71/docs/incoming/pa194dhs_conpa_2026-11-13.zip), member `pa194dhs_conpa_2026-11-13/report/append0_obstruction.tex`.

The append-zero all-start classification is also indexed in `comparison_notes.md` and `frontier194_annotated.csv`. New-search and prototype statements in this note refer to the artifacts of this session, not to the pinned repository.
