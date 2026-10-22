# Fixed-input Diophantine forms of ZFC consistency

This contribution constructs a fixed Diophantine system and several fixed
polynomials for which ZFC proves

\[
\text{there is no solution in the stated domain}
\quad\longleftrightarrow\quad \operatorname{Con}(\mathrm{ZFC}).
\]

The recommended presentation is **seven equations in 16 positive integer
unknowns, maximum degree 34**, with a complete shared circuit of 66 arithmetic
operations. A **single polynomial in 15 positive unknowns, degree 295**, uses
82 operations. A fully unrestricted integer polynomial is also supplied:
**45 integer unknowns, degree 590**, with 187 operations.

The paper is [paper/fixed_input_zfc.pdf](paper/fixed_input_zfc.pdf), with
editable source [paper/fixed_input_zfc.tex](paper/fixed_input_zfc.tex).
All definitions, proofs, domain restrictions and cost conventions are in
the paper. The coefficients are exact fixed integers given by finite
formulas; they are not small integers and are not expanded into digit strings.

## Results and choice of presentation

| Artifact stem | Domain | Unknowns | Equations | Exact degree | M | A | Total |
|---|---|---:|---:|---:|---:|---:|---:|
| `fixed16_system66_degree34` | Positive integers | 16 | 7 | 34 maximum | 35 | 31 | 66 |
| `fixed16_sos86_degree68` | Positive integers | 16 | 1 | 68 | 42 | 44 | 86 |
| `fixed15_product82_degree295` | Positive integers | 15 | 1 | 295 | 46 | 36 | 82 |
| `fixed15_outer80_degree346` | Positive integers | 15 | 1 | 346 | 46 | 34 | 80 |
| `fixed16_product74_degree157` | Positive integers | 16 | 1 | 157 | 41 | 33 | 74 |
| `fixed16_product75_degree125` | Positive integers | 16 | 1 | 125 | 41 | 34 | 75 |
| `fixed16_product76_degree113` | Positive integers | 16 | 1 | 113 | 42 | 34 | 76 |
| `integer45_product187_degree590` | All integers | 45 | 1 | 590 | 91 | 96 | 187 |
| `integer48_sos198_degree136` | All integers | 48 | 1 | 136 | 90 | 108 | 198 |

Here M counts multiplication and A counts addition/subtraction, including
operations with fixed numerals. System comparisons are separate from its
66 arithmetic operations. The one-polynomial rows include their complete
finalizers. Fixed integer coefficients are treated as constants; the ledger
does not measure their enormous bit lengths. Computed registers are polynomial
abbreviations, not extra existential variables. Every circuit is fully emitted
in `arithmetic/`; no predecessor generator is imported as executable code.

The 16-variable system is the easiest proof interface. Its sum of squares
is the lowest-degree single equation in the packet. The 15-variable polynomial
uses fewer positive unknowns. Its 80-operation alternative trades higher degree
for two saved operations. No global minimum over all Diophantine constructions
is claimed; classical universal equations can use nine nonnegative unknowns
at a far larger degree. See the literature discussion in the paper.

## What is new

The supplied universal arithmetic source uses 18 positive witnesses and an
ordinary input. We specialize its input to 1 and replace its marker by the
known integer

\[
W_0=2^{2\cdot5^{90}+5^{45}}.
\]

This removes the input Pell equation and its three positive witnesses, while
introducing one positive variable for their retained sum. Crucially, the proof
constructs a positive inverse on **every** reduced solution. It does not merely
drop a constraint or work on selected canonical witnesses. The reduction gives
16 positive unknowns. Quadratic norm elimination of the strong Pell root gives
15; the proof handles its initially undetermined sign by restoring the full
parent tuple before applying the inherited signed-quotient theorem.

The unrestricted versions replace each positive unknown by

\[
z=1+a^2+b^2+c(c+1).
\]

This is positive at every integer triple and represents every positive integer
by Legendre's three-square theorem. The JSON circuits include every gate of the
substitution. For nonnegative unknowns instead, the simple shift `z=n+1`
preserves the original number of unknowns and degree; that optional shift is
described mathematically and is not a separate emitted JSON source.

## The literal K215 coefficient instance

All inherited sources are pinned to ProveIt commit
`cdd582bec13f908df3711fa9e05d1ddac368a5db`.

The construction begins with the exact native K215 table, verifies its state
isomorphism to the dense formal endpoint, and folds its tape into a one-sided
436-state, ten-symbol machine. The normalizer first erases a unary input and
then simulates blank K215. The fixed marker selects four initial unary ones.

The tableau alphabet has 4,376 symbols. Its exact permitted-window count is
`115264654755851622862362693632`. The ordering is Start first, End second,
then the remaining locally valid windows in lexicographic tile-index order.
This is a bounded finite enumeration, with no halting query.

The coefficient recipe uses `A=2^100`, `b=L=5^45`, and `d=5^90`.
`coefficients/coefficient_specification.json` specifies all support positions,
clause coefficients, bands and fixed finite sums. `coefficient_recipe.py`
implements the definition. Its deliberately infeasible `materialize_k215()`
is **not** called by any verification command. The conservative radix choices
are proved admissible; they need not equal the historical minimal-radix choice.

The six source ports are fixed as follows:

| Source port | Fixed integer |
|---|---|
| `Bm1` | `B-1`, where `B=2^d` |
| `Kconstant` | `DC+B*DR` |
| `MC` | Modified half-binomial data mask |
| `MF` | `MF_native+B-1`, the **shifted** mask |
| `W0` | `2^(2*d+b)` |
| `W0plus2d` | `2^(2*d+b)+2*d` |

The detailed coefficient proof is also supplied as
`coefficients/coefficient_note.tex` (a LaTeX section fragment), with a separate
review in `proofs/fixed_machine_coefficient_review.md`. It includes exact marker
matrices and the support-separation, carry, population and congruence arguments.

## Reproduce the checks

From this directory, with Python 3.10 or later and no third-party packages:

```sh
python3 verify.py
```

The default command is read-only and can be run from any working directory.
It verifies:

- The pinned inherited bytes, including both K215 tables, state map and
  original complete84 JSON source.
- Literal reconstruction, graph topology, liveness and operation counts for
  all seven positive-domain and both unrestricted-integer circuits.
- Degree bounds with the explicit main-norm cancellation, and supplementary
  full-source univariate degree diagnostics. The paper and audit note give
  separate uniform nonzero-leading-form proofs.
- Independent expression comparisons on signed-integer and rational fixtures
  for all nine complete circuits.
- Eight exact local polynomial identities by sparse integer coefficients.
- All 430 dense/native row correspondences, 3,440 folded transition contexts,
  32 initialization lengths, and every emitted normalized-machine row.
- The exact window census, 995,328 directly tested cross predicates on four
  small machines, the large-instance coefficient-parameter bounds, and one
  fully materialized small coefficient instance.

`verification.json` records the delivered successful run. To intentionally
regenerate that report, use `python3 verify.py --write-report`. The individual
arithmetic builders default to checking existing output. Their `--write` flags
regenerate their respective JSON circuits. The lower-level machine and
coefficient scripts write their local receipts when run directly; the top-level
verifier imports their checking functions without invoking those writers.

Compile the paper with a normal LaTeX installation:

```sh
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error fixed_input_zfc.tex
```

The `Makefile` offers `make verify` and `make pdf`. The PDF was compiled and
visually inspected in the delivered version. Recompiling may change PDF
metadata and therefore its byte checksum while preserving its contents.

## Proof and verification boundary

The proof composes

\[
\text{polynomial/system solution}
\Longleftrightarrow \text{normalized-machine acceptance}
\Longleftrightarrow \text{blank K215 halting}
\Longleftrightarrow \text{finite ZFC refutation}.
\]

The final equivalence is the accepted K215 mathematical calibration, with its
separate existing Lean and Rocq endpoints. The H10 compiler, Pell/population
lemmas and signed-quotient theorem are inherited mathematical proof dependencies.
The new fixed-input inverse, coefficient instance and norm reductions are
ordinary mathematics formalizable in ZFC.

**This packet is not a fresh Lean or Rocq kernel verification of the full new
Diophantine theorem.** It does not contain a new formal compiler theorem or an
internally encoded ZFC derivation. No fresh full endpoint build was run. Finite
tests verify the stated finite and algebraic facts; the quantified equivalence
is justified by the mathematical proof, not by testing. The packet does not
decide whether ZFC is consistent, and does not claim an unconditional proof
that the equations have no solutions.

## Archive contents and integration

| Location | Contents |
|---|---|
| `paper/` | Main `.tex` and compiled `.pdf` |
| `arithmetic/` | Nine complete circuits, builders, independent formula checker, receipts, exact upstream data |
| `coefficients/` | Literal machine data, normalized machine, exact coefficient recipe, verifier, detailed coefficient proof |
| `proofs/` | Fixed-input inverse proof, endpoint notes, independent reviews, exact local-identity checker |
| `references/` | Selected byte-identical inherited mathematical proofs and endpoint source |
| `notices/` | Inherited K215 attribution and license chain |
| `inherited_files.json` | Original repository paths and hashes of copied source files |
| `provenance.json` | Source commit, evidence scope and delivered file hashes |
| `verification.json` | Successful finite/algebra verification receipt |

For integration into ProveIt, this directory can be placed under a new research
subdirectory of `Computability/HilbertTenthProblem/Papers/research-wip/`.
The folder is self-contained for the supplied Python checks and PDF build.
`references/` is a selected source snapshot; links within inherited Markdown
may refer to other files in the full upstream repository. Their original paths
and immutable URLs are recorded in the provenance manifest.

New contributions use the repository's MIT No Attribution terms in `LICENSE`.
Inherited source files retain their distributed notices in `notices/`.
The original sources are unmodified; new review notes identify their own scope.
