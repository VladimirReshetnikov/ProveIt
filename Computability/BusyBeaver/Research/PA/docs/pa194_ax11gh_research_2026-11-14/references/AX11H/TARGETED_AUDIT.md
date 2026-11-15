# Audit scope for the updated incoming AX11H calibration

## Which result is being inherited

The relevant artifact is the **updated incoming**
`docs/incoming/pa194_ax11h_research_2026-11-14.zip` at ProveIt commit
`1e1a41f799d4658b829cdd0eabae3775a0c8c4a0`, not merely the older filed
packet with the same stem. Its archive SHA-256 is
`93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075`.
Its own mathematical source snapshot is
`1c9524d8bf2e0a27b9a16ff622359927f536e663`, with Foundation dependency
`32e1a0956a8622fad067328ca1959729a7634428`.

This updated manuscript explicitly claims a complete ordinary written
proof of the absolute iPRA equivalence for two literal machines:

| Machine | Dense-table SHA-256 |
|---|---|
| PA194AX11H | `c5dfe1026d077d3e062eca11edb789597bfbbced4f6040f8828ae5d467b1167a` |
| PA194QAX11H | `19e215df20429fa6a35f0a99ba0dcfcb40893a6e4b9a4ae6e450b0225f110e50` |

Its consistency predicate is the negation of the pinned Foundation
`nativePARefutation`, not an unspecified interchangeable coding. The
current PA project README still reports the formal end-to-end calibration
as open. These two statements must be distinguished: the incoming manuscript
claims a new written mathematical argument, while supplying no new complete
Lean or Rocq kernel build.

## Claimed dependency chain

1. Exact blank physical table to exact primitive-register source, in iPRA:
   `proof/physical_ipra_audit.tex`.
2. Primitive-register source to explicit command scheduler, in iPRA:
   `proof/source_command_completion.tex`.
3. Command scheduler to its numerical calculus, in iPRA:
   `proof/ax11h_preservation.tex`.
4. Original and Q-oriented numerical calculi, in iPRA:
   `proof/q_exchange_ipra.tex`.
5. Numerical refutation to current PA refutation, uniformly in the relevant
   IΣ₁ models: `proof/consistency_implies_nonhalting.tex`.
6. Current Foundation PA refutation to ordinary PAeq refutation:
   `proof/foundation_paeq_completion.tex`.
7. Ordinary PAeq refutation to numerical refutation, uniformly in IΣ₁:
   `proof/term_leaf_completion.tex` and
   `proof/forward_calibration_completion.tex`.
8. Composition and the existing negative/conservation transfer endpoints:
   `proof/consistency_equivalence.tex`.

The manuscript supplies primitive recursive witness constructions for
both execution directions. Its final forward physical clock is a
composition of the PA proof compiler, a command-word scheduler bound,
the source command clock, and the physical source clock. It does not
invoke Markov's principle to recover an existential from its double
negation.

## Targeted mathematical review performed here

The central physical/source and source/command arguments have been read,
including their exact endpoint conventions, source ports, loop templates,
and cumulative clock arguments. Their method is mathematically appropriate:

- The symbolic list-width parameter is tied to the same spare list occurring
  on the tape. It is not treated as an unrelated natural number.
- Complete padded endpoint words, rather than a local tape window, identify
  successor source frames.
- The source-frame gap and spare-file bookkeeping are included in the
  primitive recursive state recursion. All nonhalting segment durations
  have positive constants.
- Physical halting is made absorbing. A physical halt at time `t` implies
  a source halt by source step `t+1`, using positivity and a later exact
  source-boundary equality. This argument is valid intuitionistically and
  needs no unbounded least-time search.
- Command clocks are defined by explicit counter formulas and compositions,
  rather than by waiting for a source macro to terminate. The source halt
  retains the register file required by its command-level endpoint.

The forward compiler's main finite-demand construction and its stratum
order have also been reviewed. The decisive distinction is that a recursive
child query is computed from the parent syntax and parameters **before**
any child proof output is used. Same-family ranks decrease. Calls on larger
replacement terms go to an already completed lower stratum, instead of
forming an uncontrolled recursion cycle. A complete finite query tree and
reverse evaluation define primitive recursive proof lists. Bounded Boolean
forward and reverse invariants justify quantifier-free induction without
inducting on an unbounded “all environments have a proof” assertion.
That is a valid technique for weakening the older proof construction.

The manuscript explicitly addresses the current/historical Foundation
coding distinction, the changed finite `addEqOfLt` axiom, the source and
target induction closure counts, and the difference between Foundation
falsity code 13 and numerical falsity code 1. Its use of fixed standard
proof templates is separated from arbitrary internal proof codes.

No immediate logical contradiction or circular dependency was found in
these central schemes. This is a targeted mathematical audit, **not** an
independent validation of every local constructor equation cited across
the much larger upstream Lean development, and not a newly reconstructed
formal derivation of the entire absolute theorem. The source remains an
explicit inherited mathematical dependency.

## Finite replay

The supplied aggregate `verify_all.py` **passed a fresh full-mode run**
from a clean extraction, with outputs kept separately. It checked all
1,186 manifest entries and byte-identically reconstructed both tables.
For each parent it replayed all construction contracts, all 4,778
independent literal source outcomes, all 3,671 source instruction bindings,
complete blank startup after 57,922 transitions, and the supplied command
checks. It also passed the physical frame/duration audit, saved source
identity checks, finite Foundation proof constructors, all 119
current/historical Foundation coding comparisons, and the fixed Q-premise
exchange certificate. The final receipt and component receipts are kept
under `references/AX11H/fresh_replay/` in the supplied audit
material. The original verifier's 82-class novelty tests are historical;
the new comparison independently covers the current 110-class frontier.

The script itself explicitly sets
`arithmetic_derivation_checked_by_this_script: false` and
`kernel_checked: false`. Its successful finite replay must not be described
as checking the entire arithmetic proof by computation. The written
quantifier-free/IΣ₁ proofs are what interpret its finite certificates
uniformly.

## Appropriate use in the new construction

The updated incoming AX11H theorem can be used as an **explicit cited
absolute-calibration premise**. The new report should prove its own
relative iPRA preservation theorem for the exact new tables and then state
the absolute conclusion as a corollary of that theorem and the cited
AX11H manuscript. This is stronger and more precise than saying the
absolute calibration is merely waiting for Lean to run.

The new relative proof must bind its own source change and its own literal
table; the inherited physical certificate does not automatically cover new
graphs. Conversely, a freshly checked universal physical certificate plus
the soundness argument and complete positive-clock composition can reuse
the same proof method without requiring a new mathematical PA calibration.

Suggested status wording:

> The new relative preservation theorem is established here by an ordinary
> computer-assisted iPRA argument. Composing it with the absolute written
> calibration in the updated incoming AX11H manuscript yields the stated
> Con(PA) equivalence. That calibration is an explicitly inherited
> mathematical dependency; this release does not claim a new end-to-end
> Lean or Rocq proof of either the inherited absolute calibration or the
> full new conclusion.

This note records what was reviewed and what is being inherited. It does
not replace the manuscript or upgrade a finite receipt into a proof of an
unbounded arithmetic statement.
