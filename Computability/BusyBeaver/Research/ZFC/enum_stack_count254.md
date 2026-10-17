The new `EnumStackCount254.lean` supplies the checked global counting link
for the actual `Enum254` enumerator. The source and scoped caller audit passed explicit pinned Lean 4.32.0.
The verification record is `results/enum-stack-count254-verification.json`: source
wall time 1.01 s and audit 0.31 s, 25 axiom reports, 12 generic callers and 4 exact
controls. Only `propext`, `Classical.choice` and `Quot.sound` occur. Dependencies
were source-matched to the checked integration157 cache; they were not rebuilt.

The marked-occurrence argument is attributed to intake155/source42, arrival
`fab89c5d26b81cd2ccab2ee5d213ff23725c7726`, report input
`61e77836565f63582561f54745f633d50efd9c7d`. The original enumerator's
Mira-Cult/Jeff Ketchersid/Andrew James Wade attribution is retained in the
module. This extends the already checked `EnumStackBarrier254` foundations.

For candidate `k`, `commands k` is the exact total decoder from that module.
Occurrences retain both the candidate number and command position. Swapping
one NIP for DROP preserves the marked position and is involutive, while the
actual Cantor command code strictly decreases. Thus every NIP in candidates
through `k` injects into a DROP in candidates strictly before `k`.

The stronger bound supplies enough credit for all pops of candidate `k`
before counting any of its own pushes. `cexec_safe` uses the existing local
whole-stack-prefix invariant, allowing arbitrary data below its witnessed
good prefix. Successful MP and AX may push additional good entries; the
count uses only DROP and discards that extra credit.

`exec_list_some` and `candidate_some` bind command-list execution to the actual
six-register scheduler with exact steps and pointer outputs. Under absence
of a `C254` refutation, `safe_boundaries` produces arbitrarily late active
candidate endpoints. The actual partial run cannot become active again
after returning `none`, so this rules out a finite halt. The
`dirty_start_iff` theorem concludes that starting with `pl=np=d=0` and
arbitrary current formula, stack and cache halts exactly when `C254 F` holds.
Candidate zero is the existing proved reset, rather than an assumed safe
initial formula. `candidate_one_iff` permits arbitrary stack and numerical
`d` with initially good current formula and cache. `credit_start_iff` exposes
the general candidate-boundary version for later initializer adapters.

The final dirty-start theorem has no assumed count invariant. This module
makes no new binary-machine, initializer-search, Choice or PA representation
claim; separate binary refinements and consistency calibrations retain their
own scope.

The joint [160-unit integration](results/stack-count-order-integration-verification.json)
freshly checks this module, `InternalWO`, `OrderRec` and the umbrella, reusing
156 source-matched checked units. All 24 axiom reports and nine generic callers
pass; the only reported axioms are the three standard Lean axioms listed above.

A later independently arriving intake156/source49 report also gives an ordinary
late-credit theorem. This module was developed from the already accepted
source42 marked-occurrence argument and the actual-code foundations; the
source49 review is separate and does not replace its provenance.
