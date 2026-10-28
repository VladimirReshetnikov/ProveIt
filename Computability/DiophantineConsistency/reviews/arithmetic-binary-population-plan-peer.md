# Internal binary population: independent plan review

27 October 2026. **Mathematical plan and read-only cache authentication
PASS; no implementation or compiler acceptance is claimed.**

I read the full proposed scope, the complete Foundation HFS/PRF source,
the precise binary-length/fbit definitions and shift proofs in
Exponential/Log, and the bounded-quantifier/represented-function closure
contracts in Definability. I also checked the established explicit
graph/totality pattern in ArithmeticSequenceHistory. No mathematical or
public-interface gap was identified in the proposed endpoints.

PR.Blueprint 1 can use the parameter a, zero output 0 and successor
`previous+fbit(a,index)`. Its fixed result formula has output/index/a
order. Construction supplies all-internal unique values, fixed Sigma1
and Delta1 graph definitions and actual successor equations. Population
can have the explicit fixed graph
`∃l≤a, lengthDef(l,a) ∧ prefixDef(output,l,a)`; the bound follows from
actual `length_le`. This is a composition of represented functions, not
a complexity claim inferred from a semantic choice function.

The prefix shifts hold at a=0 as well as at positive a. Their induction
uses `fbit_two_mul_zero_eq_zero`, `fbit_two_mul_add_one_zero_eq_one`,
`fbit_mul_two_mul`, and `fbit_mul_two_add_one_mul`. Only conversion to
the even population identity needs the zero/positive a split, because
`length_two_mul_of_pos` requires positivity. The odd length identity is
unconditional. Prefix stabilization follows from `fbit_eq_zero_of_le`,
for example by successor induction on the excess above length. The
inequality prefix(n,a)≤n uses `fbit_le_one` and includes n=0.

For concatenation, keep A fixed and universally quantify b only below
the current exponential bound. Decomposition b=2q+r, r=0 or1, gives
q<exp(n) from b<2exp(n); the next concatenation equals
`2*(A*exp(n)+q)+r`. The same even/odd recurrence applies to b itself.
The n=0 case forces b=0. Thus A=0 and leading zero blocks are included.
For complement, the justified identity
`exp(n+1)-1-a=2*(exp(n)-1-q)+(1-r)` is correct in both remainder cases;
q<exp(n) establishes all required truncation bounds before rewriting.
The two low bits sum to one, giving the successor step from the bounded
induction hypothesis. The base n=0 forces a=0 and complement 0.

An explicit Sigma1 motive may bind an exponential witness first:
`∃E, Exponential(n,E) ∧ ∀b<E, ...`, and analogously for complement.
Total uniqueness identifies E with exp(n). This makes the bounded
universal syntactic and avoids treating the represented exponential as
a primitive arithmetic term. The represented prefix/population graphs
must be installed before these definability proofs. No unbounded
universal over A or standard-index induction is required.

The proposal is pinned by SHA
`888c8e556ade5b865271dc8e7d06f156daf27f2b9dd96400eab3aab305455d58`.
The frozen inventory SHA is
`8db28403220c05983a67306abafc73e78ee1fb85447948ab05ab584f29fae16e`.
My independent audit JSON is
`arithmetic-binary-population-plan-peer-audit.json`, SHA
`bf9a51d46c71a976828e9069ee14605c1dcce045d5f1d40265b82a2ddba72d11`.
All 4,368 comparisons passed across 1,050 paths: exact reachable
95-module Foundation DAG, 380 custom artifacts, 38 explicit boundaries
with 114 total boundary artifacts (38 primaries and 76 companions),
all 494 first-provider mappings, unchanged package search and pinned
Lean4.32 compiler. Zero prerequisite refreshes. Source headers include
implicit Init and all actual import modifiers; every selected source,
object, companion and inherited evidence pin was rehashed.

The selected provider remains the accepted PellRecurrence peer closure.
I independently reviewed/replayed that earlier leaf; I did not author
this new population proposal or its forthcoming implementation. The
current audit does not rebuild Foundation or authenticate external
package interiors beyond the explicit inherited boundary. The parent's
historical word “companions” for 114 means total boundary artifacts;
the present counts distinguish primaries and companions correctly.

I read and verified the preserved administrative first audit correction:
its only source difference is accepting the actual historical status
INDEPENDENT_PEER_PASS rather than PASS. It stopped before output creation.
My new audit passed its first attempt and made no overlay, compiler call,
source edit, prerequisite mutation or Git change. The driver, logs and
this audit are frozen separately for ROOT review.

Population subadditivity/carry defects, fixed-mask population, binomial
valuations and the half-binomial estimate remain separate proof work.
This plan review supplies no source/tableau/HA endpoint and does not
replace independent review of the eventual complete Lean pair.
