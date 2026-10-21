# A single ranking proof for K215's enumerator

## Scope and baseline

This component starts at ProveIt commit
`aa66d0a33f1f8237a348899eb8095b045a502832` (21 October 2026), after the latest
ordinary-certificate, implication, AX-word, and semantic-lemma simplifications.
It changes no machine row, arithmetic code, command encoding, derivability
predicate, or existing enumerator/seed endpoint type.

The new concrete contribution is a checked replacement of three scheduler
inductions by one ranking argument, plus a stronger arbitrary-initial-state
completeness theorem. This is independent of the existing source-certificate
normalization and positive-stuttering proposals. The simple opacity change is
an application of the already used local-opacity technique to another concrete
module; it is not claimed as a new proof method.

## The ranking argument

For a chosen candidate number N and enumerator state s with np(s) <= N, put

    R_N(s) = (N - np(s)) (N + 1) + pl(s).

The existing exact `step_pl` lemma says that every successful step satisfies:

* when pl(s)>0, the next candidate counter is unchanged and pl(s') <= pl(s)-1;
* when pl(s)=0, np(s')=np(s)+1 and pl(s')<=np(s).

Stop at the boundary pl(s)=0, np(s)=N. Before that boundary, every successful
step decreases R_N strictly and keeps np<=N. The nonboundary refill case has
np<N, and

    R_N(s') - R_N(s) <= np(s) - (N+1) < 0.

`find_candidate_bounded` proves constructively that some n<=R_N(s) successful
steps reach a state t which either takes a halting step or is exactly that
candidate boundary. If the halting transition itself is counted, the bound
is n+1, not n. This distinction follows the existing `halts_from` convention.

The old proof used a separate drain induction on pl, an induction over
candidate numbers from s0, and a second candidate-number induction from the
seed. None is needed in the new source.

## Stronger compiler theorem

The existing compiler yields, from thm222(1), a finite word L satisfying
`blk 1 L`. Its existing `program_halts` theorem already says that
`START Y :: L ++ SUFFIX` halts from every working-register tuple, including
arbitrary current formula, stack, counter and cache values.

Choose Y=np(seed). The exact candidate number of this word is

    N = P(3, P(Y, P(1, enc_tail(L ++ SUFFIX)))).

The inherited Cantor inequalities prove N>=Y. The new rank theorem therefore
reaches this word or an earlier halting configuration from *any* initial state,
even when its proof-list pointer is nonzero. It gives the checked theorem:

    enum_complete_from :
      forall seed : state, thm222 1 -> halts_from seed.

The forward implication still requires the ordinary derivability invariant:

    enum_from_iff :
      forall seed : state, Inv seed ->
        (halts_from seed <-> thm222 1).

`Inv` mentions only the current formula, cache, and the derivability of every
stack-stream entry. It imposes no condition on the proof-list pointer, next
candidate counter, or arithmetic counter. In particular, every state
`mkState p n 0 0 d 0` satisfies it, for all p,n,d. This supplies a more flexible
interface for future bootstrap proofs; no shortening of the physical startup
trace has been proved here.

Do not drop `Inv` from the equivalence: putting falsity code 1 into the initial
cache can make the machine's NIP command halt immediately, whether or not that
code was derivable. The unconditional new statement is completeness only.

## Preserved interfaces and integration

The following exact public statement types still elaborate:

* `enum_complete : thm222 1 -> enum_halts`;
* `seedPerm_complete : thm222 1 -> halts_from seedPerm`;
* `seedPerm_sound : halts_from seedPerm -> thm222 1`;
* `seedPerm_iff_thm : halts_from seedPerm <-> thm222 1`.

The production `MainPerm.v` imports the unchanged last statement in its
`dagPerm_iff_standardZFC` composition. A source audit found no production
consumer of the removed private scheduler helpers outside the old seed file.
The patch intentionally does not promise compatibility with arbitrary external
clients of these private helper names.

Update the maintained templates in `rocqperm/` as well as the generated copies
under `rocq/rocq-extension/coq/215/`; then regenerate metadata and rebuild the
normal production endpoint. The supplied patches target the generated copy's
`K215F` namespace. The corresponding template change replaces `K215F` by `NS`
in its import line and does not copy the generated provenance header.

## Opacity improvement

`L1_SoundPerm.v` now includes

    Local Opaque P wim wal wex weq wel.

The proof uses their existing constructor and inverse lemmas, never expansion
of the arithmetic implementation of a formula code. Local opacity avoids
normalizing those large code expressions. Every theorem statement and existing
soundness proof script is otherwise unchanged. This introduces no axiom and
changes no public constant's mathematical definition.

The initial focused run compiled that module in 43.290 seconds; an isolated
opacity trial took 0.810 seconds, and the final fresh closure's version took
0.665 seconds. These are observations under Coq 8.18 on this host, not a
controlled whole-project benchmark or a claimed production Rocq 9.1 speedup.

## Verification boundary

All ten required project/calculus modules were freshly compiled from pinned
sources using Coq 8.18.0 / OCaml 4.14.1. The build copy changes `From Stdlib` to
`From Coq` because the standard-library namespace changed between versions;
there are no assumed compatibility lemmas. The private code copies and exact
hashes are retained. A typed client checks the four old interfaces and two new
interfaces. Six `Print Assumptions` reports are closed under the global context.
A recursive `coqchk` checks `K215F.SeedPerm` and its dependencies.

The complete binary-machine-to-ZFC closure is not rebuilt here. These are
checked calculus/enumerator theorems and compatible seed interfaces, not a new
unconditional nonhalting theorem or a state-count result. The exact arithmetic
predicate thm222 and its already established calibration are unchanged.
