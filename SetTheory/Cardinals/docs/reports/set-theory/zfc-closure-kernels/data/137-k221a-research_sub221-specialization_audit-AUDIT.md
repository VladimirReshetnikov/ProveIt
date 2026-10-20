# Independent audit of alternative seed and source specializations

Audit date: 20 October 2026. All instruction ordinals below are zero based.
This audit changes no delivered K221 file.

## Verdict and scope

Both source-level ingredients are valid under the stated seed restrictions:

1. The clean shortened-scanner startup seed
   `(4,3,0,0,3,0,0,0,0)` is sound and complete for the current
   merged-G/witness-request-K proof search, with the same inherited ordinary
   calculus-to-ZFC calibration as K221.
2. Under the reachable-entry fact `R6=0`, replacing old ordinals
   `[4598,4610)` by the six-leaf direct test is halting-equivalent. The
   independent cleanup `[4718,4721)` can also be removed.

These statements do **not** certify the shortened 220-state table. That
table still fails the existing source-runtime contract at a six-zero
instruction address. Nor do these statements establish the runtime or blank
startup of a newly compiled specialized source. No new Rocq/Lean endpoint is
claimed.

The independent scripts import neither the novelty search/checker nor a
compiler/source-language helper. They reconstruct source control flow twice,
using interval ancestry and binary arithmetic, and check agreement including
the no-stray-suffix condition.

## 1. Exact seed and the induction boundary

`check_shortened_boot.py` freshly replays the full 108,420-step blank prefix
using a finite byte array whose bounds exceed the maximum possible motion.
It verifies the complete finite support, not only selected tape cells.
Deleting native state 50 and redirecting targets to 75 yields:

- state 84, head -6, left marker -7, header 66;
- extra frame gap `66 - (-6) - 64 = 8`;
- physical register vector `(0,0,3,3,0,0,4,0,0)`;
- logical register vector `(4,3,0,0,3,0,0,0,0)`;
- exactly 61 spare registers, each with value 1;
- no other nonzero tape cells.

The source register convention is:

`(R0,...,R8) = (np,tw,ws,axiomcode,d,h,scratch1,scratch2,pl)`.

Thus the logical enumerator starts at

`s* = (pl,np,tw,ws,d,h) = (0,4,3,0,3,0)`.

The source-to-enumerator induction begins at a clean root command boundary:
axiomcode, scratch1 and scratch2 are zero. It does not begin at an arbitrary
interior instruction. The corresponding original clean-boundary relation is
the `enc` definition in upstream `prog/L2Root230.v`, lines 18–20. The
current source has the inherited all-register emitter/CFG transport for the
two changed axiom expressions.

### Soundness

Let `Thm` mean derivability in the **current** numerical calculus, not the
literal unmodified upstream `thm230`. The command invariant is exactly

`Inv(s) := Thm(tw(s)) and Thm(h(s)) and goodstack(ws(s))`,

where every iterated stream head of a good stack is a theorem. No restriction
on `np`, `pl` or `d` is used in the soundness argument. Starting completeness
from the chosen cutoff separately uses `pl=0`.

Code 0 is the retained truth axiom, and the all-zero stack has only zero
stream heads. Code 3 is literally `E(0,0)` because

`P(0,0)=0` and `E(a,b)=4P(a,b)+3`.

Equality reflexivity is a theorem of the current calculus, including label
zero. One direct derivation sets `z=R(x,x)`, `e=E(x,x)`. Contraction of
`G(x,x,z)` gives `E(z,x) -> Q(z,e)`. Existential monotonicity and retained
`rho1(z,x)` give `Ex(z,Q(z,e))`; retained `rho6(z,e)` gives `e`.
The propositional and quantifier-monotonicity steps use only retained rows,
MP and closed-theorem GEN. No discarded equality helper, old rho7, K
instance, label-distinctness assumption or open-hypothesis GEN is used.

This audit freshly replayed the inherited uniform proof checker against
`uniform_composition_proofs.json`. Its reflexivity root has 14 dependency
nodes and uses only G, GEN, MP, TAUT, rho1, rho2 and rho6. The TAUT rule
retains the documented rho8/rho6 classical bridge. The symbolic-label proof
allows every natural substitution, hence specifically x=0; this is not a
positive-label-only argument.

Therefore `Inv(s*)` holds. The usual command-by-command proof preserves it:
MP either derives its result or returns truth, DROP pushes a theorem, NIP
pops a theorem, AX pushes theorem instances and generalizes a theorem.
A halting NIP has cache 1, so every halt from this seed yields `Thm(1)`.
This is the exact argument of the upstream `L1_Sound230.v` definitions
`Inv`, `Inv_step`, `Inv_run`, and `halt_step`, with the current checked
schema definitions substituted.

### Completeness, including the changed cutoff

The proof is not “all formulas are eventually tried.” It uses exact
command-list encoding and a finite witness above the cutoff.

1. At a command boundary with `pl>0`, a nonhalting step strictly decreases
   `pl` and preserves `np`. Therefore the remainder of that candidate
   drains in finitely many commands, unless it halts first.
2. At `pl=0`, the next command loads candidate `np` and increments `np`.
   Thus, from any seed with `pl=0`, every candidate `N >= np(seed)` is
   eventually started, unless there is an earlier halt. This is precisely
   upstream `Seed230.reach_from`, whose statement is parametric in the
   entire seed. Its proof does not assume zero top/cache/stack/parameter.
3. Every current-calculus derivation of 1 has a finite compiling block L.
   The upstream block compiler transports to the current calculus:
   the AX stack retains the same ten positions, with G replacing only
   rho7 and the checked witness-request expression replacing only the
   bundle. G and the bundle have outer implication/negation codes,
   divisible by four, hence are never 1. The other logical rows and
   generalized-cache slot are unchanged. The command proofs for DISCARD,
   row leaves, bundle leaf, GEN and MP therefore retain their exact stack
   contracts. In particular L either halts or leaves top=1 with counters
   zero and preserves its input stack.
4. `START = CAX 0 1 1 0` resets the parameter/cache counters to zero before
   L. The program `START :: L ++ [DROP; NIP; NIP]` halts from **every**
   retained `(top,stack,parameter,cache)` tuple. This is the actual
   quantified statement of upstream `L1_Comp230.program_halts`, not merely
   its all-zero instance. The changed formulas do not alter that argument.
5. Write `r = enc_tail(L ++ SUFFIX)`. Its candidate number is

   `N = P(3,P(1,P(1,P(0,r))))`.

   Cantor pairing is monotone on nonnegative arguments, so
   `N >= P(3,P(1,P(1,P(0,0)))) = P(3,4) = 32`.
   Since 4 <= 32, this candidate is in the enumeration beginning at 4.
   Apply reach_from with `N-4`, then run_first and program_halts.

The sufficient seed conditions exhibited here are a clean root boundary,
`pl=0`, `np<=32`, and `Inv(s)` for the sound direction. Completeness itself
does not need `Inv`; its compiler works from arbitrary retained values.
The `np<=32` bound is sufficient for this exact witness argument, not a
claim that larger cutoffs are necessarily incomplete.

The inherited finite-proof calibration then identifies `Thm(1)` with the
appropriate ZFC inconsistency endpoint. This audit does not reopen or
strengthen that inherited calibration.

## 2. Fresh all-natural source invariant

`check_specializations.py` independently computes and then independently
checks closure of an abstract invariant for **each** of these exact seeds:

- baseline `(3,0,0,0,3,0,0,0,0)`;
- alternative `(4,3,0,0,3,0,0,0,0)`.

At each source ordinal, a component is a subset of
`{0,1,2,3,4,5,6,7,8}`. Buckets 0–7 are exact, while bucket 8 represents
every natural number >=8. The abstract state is their Cartesian product;
no correlation is assumed.

The increment transformer sends k to k+1, saturating at 8. A positive
decrement sends an exact k>0 to k-1; bucket 8 becomes `{7,8}`. The zero
branch restricts the tested register to `{0}` and leaves it unchanged.
All other components are retained. These transfers cover every concrete
natural valuation in their input products. Joins are unions and therefore
cannot discard a reachable concrete state.

The checked obligations are:

1. The seed belongs to the invariant at ordinal 0.
2. Every enabled abstract guarded edge maps into its target invariant.
3. Every asserted unreachable ordinal has an empty abstract invariant.

Concrete-step induction therefore proves the invariant for arbitrarily long
executions. Fixed-point convergence and finite samples are not its proof:
the final forward-closure checks and the sound abstraction are the proof.

For both seeds, all 6,161 enabled guarded edges pass closure, and:

- `R6=0` at 4598, the entry of the entire comparison;
- `R6=0` at 4603;
- `R1=0` at 4718;
- exactly 4604, 4719 and 4720 have empty invariant.

The complete independently computed facts are in `inductive_facts.json`,
and their digest is bound into `audit.json`.

## 3. Constant-one halt comparison

The old interval `[4598,4610)` has exactly one external incoming edge,
from ordinal 39 to entry 4598. Its sole nonhalting outward edge is
4608 -> 4610. The only halt is ordinal 4609. No outside edge enters
an interior comparison instruction.

Its exact CFG is:

    4598: R6++                  -> 4599
    4599: dec R6                -> zero 4605, positive 4600
    4600: dec R5                -> zero 4602, positive 4601
    4601: jump                  -> 4599
    4602: R5++                  -> 4603
    4603: dec R6                -> zero 4605, positive 4604
    4604: jump                  -> 4602
    4605: dec R5                -> zero 4609, positive 4606
    4606: dec R5                -> zero 4608, positive 4607
    4607: jump                  -> 4606
    4608: jump                  -> 4610
    4609: HALT

Assume entry `R6=0` and put `n=R5`.

- n=0: the first R6 decrement leaves zero; the zero R5 branch temporarily
  increments R5 to one, the 4603 zero branch leaves R6 unchanged, and 4605
  consumes that one. The clear loop immediately exits. Normal return
  after 8 primitive steps, with R5=R6=0.
- n=1: the first two positive decrements leave R6=R5=0. The next R6
  test takes its zero edge, and the R5 test reaches CH. Halt after
  7 primitive steps including CH, with R5=R6=0.
- n>=2: the first positive R5 decrement leaves n-1, and the test at
  4605 leaves n-2. The clear loop at 4606 consumes the remaining n-2,
  then exits. Normal return after `2n+4` steps, with R5=R6=0.

The clear-loop proof is induction on its natural input k. At k=0, the
decrement takes the zero exit in one step. At k+1, one decrement and one
jump reduce to the k case. Hence it terminates after `2k+1` steps and
preserves every other register. This establishes the n>=2 case for every
natural n, not only sampled values.

The replacement tree is exactly

    (CD5, ((CD5, ((CD5, CC1), CB1)), CH)).

Its six-leaf CFG has first test `zero -> exit`, second test
`zero -> CH`, followed on two successes by the same clear-loop shape and
a jump over CH. Thus n=0 returns in one step, n=1 halts in three steps
including CH, and n>=2 returns in `2n` steps. At every terminal or normal
outcome R5=R6=0 and all other registers equal their entry values.

The precondition is essential. The checker includes a negative control:
at entry R5=2,R6=1, the original comparison halts and the replacement
returns. This is not an unrestricted all-register equivalence.

### Whole-program stuttering argument

Compare configurations only at retained outside ordinals and at the
comparison entry, with equal nine-register vectors and the old reachable
invariant. Outside the interval, the checker verifies every operation and
successor against the exact ordinal map (subtract six after the interval).
At the interval entry, the just-proved total local contract gives matching
normal exits or matching halts.

Induct over these matched boundaries. The old seed invariant supplies R6=0
at each comparison entry, not just its first occurrence. All internal
comparison blocks terminate after a positive finite number of steps;
their bounds may depend on n but exist for every entry valuation. Thus
neither execution can remain forever in an unmatched internal block,
and no unaccounted intermediate halt exists. If the boundary sequence is
infinite, both primitive executions are infinite. If either halts, the
corresponding matched block on the other side halts. This establishes
both directions of halting equivalence from either certified seed.

One must not assume the old invariant automatically holds at every new
interior ordinal. The relation deliberately uses old reachable states
only at matched boundaries; the local proof handles new interiors.

## 4. Reachable no-op quotients

The interval `[4603,4605)` contains a reachable zero-branch decrement of
R6 followed by an unreachable jump. The interval `[4718,4721)` contains a
reachable zero-branch decrement of R1 followed by two unreachable
instructions. Each reachable removed segment changes no register, has
length exactly one and reaches a retained ordinal. It cannot halt or
support an infinite removed-only run.

The independent checker reconstructs all three proposed deleted-source
graphs and verifies the exact quotient: each retained operation is
unchanged and each successor is the old successor followed through the
removed zero branch. The entry remains ordinal 0 and the halt is retained.
The same matched-boundary induction therefore proves two-way
seed-restricted stuttering equivalence.

The whole-test replacement already removes 4603–4604; those two leaves
cannot be counted as an additional saving. The independent 4718–4720
cleanup may compose with it. A literal combined source must still have
its mapped CFG checked; after the test replacement, the old cleanup
entry's ordinal is 4712 rather than 4718.

## 5. Reproduction and remaining obligations

Run:

    python -B research_sub221/specialization_audit/check_specializations.py
    python -B research_sub221/specialization_audit/check_shortened_boot.py

Outputs:

- `audit.json`: source binding, two invariant closures, exact specialized
  CFG, no-op quotients and the essential-precondition negative control.
- `inductive_facts.json`: the complete two-seed invariants.
- `shortened_boot_audit.json`: exact finite startup support and decoding.
- `uniform_reflexivity_dependency.json`: freshly replayed inherited
  symbolic-label proof receipt, with its unchanged dependency scope.

Promotion of any <=220-state candidate still requires:

1. The exact new source's source-semantic binding, including every later
   reassociation and combined specialization.
2. Candidate-specific decoder allocation and primitive runtime simulation,
   over every required register/guard/frame case.
3. Exact blank startup for that candidate, rather than importing this
   startup endpoint after changing decoder/source layout.
4. Verification that the actual startup seed satisfies the applicable
   source invariant and soundness/completeness conditions.

The current shortened-scanner runtime failure is a real unresolved
obligation, not cured merely by the admissibility of its alternative seed.
