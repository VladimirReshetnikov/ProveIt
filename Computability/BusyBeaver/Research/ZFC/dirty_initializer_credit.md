The new observation is an ordinary sufficient start family for the complete
original enumerator: a finite safe stack prefix can cover the exact syntactic
DROP-minus-NIP balance skipped by the initial candidate counter. This admits
AX-first roots with dirty top, stack, cache and additive parameter. No new
251-state machine or dirty blank bootstrap was found in this checkpoint.

The source42 argument is attributed to intake155, *A 252-state ZFC consistency
machine and a smaller finite kernel*, arrival
`fab89c5d26b81cd2ccab2ee5d213ff23725c7726`, report input
`61e77836565f63582561f54745f633d50efd9c7d`. The actual original calculus and
enumerator are those of Mira-Cult, Jeff Ketchersid and Andrew James Wade,
upstream `297ab8df7e5de329605c3875b4934643b371a5e3`. The exact-balance
refinement and the finite follow-up below are repository research.

The original command conventions matter. Candidate zero is the one-command
program `MP 0`, not an empty program. Proof-list remainder zero terminates a
candidate; a positive remainder `r` continues with candidate code `r-1`.
The theorem stack uses the unshifted Cantor pair and its zero code is an
infinite zero stream. These are the actual definitions in
[`Enum254.lean`](../../Lean/BusyBeaver/ZFC/Enum254.lean).

Let `B(k)` be the integer number of DROP occurrences minus NIP occurrences
in all decoded candidates strictly below `k`. Source42's marked-occurrence
map replaces a NIP by DROP at the same position. The resulting candidate is
strictly earlier, and the map into marked DROP occurrences is injective.
Consequently, at every syntactic prefix immediately before a NIP, the global
DROP-minus-NIP balance is at least one; at candidate boundaries it is
nonnegative. Every marked image is positive, so omitting candidate zero
removes no image.

Suppose the enumerator starts with `PL=0`, `NP=k`, theorem-valued active
formula and cache, any additive parameter, and a witnessed safe prefix of
length `p >= B(k)` above any dirty stack bottom. At a future pre-NIP prefix,
the available safe depth is at least

```text
p + futureDROP - futureNIP
  >= B(k) + globalBalance - B(k)
  >= 1.
```

DROP pushes one theorem. Successful MP pushes the theorem zero and AX
pushes additional safe entries; these only increase this lower bound.
Thus a nonhalting NIP pops a theorem without reaching the dirty bottom.
Every active formula/cache remains derivable. A halting NIP therefore
certifies `C254 F`. Conversely, the existing enumerator completeness theorem
starts from every state. This gives an ordinary refutation equivalence for
this start family. It does not require that hypothetically skipped
candidates execute without halting: their counts and marked images are
syntactic. All induction statements concern an actually reached prefix.

The checked
[`EnumStackBarrier254.lean`](../../Lean/BusyBeaver/ZFC/EnumStackBarrier254.lean)
currently supplies actual-code decoding, occurrence lowering/injectivity,
candidate-zero reset and local safe-prefix preservation. Its global
scheduling/counting-to-runtime bridge remains open. The displayed argument
and the new family are not yet Lean theorems or an internal PA endpoint.

There is a concrete adapter to actual nine-register roots. Use logical
register order

```text
(N,T,W,A,D,H,X,Y,L) = (NP,TW,WS,AX-selector,parameter,cache,scratch1,scratch2,PL).
```

Assume an actual empty-PC root, `X=Y=L=0`, and `N=n`. The checked absorption
map in
[`DirtyRoot254.lean`](../../Lean/BusyBeaver/ZFC/DirtyRoot254.lean)
first reads `unP(n)=(op,rest)` and executes opcode `A+op`. If `A+op>=3`, this
is AX. Read its three parameter fields `(x,y,u)` from `rest` and require
the remaining proof-list pointer to be zero. The next candidate is `n+1`.
Regardless of old `T,W,D,H`, AX makes the active formula
`gate(D+x,H+y,A+op-3)`, resets `D=H=0`, and puts eight unconditional logical
axiom instances at the top of the stack. Under them lie `All(D+x,oldH)`,
`oldT`, and `oldW`, which may all be dirty. Hence the root is admitted by
the ordinary argument whenever `B(n+1)<=8`. The dirty stack tail is not
required to be zero. The zero requirement concerns the proof-list remainder.

[`dirty_initializer_credit.py`](dirty_initializer_credit.py) independently
checks the command codec with binary-search and square-root inverses,
the marked images and all prefix balances for 100,000 candidates. It finds
161 eligible `n < 100000`, with largest eligible `n=250`; each row records
the minimum AX selector and all three parameter fields. This is a finite
list, not a claim that no larger `n` is eligible. The simpler subfamily
`N=0,A>=3,X=Y=L=0` already allows arbitrary `T,W,D,H`. `NP=1` with an empty
safe prefix is also admitted because `B(1)=0`. Prefix pairing may collapse
zero entries numerically, but a witnessed finite prefix is sufficient;
no injective finite-list interpretation of stack zero is assumed.

The bounded binary diagnostic kept the complete original logic, 252 working
states, all 55 protected box rows and every read-zero row. It replayed the
4,096 previously selected physical-register maps across all seven exact
first-write blank-start classes, with one million literal steps per class.
The root detector required old state96, an empty PC, gap at least40, all
nine primary registers, every spare block and the complete blank exterior.
It accepted source42's zero-counter dirty start or the simpler AX-first
subfamily. Every other structural root would have been counted, allowing a
posthoc check of the stronger credit family.

The result was 27,595 fuel cutoffs, 1,074 halts, and three admitted roots in
191.06 seconds. Exactly three structural roots were encountered before
stopping: all were the known map
`[0,3,4,5,8,1,6,2,7]`, with nine zero primary registers, gap40, and the same
65 spares (only spare8 is one). No other run contained a structural root in
its tested prefix, so the stronger credit classifier adds no hit. All
1,074 early halts, all three positives and 21 fuel controls were independently
replayed in Python: 1,098 final configurations and 52,318,944 literal steps.
The positives match the complete 77-one tape, not just a fingerprint. The
existing hit table's 8,391 affine cases were replayed successfully.

This all-class census is **redundant control evidence** in light of the
earlier source04 234-ray/18-common-orbit classification. An initial progress
message described the extra map/class combinations as new search
opportunities; that novelty claim was withdrawn after rereading the stronger
classification. The new mathematical result here is the balance-credit
family. These finite replays establish no lower bound, global failure of
dirty initialization, or new machine equivalence. They stopped at the known
clean roots rather than following those already valid initialized runs.

There is also no globally unused startup-only row under the retained
universal contracts: tracing all 8,391 cases queries 473 literal rows, and
their union with the 55 protected box rows is all 504 rows. This does not
rule out a phase-sensitive rewrite. It explains why accepting dirty roots
alone does not justify another state deletion; such a deletion still needs
a weaker invariant relating its altered runtime to the original program.

The finite family is reproducible with:

```bash
uv run --no-project python -B Computability/BusyBeaver/Research/ZFC/dirty_initializer_credit.py \
  --output /tmp/dirty-initializer-credit-family.json
```

[`results/dirty-initializer-credit.json`](results/dirty-initializer-credit.json)
preserves the arithmetic output, all three complete root frames, timing,
independent checks and exact scratch source/output identities. The literal
census sources and raw 28,672-row output remain at
`/tmp/zfc-dirty-init-followup/`; they are a diagnostic, not a maintained new
machine generator. No Lean or Coq build, frozen-table edit, or shared-runner
change was performed for this follow-up.

The subsequent checked [`EnumStackCount254`](enum_stack_count254.md) closes the
global counting and scheduler argument for this balance-credit interface on the
actual enumerator. Its `credit_start_iff` accepts a witnessed good stack prefix
of length at least `B(n)`, with good current formula and cache and arbitrary
additive parameter. Its dirty candidate-zero theorem additionally removes the
initial formula/cache premises when `d=0`. Composing a dirty AX root with its
eight unconditional good entries is still a separate interface step; the finite
binary diagnostic above does not acquire a new machine-equivalence theorem.
