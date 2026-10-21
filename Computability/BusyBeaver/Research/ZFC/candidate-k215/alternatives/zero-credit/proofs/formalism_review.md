# Independent mathematical review of ZC215 and the synchronizer

## Scope

This review checks the ordinary mathematical source calibration and the
new abstract scheduler arguments. It is not a new proof-assistant
endpoint, a rerun of the quantified binary checker, or a claim of a
214-state machine. The exact runtime and blank frame are separate
premises, supplied by the other verification artifacts.

Reviewed ZC215 inputs:

- Source SHA-256: `5f2df4a6c25098d27b20b744b5f8ab3db6ebc8a37e1f01a9abdafc035297563f`.
- Native table SHA-256: `fd9571a0d9bd7a01ab141585e79e956a0a029a608afa8b1ca421e6c4dddbdb47`.
- Native start 74; dispatcher 84; halt 254; 215 working states.
- Claimed full runtime: 6,177 cases, 1,698,860 symbolic rules.
- Exact startup: 117,004 binary steps, dispatcher 84, head -4,
  header 80, gap 20, logical registers `[1,0,5,0,0,0,0,0,0]`.

## Refill and source correspondence

The source retains the accepted DROP0/NIP1/MP2/AX>=3 command bodies.
I independently inspected the source CFG for its initial 26 primitives.
The added ordinal-9 CB1 returns to ordinal 0, rather than to the field
reader or selector. The two refill loops copy an old counter n into the
residual and scratch, then restore the counter as n+1 and clear scratch.
The added return causes the root to decrement that copied residual.
For n>0, the reader therefore receives n-1; n=0 performs one additional
refill and then reads 0. The actual counter-1 seed launches precisely
0,1,2,..., while positive within-candidate continuations retain the
existing predecessor convention.

This conclusion is also supported by the independent interval-CFG audit
in `audit_cb120.py`, which checks every transported primitive and edge,
and isolates the extra CB1 edge. It does not rely on matching source
subtree counts alone.

## Strong compiler

I checked the inherited command equations and the displayed strong-block
constructions in `candidate-k216/alternatives/permuted/proof.md`.
The contract is universal in natural incoming top and buried stack:
starting from `(t,w,0,0)`, a block for X either halts early or returns
exactly `(X,w,0,0)`.

The checks include:

- DISCARD: MP(1) necessarily fails against cache zero, because
  I(t,1)>0. Its gated AX produces top zero and ten nonfalsity entries;
  ten NIPs restore the original stack and cache zero.
- J(0) is empty. Treating it as MP(0) would incorrectly add a truth head
  through the genuine alias I(0,0)=0.
- The row selectors' NIP/DROP counts return the chosen row while
  restoring the exact original stack; the dominated-row offset is
  permitted because U<=A.
- The generalization block puts X into the old cache, uses offset i,
  and selects exactly Q_i(X), with the original stack restored.
- The modus-ponens block puts X into top and I(X,Y) into cache, so MP(Y)
  succeeds, including X=Y=0. Its cleanup returns Y or halts early when
  a tested formula is 1. The deliberately pushed zero is accounted for.

These are command equations independent of command tag values. The new
refill changes only which raw candidates are fetched. It therefore
preserves the strong derivation compiler. The unchanged raw/continuation
encoding yields cofinally many successful candidates from any retained
tuple after an initial resetting AX. Since the new scheduler visits all
raw numbers, a native refutation forces a halt.

## Soundness above an entirely opaque stack tail

The initial top, offset and cache are zero, but the stack is 5. No
theoremhood assertion about any decoding of 5 is needed.

The supplied diagonal proof in `cb120_credit_review.md` is valid: its
pullback-prefix argument uses only earlier candidate indices, its first
six words have nonnegative prefix balance, and its final MP/NIP/DROP
estimates hold at every prefix of each relevant candidate. Thus it
already proves zero initial debt when AX is credited with ten heads.

A stronger independent argument is given in `tag_lowering_credit.md`:
each NIP occurrence is injectively paired with a DROP occurrence in an
earlier raw candidate by lowering only its tag from 1 to 0. Strict
Cantor monotonicity and the commands' equal field arity prove the
pairing, including code zero. Consequently every command prefix has at
least as many DROP commands as NIP commands, even when AX is credited
with zero heads. Every NIP therefore pops an explicitly generated
theorem head and never enters the initial tail. This closes the actual
seed's soundness direction with zero protected heads.

Combined with the inherited numerical-calculus calibration, these
arguments give the ordinary source equivalence to ZFC refutability.
The fresh arbitrary-value runtime and full blank-frame audit then bind
that source theorem to the exact 215-state binary table. No unconditional
nonhalting is asserted.

## Review of the seven-shift synchronizer

I separately checked `seven_shift_synchronizer.md` as an abstract theorem
for its stated scratch-biased parser. Its proof is valid:

1. The delayed recurrence uses the previous candidate's ending bit. The
   forced-hit lemma covers both possible ways to enter the relevant
   three-bit interval and does not assume every candidate is visited.
2. F(x)=P(0,1+x) satisfies F(x)+1=P(x+2,0) and F(x)-1=P(1,x).
   Three right projections of F^3(z)-j produce z+3-j for z>2 and
   j in {3,4,5}. The resulting seven-shift pattern is exactly 110.
3. For q>5, the AX wrapper preserves the three ending bits at offsets
   -5,-4,-3: each of its three right projections lowers the preserved
   residual by the same offset. Its selector remains an AX selector.
4. Varying the wrapper's natural payload makes forced-hit candidates
   cofinal. An inner resetting AX restores the hypotheses of the
   inherited strong refutation block after the seven shifts.
5. Appending terminal S^3 avoids the raw-zero suffix exception after MP
   or AX. Its last S has raw code zero, its predecessor S uses positive
   residual one, and all earlier suffixes are positive.

**Critical scope:** the historical delivered scratch-biased table does
not implement those abstract equations. Its inserted CC3 returns to the
selector rather than the scheduler root. The synchronizer must be
presented as a reusable abstract compiler theorem, not a calibration of
that historical table or an additional 215-state consistency machine.

## Material difference

The proposed table is not obtained by relabeling an accepted table: its
refill control and spare-writing transition change, its start is 74,
and the exact initialized source frame changes. The accepted ordinary
calibration beginning at counter 4 with a clean theorem stack cannot be
applied directly to its counter-1, opaque-stack-5 frame. The new
zero-debt theorem is the mathematical reason this composition is safe.
The stronger tag-lowering formulation explains a reusable design
principle: exhaustive enumeration from zero can supply each pop with
an earlier syntactically matched push, eliminating an initial protected
reserve. Finite novelty comparison against 67 available tables is
supporting evidence only; it is not a universal uniqueness theorem.

**Review result:** ordinary source calibration passes, with the physical
runtime and exact blank-frame verification retained as explicit separate
premises. The seven-shift theorem passes only in its abstract scope.
