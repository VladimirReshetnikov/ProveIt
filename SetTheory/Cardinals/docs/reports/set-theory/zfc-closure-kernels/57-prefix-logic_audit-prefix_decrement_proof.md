# Prefix-right decrement: unbounded tape lemma and composition audit

## Scope and status

This note gives an ordinary mathematical proof of the new positive-decrement
register excursion, audits the symbolic rules used for the whole runtime,
and states the exact imported logical lemmas needed for the consistency
endpoint. The proof applies to the literal old-label table
`bootstrap/prefix_rebased252.tm`, SHA-256

```
b91dc16e60c26780a3006072347c15ea058fa0fab6c0b4b5493967cab11c6234
```

The table has 252 working states, starts in old state 64, and halts in old
state 254. Its canonical relabeling has start 0 and halt 252. This note does
not claim fewer than 252 states. No new Lean or Coq build has been performed
for the changed table, changed oracle, or composed endpoint.

Three of the four original register excursions are inherited from the
pinned source. The positive-decrement excursion is changed and is proved
below. The new lemma has an explicit left-context premise that the original
positive-decrement lemma did not require. The affine checker verifies that
premise at every use. It would be incorrect to describe this audit as using
four unchanged `Box.v` contracts.

## 1. Tape and zipper conventions

For a finite register list `v`, define

```
R(v) = concat_r [0, 1^(v_r+1)].
```

There are exactly nine logical registers in the source program. The physical
ordering used here is

```
old physical -> new physical: (7,8,4,2,5,6,0,3,1),
logical -> physical:          (0,3,7,4,8,1,5,2,6).
```

The logical order is `(N,T,S,A,d,H,X,Y,L)`. Each physical block has a leading
zero and a nonempty run of ones. Marking block `r` erases its first one, so
for a split `v = pre ++ [w] ++ rest` with `length(pre)=r`,

```
M_r(v) = R(pre) ++ [0,0] ++ 1^w ++ R(rest).
```

A zipper `zc(q,l,r)` has the head on the first bit of `r`; `l` is read from
nearest to furthest left. A zipper `zl(q,l,r)` has the head on the first bit
of `l`. Bits beyond the finite displayed lists are zero. These conventions
specify the entire two-sided tape relative to the head, not just a local
window.

The command-boundary frame is

```
state 96; left=[1]; right=PC ++ 0^(D-|PC|) ++ [1] ++ R(v),
```

with `D>=43`. The marker is immediately left of the PC, the following one
after its zero padding is the header, and `R(v)` begins immediately after
that header. There is no spare-block suffix in the verified blank-start
invariant. All other tape cells are zero.

## 2. The exact new positive-decrement lemma

Let `v` be any finite list of at least nine natural numbers, let `r<9`, and
suppose `v_r>0`. Let the left context be

```
l = 1^k ++ [0,0] ++ L,     k>=1,
```

where `L` is arbitrary. The two displayed zeros need not be the entire zero
run. Let `dec_r(v)` decrease precisely register `r` by one, preserving the
length of the register list.

**Lemma.** The changed table has a finite, positive, nonhalting computation

```
zc(43,l,M_r(v))  ->+  zl(e_r,[1]++l,R(dec_r(v))),

e_r = 63 if r=0, otherwise 48.
```

No new register block is appended. The rule's extra leftmost 1 shifts the
abstract boundary of the register file one cell to the right. Later runtime
cleanup turns this into an increase of the header gap by one.

The full statement is independent of the magnitudes of all register values,
of the number and values of any optional extra blocks, and of the length of
the one-run `k`. In particular it is valid for exactly nine blocks and no
extras. The eventual blank-start simulation uses that exact-nine instance.

### Relevant changed rows

The changed positive branch and its leftward search are:

| State | Read0 | Read1 |
|---:|---|---|
| 75 | unchanged zero branch `(0,L,0)` | `(1,L,85)` |
| 85 | `(0,L,85)` | `(1,L,97)` |
| 97 | `(0,L,112)` | `(1,L,97)` |
| 112 | `(0,R,131)` | `(1,L,97)` |
| 131 | `(0,R,95)` | unused by this lemma |

The forward search43/59, the existing right-shift95/109, and the return
scan63/48 retain their required rows:

```
43: 0 -> (0,R,59),  1 -> (1,R,43)
59: 0 -> (0,R,75),  1 -> (1,R,43)
95: 0 -> (1,R,109), 1 -> (1,R,95)
109:0 -> (0,L,63),  1 -> (0,R,95)
63: 0 -> (0,L,48),  1 -> (1,L,63)
48:                  1 -> (1,L,63)
```

The endpoint is reached before the next read of the endpoint state's tape
cell. Thus the lemma does not impose a requirement on state 131/read 1 or
state 48/read 0.

### Proof, stage A: reach and identify the positive mark

Write `v = pre ++ [a+1] ++ rest`. Every plain block in `R(pre)` has a single
leading zero followed by at least one one. States43/59 therefore scan across
that finite prefix without changing it and arrive at the first zero of the
selected mark.

The next three transitions read the selected pattern `0,0,1`: state 43 on
the first zero, state 59 on the second zero, and state 75 on the first one.
The last transition turns left into state 85. It preserves that one. The
positive hypothesis is exactly what supplies this one; no assumption on the
value or existence of a later register is used.

### Proof, stage B: find the prepared left phase delimiter

State85 crosses the two mark zeros leftward and reaches a one immediately
before them. Such a one exists: it is the last one of the preceding register
when `pre` is nonempty, or the first bit of `l` otherwise.

State97 scans left across ones. On an isolated zero it moves left to112;
when the next bit is one,112 returns to97 and the search continues. Since
`R(pre)` has no adjacent zeros, this crosses precisely the plain register
prefix. It then crosses the `1^k` in `l`. The first encountered pair of
adjacent zeros is the displayed phase delimiter.

On that pair,97 reads its right zero and112 reads its left zero. The two
rightward transitions112/read 0 and131/read 0 put state 95 on the first one
immediately to the right of the pair. Nothing in this search changes the
tape. The arbitrary older context `L` is not visited.

Consequently the finite tape word now in front of state 95 is

```
1^k ++ R(pre) ++ [0,0] ++ 1^(a+1) ++ R(rest).
```

### Proof, stage C: shift the register prefix right

The following elementary right-shift fact is proved by induction on `pre`.
Starting in state 95 at

```
1^b ++ R(pre) ++ [0,0] ++ Y,
```

the 95/109 loop changes that displayed word to

```
1^(b+1) ++ R(pre) ++ [0] ++ Y,
```

and stops in state 63 on the one immediately before the remaining zero. All
tape before the displayed word and all of `Y` are unchanged. The lemma is
valid for `b=0` as well as positive `b`.

For empty `pre`,95 scans the `b` ones, writes 1 over the first of the two
zeros, and109 reads the second zero, preserves it, and turns left into63.
For `pre = [c] ++ tail`,95 writes 1 over the block's separator;109 writes 0
over its first one; and95 then faces `1^c ++ R(tail) ++ [0,0] ++ Y`.
The induction hypothesis performs the remaining shift. This establishes
the stated word equation and exact stopping position. Every scan is finite.

Apply this fact with `b=k` and
`Y=1^(a+1) ++ R(rest)`. The resulting tape is

```
1^(k+1) ++ R(pre) ++ [0] ++ 1^(a+1) ++ R(rest).
```

The selected ordinary block now has `a+1` ones and therefore value `a`.
It has been decremented exactly once. The preceding register blocks have
the same values and have shifted right by one cell. The selected block's
remaining ones and the entire later suffix retain their original physical
positions. No scan to the right end of the file occurred, so no end marker
or extra block was manufactured.

### Proof, stage D: return to the new boundary

If `pre` is empty, state 63 is already on the newly added one just left of
the new file boundary. This is exactly the stated `zl(63,1::l,...)` endpoint.

If `pre` is nonempty, the original63/48 return scan traverses those preceding
plain blocks leftward. It stops in state 48 on the same newly added boundary
one. The register word at its right is exactly `R(dec_r(v))`. This gives
`zl(48,1::l,...)` as claimed. The preceding phase word and older tape are
unchanged. The forward detection took three literal transitions, so the
whole excursion has strictly positive length. QED.

### Why the left-context premise is necessary

The stronger statement with arbitrary `l` is false. For example take
`l=[1,0,1,0,0,1]`, select physical register 0 of `[1,0,0,0,0,0,0,0,0]`, and
start the file at coordinate 0. A literal 16-step run reaches state 63 with
head 0, but it has moved an isolated separator in the old left context:
relative to the incorrectly claimed target there is an extra one at -2 and
a missing one at -1. The prepared phase requirement prevents this behavior.

## 3. The three inherited box lemmas

The original `box_mark`, `box_inc`, and `box_dec0` apply unchanged. Inspection
of their source proofs shows that all transitions they use retain their
required values:

* Marking uses the nine skip states, state 0/read 1, and the 2/4/6 return scan.
* Increment uses73/83,95/109, and63/48.
* Zero decrement uses43/59,75/read 0,0/read 0, and1/3. Its endpoint is reached
  before state 3/read 0 is consulted.

The modified rows in 85/97/112/131 and 75/read 1 belong to the old positive
branch. Their inclusion in the older union of 55 protected transition pairs
does not mean the other three box proofs need them. One must import the
individual lemmas with their actual transition dependencies, rather than
assert that the old 55-pair union is unchanged.

These three lemmas require a finite file of length at least nine. They do
not require an additional spare register. Increment may shift the later
blocks into previously blank tape, preserving the number of blocks. Zero
decrement on the final zero block uses the available blank zeros beyond the
file and returns the same file. Marking preserves its length.

## 4. What the affine checker verifies

The checker represents a whole tape zipper by literal bit segments, runs
of `a*n+c` identical bits, and one final opaque register-box segment. All
coefficients and constants are nonnegative and `n>=0` is arbitrary. The
register box is universally quantified over the entire register list;
its values are not bounded numerical samples.

For this machine, the box-state meanings are:

```
plain(None):   R(v)
mark(r):      M_r(v)
plain(inc,r):  R(inc_r(v))
plain(dec,r):  R(dec_r(v))
```

The last line deliberately has **no appended zero block**. The new positive
oracle also prepends 1 to the left zipper. Those two coordinated changes are
the denotation of the lemma in section 2.

The ordinary soundness proof for each symbolic rule is direct:

1. A literal bit step is exactly the selected binary transition.
2. A same-state scan over a run is that transition repeated exactly
   `a*n+c` times, including the possibility of zero repetitions.
3. Peeling a cell requires a positive constant part, so it is valid for
   every `n>=0`. Empty-segment removal and head recentering only change the
   zipper representation.
4. Reading the box's first bit is permitted literally only when that known
   zero is preserved and the head moves left. Every box begins with zero.
5. A box excursion uses one of the four mathematical lemmas just specified.
   Marking is permitted only before any effect; decrement requires the
   guard to name the same selected register; no second mark is allowed
   after an increment or decrement effect.
6. At every positive-decrement oracle, `assert_prefix_phase(left)` checks
   that the canonical left zipper begins with `(1,a,c)` with `c>=1`, followed
   by `(0,a',c')` with `c'>=2`. This implies the section 2 phase premise for
   every `n>=0`.

The checker stops a nonhalting case only at state 96 with the **entire**
canonical left and right target equal: PC, gap, header, register effect,
and exterior blanks. Intermediate visits to96 are not accepted by
themselves. Canonicalization merges equal-bit runs and discards only
irrelevant zeros at the far left. It does not discard unexamined PC bits or
register effects. Since positive progress is counted only on literal
transitions, a zero-length affine scan cannot falsely certify progress.

Each accepted finite symbolic run therefore denotes a valid finite binary
run for every permitted gap and every complete register valuation. This is
an ordinary rule-by-rule argument; the modified Python checker has not
itself been newly proved sound in a proof assistant.

### Independent complete replay

`audit_prefix_phase.py` independently replays the complete materialized
best-permutation case inventory, instrumenting every positive oracle with
the pure phase assertion. The result in `prefix-phase-verification.json` is:

| Property | Result |
|---|---:|
| Guarded instruction cases | 8,366 |
| Positive-decrement phase checks | 1,925 |
| Halting instruction cases | 1 |
| Maximum consumed PC length | 34 |
| Minimum literal progress in any case | 13 |
| Minimum one-run constant before each positive oracle | 9 |
| Minimum following zero-run length | 3 |

Every leading one-run has coefficient 1 in `n`; every immediately following
zero-run has coefficient 0. Thus the required one-run and two-zero phase
conditions hold with margin even when `n=0`. The replay checks all nine
registers through their named symbolic guards; it does not substitute a
single register valuation or a fixed small tape window.

The source inventory contains 6,441 leaves. The extra 1,925 cases split every
conditional decrement into its zero and positive branches. Root's
`verify_prefix_rebased.py` separately regenerates this inventory from the
modified literal source tree, rather than trusting only the materialized
case file used by the independent replay. It also re-decodes all 8,365
nonhalting canonical successor PCs in that tree, checking that every bit
beyond the consumed leaf prefix is zero. This includes three overflow
cases. The recorded run passes all of these checks.

## 5. Exactly nine blocks is a closed runtime invariant

For a successful increment the register list changes to `inc_r(v)` and
keeps its length. For zero decrement it is unchanged. For positive
decrement the new lemma returns `dec_r(v)`, again with the same length.
Marking is temporary and has no length effect. All control instructions
have the plain unchanged box target.

Induction on completed source instructions therefore proves that an
initial file of exactly nine blocks remains exactly nine blocks forever,
until halting. No operation requires or creates a tenth block. This does
not bound the active tape width: the nine unary values and the gap can be
arbitrarily large.

If `epsilon` is 1 for positive decrement and 0 otherwise, and `overflow` is1
when the PC carry moves the marker left, the new frame gap is

```
D' = D + epsilon + overflow.
```

It never decreases, so `D>=43` is preserved. Only the first nine physical
blocks are selected, by the fixed permutation. The minimum gap exceeds the
maximum consumed PC length 34, and the full affine checks cover all
intermediate interpreter phases.

## 6. Exact startup

The independent sparse-tape replay in `prefix-blank-independent.json`
executes the literal table from blank state 64 for exactly 25,612 steps and
checks full tape equality. The endpoint is:

```
state 96, head 4, root PC, gap 43,
all nine logical and physical registers zero,
no extra blocks,
ones exactly at {3,47,49,51,53,55,57,59,61,63,65},
all other cells zero.
```

Thus the initial command-boundary soundness condition is immediate: current
formula, theorem stack, and cached theorem are all truth 0; both scratch
registers and both candidate-enumeration registers are zero. No unsafe
cached falsity or buried stack value needs a recovery argument for this
startup. The state renumbering to the canonical table is a finite bijection
and preserves every transition and blank computation.

## 7. Composition with the source program and prior ZFC calibration

The engine modification leaves the arithmetic instruction effects and
control successors equal to those of the successful-MP0 source program.
Positive decrement changes the tape representation by growing the gap
instead of appending a spare, but its selected numerical register still
decreases by exactly one. The 8,366 complete affine cases establish the
corresponding per-site runtime statements, subject to the four proved or
imported box lemmas above.

The usual source-PC glue is also needed: a canonical successor must decode
to its source leaf with no nonzero stray suffix; the structured tree and
its break/continue levels must be well formed; and the MP0 modified tree
must implement the stated source command semantics. These are finite
control/structural obligations, not consequences of a table's state count.
The successor-PC check above supplies the no-stray condition for this
modified tree. The MP0 route retains the repository's known specific
success-branch edit and source comparison. The new independent
`bootstrap/verify_mp_source_certificate.py` replays its regenerated
2,998-pair relation, checking the initial pair and all 5,994 nonhalting
successor edges. Each compared straight-line segment has the same finite
register increment multiset, and each related endpoint has the same
conditional-decrement register or the same halt instruction. Thus induction
on these segments proves equality of all register values and corresponding
source halting behavior. This is a fresh executable replay of a prior
certificate construction, not a new kernel-checked source proof. The
companion
`destructive_axiom_theorem.md` supplies explicit command blocks for the
unchanged AX with MP0, including the all-zero candidate-counter case.

Once these exact source ingredients are composed, every nonhalting source
step has a finite positive binary implementation and no intervening halt.
The accumulated binary lengths exceed the number of completed source steps.
Determinism therefore gives both directions of the halting equivalence;
an infinite source execution cannot leave an unexplained finite binary
halting time between frames.

The mathematical endpoint uses the following **prior lemma**, not a newly
built formal certificate:

> The original numerical C254 calculus is refutable exactly when the
> repository's literal native first-order theory is refutable, and that
> theory is equiconsistent with ordinary ZFC.

The lemma's source is the pinned ProveIt native-theory, internally
well-founded model, and Choice-calibration development. The new source
proof gives

```
MP0 enumerator from the zero frame halts iff C254 proves falsity 1.
```

Combining it with the changed binary representation and startup gives the
same mathematical consistency equivalence for this 252-state table. To read
the biconditional as a theorem **in ZFC**, reconstruct the cited finite
syntax and computation proofs and the countable set-model comparison in
ZFC as described in `zfc_internal_mathematical_proof.md`. The inherited
external Lean endpoint is not automatically a serialized proof in the
repository's object language of ZFC, and no such serialization is newly
supplied here.

Accordingly, the present deliverable provides an explicit ordinary proof
of the changed unbounded tape lemma, exact finite startup and symbolic-case
checks, and an ordinary composition argument with clearly named prior
logical ingredients. It provides neither a new kernel-checked binary/ZFC
endpoint nor a table below 252 states. The separate, stronger PA
internalization remains outside this result.

## Primary sources

* Original register excursions and their exact zipper contracts:
  [Box.v](https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/coq/tm/Box.v).
* Original symbolic segment denotations and rule soundness:
  [SymExec.v](https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/coq/tm/SymExec.v).
* Existing ProveIt frame and prior-box scope:
  [permutation252_frame.md](https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Research/ZFC/permutation252_frame.md).
* Prior MP0 source edit and comparison:
  [mp_dummy_push_partial_cost.md](https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Research/ZFC/mp_dummy_push_partial_cost.md).
* Prior external ZFC calibration and formalization boundary:
  [choice_calibration254.md](https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Research/ZFC/choice_calibration254.md),
  [binary_zfc252.md](https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Research/ZFC/binary_zfc252.md).
