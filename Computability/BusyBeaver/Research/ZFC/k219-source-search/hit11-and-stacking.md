# Hit11 cleanup and membership/equality stacking

The84 measured combinations do not improve the205-node best membership
source. Equality hits10 and11 retain each parent's DAG count; each of
hits0/1/2/3/12 adds one. This is a source result only. Every membership-based
calculus still has an **open consistency calibration**, independently of
the exact equality equivalence below.

## All-natural hit11 contract

Use the source-pair conventions in [proof.md](proof.md). Let

```
Z' = (dec5, inc6)
P  = (dec6, continue2)
U  = (P, break1)
R' = (Z', U).
```

At entry to R' put `(a,b)=(register5,register6)`.

* If a>0, Z' leaves `(a-1,b+1)` normally. U decrements6, necessarily taking
  its positive branch, and returns continue1. R' catches that continue and
  repeats with `(a-1,b)`. This iteration has four primitive steps.
* If a=0 and b>0, Z' returns normally with `(0,b)`. U decrements6 and returns
  continue1, repeating R' with `(0,b-1)`. This iteration has three steps.
* If a=b=0, Z' returns normally without changing either counter. The zero
  decrement inside P returns normally, after which U emits break1. R'
  returns that break unchanged, with both counters zero, after three steps.

These cases give a lexicographic descent on natural `(a,b)` at loop entries.
More explicitly there are exactly a first-kind iterations, then b
second-kind iterations and one final exit, totaling `4*a+3*b+3` primitive
steps. Every other register is untouched. Thus R' is total, clears5/6 and
always returns break1 for **every natural input pair**.

Delivered hit11 is exactly `(L,R')`, where L is the unchanged left child of
accepted hit10. Accepted L returns break1 with both counters zero on equal
inputs; otherwise it returns normally. The outer pair consumes L's equality
break and returns normally. On inequality it executes R' and returns
break1 with both counters zero. Therefore hit11 has exactly hit10's clean
all-natural equality contract, in arbitrary surrounding source contexts.
No side condition about zero scratch registers, standard bounds, or reachable
states is used.

The [finite diagnostic](results/hit11-diagnostic.json) checks the literal
cleanup and full macro on194 pairs including selected inputs10000, with
nonzero unrelated registers. It also checks the exact cleanup step formula.
This is a diagnostic of the transcription, not the reason the theorem holds.

## Exact84-source measurement

The twelve parents are the committed
[membership-protected sources](../k219-pivot-fusion/results/membership-protected/).
Their only source splice changes the old fourth-field read, before the four
literal accepted equality macros. For each parent the script replaces all
four macros uniformly by each of0/1/2/3/12/10/11. Hit10 is an identity
control. Both complete CFG resolvers agree for all84 outputs, including every
guarded successor and root restart; no whole-word equality across different
macro implementations is assumed.

| Membership parent | Hits0/1/2/3/12 | Hits10/11 |
| --- | ---: | ---: |
| RAB-left | 206 | 205 |
| RAB-right | 208 | 207 |
| RAC-left | 207 | 206 |
| RAC-right | 208 | 207 |
| RBA-left | 208 | 207 |
| RBA-right | 207 | 206 |
| RBC-left | 206 | 205 |
| RBC-right | 208 | 207 |
| RCA-left | 208 | 207 |
| RCA-right | 206 | 205 |
| RCB-left | 208 | 207 |
| RCB-right | 208 | 207 |

All outputs retain maximum depth38 and maximum zero-run6. Hits2/10/11 have
4791 leaves; hits0/1/3/12 have4795. The six best outputs are
RAB-left/RBC-left/RCA-right with hit10 or11. These are distinct source
encodings, not verified205-state or<=218-state machines.

The [result](results/membership-equality-stack.json) pins every input and
output. [All84 exact sources](results/membership-equality-sources.tar.gz) are
preserved; extraction writes only `NAME/sites.json` members. Reproduce into
a fresh directory with:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k219-source-search/stack_membership.py \
  --output /tmp/k219-stack-fresh
```

The script uses only this packet's source model and the standard library. It
does not invoke a compiler, binary runtime checker or proof assistant. A
valid equality substitution cannot establish the membership restriction's
consistency calibration, and a smaller source DAG does not imply a smaller
physical decoder.
