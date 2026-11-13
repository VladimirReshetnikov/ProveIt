# A source shortcut for `copyH; cons`

Starting from the experimental [combined negation/MP source](../negation-mp197/README.md),
this replacement removes **105 source instructions**: five identical 53-site
blocks become 32-site blocks. The resulting source has 3,468 sites but **no
new tape table has been constructed**. Its source DAG grows from 159 to 164
internal nodes, so the instruction reduction does not demonstrate a state
reduction. The new source has not been proved equivalent to `Con(PA)` in PA.

Write `T=r1`, `W=r2`, `H=r5`, `S=r6`, and `R=r7`. For any natural inputs
`t,w,h,s`, when `R=0` on entry, the original and replacement blocks have the
same effect on the complete register file:

```
(T,W,H,S,R) = (t,w,h,s,0)
       becomes (4*pair(t+s,h), w, h, 0, 0).
```

All other registers are unchanged. Here `pair(a,b)=triangle(a+b)+b` is the
PA196 Cantor pairing. The source transformation uses five existing closed
fragments, except for one register-renamed drain:

```
drain S into T; drain T into R; copy H into T preserving H using S as scratch;
drain R into S; pair S,T and multiply the result by four.
```

## Mathematical block argument

In the old block, `copyH` first executes `node49`: draining `T` into `S`,
pairing `S` and the old `W`, and storing that pair in `W`. Its result is
`W=pair(t+s,w)` and `T=S=R=0`. Its subsequent `node57` copies `H` into `T`,
restoring `H` and clearing its scratch register. The `cons` block decodes
`W`, restoring `W=w` and `S=t+s`, then computes four times the Cantor pair
of `S` and `T`; it clears `S` and `R`.

In the new block, the first two drains put `t+s` in `R` and clear `T,S`.
The same `node57` copies `H` into `T` and restores `H`; the fourth fragment
moves `R` to `S`. The existing `node64` then executes the same pair-and-times-4
suffix as the old `cons`. Thus both terminate with the displayed register
file. Each drain and copy loop terminates by decreasing the register it drains;
the pairing and decoding loops use the Cantor pair/decoder identities described
in the [independent negation-block audit](../negation-mp197/local-audit/README.md).
This is an ordinary mathematical source argument, not a PA-internal derivation.

The condition `R=0` is necessary. With
`(r0,...,r8)=(7,0,0,3,3,0,0,2,9)`, the old block exits with `(T,W)=(0,1)`
while the replacement exits with `(T,W)=(12,0)`. Neither isolated block may be
substituted unconditionally.

## Exact source context

The five original entry sites are `317, 396, 679, 1435, 1907`. The
[replay](replay.py) recomputes the joint zero/positive closure from the actual
clean source seed; it contains 258,660 site/mask pairs and forces `r7=0` at
all five entries. This is an inductive overapproximation, not a sampled trace.
For each region the script checks the exact local control-flow graph, that
outside edges cannot enter its interior, and that its only outside continuation
is the corresponding exit. It checks all 3,308 outside source rows after
ordinal relocation and compares two independently implemented source-graph
resolvers. Consequently the mathematical block argument and the entry
invariant support preservation of source execution from the seed; they do not
by themselves connect this modified source to a tape machine.

The script also checks the closed-form output on 1,280 finite zero-scratch
inputs and validates the nonzero-scratch counterexample. These finite controls
check the transcription of the argument; they are not a substitute for it.
The exact input and deterministic results are in [receipt.json](receipt.json).

## Allocation experiment and reproduction

From the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/copyh-cons/replay.py --output /tmp/copyh-cons.json --sites /tmp/copyh-cons-sites.json
```

The optional site file uses the existing allocator's format. An exploratory
run of the [restricted allocator](../allocator-screen/README.md) against the
published 196-state native baseline, preserving the 238 startup/core rows and
additional helper requirements, used no fresh labels. It returned `UNKNOWN`
after both 20 and 120 seconds; the 120-second run had 57 new source nodes,
107 fixed nodes, and 252 protected rows after helper expansion. `UNKNOWN` is a
timeout, not a proof of impossibility or evidence of a smaller machine.
With `z3-solver==4.15.8.0` installed, reproduce the 120-second search with:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/allocator-screen/allocate_current.py /tmp/copyh-cons-sites.json /tmp/copyh-cons-allocation --protected Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/startup-preserving/protected-startup.txt --seconds 120 --feasible-only --fresh 0
```

Solver behavior may vary by host. A future allocation must still pass a complete
arbitrary-value primitive-runtime check, exact blank startup, and PA-internal
source/command and literal-trace transport before the resulting machine can
satisfy the goal.
