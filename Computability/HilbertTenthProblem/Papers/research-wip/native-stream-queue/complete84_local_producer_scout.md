# Complete84 local producer scout: a bounded paid-graph obstruction

No smaller complete source was found in the specific grammar below. This is
not a global arithmetic lower bound and does not exclude a larger joint-norm
identity, a later-register rewrite, or a sound nonlinear coordinate change.

The [new helper](complete84_local_producer_scout.py) reads the following
complete parent trio as pinned data; no predecessor Python or historical
suite executes. Its [receipt](complete84_local_producer_scout.json) retains
the entire unchanged parent packet, including all source rows, free ports,
witnesses, factor names, finalizer and inherited degree metadata.

| Parent file | SHA256 |
|---|---|
| [complete84_scaled_strong_output.py](complete84_scaled_strong_output.py) | `8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737` |
| [complete84_scaled_strong_output.json](complete84_scaled_strong_output.json) | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` |
| [complete84_scaled_strong_output.md](complete84_scaled_strong_output.md) | `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade` |

All 84 gates and 25 supplied ports are live. The paid source is
84=47M+37A with 18 positive witnesses. Its exact degree is inherited with
the identical source; this packet makes no new degree argument.

## Exact local costs and consumers

Write c=R10a, R=r_lhs, T=auxiliary_quotient, S=aux_coefficient_root.
The existing f² and S² registers remain live in the scaled strong factor.
All quantities in the following identities are arbitrary ring elements.

| Complete local expression | Additional M | Additional A | Difference |
|---|---:|---:|---:|
| Existing V=c(Tf-1)-Rf², with existing f² | 3 | 2 | baseline |
| V=f(cT-Rf)-c, retaining existing f² for strong | 3 | 2 | tie |
| Existing Na=S²(V²-y²)+y², with existing S² | 3 | 2 | baseline |
| Na=y²-S²(y-V)(y+V), with existing S² | 3 | 3 | +1A |
| Na=(SV)²-(S²-1)y², with existing S² | 4 | 2 | +1M |

The first equality is ordinary distribution; the next two follow by expanding
the difference of squares. They do not require zero-set or positivity premises.
None suppresses the f² or S² consumer in `norm_strong`.

Likewise `gap=(q-1)(q-F)+(q-F-Z)` equals `q(q-F)-Z` and costs 1M+1A
in either arrangement. The apparent saving from deleting `q_minus_FZ` is
unavailable: the original positive outer bound still consumes it in
`C_after_alpha`. This is an actual retained consumer, not a metadata obligation.

On main-norm-one zeros, Delta*c²=Dmain²-1, but Delta*c² remains required
by the main norm itself. Replacing only its auxiliary consumer adds a
subtraction; deleting its old producer would delete the retained main
constraint. Thus this proposed use of the main equation yields no saving.

## Exhaustive bounded graph search

The helper builds three exact finite-field evaluations of the entire literal circuit. For each of the 70
producer targets other than `norm_*`, `all_units`, `seven_units` and
`polynomial`, it enumerates:

- every zero-operation alias to an allowed leaf;
- every one-operation expression op(a,b);
- every two-operation expression op(a,op(b,c)) or op(op(b,c),a);
- every two-operation DAG op(v,v), where the new temporary v=op(a,b);
- op in addition, subtraction or multiplication;
- each leaf any original free port, constant 0,1,2,3,4, or strictly earlier
  original register.

Commutative inner operations identify only operand-order duplicates. All
matching expression witnesses are retained, even if multiple expressions have
the same evaluation. Outer multiplication uses field inversion only when the
outer operand is nonzero; the helper explicitly rejects a run if a degenerate
zero bucket could hide a matching expression. No such bucket occurs here.
For every matching schedule, the helper replaces that producer and recomputes
backward liveness from the full original polynomial output. Cost is the number
of surviving binary operations, including the finalizer. It does not compare
isolated expressions while ignoring their other consumers.

Results: 4,741 alias tests and zero alias matches; 719,027 inner binary
expressions; 70 matching one-operation schedules and 994 matching two-operation
schedules (939 tree schedules plus 55 schedules reusing the new temporary). **Zero schedules have fewer than 84 live operations.** Every target
has minimum matching cost 84. The original gate is among its one-operation
matches. The receipt records each target's counts and minimum, all three
moduli, the fixed random seed, and the resulting free-port evaluations.

An alias substitutes the earlier port into every later consumer and deletes
the target definition before liveness is recomputed. It is not represented as
an uncharged arithmetic gate. Seventy zero outer-multiplicand choices are
rejected by a nonzero target evaluation, so none needs inversion. A degenerate
multiplication bucket that might contain a match would explicitly fail this
helper instead of being silently skipped.

The finite-field evaluations are rejection filters, not proofs of an identity.
A true polynomial identity over all 25 free ports must survive every one of
these evaluations, so rejection is sound within the declared grammar. Hash
collisions are not used. Additional matches could only enlarge the set checked
for a cost reduction. Since none has lower cost, there is no unproved positive
candidate to promote. This statement does not cover identities that hold only
on valid fixed-numeral recipes or only on positive zeros.

## Replay and scope

From any working directory, using only Python's standard library:

```sh
producer_wip=/absolute/path/native-stream-queue
python3 "$producer_wip/complete84_local_producer_scout.py" \
  --root "$producer_wip" \
  --expect "$producer_wip/complete84_local_producer_scout.json"
python3 -O "$producer_wip/complete84_local_producer_scout.py" \
  --root "$producer_wip" \
  --expect "$producer_wip/complete84_local_producer_scout.json"
```

`--root` is required, as is exactly one of `--expect FILE` or `--output FILE`.
The helper authenticates all three parent files before parsing the source
receipt and checks its recorded self-source hash. It rejects duplicate JSON
keys and nonfinite JSON numbers; receipt equality recursively distinguishes
integers, Booleans, floats, lists and dictionaries. Every required check uses
explicit exceptions, so optimized Python does not disable it.

Writer and fresh normal/optimized exact replays from `/` pass. Focused negative
checks reject one duplicate-key input, three nonfinite-number inputs and a
missing pinned parent; two recursive type comparisons distinguish true from
one and 1.0 from one. These are bounded CLI and receipt checks, not a broad
hostile-input compiler API audit.

The search makes no simultaneous multi-target replacement and does not use
later original registers or new supplied coordinates. It searches identities
over all free ports, not equations valid only on the positive zero set or
under special fixed compiler numerals. A future larger algebraic identity can
therefore lie outside this result. No exact expansion of the surviving
fingerprint matches is needed for the negative conclusion: none lowers cost,
even when every such match is provisionally allowed.

This result changes no frozen source or arithmetic frontier.
