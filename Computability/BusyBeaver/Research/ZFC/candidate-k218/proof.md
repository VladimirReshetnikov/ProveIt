# Proof of the 218-state construction

This is an ordinary mathematical proof summary for the exact published table. It uses the inherited K219 finite-refutation calibration and the fresh finite construction, unbounded runtime and complete-startup certificates. It does not claim a new proof-assistant endpoint.

## Preserve the represented source

Identify primitive instructions by left-to-right occurrence number. The submitted source constructor compares all 4,744 instructions and operands, then every outgoing control edge, including both branches of each decrement. Address arithmetic with a no-stray-one check, subtree intervals, and an independent continuation-stack resolver produce the same graph as K219. Induction on primitive steps therefore preserves the complete register vector and control occurrence for every initial register vector.

The intermediate source has 205 distinct subtrees. Five occurrences of `((A,B),C)` are reassociated to `(A,(B,C))`, with component lengths 26, 19 and 7. Each factor is closed and halt-free: it has neither an escaping break nor an escaping continue. Ordinary sequencing associativity applies. The independent graph comparison also checks every resulting edge. This affects 260 primitive addresses without changing the primitive word or the 205-node count.

The intermediate allocation and the reassociated allocation each have 219 physical states. The new 52-instruction role changes state 188 to

| Read | Action |
| --- | --- |
| 0 | `0 R 166` |
| 1 | `1 R 12` |

The newly available read-one route supplies the continuation used in the final merge.

## Recover the deleted state from the incoming bit

Let U denote the unfolded 219-state table after this reassociation. Its only incoming edges to the two states being merged are

```text
155/0 -> 0 R 85
177/1 -> 1 R 212.
```

A run from state 0 therefore has a 0 immediately left of the head at state 85 and a 1 there at state 212. This is true on every initial tape because those edges write the marker themselves.

Both old states have zero action `0 R 98`. Their one actions are `1 R 12` and `1 R 150`, respectively. In the new table M, redirect the latter incoming edge to 85, remove the two state-212 rows, and set `85/1 -> 1 L 190`. All other rows equal U.

For a scanned one at head position h, the two new paths are

```text
marker 0: (85,h) -> (190,h-1) -> (188,h) -> (12,h+1)
marker 1: (85,h) -> (190,h-1) -> (189,h) -> (156,h-1)
                    -> (176,h) -> (150,h+1).
```

The literal rows restore every bit read. Only cells h−1 and h are inspected. Thus arbitrary exterior tape is preserved, and the full ending tape, head and state equal the corresponding old one-step endpoint. The scanned-zero case agrees in one step.

Map old state 212 to 85 and fix every other state. At block boundaries the two runs have identical complete tapes and head positions. The incoming edges reestablish the required marker, and every old transition expands to a nonempty block without an interior halt. A prefix of n old transitions containing u uses of 85/1 and v uses of 212/1 expands to exactly n+2u+4v transitions. This lies between n and 5n.

Induction gives the simulation in finite time. Determinism makes the new run precisely the concatenation of these blocks. Consequently either machine halts exactly when the other does, and infinite runs correspond. This is an all-initial-tape theorem for U and M. It does not assert arbitrary-tape equivalence between the original K219 table and U's reallocated source implementation.

## Connect the exact blank tape to the source execution

Separate sparse and dense computations verify the complete blank configuration at step 312,909: native state 84, head −5, header 139, gap 80, logical vector `[3,0,0,0,3,0,0,0,0]`, 130 spares of value one, and exactly 277 one-cells. All other tape cells are zero. No earlier halt occurs. The independent root-address check excludes the earlier non-root dispatch at step 92,808.

For the final exact table, all 6,167 guarded primitive interfaces have regenerated symbolic proofs. They quantify independent arbitrary natural registers, extra gap, first spare value and finite remaining spare list. Rules are literal transitions and induction over verified unary loops and finite lists of unary blocks. Complete tape equality and positive affine clocks are checked at each endpoint. Every duration constant is at least 12; the finite checker-fuel cap bounds derivation construction, not any modelled register value or machine execution.

Startup supplies the base represented frame, and the primitive contracts supply the induction step. A source halt reaches the machine's terminal outcome. A nonhalting source primitive advances by a finite positive block without an intermediate halt, so infinite source executions remain infinite. Thus blank halting of the final binary machine is equivalent to halting of the new source at the displayed seed.

The complete source graph equality identifies that source run with K219's source run at the same logical seed. K219's independently established startup and runtime bridge identifies the latter with its blank run. Its unchanged calculus has effective finite-refutation transformations with ZFC. Composition yields

```text
Halt(K218, blank) <-> Halt(K219, blank)
                 <-> existence of a finite ZFC refutation.
```

Negating gives the displayed Con(ZFC) equivalence. These finite syntactic constructions and induction arguments are formalizable in ZFC without assuming Con(ZFC). Nothing here proves unconditional nonhalting, minimality, or a newly compiled internal PA theorem.

## Accounting and evidence scope

The final source has 23 distinct primitive types and 182 distinct interior subtrees. Its physical allocation has 183 source roles on 168 decoder states; an open subtree has two distinct physical entries, while some physical states serve more than one logical role. With 50 other working states, the total is 218. The literal table has 436 rows, and every working state is graph reachable. Symbolic row coverage and graph reachability are not claims that every row occurs on the blank execution.

The case JSON contains guard identifiers, affine durations and rule counts, rather than complete proof traces. Fresh regeneration supplies the symbolic derivations. The independent audit checks complete ordered coverage and derives four block schemas directly from the exact rows. The final fold's independent checker establishes finite premises of the ordinary induction above. None of these receipts is represented as a proof-assistant kernel result.
