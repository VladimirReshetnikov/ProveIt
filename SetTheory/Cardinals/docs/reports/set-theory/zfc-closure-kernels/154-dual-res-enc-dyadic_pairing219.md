# Global dyadic pairing prototype

This experiment replaces Cantor pairing everywhere by

\[
P_2(a,b)=2^a(2b+1)-1.
\]

It replaces all 174 occurrences of the shared pairing routine and all 86 unpairing occurrences together, including formula constructors, formula stacks, and proof-command lists. The source prototype has **218 distinct DAG nodes**, compared with the original source's **206**. This is **not** a 218-state machine: no transition-table allocation was attempted.

## Exact macro contracts

Write `I_r`, `D_r`, and `C_k` for increment, decrement, and continue; parentheses denote the inherited binary structured composition. Define the destructive transfer

```
M(i,j)  = (D_i,(I_j,C_2))
M2(i,j) = (D_i,((I_j,I_j),C_2)).
```

The first measured pair routine is

```
(M2(1,7),
 (D_6,((M2(7,1),(M(1,7),I_7)),C_2))).
```

Its precondition is `r1=b,r6=a,r7=0`. It terminates with `r1=r6=0` and `r7=P2(a,b)`, preserving the other six registers. The first transfer sets `r7=2b`. Each outer loop iteration consumes one unit of register6 and replaces `n=r7` by `2n+1`; the recurrence gives `2^a(2b+1)-1`. Each transfer terminates by decreasing its source counter, and the outer loop terminates by decreasing register6. These facts establish the macro contract for all natural inputs satisfying the precondition.

For input register `i` equal to2 or8, the unpair routine is

```
(D_i,
 ((D_i,(I_7,C_3)),
  ((I_6,M(7,i)),C_3))).
```

Its precondition is `ri=n,r6=r7=0`. It terminates with `ri=0` and `(r6,r7)=unP2(n)`, preserving the remaining registers. Within one division pass, every pair of successful decrements adds one to register7 and restarts the first decrement. If that first decrement fails, the input was even and the routine returns its quotient. If only the second decrement fails, the input was odd; the routine increments register6, moves the quotient back into the input register, and starts another pass. Thus it recursively implements

```
unP2(2b)   = (0,b)
unP2(2b+1) = let (a,c)=unP2(b) in (a+1,c).
```

An odd pass strictly reduces the remaining input, and every pair of successful decrements strictly reduces it within a pass. The two continue instructions select exactly the ancestors needed by these branches. The argument gives termination and the displayed contract on every natural input.

## Measured source family

Nine pair implementations were measured. Four use the14-leaf recurrence above, with the two final additive operations interchanged and the two possible associations. Five use a21-leaf alternative: form `2b+1`, double it `a` times, then subtract1. Each input-specific unpair routine has two equivalent arrangements of its increment and transfer, yielding `9*2*2=36` complete sources.

All layouts replace exactly174 pair,82 input-register2 unpair, and4 input-register8 unpair occurrences. The minimum is218 DAG nodes,5,526 primitive occurrences, maximum depth39, and maximum zero run6. The minimum under the inherited six-zero constraint is also218 DAG nodes. The old pair/unpair routines have10 and8 primitive occurrences; the new ones have14 or21 and9 respectively.

The script checks441 bounded pair cases and1,040 bounded unpair cases, as regressions alongside the preceding macro arguments. Both independent source-control resolvers agree for every generated complete source. The script saves the best literal source and all aggregate counts.

## Scope still open

The complete proof enumerator has not been recalibrated for this representation, and no machine runtime or blank initialization has been verified. In particular, a finished argument must bind the new macro preconditions at every caller and prove the proof-command list translation and theorem-stack invariants. Numerical conveniences include `P2(0,0)=0`, `P2(2,0)=3`, and unshifted `Push0(W)=2W`, but these are not a substitute for that complete argument. The present source count is already larger than the accepted decoder, so no further allocation search was run.

Replay from the portable encoding directory:

```sh
python3 -B dyadic_pairing219.py
```
