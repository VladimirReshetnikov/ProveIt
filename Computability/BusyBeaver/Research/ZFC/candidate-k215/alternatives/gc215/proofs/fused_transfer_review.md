# Independent review of the fused 25-leaf single-cache-guard transfer

The primitive macro in `fused25_macro.sites.json` was extracted from subtree111 of `source_work/fused25-simple.sites.json`. The accompanying checker is independently written and imports no source generator or repository module. It resolves the structured control graph compositionally and compares the complete result with the literal graph used below.

Registers are `(N,T,W,A,D,H,X,Y,L)`. Assume only that A=X=Y=0 on entry; let incoming T=t, W=w, D=d, H=h. There is no size or theoremhood assumption on t,w,d,h. Its exact contract is

```
HALT iff h=1;
otherwise return (N,h,tail(w),0,d,head(w),0,0,L).
```

In particular incoming top1 and cache0 return normally. It realizes the direct single-cache-guard command, not the earlier composite command with an additional incoming-top guard.

## Clear and fused guard/transfer, leaves0--10

Leaves0--1 repeatedly decrement T until zero. They terminate because T strictly decreases each iteration.

Leaf2 tests/decrements H. If H=0 it jumps directly to the stack pop at11. If H>0, leaf3 increments T, so T=1 and H=h-1.

Leaf4 tests/decrements this remaining H. If it is0, the original h was exactly1 and control reaches the unique halt at10. Otherwise leaf5 increments T, so T=2 and H=h-2. Leaves6--8 move the rest of H to T, preserving T+H=h, with H decreasing each iteration. On termination leaf9 jumps past the halt to11.

Thus for h=0 or h>=2, the complete prefix returns T=h and H=0, with X=Y=0. It reaches the halt exactly for h=1. D, N, L, W, and A have not changed.

## All-natural Cantor unpairing, leaves11--24

At11, H=X=Y=0. During the main loop11--18 let `a=X,b=Y`, and let k be the number of decrements already made to the incoming W. The invariant is

```
W=w-k,     P(a,b)=k.
```

At each positive W iteration, W decreases and Y increases. If the former X was positive, X decreases once and the branch at14 skips the inner transfer. The resulting pair is `(a-1,b+1)`, and

```
P(a-1,b+1)=P(a,b)+1        when a>0.
```

If former X=0, leaves15--17 move all of the now-positive Y to X, ending at `(b+1,0)`. The corresponding identity is

```
P(b+1,0)=P(0,b)+1.
```

Both cases preserve the invariant. The inner loop decreases Y to zero; the outer loop decreases W to zero. Hence the unpairing terminates for every natural w and ends with W=0 and `P(X,Y)=w`. Cantor bijectivity identifies X=head(w), Y=tail(w), including w=0.

Leaves19--21 transfer all Y to W, leaving Y=0 and W=tail(w). Leaves22--24 transfer all X to H, leaving X=0 and H=head(w). Both loops terminate by decreasing their source register. The macro exits normally with no unresolved break or continue, and every unmentioned register is preserved.

The exact control-graph check is finite; the decreasing-register invariants above prove the unbounded contract. The additional bounded input executions in the receipt corroborate indexing and implementation, but are not used as the universal proof. This confirms the macro's semantics only. Its measured full-source DAG cost and any physical allocation remain separate matters.
