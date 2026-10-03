# The aggregate packed bound cannot replace the left tape range lane

This is a bounded obstruction to a proposed compression of the actual [505-operation U15 compiler](u15_packed_consumed_affine505.md). It is **not a defect in that compiler**: its retained range lane rejects every fixture below. No operation improvement was found in this investigation. The imported Waterfall construction already has a paid unbounded ordinary-input route through this compiler; its separate grouped quadratic certificate has an external horizon. Adding a timestamp interface would not itself improve that representation.

The existing [unbounded scout](waterfall_unbounded_scout.md) warns about carries, but its one-step counterexample does not satisfy the current aggregate bound. The following family does, while satisfying every other typed packed interface obligation. It therefore rules out deleting the left tape range lane merely because the aggregate bound and complete controller are retained.

## Exact family

Let `B=2^a`, `a>=9`, `D=B/64`, `t=7`, `P=B^7`, and `J=1+B+...+B^6`. Set the natural raw input to `(L0,R0)=(0,0)` and the positive height witness to `D`. Use the actual table's seven rules

```
A0, B0, C0, G1, G0, H0, I1 -> J1.
```

These are edge indices `0,2,4,13,12,14,17`; relabeling B/J in the later compiler does not change the edge indices. In increasing digit order, supply

```
left   = [0,0,1,0,0,B/2,B/4-1]
right  = [0,0,0,0,1,2,5]
popped = [0,0,1,0,0,1,1]
```

with final tapes `Lf=B/8-1`, `Rf=11`. Pack these as `H,G,U`; obtain `ZL,ZR,ZU` by the literal direction selections. Set each edge hat to one plus its incidence word. All supplied history witnesses are positive, with `Lfhat=Lf+1`.

The local left-tape residuals `2 L_(j+1)-L_j+r_j` at the left-moving positions are zero except at `j=4,5`, where they are respectively `B,-1`. Their contributions to the packed equation cancel: `B*B^5-B^6=0`. The right-tape equations hold individually. Consequently both actual complete packed tape equations vanish. The chosen controller path, head shift, and terminal head/state also satisfy the actual source equations.

The aggregate word is exactly

```
H+G+ZL+ZR+ZU
 = (B/2+9)B^6+(B+5)B^5+2B^4+3B^2
 = (B/2+10)B^6+5B^5+2B^4+3B^2 < B^7.
```

The last inequality follows, for `B>=512`, from `5B^5+2B^4+3B^2<B^6` and `B/2+11<B`. Thus `bound=P-(H+G+ZL+ZR+ZU)` is positive. At `B=1024` it is `578760963614076567552`.

All 29 controller lanes, all three selection lanes, and the right-tape range lane satisfy the exact bitwise AND relation. The right digits are at most five and hence less than `D`. The left digits `B/2` and `B/4-1` violate the intended range. If only its mask is widened from `(D-1)J` to `(B-1)J`, all 34 lanes pass. In the actual joined words this changes only

```
Mjoin -> Mjoin + P^3 (B-D) J.
```

The disjoint top tags in the current compiler remain valid as well. This is equivalent at the typed interface to removing that one range restriction while retaining the same lane positions. Deleting the lane and repacking the others would not repair the missing restriction.

Yet literal execution from `(0,0)` reaches `I0` before the seventh instruction, and after seven instructions is at `A1` with half tapes `(0,2)`, rather than the proposed `J1` with `(B/8-1,11)`. The family is therefore a false seven-step history. This does **not** assert that the raw input never halts, nor that it lies in a particular ordinary-input program slice.

## Clock boundary and scope

The genuine macro-count identity already established in the unbounded scout is

```
C=6t-(L0+R0)+(Lf+Rf)+2 sum_(j<t)(L_j+R_j)-sum_(j<t)w_j,
tau=1+2C+7t.
```

Packed words provide these unweighted digit sums only modulo `B-1` without further work. The present aggregate bound controls packed magnitudes, not the digitwise tape bound: this counterexample separates those obligations. A no-repeat bound on a deterministic first-halt run would require the valid bounded configuration history first, so invoking such a bound to remove the very range hypothesis that establishes that history would be circular. No claim is made that every possible strengthened clock construction is impossible. The existing [endpoint alias](waterfall_endpoint_alias.md) separately covers unsound replacement of histories by aggregate firing counts.

## Portable replay

The standard-library checker [waterfall_packed_range_obstruction.py](waterfall_packed_range_obstruction.py) authenticates the complete 505 source, its saved full-source receipt, and the placed original TM table before reading their contents. It executes the relevant dependency closure of **both actual raw emitted forms**, including the centered state equation and all five outer comparisons; it independently checks their exact current tagged AND words. It does not call the historical author checkers or rebuild native Pell witnesses.

```
python waterfall_packed_range_obstruction.py --repo /path/to/Proofs \
  --output /tmp/waterfall-range-replay.json \
  --expect waterfall_packed_range_obstruction.json
```

The saved receipt checks eight radices `2^9` through `2^16`, both raw forms, 80 actual outer residuals, 528 unchanged lane relations, and 3,648 actual source gates. The general family proof above, rather than these finite checks, establishes the obstruction for every `a>=9`. Positive native witness extension for the relaxed exact-AND interface is inherited from the existing native theorem; no complete numerical Pell certificate is materialized here. This packet changes no source and claims no new universality or operation bound.
