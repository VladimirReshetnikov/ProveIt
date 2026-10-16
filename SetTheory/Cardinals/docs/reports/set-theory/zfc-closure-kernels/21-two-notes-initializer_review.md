# Independent review of the compact blank initializer

Reviewed the complete `engineering/compact_initializer.py`, its
elementary proof in `ENGINEERING_NOTES.md`, and the relevant integration
interfaces of the unchanged `mira_backend.py`. No additional broad test
run was needed; this review checks the universal argument directly.

## Conclusion

The initializer theorem is correct as stated for positive n,m and nine
nonnegative register values of sum S. The integration preserves the
complete labeled runtime transition relation. Its smaller description is
an improvement to the clean editable assembler, not a new calibrated
ZFC-consistency-machine bound and not a proof of the runtime simulator.

## Tape support

Let R=18+S be the register-tape length. The header is written at absolute
position -R, and the last cell of the last register remains at position 0.
Coordinates below are relative to the header.

Setup writes auxiliary delimiter -1, counters -3,-5,...,-(2n+1), and
frontier f0=-(2n+3). It ends at head f0+1 in the right-scan state. Its wire
length is R+2+2n+2 = S+22+2n.

After j iterations the frontier is f_j=-(2n+3)-jm. The next counter for
j<n is c_j=-(2n+1)+2j, so d_j=c_j-f_j=2+j(m+2). Counters are isolated;
the right neighbor tested is zero. The consumed marker is erased, the
old frontier is erased, and exactly one new frontier is written m cells
to its left. No scan passes the header or reaches the register block.

After the counters are exhausted the next 1 is the auxiliary delimiter
at -1 and its right neighbor is the header 1 at 0. The finish branch
erases the auxiliary, then stops at the only remaining left-side 1, the
frontier. It preserves that marker and exits one cell to its right.

Every write outside the preserved register/header support is either
zero or the single current frontier/counter/delimiter mark just accounted
for. Induction therefore proves there are no other nonzero cells.
The final frontier is -(n(m+2)+3)=-(G+1), where G=n(m+2)+2. The final
absolute head is -(R+G)=-(18+S+G), agreeing with the independent replay.

## State and time accounting

Setup uses S+22+2n distinct states. The loop uses four shared control
states, m stride states, and two cleanup states. Hence

    N_init = S+28+2n+m.

In iteration j: d_j right-scan transitions reach the cell right of the
counter; testing and consuming take two transitions; d_j-1 zero scans
reach the old frontier; erasing it takes one; stride takes m. The total
is 2d_j+m+2. Thus all n iterations take

    sum_j(2d_j+m+2) = (m+2)n^2+4n.

Final cleanup takes G rightward transitions to pass the auxiliary,
one test, one auxiliary erase, G-1 leftward zero scans, and one frontier
exit: 2G+2. Adding setup gives exactly

    T_init = S+28+6n+(m+2)n(n+2).

For r register blocks, the same argument replaces the constant 28 by
2r+10. This is a direct construction, not a finite-run extrapolation.

## Parameter minimization

For fixed n the smallest allowed positive m is

    max(1, ceil((g-2)/n)-2).

The code's maximum with zero before taking the ceiling is equivalent
when g is 1 or 2, because the outer maximum already forces m=1.

Searching 1<=n<=g is sufficient for every positive integer g. If g<=5,
n=m=1 has minimal possible cost 2n+m=3. For g>=6, n=1,m=g-4 has cost
g-2. Any n>g has cost at least 2g+3, so cannot be optimal. The code
searches this sufficient finite range and compares exact integer costs,
then exact times, then gaps.

For g=102 put k=2n+m. If k<=26, then

    n(m+2) <= n(28-2n) = 98-2(n-7)^2 <= 98 < 100,

so the gap requirement fails. Cost k=27 is attainable, and feasibility
then requires n(29-2n)>=100. The only positive integer n are 6,7,8:

| n | m | G | N_init-S | T_init-S |
|---:|---:|---:|---:|---:|
| 6 | 15 | 104 | 55 | 880 |
| 7 | 13 | 107 | 55 | 1015 |
| 8 | 11 | 106 | 55 | 1116 |

Hence (6,15) is the exact time-minimizing pair among the state minimizers.

## Integration scope

The replacement targets the existing `d:0` entry. Runtime rows are
extracted by symbolic labels, never refer back to initializer labels,
and are re-extracted after numeric relabeling and compared exactly.
The selected assembler invocation uses gap 104 rather than the minimum
102; this meets its existing gap>=depth+6 precondition. Both labeled
initializer replay and complete numeric-table replay stop at this entry
with the asserted entire tape support.

None of those facts proves the general register-box contracts, the full
runtime simulation, the proof checker, or a ZFC halting equivalence.
Those limitations are correctly stated in the engineering report.

