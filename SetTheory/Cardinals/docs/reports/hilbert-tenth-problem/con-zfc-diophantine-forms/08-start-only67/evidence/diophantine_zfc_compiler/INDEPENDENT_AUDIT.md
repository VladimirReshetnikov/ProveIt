# Independent audit of the explicit K215 compiler

Audit date: 2026-10-22. The audit covers the newly authored
`explicit_constants.py`, its accompanying `CONSTANTS.md`, and the mathematical
compiler interfaces in the pinned 78, 77, 76, and modified-75 proof notes.
It does not independently prove the repository's K215-to-ZFC theorem or the
Pell-kernel theorems. Those remain separately identified dependencies.

## Conclusion

No defect was found in the 435-state normalization, the radius-one window
predicate, the two-marker orientation, the bounded coefficient formulas, or
their modified-75 compiler interface. In particular, the local predicate is
strong enough for soundness of every reconstructed finite cyclic tableau,
not merely the tested canonical examples. The one-marker specialization
below is also semantically valid. This is a mathematical and finite-computation
audit, not a proof-assistant certification.

## 1. Folded-machine invariant

At physical position `-n`, the two tracks encode logical positions `n` and
`-n-1`. Only the physical origin has the flagged symbols 6 through 9.
The active track is part of state `4+2q+t`. When an original transition crosses
logical 0/-1, the physical position stays fixed and the active track changes.
All other logical moves correspond to the specified physical move. The write
changes exactly the active track. Consequently, induction on steps gives an
exact simulation of the original tape, state, and head position. Neither a
nonhalting simulated transition nor a malformed state/symbol pair enters state
434. A transition into original state 215 enters exactly the absorbing state
434. Physical coordinates are always nonpositive on these initialized runs.

The initialization prefix marks the head's original cell, scans left erasing
the finite unary string, and returns right over zeroes to that unique marker.
It enters state 4 at a flagged all-zero origin. Therefore all finite positive
unary lengths have precisely the same halting behavior: blank-input K215.
The prefix does not test whether K215 halts.

## 2. Soundness of arbitrary periodic valid planes

Suppose overlapping allowed windows reconstruct a plane periodic modulo a
finite cyclic index `i=-x-hy (mod N)` and containing the Start window.
Every centered predicate holds because a window occurs at every plane point.

1. Vertical boundary tiles propagate in both time directions. Thus their
   columns are genuinely constant. Distinct adjacent V columns are forbidden.
2. Start supplies an H above its initialization row and a Q immediately to its
   right. On a non-V initialization row the phase graph is
   `L* -> I* -> Q -> R*`. It has no directed cycle containing Q. Since the row
   is N-periodic horizontally, V columns occur on both sides of that Q.
   Select the nearest bounding columns. The strip has finite positive width.
3. H status propagates across all adjacent non-V cells. The H above Start
   therefore spans this whole strip. Vertical N-periodicity supplies a next H
   row in the strip. Adjacent H rows are forbidden.
4. Immediately below the first H, the phase rules and both boundary rules force
   exactly `L^a I^u Q R^b`, with `a,u,b>=1`. In the distinguished strip Start
   further forces `u>=2`. Thus there is exactly one genuine initial head.
5. Before the next H, ordinary centered updates are exact. An existing head
   writes once; a destination receives the unique head precisely from its
   correct predecessor. Head escape through V is prohibited. Induction gives
   one genuine head in every interior time row, with the true machine tape.
6. The final interior row need not perform a further transition. Instead, its
   centered rule permits a head only in state HALT. The preserved unique head
   must therefore be halted. The rectangle is a finite genuine halting run.

This argument needs neither `h|N` nor uniqueness of Start. It also explains why
allowing headless final cells, or treating a V neighbor as blank and headless,
does not permit a false halting tableau: head conservation and the no-escape
rule are proved on the whole finite strip, starting from its unique head.

## 3. Completeness and independent padding

Take any halting blank K215 run. Initialize the normalized machine with any
chosen `u>=2`, meaning `u+1` unary ones including Q. Its full run visits only
finitely many physical cells. Choose a width `w=a+u+4` with enough left blank
margin and two right blank cells. Place a constant V column at column 0, an H
row at time 0, and initialization `L^a I^u Q R^2` at time 1. Fill later rows
with the genuine run, repeating its absorbing halt as necessary.

For an independently chosen sufficiently large height H, extend the base array
G by

    T(x,y)=G[x mod w, (y+floor(x/w)) mod H].

The only skew seam is separated by V; horizontal H-status propagation does not
cross V. Thus every centered predicate remains valid across every seam. The
plane has periods `(w,-1)` and `(0,H)`. With `h=w` and `N=wH`, the cyclic index

    i=-(x-x_Start)-h(y-1) mod N

is a bijection on the base rectangle. A physical right neighbor has index
`i-1`, and a next-time neighbor has index `i-h`, exactly matching the native
compiler's overlap tests.

Width and height can each be any sufficiently large integer. Therefore each
can independently be chosen a power of five, with `H>=25` and `N>25d`, as
required by the five-adic dummy-control construction. For `u=3`, choosing a
large five-power width h means simply choosing margin `a=h-7`. No computable
bound on K215's eventual running time or space is used in the constants.

In the two-marker version, Start is the last I and End the first I, so End is
at cyclic index `u-1`. Thus `u=3`, not `u=2`, is the canonical initialization
for the fixed loader `W0=R B^2`. There are four unary ones including Q.
There is exactly one Start and one End in this canonical cyclic presentation.

## 4. Optional one-marker specialization

Let the second enumerated window be

    F=(tile(0,q0),...,tile(0,q0))=(7,7,7,7,7,7,7,7,7).

This is allowed: q0/read0 is explicitly a stationary nonhalting self-loop, and
only the centered head is stationary incoming to each center. Adjacent heads
in this malformed homogeneous configuration do not create an incoming-head
collision. No genuine initialized run ever contains tile 7: q0 occurs only in
the phase Q with symbol 1, then the prefix and simulation never return to q0.

Enumerating Start at selector 0 and F at selector 1 therefore leaves the full
allowed alphabet unchanged as a set. The compiler can forbid selector 1 in
C=Z, with no inserted End selector. Any recovered Start-marked plane still
halts by Section 2, irrespective of its unary length or other Starts. For
completeness use the same canonical `u=3` tableau, with unique Start and no F.
The modified-75 origin field test remains satisfied because its nonzero
whole-cell temporal predecessor is not that unique Start. This validates the
semantic adaptation; the specialized arithmetic source still requires its own
positivity and polynomial-equivalence audit.

## 5. Fixed coefficient geometry and masks

The independent formulas match the modified-75 interface:

- `A>k+1` and `A>=4`; selector occupancy and copy/anchor clauses are carry-free
  in this clause radix.
- `popcount(mu)=ell-1+9a+4+p`, hence
  `m=2 popcount(mu)+12a+2=2ell+30a+8+2p`.
- The least padding p guarantees `D=m-k-9a-3>=1`, so the native exponent set
  has exactly `k+9a+D+4=m+1` elements.
- Copy exponents descend by `3a` in the row direction and by `a` in the column
  direction. The DC shifts therefore produce precisely the stated vertical
  and horizontal overlap coefficients, with no transposition or reversal.
- All old positions are below M0. Among native exponent differences,
  `18M0=v2-v1` occurs exactly once. The two clause bands are separated by more
  than `2Emax`, and their cyclic complement by more than `Emax`.
- The optional high monomial is above every tested coefficient and below the
  cell limit. Its only purpose is to make `2DC-DR` a unit modulo 5.
- `R>=4mass+8` gives unshifted coefficient mass at most `R/4-2`. Even the extra
  dummy upper bit under an arbitrary binary rotation cannot create a carry.
  Its spill at residue `b-1` can create an odd digit at only one within-cell
  position, so cannot satisfy both distinct anchor parity tests. At residue 0
  its contribution is even. The original anchor-difference proof is retained.
- The new native mask is `MF_native=MF0+4`; the data mask clears one further
  dummy bit. Their populations sum to d; `MC=2 mod 4` and `MF_native=4 mod 8`.
- The arithmetic source's port named MF is the shifted coefficient
  `MF_source=MF_native+B-1`, not the native field mask itself.

The independent basis audit checks every permitted native basis bit against
every old field-test coefficient in its synthetic cases. It checks ignored
dummies as well as selectors, copies, and anchors.

## 6. What is explicit, and what was executed

The window alphabet is defined by a total predicate on exactly
`4366^9=576439300316095098822468574875136` tuples. Its ordering, count, selector
coefficients, padding, masks, and all further integer operations are uniquely
specified by bounded formulas. No coefficient depends on an accepting run or
on an unbounded simulation until halt. Numerical materialization of these
integers is not claimed and is unnecessary to their exact mathematical
specification.

`independent_audit.py` is newly written audit code. It executes the new module,
not the upstream Python checkers. Its receipt records:

- 10,000 folded simulation steps compared against a separately maintained
  two-sided logical tape, across 100 deterministic seeded transition tables;
- 21 actual toy halting helices, totaling 28,125 local windows and 28,125
  horizontal/vertical cyclic overlap checks, including crossings of the folded
  origin, both move directions, five-power padding, unique markers, and absence
  of the forbidden window;
- 10 synthetic compiler layouts and 211,764 native-basis field checks,
  including zero-clause padding, one-dummy layouts, both modular-correction
  branches, mask populations, and the strong radix margin.

The new module's own finite audit also passes. No full `4366^9` enumeration,
full huge coefficient materialization, run of the actual K215 to termination,
or proof-assistant verification is represented by these receipts. The general
proofs above and the explicitly cited arithmetic/ZFC dependencies are essential.
