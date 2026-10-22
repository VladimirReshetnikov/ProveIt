# Blank K215 helical tableau lemma

This is a specialization of the repository's helical tableau construction. It removes the numerical unary input interface because the target computation has fixed blank input. It does not use any assumption that the machine halts or does not halt.

## Alphabet and exact local relation

Complete K215's state set by making state 215 absorbing: `(215,b) -> (215,b,0)`. Keep every original transition, including the write and movement on the transition entering 215. Use ordinary interior cells `(b,q)` where b is 0 or 1 and q is one of the 216 states or the headless value. There are 434 such symbols. Add three initialization symbols L,Q,R, whose payloads are respectively `(0,headless)`, `(0,0)`, `(0,headless)`, and two boundary symbols V,H. The total is 439.

V has bits `(v,h)=(1,0)`, H has `(0,1)`, and every interior symbol has `(0,0)`. Boundaries have no payload or phase. The initial symbols have their indicated phase; ordinary interiors have no phase.

In a 3-by-3 window centered at (x,y), require:

1. `v(x,y)=v(x,y+1)`; no pair of horizontally adjacent V symbols; no vertically adjacent H symbols.
2. If the center and right neighbor are both non-V, their h bits agree. There is no horizontal propagation through V.
3. An interior cell has a phase exactly when its predecessor (x,y-1) is H. On such a first row the leftmost interior phase is L, the rightmost is R, and successive phases belong to `{LL,LQ,QR,RR}`. Payloads of phases are fixed by the alphabet.
4. If an interior head is immediately below H, it is in halt state 215.
5. An interior head may not move left into an adjacent V or right into an adjacent V.
6. When the following row is interior, its center payload is the deterministic three-neighbor update: the tape bit is written by the old center head if any and otherwise stays unchanged; a new head can arrive from the old left head moving right, the old center staying still, or the old right moving left. Multiple arrivals are forbidden. V neighbors are treated as blank and headless.

These are the exact clauses in `blank_helical.local_valid`; there is no extra global condition hidden in that predicate.

## Two distinguished locally allowed windows

Use row-major order with time offsets -1,0,+1. The fixed first action of the pinned machine is `0/0 -> write 1, move R, state 93`. Thus the window around every initialized Q is

```
H                 H                    H
L                 Q                    R
(0,headless)      (1,headless)         (0,93).
```

Call it S. Its code is `[438,438,438,434,435,436,0,1,188]` in the executable enumeration. It passes the center predicate. In any globally valid configuration, the unique head on the initial row starts at Q, and the neighboring initialized phases are L and R. The initial row cannot be final because state 0 is nonhalting. The neighboring update clauses then force exactly the displayed following row. Consequently **every initialized Q has window S**, and the center phase of S proves the converse.

The auxiliary window E has prior-time center H, center V, following-time center V, and right neighbor H; fill the other five locations with an ordinary blank headless cell. Its code is `[0,438,0,0,437,438,0,437,0]`. It passes the center predicate: V propagates upward, its right neighbor is not V, and horizontal h propagation is disabled at V. Nevertheless E **cannot occur in any globally valid configuration**. The predicate at its prior-time H requires that cell's vertical bit 0 to equal the next cell's vertical bit 1. This is a contradiction independent of the remaining neighbors.

Thus E can occupy a designated alphabet index that the arithmetic compiler forbids, without removing any valid computation tableau.

## Soundness from a marked periodic configuration

Suppose a globally valid plane is periodic in each coordinate and contains S. Its center Q lies immediately above an H. If there were no V on its row, horizontal propagation would make the whole periodic row initial. The phase graph `{LL,LQ,QR,RR}` has no directed cycle through Q, contradicting horizontal periodicity. A V therefore exists; periodicity supplies V on both sides. Choose the nearest ones. Vertical propagation makes them the sides of a finite strip.

Within this strip, horizontal propagation extends the H below Q across every interior column. Vertical periodicity supplies another H above, and choose the nearest. Between these rows there is a finite rectangular tableau. Its first row is exactly `L^a Q R^b` with a,b positive, so it has one head in state 0 and otherwise entirely blank tape.

Induction on the finite number of rows proves that each row contains exactly one head and agrees with the genuine K215 computation on the finite interval. The update rule neither creates an uncaused head nor modifies an unrelated tape cell. The no-escape clause guarantees that the head does not disappear into a side boundary. Extending the interval by blanks gives the original two-sided tape computation. Its final row has its unique head in state 215. Therefore K215 halts on blank input.

This argument permits multiple strips, multiple initial rows, and arbitrary periods. It only uses the rectangle containing the specified S. The fixed blank-input arithmetic compiler requires S at the origin and forbids E everywhere; it does not require S to be unique. Because E is globally impossible already, its exclusion imposes no additional restriction on valid tableaux. The one-Start property used below belongs only to our chosen canonical completeness presentation.

## Completeness and all helical seams

Suppose K215 halts after t transitions. Let e and f be the minimum and maximum visited head positions in this finite run. Choose

`a >= max(1,-e)`, `b >= max(1,f)`, `w=a+b+2`, `Htime >= t+2`.

Make G with columns 0 through w-1 and times 0 through Htime-1. Column 0 is always V. At time 0 all other columns are H. Time 1 is `L^a Q R^b`, placing the initial head at column `xS=a+1`. Fill subsequent rows with the genuine computation, then repeat the absorbing halt row. The entire run stays in the interior; all initial and update constraints hold.

The width and height can be increased independently: fix a sufficiently large a and increase b to achieve any sufficiently large width, while adding halt rows achieves any sufficiently large height. No computable bound on e,f,t is assumed.

Define the infinite plane by

`T(x,y)=G[x mod w, (y+floor(x/w)) mod Htime]`.

Inside each vertical strip this is the padded computation with a shifted time origin. At a seam the V cell is independent of time, has no payload, and is treated as blank for neighboring updates. Horizontal h propagation is disabled whenever either endpoint is V. Initial phase endpoints see the neighboring V exactly as required. Therefore every seam constraint holds despite the one-row change of time origin across the seam. Vertical and horizontal nonadjacency constraints also hold because each rectangle has positive interior margins and at least two interior time rows.

The plane has periods `(w,-1)` and `(0,Htime)`. With `N=w*Htime`, assign G[r,s] to cyclic index

`i=-(r-xS)-w*(s-1) mod N`.

This is bijective: reduction modulo w recovers r, then the quotient recovers s modulo Htime. Its coordinate-neighbor offsets are -1 and -w. The single initialized Q produces exactly one S at index 0. The impossible E occurs nowhere. Both w and Htime may in particular be chosen to be sufficiently large powers of 5 (and may be chosen equal if desired), accommodating the parent's authentic size restrictions.

## Exact 3-by-3 window lift

Let A be the finite set of all center-valid 3-by-3 windows. Both S and E belong to A. Put a ternary relation on C,R,Y in A by requiring the two-column horizontal overlap of C and R and the two-row vertical overlap of C and Y. If a cyclic word of A-symbols satisfies this relation with offsets 0,-1,-h, then its entries reconstruct an underlying cyclic cell word: the (dx,dy) entry of the window at i equals the center at `i-dx-h*dy`. This follows by the two overlap equalities and their reverses. Thus every lifted window is the actual window of a globally valid periodic plane, without any requirement that those residues be distinct. For a word of length N, the plane obtained by pulling back along `(x,y) -> -x-hy mod N` has periods `(N,0)` and `(0,N)`. No assumption that h divides N, or is relatively prime to N, is needed for soundness. A zero temporal shift is impossible in a word containing S because its prior-time center H differs from its center Q.

Conversely, taking all actual windows of a valid cyclic plane automatically gives the overlap relation. Hence the lifted ternary problem has a marked solution if and only if the original blank machine halts. The center-valid but globally impossible E is excluded automatically in every such solution.

## Exact enumeration and cardinality

The compiler's alphabet is **all** center-valid windows, including those that cannot extend to a globally valid plane. Enumerate S first, E second, then the remaining valid row-major tuples lexicographically. Neither marker is omitted from the cardinality. Their arrays agree literally with `compiler_constants.START` and `compiler_constants.EXCLUDED`.

The four diagonal corners are unconstrained, so each valid five-cell cross has exactly `439^4 = 37,141,383,841` completions. The exact cross count is `38,256,607,897`; consequently the lifted alphabet has

`k = 38,256,607,897 * 439^4 = 1,420,903,358,357,108,792,377`

symbols. `count_blank_alphabet.py` derives this count from the pinned 430-action table. It checks the formula independently against `local_valid` on every left/right pair for each of thirteen center classes, summing all allowable predecessor and successor choices. The classes partition all 439 center symbols. A working-state center's class depends only on its written bit and movement; the target state of its outgoing head does not affect the next payload at that same center. Incoming-head target zero is counted separately, because `(0,0)` has both its ordinary symbol and the initial symbol Q. An output `(0,headless)` similarly has its ordinary symbol and the initial symbols L and R. These multiplicities are essential: the alphabet is defined by the center predicate alone, so the following row's own initialization check has not yet been applied.

The count uses 349 incoming-from-left symbols (348 right-moving actions and Q), 82 incoming-from-right symbols, and respectively 89 and 356 nonincoming symbols among the 438 non-H symbols. Four incoming-from-left actions target state zero; no incoming-from-right action does. The code checks every resulting category, not a random sample of windows.

## The blank-input specialization of five-adic index control

Here this section uses the arithmetic compiler's notation: `r=2^b`, `B=r^L=2^d`, `q=B^N`, and `Kconstant=DC+B*DR`; the symbol R denotes the packed Pell index rather than the initialization phase. Choose spatial width `h` and temporal height `Htime` to be sufficiently large powers of five, with `Htime>=25`, `N=h*Htime`, and `N>25d`. The helical padding argument above permits these independent choices.

For a canonical word let the intended temporal multiplier be `B^h`. Initially set every ignored dummy bit to zero and call its actual packed index R0. Because there is no input marker to remove, the word denoted Z in the universal-input construction is exactly C. With fixed q, J and masks, the new packed index is

`R = [q(q-F)-C](q^2-1) + (MC+q*MFsrc)J`.

At an ignored dummy exponent e, changing the low dummy bit in cell i changes

`delta C = r^e B^i`,

`delta F = (DC+B*DR+B^h)r^e B^i`,

provided `i+1<N` and `i+h<N`, so neither spatial nor temporal shift wraps that individual contribution. Hence exactly

`delta R = -Gamma B^i`,

`Gamma = r^e(q^2-1)[1+q(DC+B*DR+B^h)]`.

The masks' fixed offsets disappear from this difference. The missing input marker contributes nothing because Z=C. All changes preserve the selected windows, both marker conditions, and all local overlap tests; the native compiler's uniform carry bound permits any Boolean subset of them simultaneously.

Since d, N and h are powers of five, `q`, `B`, and `B^h` are all 2 modulo five. Therefore the bracket defining Gamma is `2DC-DR` modulo five. For the fixed band spacing in `compiler_constants.py` this is 3 modulo five. Thus Gamma is invertible modulo `dN`, which is a power of five.

The standard Boolean subset lemma applies to positions `{4j: 0<=j<N/5}` together with the distinct position 1: their weights `B^(4j)` and B represent every residue modulo dN by a subset. The size assumptions above ensure both no-wrap conditions. Choose the subset with weight sum

`(R0-d*h) * Gamma^(-1) mod dN`.

The **actual final** packed index then satisfies `R = d*h mod dN`. There is no factor two or additive one in this target: those belonged to the older kernel whose power was `2^(2R+1)`. Here the power is `X=2^R`, and `w=X/q` has the same residue as X modulo `q-1`. Consequently both give precisely the intended temporal rotation `B^h`. This is a specialization of the arithmetic compiler's completeness proof; it does not add a fifth program constant or an existential free stride.

The canonical high-mask condition also survives the specialization. The native field's unit r-digit comes solely from the temporal neighbor's Start selector: DC and DR have positive minimum degree and the dummy exponent is positive. In the canonical word Start occurs only at cell 0 and `0<h<N`, so that digit is 0 in the origin cell and 0 or 1 everywhere else. The shifted field mask tests low bits 0 and 1 at the origin, and bit 2 in every other cell; these all vanish. Every dummy adjustment above is at a higher exponent and leaves these tests unchanged. This is the only use here of the canonical presentation's one-Start property; the soundness proof never assumes global uniqueness.

Strict positivity follows directly from the same bound. Canonical words, including every chosen low dummy subset, have r-digits 0 or 1; the extra permitted upper dummy bit stays zero. The unshifted field coefficient is at most `r/4-2`, and the genuine temporal rotation adds at most 1. Thus every r-digit coefficient of `2C+F` is at most `r/4+1`. Since the fixed radix has `r>16`,

`2C+F <= (r/4+1)(q-1)/(r-1) < q/3`.

In particular `alpha=q-F-C` is positive throughout the dummy tuning. The actual rank remains positive and satisfies `R>q(q^2-1)`, which in particular gives `R-dN>d*h`. Hence `w=2^R/q` is a positive integer larger than `B^h`. If the native rotation has `(Kconstant+B^h)C=F+z0(q-1)`, then

`z=1+z0+[(w-B^h)/(q-1)]C`

is a positive integer and gives the exact polynomial transport equation `(Kconstant+w)C+(q-F)-z(q-1)=1`. The bracket is integral by the tuned exponent congruence. This completes the required strict outer witnesses at the final actual rank; the retained Pell converse supplies the remaining arithmetic witnesses.

## Executable evidence

`blank_helical.py` implements the exact predicate, window lift, overlap relation, finite strips, and cyclic reindexing. The recorded checks verify S and E locally, the explicit vertical contradiction excluding E globally, and all small initialization phase paths. Two halting control machines retain K215's exact first transition and exercise movement and writes on both sides of the origin; 32 independently padded presentations, 1,144 local windows and overlap tests, and 208 vertical seam windows pass. A 20-step prefix of actual K215 whose final state is nonhalting is rejected when made into a truncated tableau. These are finite implementation checks, not substitutes for the preceding universal proof.
