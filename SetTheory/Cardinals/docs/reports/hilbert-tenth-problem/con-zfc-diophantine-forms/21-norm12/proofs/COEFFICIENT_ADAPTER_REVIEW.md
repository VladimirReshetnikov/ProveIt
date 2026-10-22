# Independent review of the 5,280-tile coefficient adapter

This review concerns `coefficient-research/REDUCED_T4_PROOF.md` and
`COEFFICIENTS.json`, based on the 37,075-tile package `11-t4` at repository
commit `f0ae4e0991ca44a7bb4e5671d42e33d775e48035`. It audits the new adapter;
it does not reprove the inherited Pell/native-window compiler or build its
proof assistants.

## Local language

The three new guards are sufficient and preserve every padded finite
halting witness. A genuine initialized row has only the L/Q/R phase kind;
each later computational row has only ordinary symbols; separator rows
have only H. The symmetric row-kind rule therefore holds away from V,
while V explicitly permits the helical seam to join different row kinds.
Three permanently unvisited blank cells at each wall ensure that every
ordinary symbol in a triple containing V is the headless blank symbol.
This remains true when the two sides of V come from neighboring times.
On the last computational row the unique head is halted, so every head
in a triple whose successor is H is a halt head. Absorbing halt padding
allows arbitrary further height and blank padding arbitrary further width.

Every strict tile passes the original T4 predicate. The separately retained
Forbidden tile also passes that original predicate and is forbidden by
its selector mask. Hence the new local language cannot create a false
global computation; the original soundness theorem applies directly.
Canonical completeness retains Start and forbids Forbidden exactly as
required. The supplied proof does not assume global uniqueness of Start
in arbitrary solutions.

The independent class census sums correctly to 5,280. Working-head centers
contribute `430*4=1720`, halt-head centers `2*8=16`, headless ordinary
centers `2*(1732+12)+6+1=3495`, phases `6+1+6`, and V/H `24+12`.
The extra one in the headless class is exactly the separately inserted
Forbidden tile. This is a small complete alphabet, not a search for a
halting K215 trajectory.

## Geometry and masks

The four copy intervals are disjoint and lie below 7,475. There are
5,280 selectors, 1,756 copies, two dummies and four anchors, for 7,042
native positions. With `ell=13` and `mu_top=2849`,
`popcount(mu)=12+2849=2861`. Therefore

```
popcount(MF_nat)=2*2861+3*439+2+1=7042,
popcount(MC)=d-7042.
```

The first dummy permits the usual extra upper binary bit; the second is
an ordinary free low bit. It does not add another upper-bit spill. Both
dummies remain below the first anchor. This distinction is needed in the
arbitrary-bit-rotation argument.

The new anchors are M, 2M, 3M and 6M with M=7,480. The bare shift M
hits target 2M only from M. The bare shift 3M hits target 6M only from
3M; the possible unwanted source 5M is absent. Their other cross-source
positions are negative or absent. At the three copy target groups,
the shifts are precisely the intended next-to-center, center-to-left and
right-to-center matches. The clause bands start above every copy/anchor
test, and neither clause band contributes to the other.

For whole-radix rotations the two tested anchors differ by 4M. The only
ordered native support pair at that distance is `(2M,6M)`: all nonanchors
lie below M and inspection of the four anchor differences gives no other
pair. The circumference 390,625 exceeds twice the support diameter, so
there is no wrapped pair. Thus the whole-cell synchronization conclusion
survives the smaller anchor choice. The two clause-band contamination sets
are disjoint by their exact circular support separation. The inherited
no-carry/odd-anchor argument then has precisely the same hypotheses as
before; the verified coefficient-mass inequalities are much stronger than
their required thresholds.

## Five-adic tuning and coefficient lengths

The two clause bands differ by 89,762, which is two modulo four. The
radix exponent 78,125 is one modulo four, so their contributions cancel
modulo five independently of every tile coefficient. The bare exponents
1317 and 69077 are one modulo four, and 7480 and 22440 are zero modulo
four. Hence `DC=2+2+1+1=1 (mod 5)`. Since `Hc=68638=2 (mod 4)`,
`DR=4 (mod 5)` and `2*DC-DR=3 (mod 5)` as claimed. This is the unit
required by the inherited actual-rank dummy-bit adjustment; the actual
rank is adjusted, rather than an unrelated formal exponent.

The product of the two powers of five is
`78125*390625=30517578125=5^15`. Thus beta has exactly 30,517,578,125
binary digits. The fixed high coefficient has
`78125*(390625+68638)+1=35,879,921,876` bits. The former is exactly
125 times smaller than the previous 5^18-bit beta. These are lengths of
the mathematical integers; their expansions are not supplied or needed
for the finite recipe. The entire coefficient tuple must be changed
together, including the shifted high-mask port.

## Result

The new finite local adapter and its smaller geometry preserve the stated
inputless compiler contract. Its width and padded period remain odd
powers of five, so the canonical square-w and odd-i argument used in the
26-integer extension still applies. This review found no missing domain,
seam, population or tuning condition in the new adapter. The unbounded
native compiler and exact K215/refutation calibration remain explicitly
inherited mathematical dependencies, not consequences of the finite
enumeration or this review.
