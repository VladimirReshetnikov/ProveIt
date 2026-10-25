# Independent continuation review of complemented three-anchor radix47

Date: 2026-10-25. Reviewer: `/root/complemented47_review`, independent of
the packet author. This is an inert mathematical review, not an execution
receipt, a finite controller certificate, or a new foundational formalization.

I read the entire 603-line source
`research/compact66-complemented-three-anchor-radix47/README.md`, frozen at
commit `992a9b4aa923d8e8ce0b2a7349bc6f9786fc9792`. Its SHA256 is
`ab3211b4d9aa7842531a77fde938092c7d96e5cb8dcfdf94bf2b695e156d1ae2`.
I also read its PINS and SOURCE_SNAPSHOT, the retained radix55 whole P66
proof and complete printed finite recipe, the indexed-language proof,
the inherited P67 interface and source argument, and the earlier
three-anchor47 comparison/reviews. Relevant current source hashes match
the new packet's bindings. This review does not claim a fresh full audit
of the transitive K215/refutation/compiler calibration or of the incoming
archive's numerical claims.

**Disposition:** I found no mathematical defect in the new local carry,
alignment, occupation, canonical-rank, or P66 witness-map arguments. The
result is the stated **conditional ordinary theorem**. In particular,
this review does not remove the new finite premises in section 11.

## Carry decoding and support

The full complemented color map is a componentwise bijection. Horizontal
labels are in 6..255 and vertical labels in 73..511, so every genuine
label is positive while the empty native cell has all four labels zero.
This proves precisely the distinction needed by the replacement occupation
argument; ordinary equality and all seams are preserved in both directions.
The stated Start, Forbidden and initializer images agree with the retained
complete table.

The section 3 counting lemma handles incoming carries, rather than assuming
they vanish. The nine tests in bits 1..9 and `n+k<=972<1024` force
`n+k` to be 0 or 1. Consequently an occupied cell has `n=1,k=0`; an empty
cell may still have incoming 1. The next 36 tests force `Q=0 mod 2^36`.
For `n=0`, the strict bound `Q<2^36` gives `W=0` and all three anchors zero.
For `n=1`, the only possible positive multiple is `2^36`; reduction modulo
`2^34` gives `W=ucomp`, and then the anchor sum is 3. Each anchor is therefore
one individually. The occupied raw clause really is `2^46+1<2^47`, with
zero outgoing carry. No unstated anchor-equality premise enters this lemma.

The complete support has 943 selectors, 34 label positions, three anchors
and two coefficient-zero dummies: 982 physical positions and 980 nonzero
coefficients. The four removed positions are absent from both the support
and the coefficient definition. The selector bound follows directly from
the complete color ranges, while the three anchors attain `Mcoef=2^44`.
The reciprocal coefficient recipe, explicit `MC` correction and once-shifted
source mask agree with their support formulations. The masks contain
110 core bits and 872 padding bits, exactly balancing the 982 clear bits
of `MC`. This review does not treat `2mu+4=rho` as the old strict inequality.

The predecoded estimate is coherent. With the retained old threshold as a
premise, the strict hand comparison gives `Cold>106rho`. Reweighting all
seven old markers and then complementing all selectors gives
`Cc3=(1075/8)rho-Cold+965470` after deletion of four shared markers.
The excluded difference 1102 prevents double use of one reflected
coefficient at an output. Including the upper dummy allowance, bare terms,
and every fractional temporal phase gives `a+29<30rho`. Thus the monotone
cyclic carry map closes on the finite box 0..29. Its fixed point gives the
transport residue; strict `0<F<q-1` is used only when identifying an already
supplied soundness witness with that residue.

The temporal support cannot meet both disjoint clause bands. Applying the
whole counting lemma at a clean clause therefore precedes occupation and
alignment. After this decoding there are at most 40 physical nonzero
positions per cell. The conservative bound of 80 reflected selector hits,
the entire nonselector sum, extra dummy contribution and temporal bound
reduce the same fixed-point carries to at most 11. No global no-carry
assertion is needed at either stage.

## Alignment, tested fields and occupation

The two pre-anchor values at 2194 and 3295 are respectively zero and the
single Boolean value at 2195, before adding the temporal digit. Each total
with incoming 11 is below the radix. Thus both anchor tests receive zero
incoming carry in every fractional phase. The recovered Start anchor
requires odd temporal contributions at both targets. Phases 1..45 supply
only even digits; phase 46 has only the one possible odd spill. Phase zero
remains, and the unique support difference 1101 forces the digit offset to
zero modulo the cell length. This does not impose a preferred stride or
unique Start on arbitrary soundness witnesses.

After alignment, the initial 0..1096 band clears all carries entering the
17 ordinary copy tests. Each is an exact sum of two Boolean bits, so its
low-bit test enforces equality. The complete label fields, rather than
selected bits or sampled tiles, are compared. The separate pre-anchor
resets continue to protect the anchors.

The clause predecessor estimates include the extra reflected anchor term
at 5494. Their bounds are strictly below `rho-11`, and aligned temporal
digits cannot reach them. Both clauses thus receive zero incoming carry
and have exactly the raw values already proved by the counting lemma.
The resets at 7690 and 8791 similarly precede actual zero padding bands.
All 15 high fields, all three lower full fields, and all 26 low bits of
field 7694 are covered. The high zero tail also protects the next origin.

Finally, genuine positive labels versus empty zero labels make adjacent
spatial cells simultaneously empty or occupied. Spatial rotation is one
cycle through all cells, and the forced Start makes the entire cycle
occupied. This replaces the four removed physical occupancy markers.
The Start's unequal north/south labels exclude stride zero; inverse
complementation then recovers the retained genuine marked language.

## Canonical converse and actual rank

The converse constructs the cyclic carry fixed point before choosing strict
`F`. Occupied clause digits establish positivity, and the zero high tail
excludes the all-ones representative. This removes the potential circularity
between constructing `F` and assuming its strict bounds. Every simultaneous
safe low-dummy subset preserves the local proof and the canonical slack.

The rank identity uses the actual packed words and shifts `MF_source` once.
Binary disjointness of `S'` and `Tmask` gives the exact population `3t+2`;
the low-origin residues give `R=3 mod4`. These binary identities remain
valid although untested native radix fields can carry.

For a safe interior dummy bit, the stated local exponent bounds and strict
slack justify `Fnew-Fold=(K+B^width)deltaC` as an ordinary integer equality.
A transport congruence alone would not justify this step, and the proof
correctly supplies the additional argument for every intermediate subset.
Subtracting actual ranks then gives the asserted `-Gamma B^j` increment.

Under the new section 11 premises, `Gamma` is a unit modulo the full `dN`.
The LTE/CRT orbit and Boolean subset construction are valid: selecting
`a0` consecutive orbit coordinates is legitimate because `a0<T_orbit` and
`gcd(a0,T_orbit)=1`. The extra `B^3` term avoids a residue zero modulo the
controller prime. The available cell indices and their spatial/temporal
translates stay inside the word. Consequently the final actual rank,
not a separately selected rank variable, is tuned to `d*width mod dN`.
The displayed positive transport quotient then satisfies `Nt=1`.

## Native/P66 maps and retained source calibration

The P66 expression agrees with the retained free-port arithmetic front.
For soundness, its strong factor is `Delta` times the integer normalized
factor. Cancelling `Delta` in the proof yields integer units. The retained
negative-Pell, mod-4 and signed-index arguments must still be used in their
stated order: initially transport permits `C=0`, and only recovered index
signs exclude it. The new packet preserves this order.

The exact quotient bridge `Told=f*Tnew` is positive and satisfies the
retained P67 auxiliary expression identically. The ordinary multiplier
bridge `iordinary=Delta*i` is also positive integral. Neither bridge
divides an arbitrary supplied witness. Scalar/population recovery is
coefficient-uniform at the proved boxes and mask populations. The old
native no-carry/occupation argument is replaced by the new local proof,
so its stronger old native hypotheses are not silently transferred.

In the fresh converse, `R=3 mod4` and odd `dN` make both required powers
of two squares. For `A=a+2`, `c=psi_A(R)` and `m=cR`, expansion of the
Pell unit at index R to its c-th power gives divisibility of `psi_A(m)`
by `c^2`. Its odd parity gives a positive odd integer multiplier. Thus
the actual strong factor is `Ns=Delta`.

For the new auxiliary quotient, the printed odd-index recurrence gives
`Vstar=-c mod f^2` and `Vstar=-R mod c`. Since `gcd(c,f)=1` and
`f^2=1 mod c`, `Tstar=(Vstar+c+R*f^2)/(c*f^2)` is an integer and positive.
The norm at S gives `Na=1`. Together with the fresh retained outer
witnesses this yields five factors equal to 1 and the actual sixth factor
equal to `Delta`, so the entire polynomial vanishes. The erroneous claim
that all six actual factors equal 1 is not used.

The implication from a recovered genuine marked computation to a syntactic
ZFC refutation, and the corresponding independent cofinal rectangle
construction, remain the expressly retained source-calibration contracts.
This review checks their interface to the new recipe; it does not claim
to have reconstructed that whole transitive machine/foundational proof.

## Finite premises and claim boundary

The new controller bracket is `Hc3=1+B*K+B^2`, for this new K. Section 11
requires a fixed odd prime `lambda>d`, `101269|(lambda-1)`,
`B^2!=1 mod lambda`, valuation-one lifting, and nonzero Hc3 residues modulo
47, 8807 and lambda. The source leaves all three bracket values and both
the value and existence of a suitable lambda unresolved. The incoming
seven-marker controller and earlier radix49/53/55 certificates do not
establish these facts. This review computes none of them; any separate
new evaluator/certificate must be reviewed on its own evidence.

Precisely, relative to the retained source contracts, P66 soundness is
unconditional on these finite controller conditions, while positive
completeness is conditional on all of them. The claimed ZFC-provable
unsolvability/Con(ZFC) equivalence has that same dependency boundary until
the finite conditions are discharged. No global minimality, measured
printed saving, finite endpoint, or new Lean/internal-ZFC theorem follows
from this review alone.

Only inert text/hash/Git reads and this review write were performed. No
incoming or candidate code was executed, no frozen artifact was changed,
and no commit was made by this reviewer.
