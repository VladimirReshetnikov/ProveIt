# Proof obligations for the fixed pair-sum successor U

**CODE ONLY / HOLD.** This is a source-level verification design and
ordinary argument. No program in this folder has been imported, parsed
as an AST, compiled, tested or run. No F coefficient data has been
generated. PINS/HOLD bind the separately accepted finite T parent.
The exact new expanded height/support are unknown scientific outputs.

## 1. Fixed source, domain and inverse

For each profile let P(w)=Σi Ri(w)² be the complete accepted finite
coord35 T polynomial, separately accepted at commit0f147e16e3 under
MANIFEST314d7227908e52bb838dbb51a4e777c5bfc7045cc6ebd2cbf6d79d5762dfe7ca.
Its fixed input folder is exactly `../pell-output-gate-shear-verification/data`,
with every byte and all acceptance/evidence dependencies pinned. P has
316 variables/218 rows in the plain profile and315/217 in the weighted
profile. Its accepted endpoint is degree4, full liveness, height54709,
residual height128 and support5728/5734. These facts are checked again
from complete input coefficients; accepting them does not replace the
parent SOS identity with a collection of scalar metrics.

Define U:Z^n→Z^n by w27=z27-z10-z12 and wi=zi otherwise. Define
V:Z^n→Z^n by z27=w27+w10+w12 and zi=wi otherwise. Since10,12 differ
from27, direct substitution gives UV=VU=id on every integer tuple.
Both maps have integer coefficients and determinant1. Set F=P∘U.
Thus F(z)=0 iff P(Uz)=0, and every P zero w has the F zero Vw.
There is no positivity restriction on this quartic chart.

Each Ri has degree≤2, so Ri∘U also has degree≤2 and F has degree≤4.
Because a sum of integer squares is zero exactly when every summand
is zero, its zero set is the complete residual-system zero set. The
same statement is formalizable in elementary integer arithmetic within
ZFC. No consistency or semantic soundness assumption is used here.

## 2. Complete changed-row formulas

Use aliases a=z10, b=z11, c=z12, u=z21, p=z25, r=z27, t=z30,
v=z35, k=z36, s=z42, l=z44, m=z45, n=z46, and yj=zj for other
outputs. These are independent coordinates, not eliminated gate values.
Let D=a+c and L=-2a-4b+2c+2u+2p. The full eleven old/new rows are:

| Row | Full old Ri in P | Full new Ri∘U in F |
| --- | --- | --- |
| 11 | r-D²+2D-1 | r-D²+D-1 |
| 12 | y28-(8a+4b+8c+2u+2r)²-2a-4b-2u | y28-(6a+4b+6c+2u+2r)²-2a-4b-2u |
| 14 | t-(4c+2p+2r)²+16c+8p+8r-6 | t-(-2a+2c+2p+2r)²-8a+8c+8p+8r-6 |
| 15 | y31-(2a+4b+4c+2u+4r+2t)²+2a+4b+8c+2u+8r+4t+1 | y31-(-2a+4b+2u+4r+2t)²-6a+4b+2u+8r+4t+1 |
| 17 | y33-(6a+b+8c+2r)²-24a-3b-32c-8r-2 | y33-(4a+b+6c+2r)²-16a-3b-24c-8r-2 |
| 19 | v-L²+8L-12-4a-5c-2p-r | v-L²+8L-12-3a-4c-2p-r |
| 20 | k-4v²-4v-8a-6c-2r-3 | k-4v²-4v-6a-4c-2r-3 |
| 27 | y43-(8a+6c+2r+2s)²+8a+6c+2r+4s | y43-(6a+4c+2r+2s)²+6a+4c+2r+4s |
| 30 | n-(2a+2b+2p+2r)²+24a+24b+24p+24r-35 | n-(2b-2c+2p+2r)²+24b-24c+24p+24r-35 |
| 31 | y47-(4a+4c+4r+4l+2m+2n)²-4c-4l-2m | y47-(4r+4l+2m+2n)²-4c-4l-2m |
| 32 | y48-(5c+4r+2t)²+c | y48-(-4a+c+4r+2t)²+c |

The c term in row31's linear part remains after a/c disappear from
its square. Every output appears in the table, including n in row30.
The checker expands these independently from literal formulas and
compares each COMPLETE old and new row, not just a leading part.

The complete old coordinate27 occurrence list is exactly
[11,12,14,15,17,19,20,27,30,31,32]. The complete coordinate35 occurrence
list is[19,20]. Row19's r occurrence was introduced by T and must be
retained. No later consumer or label sum reads r. Applying U therefore
changes exactly these11 rows. The other207 plain/206 weighted rows are
literally identical. Complete source occurrence lists and every row
are checked; no local incidence guess supplies this conclusion.

Old/new collected residual term counts in that order are

    old [7,19,11,29,16,23,7,15,16,25,8]
    new [7,19,16,22,16,23,7,15,16,14,12].

The total difference is9 fewer residual monomial occurrences. This
does not imply any guessed reduction of the expanded SOS support.
The only old coefficient of magnitude>96 is row12:-128ac. All new
coefficients have magnitude≤96; unchanged rows16/26 retain -96bc.
Hence the residual height is exactly96. The complete collected rows
are checked for both the upper bound and the lower witnesses.

## 3. Two independent complete arithmetic routes

The producer represents a monomial by its sorted index tuple, including
the empty tuple for1. A coefficient dictionary denotes exactly the
finite sum of those integer coefficient times monomial products.
Its addition merges equal monomials and deletes zero coefficients.
Its multiplication visits every ordered pair of terms once, adds their
index multisets and multiplies their coefficients. These operations
are precisely the distributive laws in Z[z0,...,z(n-1)].

For each old monomial the producer starts with its coefficient and
multiplies by zi for every factor i!=27, or by -a-c+r for i=27.
Induction on the number of factors proves that its output is the
monomial composed with U. Summing proves that every produced row is
Ri∘U. Squaring every full row by ordered multiplication and summing
gives exactly F. Metrics are calculated after collection and do not
constrain the new exact height/support to a guessed value.

The checker uses a different formula. For a monomial containing q
copies of coordinate27 and a remaining product M, for each ia,ic≥0
with ia+ic≤q put ir=q-ia-ic. Its replacement is

    Σia=0..q Σic=0..q-ia
      binom(q,ia) binom(q-ia,ic) d^(ia+ic) a^ia c^ic r^ir M,

where d=-1 gives U and d=+1 gives V. The binomial product equals
q!/(ia!ic!ir!), so this is the multinomial theorem for (r+d*a+d*c)^q.
This route does not call the producer's multiplication or substitution.
It works on every complete row and the complete expanded polynomial.

For independent squaring, order all terms of a row. Diagonal terms
contribute c²M²; each unordered distinct pair contributes2cdMN.
These are exactly the diagonal and two symmetric off-diagonal terms
of the square. This checker route does not use ordered squaring.
Summing it over every row reconstructs both the complete old and new
SOS. Old SOS equality and old census must hold before transformation.

The checker requires four complete identities:

    saved_new_rows = independent U(old_rows),
    saved_F = independent_SOS(saved_new_rows),
    saved_F = independent U(saved_P),
    independent V(saved_F) = saved_P.

It also requires V of each ACTUAL saved new row to be its old row.
Thus checking a second forward implementation does not substitute for
checking the inverse of the actual artifact. Zero terms and duplicate
monomials are collected mathematically before comparison, and original
saved rows/polynomial must additionally be canonically serialized.

Only canonical JSON, inventory/hash/type/path operations are shared
in guard.py. The checker does not import the producer or any ancestor
application/helper. The source copies/adaptations are explicit pinned
provenance, not executable imports from an unreviewed prior closure.

## 4. Six exact quartic witnesses and known whole bounds

Column order below is a4,c4,a2c2,b2c2,a3c,ac3. Only rows12,14,15,17,
27,30,31,32 change their quadratic parts. Rows11/19/20 have unchanged
quadratic parts. The complete48 row witness cells on each side are:

| Row | Old six coefficients of Ri² | New six coefficients of (Ri∘U)² |
| --- | --- | --- |
| 12 | 4096,4096,24576,6144,16384,16384 | 1296,1296,7776,3456,5184,5184 |
| 14 | 0,256,0,0,0,0 | 16,16,96,0,-64,-64 |
| 15 | 16,256,384,1536,128,512 | 16,0,0,0,0,0 |
| 17 | 1296,4096,13824,384,6912,12288 | 256,1296,3456,216,1536,3456 |
| 27 | 4096,1296,13824,0,12288,6912 | 1296,256,3456,0,3456,1536 |
| 30 | 16,0,0,0,0,0 | 0,16,0,96,0,0 |
| 31 | 256,256,1536,0,1024,1024 | 0,0,0,0,0,0 |
| 32 | 0,625,0,0,0,0 | 256,1,96,0,-256,-16 |

The whole old/new coefficients, including all unchanged rows, are

    P [12716,16365,54709,36349,36692,39162]
    F [ 6076, 8365,15445,32053, 9812,12138].

The checker verifies every one of these finite table cells directly
from its independent complete squares and both whole polynomials.
In particular b²c² has coefficient32053, so degree(F)=4 and H(F)≥32053.
Pure a4/c4 are nonzero. For other coordinates liveness also follows
from the invertible substitution fixing them and the chain rule; the
checker separately measures and verifies the complete live mask.

The exact accepted ordinary source proof is the431-line
`../pair-sum-gate-shear/README.md`, with MANIFEST SHA256
dc84e27c87c705f454dfa5da099b9f4dcaf8aee4eb778bcdabf2df972c3ce711.
Its full independently accepted section5–8 arguments give

    degree4 coefficients in[-35040,41466],
    degree3 magnitudes≤40094,
    degree2 magnitudes≤21396,
    exact degree1 height2270,
    constant2674.

These bounds include every tail row and every output-coordinate cubic.
They are ordinary dependencies, not newly executed coefficient tables.
The finite checker separately tests these inequalities on EVERY actual
saved coefficient. It retains the ordinary lower witness, hence
32053≤H(F)≤41466<54709. It does not declare either endpoint to be the
exact H(F). The exact degree census/support/H come from actual complete
output and agreement of the two arithmetic routes after runtime release.

The constant remains2674. Only the a/c linear coefficients change:
old a:-1232,c:576,r:-1694 become a:462,c:2270,r:-1694; all others
are identical. Their old magnitudes≤2116 give exact linear height2270.
The checker tests the complete low-degree identity and these witnesses.

## 5. Scientific output and controls

The checker computes complete new metrics independently, and compares
the full saved metrics object by canonical JSON bytes so4.0 cannot
pass as4 and True cannot pass as1. It additionally records the complete
old/new coefficient delta, every deleted/introduced monomial, counts
by degree and net support change. None of those unknown results is
hardcoded as an expected exact value. The producer's census is not
accepted by merely checking a plausible inequality or witness.

Each negative control mutates an actual artifact model, confirms its
bytes changed, rebinds only the outer chart/prior-file/INDEX records,
and invokes the same complete verifier. It must raise the exact stated
ValueError. Algebra/source/policy/census/map fields are never repaired
by rebinding. All64 cases per profile are distinct by name, and their
literal target paths and reasons are read as part of full static review.
They include corruption outside the11 changed rows and changes to the
complete inherited83/204/203 maps, not just a local formula toy model.

The six valid cases per profile alter the actual row or expanded
polynomial by reordering, a c+7/-7 split or a cancelling±9 pair.
The semantic verifier must accept all12; the independent canonical
saved-term gate is intentionally outside these private control calls.
Every explicit gate survives Python -O. Full normal/-O outputs and
the separately released fresh same-mode repetitions must be preserved.

## 6. Whole source maps, authentication and remaining boundary

A zero z of F maps through U to a zero w of P, through T to a zero
of the neighbor, then through the complete retained neighbor N,
balanced S,58 shifts,83 free initializations,204 plain/203 weighted
reverse monic restorations, mandatory Horn private overwrites and
ordinary source maps/calibration. The forward existence construction
uses the inherited maps in their prescribed reverse order, followed
by T inverse and then U inverse. Earlier private restoration stages
remain existential; they are not claimed to be whole-space bijections.

Because T's target35 expression uses coordinate27, the composed chart
has x35=z35-3a-4c-2p-r, whereas its inverse retains
z35=x35+4x10+5x12+2x25+x27. The complete map ordering in actual
COMPOSED_MAPS must agree, and a control swaps the last two forward
steps to ensure noncommutativity is not silently ignored.

The entire parent map, endpoint, certificate and source calibration
are embedded and compared. All exact source131/Round15/C222/ZF-to-ZFC,
native/fresh-interval/Hstar/H0 dependencies remain literal. This finite
identity does not prove a compiler or rerun a native program. The
old324 polynomial/old327 body and raw private tuple identity are not
assumed. The older optimized centering exit143 remains unresolved,
cause unknown. These inherited boundaries remain visible in evidence.

Negating the inherited whole zero-set equivalence gives the same
ordinary ZFC-provable equivalence between absence of an integer zero
of F and syntactic Con(ZFC). This packet is not a new calibration or
a Lean proof; it transfers the exact accepted ordinary calibration.

Before a future run every held byte, external pin and whole-tree
membership must authenticate. The final pins bind452 external records,
17 entire trees/358 members and the accepted parent reviews/release
histories; the eight original historical T Git blobs were also checked
inertly during preparation. JSON rejects duplicate/nonfinite input;
coefficients/indices/record lengths are genuine integers. Paths are
fixed, canonical, outside the repository for output and nonsymlink.
Writes are exclusive. The producer checks authentication before/after
construction and complete saved readback. The checker reauthenticates
after controls and rereads the entire candidate data to detect change.
The exact13-file inventory and full objects/census/maps are checked.

Two complete final static approvals plus separate ROOT runtime release
precede any import/run. A first failure/interruption is preserved and
stops without repair/retry/reseal. Later fresh apps, inert evidence
closure and ordinary endpoint acceptance each remain separate gates.
The maintained one-page equation/TeX/PDF, all parent seals and parked
Lean are unchanged. No page gain, finite endpoint or optimum follows
from authoring this held code.
