# First complete ordinary review of the radix65 native/source adapter

Verdict: **CHANGES REQUIRED**, one naming/cofinality binding finding.
The complete arithmetic and native argument otherwise checks under its
stated retained contracts and the intended independent padding exponents.
This is a full first review, not a partial approval. No author byte was
edited, and no application, helper, import, compilation, AST, residue,
tuple, Lean or TeX/PDF computation was performed.

The exact reviewed adapter has MANIFEST SHA256
`4dd6c09c956a0828490231efc1da63b3ec2c882355d7054f9a4bc3c76fe59c39`
(530 bytes), two payloads61225 bytes. README is27213 bytes/551 lines,
SHA256 `4996237ed45371f0abd01650054bc6d5b0e064f9cf7ec87780bfe653479f0617`;
SOURCE_PINS is34012 bytes,
`5cda7c59bf45e4c63dd76da0a08b7bafdabc1e7bd6ee1224a52c01084b425ec9`.
All three files remain exactly frozen. The finding and this whole first
review must be preserved before any separately authorized naming repair.

## Finding NATIVE_PADDING_EXPONENT_BINDING

Section1, README line29, explicitly fixes

> Put b=65,L=8807,rho=2^65,d=bL,B=rho^L,beta=B-1 and mu=2^51-2.

Section8, lines355--356, then says

> Choose independently large spatial width w0=lambda^a and height h0=lambda^b
> for the canonical padded halting tiling; N=w0*h0=lambda^n.

There is no explicit local rebinding of b or fresh local domain for the
height exponent between these statements. Section9 explicitly distinguishes
its reused E,S,T abbreviations; section8 supplies no analogous distinction
for b. With the prior binding, h0 is the fixed integer lambda^65. That
does not supply independently arbitrarily large heights for a hypothetical
finite halting run of unrestricted length. The whole language proof grants
all sufficiently large heights, so this is a name-binding defect in the
completeness construction, not a counterexample to the intended method.

Use fresh independently variable positive integer exponent names for width
and height, state their domains/cofinal choice, and define n as their sum.
Keep the native bit width b=65 and d=65L fixed. The repair should not change
any coefficient, bound, target, unit, controller recipe or source map.
No repair is made or authorized by this review. The preserved source and
both complete first reviews should precede any bounded repair release;
the resulting final ordinary packet needs its own complete rereading.

## Exact authentication and review scope

Fresh inert checks authenticate all158 direct source pins, the own README
pin, both payloads, the MANIFEST and exact three-file membership. Every
selected complete closed parent has its exact member set and all hashes:

| Whole parent | Payloads | Payload bytes | Manifest SHA256 |
| --- | ---: | ---: | --- |
| candidates/one-page-compact66 | 62 | 559504 | `ce9915c9f494c163a4925565cfb366c9ddfbad25ecdd1ef02cc44c384459f20c` |
| research/indexed-tile-enumeration | 38 | 359892 | `e077a476c38cb9abd96217887d16b011f6f5e16847036702720d69fcf91b1f84` |
| research/compact66-radix-boundary | 2 | 13932 | `3812f425d4d1e434c0b53de547c62b77975e905a63f5422b8b386baa659c898f` |
| research/compact66-radix65-unit-probe-verification | 18 | 74110 | `b80414c01a2ca5233cbe2da4e1c95333077a3b9762687534fbc4ad75ccb5d51f` |

The exact six-file held unit probe also matches every stated byte and
flattened pin. Its presence is evidence, not permission to execute it.
Inert decompression/hash inspection reauthenticates both identical accepted
old port sets:74111 K bytes and73759 bytes each for beta,MC,MF_source,
295388 raw bytes per set. No raw integer was reconstructed, no Phi array
was generated and no new radix65 coefficient was evaluated.

I read the entire frozen551-line adapter and all its displayed formulas,
the whole indexed proof, native44 aggregate/layout/controller proof,
the radix-boundary note, premise audit and accepted modular evidence
reviews, compact66 positive source proof, squared-modulus proof, and
the retained P67/ordinary/helical/coefficient-transfer arguments relevant
to each use. The actual indexed certificate and complete normal bounded
probe report were read as data. Whole code/PDF/receipt pin authentication
does not imply a new static program audit, rendering or execution.
This review is independent of the adapter's author. My earlier review
of the conditional radix note and work on retained compact-page sources
are parent history, not approval of this new adapter by implication.

## Coherent four-port formula and aggregate decoding

All four ports are defined together at rho=2^65,L=8807. The selector
coefficients retain the exact ordered943 tile bindings, all41 copy/anchor
controls and both zero dummy holes, through all3297 Phi coefficients.
The payload lower bound127*2^34 and upper bound2^41 give positive
selector coefficients at most1+2^44; every control coefficient is at
most2^50. Thus all are canonical new-radix digits, without reconstructing
new integers. The complemented and original payload expressions agree
because2^41-127*2^34=2^34.

The scalar K0 recipe is exactly DC+B*DR, and B*DR=rho^8849. All reflected
exponents are positive, with minimum1097. The support-decoded MC formula
also checks: its indicator sum omits precisely1063/1064; expanding the
correction gives beta-sum_(E excluding1)rho^e-2rho^1063. MF_source shifts
MF_native by beta exactly once. No old numerical port is transferred or
identified with a new one.

The aggregate complement proof is complete without assuming payload carry
freedom. The low ten bits isolate the selector count n<1024 and force
n=0 or1. If empty, all41 copy bits vanish. If occupied, the remaining
integer is strictly between0 and2^42 and divisible by2^41, so it equals
2^41 and the copies equal the full payload. Both dummies have coefficient
zero, including the permitted upper dummy bit. No tile uniqueness is
used in advance of this argument.

## Predecoded cyclic carry, all targets and alignment

The low mask permits digits at most3, since only1063 can contain both
its low and upper bit. The forced Start addition has no carry at the
origin. For arbitrary supported predecoded C, the full nonnegative
kernel has mass A=2*Csum+5, so every cyclic convolution coefficient is
at most3A even with support collisions and any number of cells.

The ACTUAL indexed threshold118788496120850159560 yields Hc<rho/988 and
3A<rho/4. It is not the historical native44 numerical threshold. For
epsilon1..63, the shifted digit bound is3*2^epsilon<=3rho/4 with no spill.
For epsilon64, its low bit contributes rho/2 and the preceding upper
dummy can contribute1. That single within-cell odd spill lands at1064,
already in E. Adding3A remains strictly below rho in every case,
including epsilon0. This is a bound before aggregate/tile decoding.
The supplied strict F box excludes the0 versus q-1 cyclic ambiguity.

Every current/spatial/temporal target family in section4 is justified
formally. The north targets1013..1022 see only shift30's983..992 and
their temporal copy. The spatial targets1065..1073 see shift62's
1003..1011 and DR's1023..1031, with no temporal copy. Anchors2195/3296
see exactly1095 through1100/2201 and the temporal anchors. The clause
targets have coefficients c_e and no spatial contribution. All unwanted
bare predecessors and reflected differences are accounted for.

In particular E-E omits2198,1097,2199,1102; its sole pair of positive
difference1101 is(2195,3296). The explicit S span and two high anchors
prove these exclusions. Since L>2max(E), there is no circular exception.
Thus the two clause-hit sets are disjoint and the two anchor-hit sets
intersect exactly at0. All facts cover both dummies and arbitrary inputs,
not merely accepted local cells or the old66062 numeric checks.

At least one whole clause band is clean under every rotation. Start then
forces its three anchors. The two anchor parity tests exclude all
epsilon1..63 and the unique epsilon64 spill; the unique intersection
forces a whole-cell offset. Copy tests compare two Boolean bits after
alignment, horizontal occupation propagates through all cells, and all
typed edge labels match. A zero temporal stride is excluded by Start's
north435/south1 mismatch. Arbitrary nonzero soundness strides, multiple
Starts and unrelated components are permitted. The exact state/color/
selector conjugacy and the marked strip proof recover the original
blank machine and syntactic refutation.

## Full-width padding, population, low phase and raw slack

All intended current products end at8791, spatial products at3338 and
temporal copies at3296. The padding fields8792..8805 therefore test
actual zeros, including every safe low-dummy subset. Full65-bit padding
values are masks, not terms in the transport convolution. Soundness
only gains restrictions from them. The false doubled-padding inequality
is neither needed nor silently reused.

Their population864 plus two50-bit clause masks,19 copy tests, two
anchors and the low field gives986. MC removes985 ordinary support bits
plus the extra upper dummy bit, also986. All fields are disjoint; masks
remain strictly between0 and beta, DC lies strictly between0 and B,
MC=2 mod4 and MF_native=4 mod8. The high padding still ends below digit8806.

Replicated B-block masks remain disjoint. At the origin adding1 to MC*J
changes10 to11; subtracting1 from MF_native*J changes100 to011. Hence
the two populations sum to dN+2 exactly. The low F tests at the origin
and elsewhere pass from the canonical single Start and0<width<N; safe
dummy changes do not affect that field. Canonical digits are at most1,
so native F coefficients are at mostHc and those of2C+F at mostHc+2.
The displayed geometric estimate proves2C+F<q/3 and alpha>0 throughout
all Boolean rank adjustments.

## Orders, bounded Hctrl units and fresh actual-rank controller

The retained old full order modulo lambda implies ord_lambda(2)=581196;
the8807 order transfers as stated. New d=5*13*8807 is coprime to the
relevant orders. The orders at5,13,8807,lambda are4,12,4403,581196 and
divide lambda-1. LTE transfers valuation1 from the OLD lift to2^kappa-1
and then the NEW B^kappa-1, because lambda divides neither cell exponent.
No old lambda-square residue is asserted for the new base.

ROOT's bounded acceptance9d2ba20512 and the full ordinary evidence review
precede this freeze. Their accepted complete-Phi two-route conclusion
gives Hctrl residues4,5,62,418969 at5,13,8807,581197. These are existing
reported modular results read as data, not recomputed here. In particular
K0 being0 modulo13 is harmless: the needed bracket is a unit. This
bounded acceptance supplies no full new tuple or native/source theorem.

For independently variable sufficiently large padding exponents, the
controller is otherwise complete. N>d*lambda^2 and h0>lambda give
T>C0=d*lambda and w0<T. Orders give q=B^w0=B at each relevant prime.
The exact safe-bit change of the ACTUAL rank is-Gamma*B^j, with Gamma's
three factors reducing to a power of2,B^2-1,Hctrl; hence it is a unit
modulo dN. LTE and CRT give exactly the T orbit values1+C0*z.

After choosing epsilon to leave a nonzero residue modulo lambda, the
least a0 modulo C0 satisfies1<=a0<C0<T and is prime to T. Summing a0
distinct consecutive orbit coordinates solves every target residue.
The extra B^3 position is distinct. The maximum physical position
N-T-lambda+3 and w0<T give both required no-wrap translations and avoid
the origin. Every selected bit is Boolean. Applying this to the actual
R0 adjusts its defining F,C expression to R=d*w0 modulo dN; no rank
is independently chosen. This controller proof is sound once the padding
exponent naming in the finding is fixed.

The strict rank bound makes w=2^(R-dN)>B^w0 positive. Its congruence
modulo q-1 gives the stated positive integral z and exact Nt=1.
Forward population yields pc(R)=3dN+2; the authentic low masks give
C=1 mod4,J=1 mod4,R=3 mod4. Odd d,N make w a square, and the retained
ratio/normalized-strong construction supplies the odd cofinal promises.
No old native words, actual rank, Gamma or private Pell tuple is reused.

## Both complete positive P66 maps and retained calibration

The scaled product divides by positive Delta only in the proof. Its
four norm units become+1 by the negative-Pell/mod4 arguments, leaving
Nk=Nt as a coupled unknown sign. Weak transport supplies C>=0 only.
The uniform bounds R<q^4-2,E>R+2,a>R+2 hold from scalar mask boxes.
The retained strong/signed-auxiliary arguments recover p=R and exclude
the negative sign using eta,zeta>0. C>0 follows only afterwards.
Main projection then gives X=2^R, q=B^N and the exact Y valuation.
The shifted packing/inverse-population theorem recovers masks before
native carry/alignment is invoked, so the proof order is not circular.

The direct soundness bridge T_old=f*T preserves all positive inputs
and four new coherent ports. Alternatively i_ordinary=Delta*i reaches
the ordinary proof with the same unresolved signs. Neither bridge
divides supplied i by Delta or assumes an old quotient divisible by f.

Conversely, the new native/controller family, with properly variable
padding exponents, supplies fresh normalized witnesses. The integer
Q_j identities yield V*=chi_S(R)/S=-c mod f^2 and-R mod c. Coprimality
of c,f and f^2=1 mod c make T*=(V*+c+R*f^2)/(c*f^2) a positive integer.
Replacing only T,y preserves the other source factors. No shifted
T*-alpha endpoint or generic shifted R=3 claim is used. These are full
positive existence maps, not a pointwise transfer of private witnesses.

The unchanged free-port66/157 formula and its nonzero8*beta^92 leader
remain mathematically uniform. This review does not supply a fresh finite
DAG audit or new specialization metadata. The exact ordinary source131/
K215/refutation/foundational contracts remain inherited; no new internal
ZFC/Lean certificate or unconditional consistency claim is made.

Only this outside review pair is written. The frozen adapter, all accepted
parents, held probe, maintained compact66 page and paused Lean files remain
unchanged. No numerical65-bit endpoint or page/byte saving is accepted.
