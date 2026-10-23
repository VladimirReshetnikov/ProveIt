# A smaller Wang943 coefficient tuple

## Result and scope

This is a new complete coefficient tuple for the inputless Wang943 native/Pell
interface, retaining the literal K215 machine, tile order, and mixed-radix
decoder of wave-4 package 27. Set

    b=125, rho=2^125, L=8101, d=bL=1,012,625, B=2^d.

The four minimal little-endian unsigned integers occupy 506,644 bytes.
Compared with packages 25 and 27, d falls from 1,953,125 by 48.1536%.
This is a coefficient-height improvement, not a change in variable count,
degree, or arithmetic-operation cost. No global minimality is claimed.

The proof below transfers the ENTIRE canonical native/Pell interface,
including its positive witnesses, square scale, odd normalized multiplier,
and odd `s`. New geometry, a composite-modulus Boolean-subset lemma, and
the actual-rank unit are proved explicitly. The inherited native/Pell
compiler and K215/refutation calibration remain ordinary mathematical
dependencies; no fresh Lean/Rocq end-to-end certificate is claimed.

## 1. Source and the unchanged finite language

All source references are pinned to ProveIt commit
`8c6eec9d19ef80538c8e61ff6e0180040583446a`. Under
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/`,
the principal source is `27-wave4/coefficients/COEFFICIENT_PROOF.md`, with
its `upstream/compiler/WANG943_COEFFICIENTS.md` and
`upstream/compiler/WANG943_COMPACT_LAYOUT.md`. These are the source of
the 943-tile language, helical soundness/completeness, the compiler
interface, and mixed-radix clause decoding. This note changes the native
positions and the arithmetic used to choose the cell length.

The source's 943 ordered tiles are kept exactly. The supplied generator
independently reconstructs them from the 430 literal machine actions and
compares the complete ordered list with the pinned JSON. Tile 0 is Start;
tile 1 is Forbidden. A tile has west/north/east/south labels, each encoded
as the ten-bit word `label+512`; its highest bit records occupancy. The
source proof establishes:

1. A marked periodic Wang plane exists exactly when blank K215 halts.
2. Every finite blank halt admits the canonical single-Start helical word
   with independently arbitrarily large width `w=5^u` and height `h=5^v`,
   hence `N=wh`; spatial shift is one cell and temporal shift is `w` cells.
3. An arbitrary decoded cyclic word with the two edge matchings pulls back
   to a periodic plane, with no divisibility condition on its temporal shift.

No machine transition, edge label, tile, or tile index is changed here.

## 2. Complete finite recipe

For `j=0,...,43`, put `W_j=1024*4^j`. Native copy exponents are now

    west:  1024+2j,   north: 1004+2j,
    east:   984+2j,   south:  964+2j,    0<=j<10.

The four anchor exponents, in clause-weight order, are

    1110, 1112, 1111, 2225.

The dummy exponents are 1065 and 1066. Let E be the union of these positions
with selector exponents `0,...,942`. Its cardinality is 989. The possible
upper-dummy spill exponent is 1066, already in E. More explicitly,

    S=[0,942] union {964,966,...,1042}
      union {1065,1066,1110,1111,1112},
    E=S union {2225}.

For tile i with slot labels `x_it`, define

    c_i=1+sum_(t=0..3,j=0..9) bit_j(x_it+512)*W_(10t+j)
           +W_40+W_41+W_42+W_43.

At the copy position for slot t and bit j, put `c_e=W_(10t+j)`; at the
four anchors in the order above, put `W_40,W_41,W_42,W_43` respectively.
Both dummy coefficients are zero. Define

    mu=1022+sum_(j=0..43)W_j,
    DC=rho+rho^40+rho^61+rho^1113
       +sum_(e in E)c_e*(rho^(3341-e)+rho^(4459-e)),
    DR=rho^21,
    MF_native=4+mu*(rho^3341+rho^4459)
       +sum_(j=0..9)rho^(1004+2j)
       +sum_(j=0..9)rho^(1045+2j)
       +rho^1111+rho^2225
       +sum_(z=6685..7544)rho^z,
    MC=B-1-sum_(e in E,e!=1)rho^e-2*rho^1065.

The actual four integer coefficient ports are exactly

    beta=B-1,
    K=DC+B*DR,
    MC,
    MF_source=MF_native+B-1.

The fourth port is ALREADY shifted. A circuit using the native MF instead
would be a different construction. Replace all four ports together.

Every displayed sum is finite and bounded independently of whether K215
halts. The coefficient definition does not wait for a halting computation.

## 3. Mixed-radix decoding and exact geometry

The native low mask still permits Boolean selectors, copies, and anchors;
the low dummy has values 0..3 and its adjacent dummy is Boolean. The
low ten bits of a clause sum count selected tiles, a number between 0 and
943. All other clause coefficients are divisible by 1024. The low mask
1022 therefore forces that count to be 0 or 1, without any assumption
about carries in higher digits. Once it is 0 or 1, each of the 44 radix-4
digits is a sum of at most two Boolean bits. Its masked low bit forces
the two bits to agree. Thus a cell is empty or contains exactly one tile,
its exact forty edge bits, and four anchors equal to one. This is exactly
the source decoder.

The spacing of copy exponents has changed; the following exact identities
replace the old geometry. Write the four bare shifts as `{1,40,61,1113}`.

* At `1004+2j`, the only DC bare predecessor is `964+2j`, through shift
  40. The unwanted predecessors under shifts 61 and 1 lie respectively
  in the odd intervals 943..961 and 1003..1021, outside E. DR's predecessor
  lies in the odd interval 983..1001, also outside E. The temporal native
  predecessor is exactly the north-copy position `1004+2j`.
* At `1045+2j`, the only DC bare predecessor is `984+2j`, through shift
  61. Shift 40 sees the odd interval 1005..1023; shift 1 sees the even
  interval 1044..1062. Both miss E. DR shift 21 sees exactly `1024+2j`.
  The target itself, in the odd interval 1045..1063, is outside E.
* At 1111, DC sees only 1110, through shift 1. Its other predecessors
  are 1071,1050,-2; DR sees 1090; all are outside E. The temporal anchor
  is 1111.
* At 2225, DC sees only 1112, through shift 1113. Its other predecessors
  are 2224,2185,2164; DR sees 2204; all are outside E. The temporal
  anchor is 2225.

For a reflected clause term to contaminate a tested target t one would
need `3341-t` or `4459-t` in E-E. All these differences exceed `max(E)=2225`
except `3341-2225=1116`. That last difference is absent: a pair within S
is too close, and `2225-1116=1109` is outside E. Thus the displayed bare
identities are the full DC identities, not just a check of its four
unweighted monomials. At each clause target, every bare or DR predecessor
lies above E: the smallest is `3341-1113=2228>2225`.

The separation of the clause bands is 1118. It exceeds the span of S,
and `2225-1118=1107` is outside E. Hence 1118 is absent from E-E. As
`L=8101>2*2225`, this also proves that the two sets

    (3341-E) mod L,     (4459-E) mod L

are disjoint. Therefore every binary rotation leaves a clean clause band.
The exact source selector decoder applies before any stride is assumed.

The two tested anchors differ by 1114. It exceeds the span of S, and
the unique pair in E of that difference is `(1111,2225)`. Consequently

    {(1111-e) mod L:e in E} intersect
    {(2225-e) mod L:e in E} = {0}.

The inherited parity argument excludes within-radix binary offsets
1 through b-2 and b-1 (the latter supplies at most one odd upper-dummy
spill, whereas both tested anchors require an odd digit). The displayed
intersection then forces a whole-cell temporal shift. No new stride
assumption has been made. The copy equalities give the unchanged Wang
matching contract, and the occupancy bit propagates from Start around
the cyclic word by the one-cell spatial shift.

## 4. Carries, population balance, and safe dummy changes

The clause coefficients and native support cardinality are unchanged.
Use the source's conservative bound

    mass=(989+2)*(2*sum_(e in E)c_e+6).

Its bit length is 118; `4*mass+8` has bit length 120, and mu has bit length
97. Thus `4*mass+8<2^125` and `2*mu+4<2^125`. These bounds hold BEFORE
selector extraction, including every allowed dummy value. The source's
global no-rho-carry and strict positive-slack estimates therefore apply.

All reflected exponents are positive; the smallest is `3341-2225=1116`.
The maximal unshifted convolution exponent is

    4459+2225=6684.

DR products reach at most 2246, and temporal native terms at most 2225.
Consequently the 860 added field tests at 6685..7544 are identically zero
in every aligned intended cell, including after every safe dummy change.
They are below L=8101, so unshifted products and masks stay inside one
radix-B cell. Soundness may ignore these added tests; completeness satisfies
them automatically.

The clause mask population is 53, so the original field tests have
population `2*53+20+2+1=129`. Adding 860 gives 989. MC removes 988 low
native bits plus the upper bit of the low dummy. Hence

    pc(MF_native)=989,
    pc(MC)=d-989,
    pc(MC)+pc(MF_native)=d,
    MC=2 mod4, MF_native=4 mod8,
    0<MC,MF_native<B-1.

The generator verifies these identities on the fully materialized integers.
The two masks are not asserted disjoint; each constrains its corresponding
packed data object, exactly as in the source compiler.

## 5. Boolean rank control without a power-of-five cell length

The following lemma is the only change to the source rank-tuning proof.

**Lemma.** Let `d=125*8101`, `B=2^d`, `N=5^n`, `M=dN`, `T=N/5`, and
assume `T>5d`. Every residue modulo M is a Boolean subset sum of the
distinct physical weights

    {B^(4j):0<=j<T} union {B}.

**Proof.** Since `2^125=90 mod8101` and `90^2=-1 mod8101`, we have
`B^4=1 mod8101`. By the elementary lifting-the-exponent identity,

    v5(B^4-1)=v5(2^(4d)-1)=v5(2^4-1)+v5(d)=4.

As 8101 is coprime to 5, `B^4` therefore has exact order T modulo M.
Its powers lie in, and hence enumerate bijectively, the T residues
`1+5d*t`, `t modT`. This uses only the displayed congruence and coprimality;
no primality assumption on 8101 is needed.

Given a target z, choose epsilon in {0,1} so that `z-epsilon*B` is a unit
modulo 5. Choose the unique k with `1<=k<=5d` and
`k=z-epsilon*B mod5d`. Then `k<T` and `gcd(k,T)=1`. Put
`u=(z-epsilon*B-k)/(5d) modT`. Choose

    r=k^(-1)*(u-k(k-1)/2) modT.

The k distinct cyclic residues `r,r+1,...,r+k-1 modT` have sum u modulo T.
Their corresponding distinct powers `B^(4j)` sum to `k+5d*u` modulo M.
Adding `epsilon*B` gives z. This is a Boolean subset with no repeated
physical cell, negative coefficient, or uncharged multiplicity. QED.

The same proof works for any fixed positive d for which the powers
`B^(4j)` enumerate `1+5d*t mod dN`; it isolates the needed hypothesis
rather than assuming d itself is a power of five.

For the canonical helical word take sufficiently large independent powers
of five w and h, with `N=wh`, `N/5>5d`, and `w<N/5`. The chosen physical
indices are at most `4N/5-4`, and the optional index is 1. Their spatial
and temporal destinations remain below N, so the source's literal
nonwrapping rank-difference identity applies to every selected cell.

## 6. The actual rank switch is a unit

Put `q=B^N`. Changing the ignored low dummy at cell j changes the ACTUAL
packed rank by

    -Gamma*B^j,
    Gamma=rho^1065*(q^2-1)*[1+q*(DC+B*DR+B^w)].

It remains to prove that Gamma is invertible modulo dN. The relevant
coprime components are the power of five and 8101. Modulo each component's
base modulus (5 and 8101), rho has order four: rho=2 mod5 and rho=90
mod8101, with rho^2=-1. Since `L=8101`, `N`, and `w` are all 1 mod4,

    B=q=B^w=rho.

The paired clause terms cancel because their separation 1118 is 2 mod4.
The four bare shifts 1,40,61,1113 give

    DC=1+3rho,     DR=rho.

Therefore

    q^2-1=-2,
    1+q*(DC+B*DR+B^w)=-3

modulo both 5 and 8101. As `gcd(8101,30)=1`, both are units. Thus Gamma
is a unit modulo dN. The Boolean lemma chooses a safe lower-dummy subset
so that the actual rank R satisfies

    R=d*w mod dN.

All selector, edge, anchor, mask, and added-zero-field conditions are
preserved by these allowed dummy changes. This closes the new completeness
obligation. It does not replace R by an arbitrary formal parameter.

## 7. Full interface, parity, and odd scale

Soundness follows from the unchanged native arithmetic recovery, clean
clause decoding, synchronization, and Wang-language soundness already
proved. Completeness starts with an actual finite blank halt, chooses the
canonical padded word, tunes its actual rank as above, and then applies
the source half-binomial/Pell construction to that modified genuine word.
The source strict inequalities and positivity estimates are unchanged:
the same mass bound holds and all products remain inside their cell.
In particular the inherited bounds `3q+1<R<q^4-2` remain available.

For completeness, here is the exact population and parity calculation
needed by the signed and normalized downstream forms. Write `t=dN`, so
`q=2^t`, and set

    S_data=(C-1)+qF,
    Tmask=(MC*J+1)+q*(MF_native*J-1),
    M0=q^2,
    R=(M0-S_data)*(M0-1)+Tmask.

The genuine native masks give `S_data AND Tmask=0` and both integers in
`[0,M0)`. Replicated mask blocks do not overlap. Since the canonical
Start gives `C=1 mod4`, and `J=1 mod4`, the mask congruences yield

    pc(Tmask)=N*pc(MC)+1+N*pc(MF_native)+1=t+2.

The exact identity

    R=(M0-1-S_data)*M0+(S_data+Tmask)

then gives `pc(R)=3t+2`, because the high block is the 2t-bit complement
of S_data and the low block has no binary carries. Also `S_data=0 mod4`
and `Tmask=3 mod4`, so `R=3 mod4`. Both t and R are odd. The main Pell
witness `X=2^R` thus gives a square scale `X/q=2^(R-t)`.

The source's even Pell parameter `A=Y*(X+1)+2`, odd index R, and choice
`m=cR` supply an odd positive normalized multiplier; the ordinary
Delta-scaled multiplier is also odd because `Delta=A^2-1` is odd.
Finally the authentic half-binomial kernel gives

    v2(Y)=pc(R)-2=3t.

As `Y=s*q^3`, this forces s positive and odd. Thus the full source
odd-scale promise transfers. The coefficient change may be used by an
arithmetic skeleton proved from this complete interface, provided ALL
four ports are rebound together. This package's main signed16 theorem
retains its original source tuple; the present tuple is an independent
optional improvement, not a silent change of that fixed instance.

## 8. Verification boundary and reproducibility

Run `python3 build.py` to reconstruct the complete language, verify all
69,230 native-basis convolution identities, materialize the four integers,
and check all scalar, population, residue, and file-round-trip identities.
Run `python3 audit_independent.py` for a separately written reconstruction
and comparison, plus a finite check of the general Boolean-subset lemma.
Both scripts use only Python's standard library and the bundled inert JSON.

These finite calculations verify the displayed finite recipe and its
arithmetic identities. They neither decide Con(ZFC) nor replace the
unbounded mathematical compiler argument. The exact ZFC-provable
equivalence is obtained by composing the transferred interface with the
source finitary K215/refutation calibration.
