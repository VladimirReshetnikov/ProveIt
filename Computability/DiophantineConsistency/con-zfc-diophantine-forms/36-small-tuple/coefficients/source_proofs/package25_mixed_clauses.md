# A smaller coefficient tuple: mixed radix and external zero padding

## Result and scope

This compiler adapter combines package 19's 943-tile language and exact-support
layout with three changes: a short spatial transport, mixed-radix clause
fields, and population-balancing tests placed outside the computation support.
It replaces all four fixed ports together. The resulting base is

    B = 2^(5^9) = 2^1,953,125,

versus package 19's `2^(5^10)`. The four actual unsigned integers occupy
977,220 bytes in total, versus 5,312,269 bytes. The largest coefficient K has
1,958,376 bits, versus 13,201,251 bits. All arithmetic skeleton variables,
degrees and operation counts are unchanged by this coefficient substitution.
The proof is ordinary mathematics relative to the inherited native compiler
and K 215 calibration, not an end-to-end proof-assistant certificate.

Source pin: `ae3007ca4467011e0e051c84acb4a1dd13971b0e`, package directory
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/19-wang943`.
The inherited 943-tile language, marked periodic tiling theorem, helical
padding theorem and dummy-control argument are unchanged.

## 1. Complete coefficient recipe

Use exactly package 19's ordered 943 tiles. Tiles are `(west,north,east,south)`.
The builder independently reproduces the table from the pinned 215-state
machine; its tile-list SHA-256 is
`66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f`.
Start is selector 0 and the impossible tile is selector 1. Every edge label
is encoded by its ten-bit value `x+512`; the high bit expresses occupation.

Put `rho=2^125`, `L=15625`, `d=125 L=5^9`, `B=rho^L`. For `0<=j<10` set

    e_0(j)=1023+j, e_1(j)=1013+j,
    e_2(j)=1003+j, e_3(j)=983+j.

Let the anchors be `(u1,u2,v1,v2)=(1095,1096,2195,3296)` and define

    E = {0,...,942} union {all e_t(j)}
        union {1063,1064,1095,1096,2195,3296}.

Thus `|E|=989`. Define `w_j=2^(10+2j)` for `0<=j<44`. If tile i has labels
`x_it`, define

    c_i = 1 + sum_(t=0..3,j=0..9) bit_j(x_it+512) w_(10t+j)
            + sum_(j=40..43) w_j;
    c_(e_t(j)) = w_(10t+j);
    (c_1095,c_1096,c_2195,c_3296)=(w_40,w_41,w_42,w_43);
    c_1063=c_1064=0;
    mu = 1022 + sum_(j=0..43) w_j.

The two clause targets are `T1=4393`, `T2=5495`, the spatial transport
exponent is `H=42`, and the four bare shifts are `(30,62,1100,2200)`.
Define the external padding mask

    Z = (2^123-1) sum_(e=9000..9005) rho^e
        + (2^122-1) rho^9006.

The native constants are

    DC = rho^30 + rho^62 + rho^1100 + rho^2200
         + sum_(e in E) c_e (rho^(4393-e)+rho^(5495-e));
    DR = rho^42;
    MC = B-1 - sum_(e in E, e != 1) rho^e - 2 rho^1063;
    MF_native = 4 + mu(rho^4393+rho^5495)
                + sum_(j=0..9) (rho^(1013+j)+rho^(1065+j))
                + rho^2195 + rho^3296 + Z.

The four actual arithmetic ports are

    beta=B-1, K=DC+B DR, MC, MF_source=MF_native+B-1.

All sums are finite. No coefficient depends on waiting for a halting run.
Downstream `MF` always means `MF_source`.

## 2. Why mixed-radix clauses work

At a clean clause target, the native compiler tests the binary disjointness
of `S=sum_e c_e d_e` and `mu`. The native digits are Boolean, except for
the two dummy positions; their clause weights are zero. Let `n` be the sum
of the 943 selector digits. The lower ten bits of S are precisely n because
`0<=n<=943<1024` and every other clause contribution is divisible by 1024.
This statement needs no prior bound on any higher field. The low mask 1022
therefore forces `n` to be 0 or 1.

Once this has been established, every higher field is the sum of at most one
selected tile bit and one copy bit, or of n and one anchor bit. Every such
sum is in `{0,1,2}` and thus is carry-free in radix4. The corresponding
masked bit is its low bit, so the allowed values are 0 and 2. Therefore:

* n=0 forces every copy and anchor digit to 0;
* n=1 forces every copy to equal its tile bit and every anchor to 1.

Conversely, every one-tile encoding and the all-zero encoding pass exactly
these tests. The mask's 53 bits comprise nine selector-count bits and one
bit for each of 44 copy/anchor fields. The logic is identical to the earlier
uniform-radix clause, but count decoding is proved first. Prematurely
assuming all upper fields are carry-free would be incorrect; the argument
above avoids that assumption.

## 3. Exact geometry and synchronization

The native support E, its potential upper-dummy spill position 1064, and its
anchor pairs are the same as package 19's compact compiler. In particular:

    {(4393-e) mod15625:e in E}
      intersect {(5495-e) mod15625:e in E} = empty;
    {(2195-e) mod15625:e in E}
      intersect {(3296-e) mod15625:e in E} = {0}.

The first identity supplies a clean clause band for every binary rotation;
the second supplies unique whole-cell anchor synchronization once binary
alignment has been proved. The band gap 1102 is outside E-E. The support
span 3296 is less than half the circumference, so there is no missed circular
case. The inherited two-anchor parity argument also excludes the unique
upper-dummy spill when the binary remainder is 124, exactly as before.

The target identities are:

| target | DC native source | DR native source | temporal source |
|---|---|---|---|
| 1013+j | 983+j | none | 1013+j |
| 1065+j | 1003+j | 1023+j | none |
| 2195 | 1095 | none | 2195 |
| 3296 | 1096 | none | 3296 |

For every e in E, these are exact coefficient identities, including both
reflected clause bands. At each clause target T, `coefficient(DC,T-e)=c_e`
and `e+42 != T`. The supplied checker enumerates all69,230 native-basis
identities; by linearity they prove these statements for every native
assignment, including dummy digits 0..3. They are finite exact arithmetic,
not random tests or simulations of the unknown blank run.

One can also inspect the small gaps directly. For example, the spatial
targets 1065..1074 minus 30 are 1035..1044, absent from E, while minus 62
are precisely the east-copy positions 1003..1012. The temporal targets
1013..1022 minus 62 are 951..960, absent from E, and minus 42 are 971..980,
also absent. The clause bands and anchors satisfy the same finite identities.

## 4. Why external population padding is harmless

The two short clause masks contribute 106 bits. The twenty overlap tests,
two anchor tests and low bit contribute 23, leaving 860 bits to reach 989.
Z contributes exactly `6*123+122=860`.

For an aligned canonical witness, every term of `DC C_current` is supported
at rho-exponents at most `5495+3296=8791`, and `DR C_spatial` at most3338.
The temporal native word has support at most 3296. Thus every bit tested
by Z (at exponents 9000..9006) is identically zero. Adding Z never excludes
a canonical halting witness, including any dummy choices. Soundness uses
only the original clause/overlap/anchor/low tests; the added tests can be
discarded when extracting a tiling. They cannot create a spurious solution.

The complete population identities and low congruences are

    pc(MF_native)=106+23+860=989;
    pc(MC)=d-989;
    MC=2 mod4; MF_native=4 mod8;
    0<MC,MF_native<B-1.

Therefore the inherited inverse-population arithmetic and exact two-bit
surplus work without change. Population-balancing bits do not need to be
located inside the clause band: only their count and canonical zero values
matter to this argument.

## 5. Carry bounds and five-adic tuning

With the new clause coefficients, the same inherited uniform bound

    mass=(989+2)(2 sum_e c_e+6)

has118 bits; `4mass+8` has120 bits. The compact clause mask has97 bits.
The largest external padding digit has 123 bits, so even the conservative
bound `2(2^123-1)+4` is smaller than `rho=2^125`. Thus every old no-carry
and positive-slack estimate holds. The padding is a mask, not an additional
summand of the computation, so it causes no new computational carries.
Unshifted support and all tested mask positions lie strictly below L.

Since125 is a power of five, `rho=2 mod5`. The gap1102 is2 mod4, so each
paired reflected-clause contribution cancels modulo 5. The bare exponents
give `DC=0 mod5`, while `DR=4 mod5`. Hence

    2DC-DR=1 mod5,

a unit. The native dummy-control proof therefore still adjusts the actual
packed rank to the required temporal stride. It does not require the
earlier unit value 4. The same independently padded power-of-five width
and height witnesses supply its size and no-wrap conditions.

## 6. Conclusion and verification limits

The new four-port tuple has the same inputless native compiler interface as
the original 943-tile tuple: solutions correspond to marked periodic Wang
tilings, hence to blank K 215 halting, hence to finite ZFC refutations under
the pinned K 215 calibration. Replacing the four ports of any proved
compatible skeleton therefore preserves the claimed ZFC-provable
equivalence between unsolvability and Con(ZFC).

`build_coefficients.py` generates all four exact gzip payloads, decodes
them, checks masks and congruences, and records hashes/bit lengths. Its
69,230 exact finite support checks and local decoding checks complement
the mathematical argument. They do not formalize or reprove the imported
native Pell/compiler or foundational endpoint theorems.
