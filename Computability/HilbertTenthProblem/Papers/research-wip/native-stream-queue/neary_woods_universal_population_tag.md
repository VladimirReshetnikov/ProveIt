# An explicit universal tag polynomial in 399 operations

The fixed U9 machine, its proved ordinary-input format and a population
constraint for the recoder width give one universal polynomial using
**399=192M+207A operations**, **70 positive existential witnesses** and
four positive program parameters besides the ordinary positive input x.
The certificate costs **325=167M+158A operations** and25 comparisons.
Its total degree is **at most2204**, including the four program
coordinates. The same fixed polynomial represents every r.e. subset of
the positive integers by choosing those four parameters.

This replaces the fixed-exponent chain of the
[524-operation U9 construction](neary_woods_universal_u9_tag_chain.md)
by two paid gates and one extra positive witness. The actual fixed
machine, production, program slices and all eleven huge fixed-numeral
definitions are unchanged. This is a positive-existence equivalence;
the changed raw source is not the same polynomial away from its zeros.
The separate best established universal bound remains
[87 operations](complete75_normalized_strong87.md).

The [source](neary_woods_universal_population_tag.py) and
[receipt](neary_woods_universal_population_tag.json) contain the complete
399-gate DAG, every supplied coordinate, all comparisons, the actual
finite-table metadata and exact fixed-coefficient recipes. The degree
is an upper bound, not an asserted exact degree.

## 1. The fixed U9 slice and positive loader

We retain the complete [U9 metadata theorem](neary_woods_u9_tag_metadata.md)
and the coefficient binding in the524 application. In particular this
uses the original1968-state binary clockwise table, without quotienting
or adding padding states. Its finite table determines the sparse CTS
appendants and the fixed tag production u by exact random access.

| Fixed quantity | Value |
|---|---:|
| Binary clockwise states |1968|
| z |59101|
| CTS appendants p=2z |118202|
| Tag deletion beta=10p |1182020|
| Encoded production length E_u |5362069348135347630|
| Common encoded CTS-bit-block length K |6338014228120114128608890|
| Data width D=128zK |47946621298704238734708993009920|

The production begins bcb, ends b and has length one modulo beta-1.
For L=E_u-beta+1 and the fixed production offset

    d=val(1 e(u without its last b) 10),
    e(b)=10^beta1, e(c)=1,

the eleven fixed coefficients are exactly those of the
[compressed compiler](binary_tag_parameterized_compressed_compiler.md).
In particular `recoder_radix` means2^(D-1), and `repunit_divisor` means
2^D-1. The latter already occurs in the paid counter-loader comparison;
its new use below is a separately charged multiplication. These are
fixed integers, not extra parameters or instructions to evaluate powers
at runtime. The receipt preserves their recipes rather than expanding
the astronomical production or its binary numeral.

For each r.e. set S choose the reviewed recognizer on pairs(3,1) for0
and(1,3) for1, ignoring leading-zero padding. The actual U9 head cut,
two permanent boundary symbols and n>=2 give at least six A symbols
throughout its valid bi-tag simulation. The singleton-A escape case
remains excluded by that proved input slice. The encoded circular tape
has exactly64n+b_S binary cells, with b_S>0 fixed by S.

The four positive loader parameters A_S,B_S,T_S,E_S are those of the
fixed physical prefix, middle and tail. The strict data-block ordering
proved for this U9 slice gives B_S>0. The sentinel E_S is the integer
encoding of PREFIX MIDDLE TAIL with data and counter omitted. The fixed
prefix and middle already encode all b_S fixed binary cells through
nonempty blocks, so E_S>=b_S. We retain the paid definition

    duration=program_E+program_duration_gap,  gap>0.       (1)

Thus every valid slice forces n>E_S>=b_S. When n is dyadic,
64n<64n+b_S<128n, and the exact least dyadic counter at least the tape
length is128n. Arbitrarily long dyadic zero padding is available for
every ordinary positive input x; the chosen recognizer accepts the
same x under every such padding.

Write z=spread_D(x), Q=2^(Dn) and r_load=(Q-1)/(2^D-1). The unchanged
paid loader gives

    Vinitial=(A_S*r_load+B_S*z)*Q+T_S*r_load+E_S.       (2)

It is positive before typing on all positive supplied tuples. For a
genuine slice it is exactly the sentinel of

    PREFIX DATA_w1 ... DATA_wn MIDDLE MU^(128n) TAIL.

Each DATA contains128z CTS-bit blocks and MU contains z, all encoded
blocks having length K. Their shared scale is therefore exactly Q.
The tag input has length one modulo beta-1, ends b and has length at
least beta. The nonempty four-tile history predicate applies directly;
there is no uncharged initial-halting branch or arbitrary-counter
substitution.

## 2. The changed raw recoder and its bootstrap

Apply the [population-width recoder](native_binary_population_width_recoder.md)
to the literal raw compressed source with its actual fixed width D.
Remove only the guarded private q^D chain and insert

    Q=q+power_gap,       R=(2^D-1)*J.                 (3)

The gap is a new positive witness. Keep B=2^(D-1)Q and all outer
repunit, input, output, duration and joined-AND expressions. Change the
raw geometry scale from q to Q and its index from J to R, including
all bounds and their comparisons. The rewriting helper checks every
old consumer before changing it. The geometry still includes both
ratio slacks, its full strong relation and its auxiliary congruences.

For clarity the synchronization argument is recalled here. At a raw
positive zero, the input bound gives q>=2; the gap gives Q>q. The
retained geometry bound gives R>B>=12 and R>Q. The proved raw geometry
theorem therefore yields Q=2^popcount(R) before any joined-AND typing.
In particular Q and B are dyadic. The unchanged positive fused ports
permit the complete prescribed-scale AND theorem; its scale BqP is
dyadic, hence the positive factors q and P are dyadic.

The first repunit comparison is (B-1)J=P-1. Writing B=2^b, dyadic
divisibility yields P=B^n and J=1+B+...+B^(n-1). Since B>2^D, each
copy of the mask2^D-1 occupies D separate one bits with no carries.
Thus popcount(R)=Dn, Q=2^(Dn) and b=Dn+D-1. If n=1 then R=2^D-1<B,
contrary to the retained strict bound, so n>=2.

Write q=2^e. The second repunit comparison (2B-1)K=qP-1 yields
e=(b+1)m-bn for an integer m. The gap gives0<e<b, while b>n.
Values m<=n-1 give e<0 and values m>=n+1 give e>b. Hence m=n and
e=n: q=2^n and Q=q^D have been recovered from the paid comparisons.

The retained duration comparisons are

    (B-1)*duration_quotient+duration=J,
    duration+duration_slack=B-1.

They force duration=n since J=n modulo B-1 and2<=n<B-1. The joined
AND uses low fields n and n-1; its low residue makes n AND(n-1)=0
without assuming an output-field bound. Therefore n is dyadic. The
unchanged high-field selection and modulus Q-1 then give the unique
output z=spread_D(x), with0<x<2^n. This proves that (1) and (2) receive
their actual intended duration and scale.

Conversely, for every sufficiently long dyadic n and0<x<2^n, take
the usual q,Q,B,P,J,K,z and choose power_gap=Q-q>0. The new index
R is odd, exceeds B>Q and has population Dn. The raw geometry converse
constructs fresh positive witnesses at this new scale and index. The
joined AND converse supplies its independent witnesses, and the
unchanged positive quotient and duration choices restore every other
recoder comparison. No old geometry tuple at scale q,index J is
claimed to survive this change.

## 3. Unit projections, normalization and universality

The actual new raw source is passed through the existing complete unit
wrapper and then the three-core normalized-strong wrapper. Their
critical source guards all pass. The restored q=x+input_slack is at
least2 before typing, Q adds a positive gap, B>1, P=(B-1)J+1 is
positive, and R is a positive fixed multiple of J. The fused AND hats
and native packed indices retain their unconditional positive forms.
The loader and history inputs are positive as established above.

The safe product contains the nine recoder/history norm factors and
one unrestricted recoder checksum, together with the three new strong
norm factors in the normalized form. Each norm excludes minus one
on arbitrary integer tuples by the retained norm identities. Product
one therefore restores all of them and the one checksum before any
native typing. The independent history checksum remains outside this
product as its own comparison. It is never silently multiplied into a
second unchecked checksum.

In each core the new strong unit is
f^2-Delta*(i*c^2)^2. Its value one restores the old strong equation
under i_old=Delta*i; the exact auxiliary-coefficient correction restores
the rest of that core. The full positive converse rebuilds only the
five canonical coordinates f,i,j,o,y in each of the three independent
cores. The unchanged dependency guards ensure that these fifteen
coordinates touch no recoder duration, gap, joined port, loader,
boundary, history checksum or program parameter. This is the reviewed
positive-existence projection, with its complete signed correction
identities; it is not an off-zero identity with the raw SOS polynomial.

Consequently a normalized positive zero restores a raw zero. Section2
recovers the ordinary input, dyadic duration and exact scale; Section1
recovers the physical tag word. The selected history proves that word
halts, and the fixed-halt bridge, finite clockwise compilation and
valid U9 simulation imply x in S.

Conversely, for x in S choose a sufficiently long dyadic n>E_S.
The literal simulations halt, tag cleanup reaches singleton b, and
the independent complete recoder and nonempty-history converses supply
all raw positive coordinates. The positive unit projections and fresh
canonical auxiliary reconstruction give a normalized zero. Thus the
one fixed integer polynomial F constructed here satisfies

    x in S iff there exist y_1,...,y_70>0 such that
    F(x,A_S,B_S,T_S,E_S,y_1,...,y_70)=0.

Program parameters are fixed per S; they are not additional existential
witnesses. Malformed positive parameter tuples need not describe a
program. No such claim is needed for universality.

## 4. Literal ledgers and degree bounds

The former127-multiplication U9 power chain is replaced by1M+1A.
All three forms save126M and add1A, giving a net125-operation saving.
The new gap adds one witness; no comparison is added. The source
derives its own ledger and does not reuse the old chain-count assertion.

| Form | Certificate | Comparisons | Positive witnesses | Polynomial | Degree upper bound |
|---|---:|---:|---:|---:|---:|
| Raw SOS |310|56|89|477=208M+269A|544|
| Native units |319|28|70|402=189M+213A|1384|
| Three normalized strong units |325|25|70|**399=192M+207A**|**2204**|

The optional five-parameter interface with an independent duration bound
has the same counts and degree bounds. The default identifies that
bound with E. It changes the permitted padding for a program slice,
not the ordinary-input language.

Every parameter and supplied witness is assigned degree one; each fixed
numeral has degree zero. Source propagation gives degree one for Q,B,R
and degree three for the computed loader output. After positive field
projection the three native scales have degrees1,4,44. The main norm
at each core uses the exact guarded cancellation

    (X+a*c+G)^2-(a^2+H)*c^2,
    H=4a+3, G=ga*H.

The a^2*c^2 terms cancel; the degree audit bounds the six remaining
terms separately and checks every defining source row. No other
unproved cancellation is used. For the raw form the largest comparison
degree is at most272, so its SOS degree is at most544. In the native
unit form the ten-factor product has degree at most1012 and the largest
outer residual at most186, giving1012+2*186=1384. In the normalized
form the thirteen-factor product has degree at most1874 and the largest
outer residual at most165, giving1874+2*165=2204.

The receipt records every individual factor bound. These bounds include
all four program coordinates and are independent of the size of D.
They do not assert a nonzero highest coefficient or an exact degree.

## 5. Executable checks and limits

Six literal ledgers cover all three forms and both duration-bound
interfaces. The raw checker independently reconstructs the recoder,
changed geometry ports, joined AND, duration, loader and independent
history residuals, then compares their complete SOS with the emitted
source on128 assignments. The two projected forms run256 full retained
residual/product/output correction checks, including both restoration
layers for normalized sources. In total192 assignments have signed
coordinates. Each fixed-numeral role receives one consistent finite
integer specialization throughout each complete DAG.

These are algebra audits, not numerical zeros at the huge actual
coefficients. The fixed metadata and production-letter checks bind
the final source to the actual original U9 table; the parent metadata
and recoder packets supply their independently checked finite simulation
and synchronization cases. The full positive extensions follow from
the theorems above, without materializing an astronomical Pell witness
or expanded universal production.

```sh
python3 neary_woods_universal_population_tag.py
```

Author writer and fresh-default replay passed. Root's independent full
proof/source review and fresh replay passed without findings.
Native_controller's independent full proof/source review and fresh
replay also passed without findings. Its separate scalar executor checked
192 three-core factor/restored-raw-residual/complete-output identities,
96 signed, across both projected forms and both bound interfaces, with
consistent finite Numeral values and rational off-zero root restorations.
All seven local links resolve. No source change followed these reviews.
