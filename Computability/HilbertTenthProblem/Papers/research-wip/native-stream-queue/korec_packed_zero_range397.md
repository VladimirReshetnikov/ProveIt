# One range mask also checks zero branches:397 U21 operations

The [literal compiler](korec_packed_zero_range397.py) gives **397=141M+256A**
operations with one fixed positive program parameter, ordinary positive input,
50 positive witnesses and degree at most21549. Its two-program radix interface
costs **396=142M+254A**, with uniform degree at most40706 and the same witness
count. Both defaults have one comparison and certificates one operation shorter.
The [receipt](korec_packed_zero_range397.json) includes all six complete sources.

This saves eight gates from [minimal_radix405](korec_packed_minimal_radix405.md).
A zero branch can clear one register's allowed range mask, so one prescribed
submask relation enforces both its zero test and every counter bound. Crucially,
the scalar global bound is narrowed to that same mask **before** the native
sign proof. The accepted-input relation is unchanged; the positive global
slack and private native witnesses are rebuilt. No same-tuple, triangular-map
or arbitrary-point polynomial identity to405 is asserted. The separate75/87
bounds remain unchanged.

## 1. Combined mask and the paid graph

Retain the canonical U21 table, its34 edges, eight registers and both program
recipes from the parent. Write

    one parameter: h=E+x+eta, D=2h;
    two parameters: h=x+eta, D=C*h, C dyadic, C>=4, C>E;
    B=D^8, E_i=edgehat_i-1, J=sum E_i, P=(B-1)J+1,
    W=counter_word_hat-1, Y=final_counter_hat-1.

The same E and, where used, C stay fixed as the ordinary positive input x
varies. Set

    V=1+D+...+D^7,
    Zword=sum_(zero edges i) D^register(i)*E_i,
    Rstar=(h-1)*(V*J-Zword),
    Cpack=sum_(i=0..33) E_i*P^i, Cmask=J*(1+P+...+P^33).

The new single joined relation is

    H=Cpack+P^34*W,
    M=Cmask+P^34*Rstar,
    Z=H, Q=B*P^35,                  H AND M=H.       (1)

Replace the global comparison by W+1+gamma=Rstar, or its signed range
factor by N_G=Rstar-(W+1+gamma). The two chronological transports are unchanged.
The combined mask is also the scalar bound: retaining the former larger
RJ bound here would not establish positive native fields.

The source changes the old mask-base product to V*J, reuses the old mask
addition as its subtraction of Zword, then multiplies by h-1 in the old
range-mask row. Its mask-shift product now directly multiplies Rstar by
P^34. It deletes the former D-1 subtraction, zero-mask product and separate
zero-lane shift. The second copy of W in H disappears, together with its
multiplication and addition; H becomes an alias of the existing Z word.

Consequently the padded ports obey A=Zp+4, where

    q=16Q, A=16H+12, Bp=16M+10, Zp=16H+8.

The duplicate16H product disappears. The paid packed-index identity specializes
to

    S=5+Bp+q*(Bp+q*Zp), r=(q-1)*S.                 (2)

Compared with the parent's generic factored S, this saves one addition.
The native bound remains X=q*(S+beta), using the same paid S.

Finally P^34 is already computed by the selector-repunit circuit. Multiply
it once by the existing P to obtain P^35, replacing the two private squares
that produced P^32 and P^64. The scale Q=B*P^35 retains its charged B product.
All fixed coefficients are charged, including16 and the literal additions.
Overall the replacement saves **5M+3A**. Every remaining row reaches either
complete finalizer. Guards require the whole canonical parent, update active
interfaces and diagnostic lists, and retain preceding packets as historical
provenance. Their old packing/lift helpers are not current zero-range maps.

## 2. Positive fields before any selector or bit semantics

Before typing, E_i,W,Y are nonnegative and h>=3,D>=6 in the first interface,
or h>=2,D>=8 in the second. Since the edge selectors are nonnegative,

    0<=Zword<=D^7*J<=V*J,
    0<=Rstar<=(h-1)VJ, (h-1)V<B-1.                 (3)

At a zero, ordinary comparisons hold and every integer factor is a unit.
For the global comparison or either sign of its unit, J=0 is impossible:
then Rstar=0 while W+1+gamma>=2. Thus J>=1 and P>=B. The same global
condition gives W<Rstar, even when N_G=-1. It follows that

    0<=W<Rstar<(B-1)J<P, E_i<=J<P.                 (4)

All35 coefficients of H and M are below P, so H,M<P^35<Q. Also

    M-H=sum (J-E_i)P^i+P^34*(Rstar-W)>0.

There is no binary interpretation in this inequality. The implicit fields are

    F0=q-A-Bp+Zp-1=16(Q-M)-15>0,
    F1=A-Zp=4,
    F2=Bp-Zp=16(M-H)+2>0,
    F3=Zp=16H+8>0.                                  (5)

Their sum is identically q-1, each is below q, and their residues modulo16
are1,4,2,8. Expanding their four-place packed index proves (2). Thus S>0 and

    X-r=q*(S+beta)-(q-1)*S=S+q*beta>0.              (6)

This establishes the complete pretyping native hypotheses at both allowed
minimum heights, including the negative range sign. It does not invoke the
prescribed AND to prove the positivity needed to recover that AND.

## 3. Native signs and exact decoding of the combined mask

Use the local sign/rank proof of
[the U21 unit theorem, Section4](korec_packed_counter_units.md), with the
bound-only justification in minimal_radix405, Section3. Its norm congruences,
full normalized strong condition, both strict ratios and X>r recover the
linear sign independently of any outer unit sign. The shifted scalar population
theorem gives q=2^popcount(r+epsilon-1). The positive checksum fields and
r=1 modulo16 exclude epsilon=-1 by

    popcount(r-2)=popcount(r)+v2(r-1)-2>=log2(q)+2.

All native factors are therefore+1 and the full prescribed AND holds.
In particular q=16BP^35 is dyadic. Its positive factors B and P are dyadic;
B=D^8 types D, and the respective dyadic multiplier types h. Thus D>=8
in both interfaces. The repunit equation gives P=B^T and
J=1+B+...+B^(T-1), with T>=1.

The first34 lanes of (1) give E_i AND J=E_i. Together with sum E_i=J and
34<B, this forces exactly one edge at every chronological base-B position.
To see that addition has no carry, each selector digit is0 or1 and their
sum is at most34, strictly less than B.

At each such position, Zword now has either no nonzero register digit or
one digit1, identifying the register of the unique selected zero branch.
Therefore V*J-Zword subtracts at most one1 from one of the eight1 digits in
each time slice, without borrow. Multiplication by h-1 produces the mask
whose eight base-D digits are h-1, except that a selected zero branch clears
its addressed digit. Since h is dyadic and h<D, these are disjoint binary
masks. The last lane of (1) says

    W AND Rstar=W.

It is equivalent to every counter digit of W lying in[0,h-1], and the addressed
digit being0 on a selected zero branch. These are exactly the former separate
range and zero-test conditions. There are no higher digits because W<P.
A positive decrement or positive pure test still uses the one-below counter
representation; increments, zero branches and the test's two action contributions
retain their original meanings.

The transported before/after vectors consequently have digits at most h<D.
The unchanged control labels are at most5<D-2. A negative counter-transport
unit would require a low digit D-2>h; a negative control unit would require
D-2 or D-1, outside the legal code residues. Both signs are+1. The product
then forces N_G=+1. In the range-only form the transports are already exact;
in the computed-field form the global comparison also remains exact.

The exact transports start at ED+xD^2 and control code D, both below B.
Their carry-free chronological comparison reconstructs every genuine U21
instruction and the final halt. The top coefficient bounds and identifies the
terminal vector as in the parent, without a separately supplied endpoint bound.
Thus every positive zero represents an actual halt on the ordinary input x.

## 4. Positive completeness and scope of equivalence

For any finite halted run with E>0 and the chosen fixed C when applicable,
choose a dyadic h larger than every counter by more than2 and above E+x
or x as required by its height formula. Pack selectors, post-decrement
vectors and the final vector exactly as in minimal_radix405, at B=D^8.
The genuine zero-branch semantics make (1) hold.

At each chronological position, at least seven register digits in Rstar
remain h-1. Every corresponding W digit is at most h-3, hence their differences
are at least2. The possibly cleared digit is0 in both. No subtraction borrows.
It follows that Rstar-W>2. Thus

    gamma=Rstar-W-1     in the plain comparison form,
    gamma=Rstar-W-2     in either range-unit form

is positive, and every required outer factor is+1. This strict margin is
why narrowing the global bound does not remove any accepted finite history.

The complete prescribed native extension now supplies fresh positive private
witnesses at q=16BP^35 and the new index r. Its canonical X=2^(2r+1), with
q<r and S=r/(q-1)<r, gives beta=X/q-S>0; divisibility by q belongs to that
extension. Its full normalized auxiliary construction and ratios supply all
other native coordinates. Hence every actual halt has a complete positive zero.

Both parameter interfaces therefore retain the same universal ordinary-input
relation. The new range slack and native coordinates generally differ from the
parent's. The literal arbitrary-point audit replays the old source only after
explicitly overriding the changed range, ports, index and scale definitions;
it is not an equality to the unchanged parent polynomial.

## 5. Literal counts, degree and reproducible evidence

|Program interface|Form|Certificate|Comparisons|Witnesses|Polynomial|Degree bound|
|---|---|---:|---:|---:|---:|---:|
|One parameter|Computed fields|388|4|50|399|21540|
|One parameter|Range unit|390|3|50|398|21549|
|One parameter|All units|396|1|50|397|21549|
|Two parameters|Computed fields|387|4|50|398|40690|
|Two parameters|Range unit|389|3|50|397|40706|
|Two parameters|All units|395|1|50|396|40706|

The default SOS alternatives cost398 and397, with degree bounds43098 and81412.
All bounds are propagated through the literal graph with only the inherited
main-norm polynomial cancellation. They are not exact-degree or optimality
claims. The larger uniform two-program degree counts C as a variable.

Run `python3 korec_packed_zero_range397.py`; `--write` regenerates the receipt.
A symbolic calculation checks the specialized packed index. All six contexts
check144 direct outer/retained-register recipes, including72 signed assignments,
and288 complete finalizer outputs against explicit changed-definition replays.
Nine actual halted U21 histories give81 new outer packs covering13365 chronological
rows, with full transports and the combined AND. Another2448 pretyping scalar
contexts include1224 negative range signs and408 height-two cases;18688 exhaustive
small digit cases check the combined range/zero-mask equivalence. Four incompatible
callers are rejected. These checks do not materialize complete private Pell zeros;
the full extension in Section4 proves their existence.

Author receipt generation and a fresh replay pass. Independent full
proof/source/dependency review and another fresh replay pass without findings.
Its separate executor checks288 retained-register maps and576 complete outputs,
including288 signed outputs, using only physical port/mask/scale overrides: the
old generic S then specializes correctly without an S override. Twelve independent
degree/opcode/closure ledgers,6048 eight-register mask cases and528 actual-source
weak-bound cases pass, including264 negative signs and96 height-two cases. An
independent U21 interpreter/packer at inputs7,8,11 gives nine halted histories,
54 positive outer packs covering8910 rows and54 terminal-corruption rejections.
All four local links and whitespace checks pass. These remain algebra and outer
history checks, not materialized complete private Pell tuples.
