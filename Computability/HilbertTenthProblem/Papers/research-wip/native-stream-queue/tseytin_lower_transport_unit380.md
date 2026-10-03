# Delimiter balance gives a380-operation C2 polynomial

The [complete source](tseytin_lower_transport_unit380.py) reduces the
[upper-transport381 compiler](tseytin_upper_transport_unit381.md) to
**380=176M+204A**, with375 certificate gates, two comparisons and62 positive
witnesses. It retains one fixed positive program parameter and ordinary
positive input. The total degree is **at most4720**; no exact-degree or
global circuit-optimality claim is made. The [receipt](tseytin_lower_transport_unit380.json)
contains all eight complete schedules.

For each valid recompiled C2 program, the full supplied positive zeros
correspond by the affine map

    I_parent = I_new+1,

with all other supplied coordinates unchanged. Here the supplied register
`c2_initial` now means I_new, **the literal initial encoding minus one**.
The active interface is `initial_minus_one`; the program recipe explicitly
records this meaning. This is not same-tuple zero equality or an off-zero
polynomial identity. The separate75-certificate/87-polynomial results are
unchanged.

## 1. Shift the initial coordinate and unitize its transport

Use the literal encoding and recipe of
[permuted-digits387](tseytin_permuted_digits387.md):

    a=0, b=3, c=1, d=2, e=4, #=5,
    enc(w)=8^|w|+raw8(w), d0=8^64−1.

For a valid primary program word S over c,d, ordinary positive input x
and its literal query w, the old paid loader gives

    d0*I_parent=N(A,Q), I_parent=enc(w#)=8enc(w)+5.   (1)

The query program parameter A is unchanged. Replace the final numerator
subtraction constant C by C+d0. It now computes N−d0, at exactly the old
cost. The retained ordinary comparison is

    d0*I_new=N−d0.                                  (2)

Thus(1) and(2) are equivalent under I_parent=I_new+1, on arbitrary integer
assignments to the other ports. Both wrong-exponent residues modulo d0
are unchanged. In particular this modification does not assume the
positive exponent branch before proving it.

Write B=65536D, D=`height_slack`, P=(B−1)J+1 and
Vfinal=4096Ufinal+2560. The parent lower transport is

    B*NV+I_parent=H_V+P*Vfinal.                      (3)

Keep its two side registers, with the new meaning of `c2_initial`, and add

    L=V_rhs__157−V_lhs__153
     =H_V+P*Vfinal−B*NV−I_new.                      (4)

Multiply L into the word-unit product and remove the ordinary comparison
between those sides. This adds one subtraction and one multiplication to
the certificate, while removing a squared residual and its finalizer
addition. The complete difference is **one fewer addition**. The query
comparison stays paid.

|Global bound|Power products|Finalizer|Operations|M|A|Certificate|Comparisons|Degree bound|
|---|---|---|---:|---:|---:|---:|---:|---:|
|unit|merged|anchor|380|176|204|375|2|4720|
|unit|merged|SOS|380|176|204|375|2|9412|
|unit|separate|anchor|382|176|206|374|3|4760|
|unit|separate|SOS|382|176|206|374|3|9304|
|equality|merged|anchor|381|176|205|373|3|4718|
|equality|merged|SOS|381|176|205|373|3|9408|
|equality|separate|anchor|383|176|207|372|4|4758|
|equality|separate|SOS|383|176|207|372|4|9300|

All schedules use the same62 positive witnesses. The complete canonical
parent guard fixes the actual24 tiles, digits, query recipe, source,
comparisons and interfaces. Additional guards verify the literal query
and terminal definitions, the unique lower comparison and both product
interfaces. The only source consumers of `c2_initial` are its query product
and lower left side; both are explicitly checked. The active metadata
records the shifted meaning, while nested parent records remain historical.

## 2. Recover local signs and typed digits before resolving L or G

At a zero of either finalizer, every ordinary residual vanishes and every
factor of each constrained integer product is a unit. Denote the inherited
upper transport factor by T and, when enabled, the global-bound factor
by G. Initially T,L,G may each be−1 or+1.

The global-unit equation gives Sigma<=P for the unchanged sum Sigma of
ten positive history and selected-product ports. Each port is strictly
below P; Sigma>=10 excludes J=0 and P=1. Thus J>=1 and B<=P. The equality
form supplies these same inequalities directly. These are the weak
pretyping bounds used in
[global-bound385, Sections1–3](tseytin_global_bound_unit385.md#1-the-source-change-and-its-initially-unknown-sign).
Changing the initial coordinate does not change any history pack, range,
selector, computed truth field, or native bound.

The exponent signed-unit theorem applies to its own product being a unit.
Its two candidate powers are Q=2^(96x) and Q=2^(96x−4). On the valid program
recipe, the two parity-dependent wrong-power residues of N are

    29966043244819123951156626953424814080,
    45854471631935696494459945720637767680.

They are nonzero modulo d0; subtracting d0 changes neither. Therefore the
paid comparison(2) excludes the negative exponent branch without using
any history transport. Its product is+1 and(2) gives the exact integer
I_new=enc(w#)−1. In the separate form its product was already constrained
to+1 and the same literal query conclusion holds.

For the word native core, the weak scalar bounds supply positive computed
fields of sum q−1, with low residues(1,4,2,8) modulo16. The four norms are
positive units by their individual modulo4 obstructions. The strong norm,
positive ratio intervals and rank argument force the linear unit positive
before the total-product sign is used. The alternative index sign would
replace the raw population argument r by r−2, giving residues(15,4,2,8)
and population at least log2(q)+2 instead of the required log2(q). Thus
it too is positive. This is exactly the independent local argument used
in381, and it uses neither transport nor the sign of G.

The resulting prescribed AND and the unchanged product scale q=16B*P^34
recover dyadic B and P, then the exact repunit relation gives

    D=2^d, B=2^(d+16), P=B^t,
    J=1+B+...+B^(t−1), t>=1.                        (5)

The physical/controller/range lanes recover one literal tile in every
row, its selected slope products, and current history digits in[0,D).
These conclusions precede both chronological boundary arguments. They
remain valid at D=1, with a zero range coefficient.

As in381, T=H_U+P*Ufinal−B*NU has residue u0=H_U mod B in[0,D).
Since D<B−1, T cannot be−1; hence T=+1 and the upper initial digit is1.
This also excludes D=1 at this later stage. **Do not infer G=+1 yet.**
After the local native, exponent and upper signs are restored, the
remaining product relation in the global-unit form is G*L=1. In the
equality form it already gives L=1; the next direct argument applies
to both.

## 3. Restore a literal initial word for either lower sign

Equation(4) can be written

    B*NV+I_eff=H_V+P*Vfinal, I_eff=I_new+L.           (6)

The exact query equation gives the two possibilities

    L=+1: I_eff=enc(w#),
    L=−1: I_eff=enc(w#)−2=enc(wb).                  (7)

There is no base-eight borrow in the second line: the final digit5 is
replaced by3. Both values are positive.

The primary word S uses only the nonzero digits c,d. The query suffix is

    a (ab^63)^x abb (ab^31)^x abb
      (ab^63)^x abbb (ab^31)^x abbb aa.

For x>0 this has no aaa, including the joins with S and the final symbol
in either line of(7). At most two zero base-eight digits occur consecutively;
nonzero digits contribute at most two leading and two trailing binary zeros.
The binary expansion of either I_eff has no zero run longer than10.
The leading sentinel1 causes no extra run.

Reducing(6) modulo B gives I_eff mod B=v0<D. The established
[free-height zero-run lemma](tseytin_free_height415.md#3-the-literal-input-supplies-its-own-initial-bound)
with gap16>10 forces I_eff<B: otherwise the block at binary positions
d through d+15 would be all zero between a nonzero higher block and a
residue below2^d. A zero residue is also covered, giving a trailing zero
block. Consequently **I_eff=v0<D<B**. No chronological interpretation
was assumed to obtain this initial bound.

Every actual tile has a positive slope and nonnegative offset, with their
sum below65536. For a current digit z<D its updated value satisfies

    0<=a*z+c< (a+c)*D < B.

The selected update words NU,NV and current history words therefore lie
in[0,P). For either positive terminal, a transport with initial in[0,B)
gives

    P*terminal<=B*(P−1)+(B−1)=BP−1,

so the terminal is below B. Comparing the canonical base-B digits in
both transports now recovers the full chronology, starting at upper1
and lower I_eff. This is the parent terminal-radix argument; no terminal
height inequality or old positive height gap is assumed.

## 4. Delimiter balance excludes the negative lower sign

Let top and bottom be the words concatenated along the recovered common
tile sequence. The upper initial1 and the two literal affine updates give
Ufinal=enc(top). The endpoint relation gives

    Vfinal=4096*enc(top)+2560=enc(top # aaa).          (8)

The lower chronology gives enc(w # bottom) if L=1, or enc(w b bottom)
if L=−1. The sentinel encoding is injective even with a=0, so (8) is a
literal word equality.

Every one of the24 tiles has equal numbers of # in its two words.
The only tile containing # is the copy #/#; the18 relation tiles use
letters a through e. Thus top and bottom have the same delimiter count.
The query w has no #. If L=−1, the left word w b bottom has #bottom
delimiters, while top # aaa has #top+1. These counts cannot agree.
Therefore **L=+1**.

If the global bound was unitized, G=+1 now follows from G*L=1. Restoring
I_parent=I_new+1 makes(6) exactly the parent lower transport(3), and its
query comparison follows from(2). Every parent native factor, upper
factor, global condition and ordinary residual holds. Thus each positive
new zero on a valid program slice gives a positive parent zero.

Conversely, a positive parent zero has I_parent=enc(w#)>2 by its paid
valid-program query. Set I_new=I_parent−1>0, retaining every other
coordinate. Equation(2) holds, L=1, and all products and remaining
comparisons hold. The maps are inverse on these full positive zero sets.
They do not assert a positive inverse on arbitrary tuples or a theorem
for invalid program coefficients. In particular no new native private
extension is needed for either direction on the stated zero sets.

## 5. Full-source correction, degree bounds and replay

For arbitrary integer assignments, evaluate the parent at
I_parent=I_new+1. Its lower left side is the new side plus1; its query
product and query numerator are each the new register plus d0. Every
other retained certificate register agrees except a merged product that
now includes L. The old lower residual is1−L; all surviving ordinary
residuals agree under this affine substitution.

Let W,E be the old word and exponent products and S the sum of retained
ordinary residual squares. Put U=WE and Splus=S when merged, or U=W and
Splus=S+(E−1)^2 when separate. The anchor output difference is

    U*L*(1+Splus)−1 − [U*(1+Splus+(L−1)^2)−1]
      =U*(L−1)*(Splus−L+2).

The corresponding SOS difference is

    U^2*(L^2−1)−2U*(L−1)−(L−1)^2.

These explicit corrections are checked on arbitrary positive and signed
assignments. They are not claimed to vanish off zero.

The two guarded main-norm cancellation graphs are unchanged. The new
factor L has degree bound3, and changing a fixed numerator constant does
not change its degree bound7. In the default anchor, the old factor bound
4703 becomes4706; adding twice the query-residual bound gives4720.
The literal degree propagation gives every entry in the table. Complete
source, degree and ledger APIs require the entire canonical successor;
Boolean mode validation occurs before caching. Every emitted row reaches
the final polynomial output.

The author writer passed192 complete affine retained-register maps
(96 signed),384 complete parent corrections and manual-finalizer outputs
(192 signed),16 zero-selector contexts, all eight emitted schedules and
78 malformed caller checks. Literal component tests passed24 tile
delimiter balances,240 paid queries and positive initial shifts,480
signed-initial zero-run bounds,77644 radix-wrap exclusions,960 negative
word delimiter obstructions and both exact wrong-power residues. These
are arbitrary-integer identities and query/history component tests;
they are not materialized complete compiled Pell-zero tuples. Author
writer32632 and separate fresh98949 passed; all six local links and
whitespace checks passed.

Root's full proof/source/dependency review and fresh2352 passed without
findings. Gibbs's independent full review and fresh94861 also passed.
His separate executor checked160 affine retained-register maps and320
complete output corrections(160 signed), all eight degree/opcode/domain/
liveness ledgers and16 zero-selector contexts. Independent literal-word
checks covered96 queries from separately derived program numerals,
192 signed initial bounds,1920 wraps,24 tile delimiter contracts and576
two-tile delimiter obstructions. Additional checks covered1555 sentinel
words and205224 exhaustive small binary-gap cases. Both reviews confirmed
the valid-slice scope and the order of sign and chronology recovery.
