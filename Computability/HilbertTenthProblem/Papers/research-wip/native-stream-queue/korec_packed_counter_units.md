# A 411-operation universal counter compiler with exact chronological units

The explicit Korec route has a **411=147M+264A** successor to the
[453-operation U22 compiler](korec_packed_counter_compiler.md). It has
**50 positive witnesses**, one positive program parameter, ordinary
positive input, and a conservative total-degree bound **42589**. Its
certificate has410 operations and one final product comparison. This
improves this independent register-machine route; the separate
[258-operation U9 route](neary_woods_universal_offset258.md) and
established75/87 results are unaffected.

The [source](korec_packed_counter_units.py) emits every gate, including
fixed-coefficient multiplications. The [receipt](korec_packed_counter_units.json)
contains the complete default schedule, table, labels, ledgers and
reproducible checks. The construction has no duration bound, encoded-input
parameter or uncharged rank oracle. Its final polynomial is an integer
product minus1, rather than a sum of squares. An SOS alternative costs412.

## 1. The actual strongly universal table and ordinary input

Korec's primary paper, [*Small universal register machines*](https://www.cs.cmu.edu/~cdm/resources/Korec1996-small-universal-RM.pdf),
Theoretical Computer Science168(1996),267–301,
[DOI10.1016/S0304-3975(96)00080-1](https://doi.org/10.1016/S0304-3975(96)00080-1),
proves strong universality in its Main Theorem(a3):21 instructions using
increment, conditional decrement and pure test. Definition2.3(i) fixes
the input convention; Section7 gives the contractions of Figure1's U32.
The parent packet checks that primary table, including the original
q27 zero branch to q29, also confirmed by the printed Table4. This packet
retains that correction and derives U21 from the parent's literal U22:
replace instruction8's decrement/restore pair with a pure test, delete
instruction9, and relabel every target at least10 down by1.

In the following literal table, `I r a` increments register r and goes
to a. `D r a b` decrements a positive register and goes to a, or goes to
b when it is zero. `T r a b` takes the same branches without changing
the register. State0 is the start and state21 is the unique halt.

|State|Instruction|Control label lambda|
|---:|---|---:|
|0|D 1 1 2|1|
|1|I 7 0|2|
|2|I 6 3|2|
|3|D 5 2 4|1|
|4|D 6 5 3|1|
|5|I 5 6|2|
|6|D 7 7 8|1|
|7|I 1 4|2|
|8|T 6 9 0|3|
|9|D 4 0 10|1|
|10|D 5 11 12|3|
|11|D 5 13 14|4|
|12|D 2 17 18|1|
|13|D 5 15 16|5|
|14|D 3 17 19|1|
|15|I 4 10|2|
|16|I 2 20|2|
|17|D 4 0 21|3|
|18|D 0 0 17|1|
|19|I 0 0|2|
|20|I 3 17|2|

There are8 increments,12 conditional decrements and one pure test,
hence34 branch edges. The positive branch of instruction8 exactly
replaces the two old steps; every other retained checkpoint takes one
old step. This preserves the entire counter vector and both halting
directions. The generic compiler also accepts any finite nonempty table
of these three instruction types on k>=3 registers, starting at0 and
halting at the table length.

Write E for the positive program parameter and x for the ordinary
positive input. The initial register vector is exactly

    (R0,R1,R2,R3,...,R7)=(0,E−1,x,0,...,0).

For each recursively enumerable set S, strong universality supplies a
fixed E such that this particular table halts exactly on x in S. Only
E depends on the represented set. The input x is used directly; no
existential integer is allowed to choose an encoding of x. Consequently
the single displayed411-operation polynomial is universal with one
positive program parameter and50 positive existential coordinates.

## 2. Shared control codes and chronological packing

Assign to each nonhalting state q a code

    code(q)=lambda_q D^r(q),       code(halt)=0,             (1)

where r(q) is its addressed register. Within each register, the labels
are a permutation of1 through the number of states using that register;
the start label is1. The literal default labels are in the table above.
They were selected by a bounded search; no optimality is claimed.

Let mu be the least nonnegative fixed integer such that
Dmin=6+2mu exceeds every label and the least power of two at least Dmin
exceeds every label by more than2. Define, with positive height witness u,

    h=E+x+u+mu, D=2h, B=2D^k.                              (2)

All these operations are paid; mu=0 in the default table. Before typing,
all codes are distinct positive integers below D^k. After D becomes a
power of two, every label is strictly below D−2. Code0 is reserved for
halt. The number K of branch edges satisfies K<B: if m is the number of
instructions and l the largest label, K<=2m<=2kl<2kD<=2D^k.

For every edge e introduce a positive hat and put E_e=hat_e−1>=0.
Let W=counter_word_hat−1 and Y=final_counter_hat−1. The paid definitions
are

    J=sum E_e,      P=(B−1)J+1,
    R=(h−1)(1+D+...+D^(k−1)),       range_mask=RJ.           (3)

An increment edge contributes D^r E_e to I. A positive decrement edge
contributes D^r E_e to L. A positive pure-test edge contributes to
**both** I and L. Every zero branch contributes to Z. Thus W stores the
post-decrement counter vector; a positive pure test stores its selected
register one below both the unchanged current and next values.

The control sums use(1). In particular

    current=I+L+Z
       +sum_e (lambda_source−multiplicity_e)D^r(source) E_e,
    following=sum_e code(target_e)E_e,                     (4)

where multiplicity is2 for a positive pure test and1 otherwise. Signed
correction coefficients are allowed: the full expression is identically
the nonnegative current-code sum. The source groups coefficients by
register, and deterministically chooses the shorter of two exact paid
linear-form schedules. Targets equal to halt have coefficient0. The
initial code is a paid existing power D^r(start), since its label is1.

Initially retain three comparisons, with positive range slack gamma:

    W+1+gamma = RJ,
    B(W+I)+(E−1)D+xD^2 = W+L+PY,
    B*following+code(start) = current.                     (5)

The single prescribed AND is the P-lane concatenation of

    (E_e,J,E_e) for all K edges,
    (W,RJ,W),
    (W,(D−1)Z,0).                                        (6)

Its unpadded words are H,M,A and prescribed scale Q=B P^a, where a is
the least power of two at least K+2. Explicitly, with
C=sum E_e P^e and Jrep=1+P+...+P^(K−1),

    A=C+P^K W,
    H=A+P^(K+1)W,
    M=J*Jrep+P^K(RJ+P(D−1)Z).                             (7)

These shared expressions save gates without replacing chronology by
endpoint balance. Once Q is dyadic, B and P are dyadic positive factors,
and D is dyadic by(2). The divisibility B−1 divides P−1 gives P=B^T
for an integer T>=1. Indeed if B=2^b and P=2^s, reduction of s modulo b
in2^s−1 shows b divides s. Equation(3) then makes J the T-digit base-B
repunit. The AND lanes say E_e is a submask of J; K<B and sum E_e=J
force exactly one selected edge at each chronological digit.

The range lane bounds each counter digit of W by h−1. Adding the selected
increment or decrement weight produces digits at most h<D, with no
carry. The zero lane makes the addressed post-decrement digit zero on a
zero branch. Comparisons(5) recover the exact first counter vector,
every adjacent vector, the final vector, the first control code and every
adjacent control code. Although Y is unbounded before equations, after
typing both W+I and W+L have T base-B digits below B, and the initial
vector is below B. The top digit of the second comparison in(5) forces
Y to equal the last after-vector, hence Y<B; no uncharged endpoint bound
is assumed. Since all source codes are nonzero and the halt
code is0, an earlier halt cannot be followed by another row. The final
row targets halt. This proves the fixed-program halting relation once
the comparisons and complete AND have been restored.

## 3. Computing the three truth fields before bit typing

The new range comparison is deliberately stronger than the parent's
old total-word bound. It supports all three native field definitions.
This argument also tolerates its later unit relaxation. Suppose

    N_G=RJ−(W+1+gamma) is either +1 or −1.                  (8)

J=0 would give N_G<=−2, so J>=1 and P>=B. Moreover
RJ−W=1+gamma+N_G>=1. Therefore W<RJ<P. Every E_e<=J<P;
R<B−1 and (D−1)Z< P. All lanes in(6) lie in[0,P), before
assuming any native or binary semantics.

Equation(7) now gives

    H−A=P^(K+1)W>=0,
    M−A=sum (J−E_e)P^e+P^K(RJ−W+P(D−1)Z)>0,
    Q−H−M+A>0.                                           (9)

For the last inequality, H,M<P^(K+2), A>=0, a>=K+2 and B>2.
The same argument holds under the exact range comparison in(5).
Use the standard padded native ports q=16Q,
Aport=16H+12, Bport=16M+10 and F3=16A+8. Compute

    F1=Aport−F3=16(H−A)+4>0,
    F2=Bport−F3=16(M−A)+2>0,
    F0=q−Aport−F2−1=16(Q−H−M+A)−15>0.                    (10)

Thus all four fields are positive and sum Fi=q−1 identically. The two
input comparisons disappear, and the native checksum factor is exactly1.
The source removes its product multiplication as well. This is a graph
projection at the required outer loci. Computed fields can be negative
on arbitrary positive assignments away from those loci; no off-zero
positive inverse is asserted.

The remaining native factors are the three norm units, normalized strong
unit, first-index unit and coupled-linear unit of the
[complete native coupled kernel](native_binary_index_coupled_units.md).
The strict positivity in(10), the full normalized strong relation and the
unchanged native bounds are important to the sign argument below.

## 4. All three chronological comparisons can be units

Let r_G,r_C,r_S denote left minus right in(5). Replace the three comparisons
by factors

    N_G=−r_G,       N_C=1−r_C,       N_S=1−r_S,              (11)

and multiply them into the six native factors. The final polynomial is
this nine-factor product minus1. Every factor is an integer unit at a
zero. The range implication(8) establishes the positive ports(10)
without using native typing or chronological comparisons.

Here is the order of sign recovery; in particular the unsigned native
index is **not** assumed when proving dyadic typing. The independent
modulo4 arguments in the native proof force the first, main, auxiliary
and normalized strong units to+1. Let epsilon and lambda be the still
signed index and coupled-linear factors. Write r for the packed native
index, K0 for its index expression and Jtarget=2K0−lambda. Positive
fields summing q−1 give

    r>=q^3+q^2+q+1>=4369,    r<q^4,    q>=16.

The unchanged X=q(r+beta)>r, Y=sq and positive ratio slacks give all
large-index/rank hypotheses of the native proof's Sections2–4. Applying
that proof locally gives K0=r+epsilon, first Pell index n=K0 and main
index p=2K0−lambda. If lambda=−1, the exact duplication inequality
contradicts the upper ratio. Hence lambda=1. This local argument uses
the norm signs and individual index factors, not a relation between
the signs of the new outer factors.

Set r'=r+epsilon−1. The full scalar native equations hold at r', with
the restored positive bound slack; r'>q and r'>=9. The
[raw population theorem](native_binary_input_dilation129.md#2-the-raw-geometry-theorem-at-j9-and-jq)
therefore gives q=2^popcount(r') independently of the checksum sign or
truth-field interpretation. This is the same scalar restoration used in
[the coupled two-core proof](neary_woods_universal_joint_and_coupled.md#3-the-raw-population-theorem-at-the-shifted-native-index).

Now q=2^t. Positive fields of sum q−1 all lie below q, so the packed
index has disjoint blocks and

    popcount(r)=sum popcount(Fi)>=popcount(q−1)=t.

The literal residues in(10) give r=1 mod16. For r>1 of this residue,

    popcount(r−2)=popcount(r)+v2(r−1)−2>=t+2.

Consequently epsilon=−1 contradicts q=2^popcount(r−2).
Both index and coupled-linear signs are+1. All six native factors are
therefore+1, and the unchanged full prescribed AND is restored. In
particular D,P are dyadic and all conclusions of(6) hold.

The two transport signs are now excluded separately. If N_C=−1,
its right minus left is−2. Modulo D, both B and P vanish and the initial
counter value (E−1)D+xD^2 vanishes. Thus the low digit of W+L would be
D−2. The range lane and one selected edge put that digit in[0,h],
where h=D/2 and D>=8; D−2>h. This is impossible.

If N_S=−1, the low digit of current is code(start)−2 modulo D.
It is D−1 when the start addresses register0, and D−2 otherwise.
Every current code has low digit0 or a label strictly less than D−2,
by the paid fixed margin in(2). This too is impossible. Therefore
N_C=N_S=1. Since the total product is1, N_G=1 as well.

The recovered range comparison is RJ=W+1+gamma+1. Increasing the
range slack by1 gives the exact plain comparison(5); the two transport
comparisons are already exact. Section2 proves soundness.

For completeness, start from any actual finite halted run. Choose a
power of two h larger than E+x+mu and more than two above every counter
occurring in the run. Pack its edge indicators and post-decrement
vectors as in Section2. All input and height witnesses are positive.
Each post-decrement counter digit is at most h−3, so RJ−W>2;
set gamma=RJ−W−2>0. Then N_G=N_C=N_S=1, and(6) is the actual
joined AND. The complete parent native theorem supplies positive
canonical auxiliaries, with fresh five-coordinate strong normalization
where required. Their native factors are all+1. This completes both
halting directions for every finite table and every positive E,x.

This existential extension theorem preserves the actual program and
input. It is not an all-tuple positive bijection with453: the instruction
table, control labels and range bound changed, and canonical native
extensions may be rebuilt.

## 5. Paid source identities and exact ledgers

`build(table,form,registers,lambdas)` accepts `raw`, `coupled`, `fields`,
`range_unit` and `units`; the default is the literal U21 and `units`.
All forms use the new table/control/range source. The first two retain
the supplied native truth fields. The last three compute(10).
`project_ports` checks the private input/checksum rows before substituting
five paid differences for five old additions/differences and deleting the
checksum-product multiplication. It removes exactly two comparisons and
three witnesses. `outer_units` accepts only the range-only or all-three
specializations used in the proof. Fixed multiplications by16,2 and all
control coefficients are counted whenever an actual gate is emitted.

|U21 form|Certificate|Comparisons|Witnesses|Final polynomial|Degree bound|
|---|---:|---:|---:|---:|---:|
|raw|395=138M+257A|19|60|451=157M+294A|7024|
|native coupled|403=145M+258A|6|53|420=151M+269A|43780|
|computed truth fields|402=144M+258A|4|50|413=148M+265A|42580|
|range unit|404=145M+259A|3|50|412=148M+264A|42589|
|all chronological units|410=147M+263A|1|50|411=147M+264A|42589|

The first row is SOS. The other displayed rows use the native product
finalizer. With three outer units there are no retained ordinary
residuals, so the final gate is simply product−1; no artificial outer
`1+0` multiplication is emitted. Squaring this output gives the412-gate
SOS alternative with degree at most85178.

Every computed-field graph identity is checked on arbitrary integers,
including signed assignments. The native checksum becomes1 identically,
the removed input residuals vanish, and both full finalizers agree with
the parent after the three field lifts. For the outer-unit rewrite,
lift the parent's range slack to gamma+1. Then every new factor is
1 minus the corresponding old residual. Let G be the old six-factor
native product, S the set of unitized outer comparisons, r_i the old
residuals, and M=product over S of(1−r_i). Exactly, without division,

    new+1=M(old+1)−GM*sum_{i in S}r_i^2.                   (12)

This is a whole-output correction identity, not an off-zero equality or
an off-zero sign claim. The SOS form is checked independently from the
retained residuals and the new product.

Degree propagation uses the inherited, guarded polynomial cancellation
in the main norm; it never uses a zero equation to lower degree. After
field projection the six native factor bounds are
7043,16430,3815,8802,3229,3229, summing42548. The outer factor bounds are
9,16,16, giving42589. These are conservative total-degree bounds on the
emitted polynomial, not optimal-degree claims or arithmetic-circuit
lower bounds. A dummy degree-zero residual is used only to call the
old degree-analysis routine when no ordinary residual remains; it is
absent from every emitted source and operation count.

## 6. Reproducible verification and scope

Run `python3 korec_packed_counter_units.py` to replay the checked receipt;
`--write` regenerates it. The checker emits30 ledgers across six actual
tables and all five forms, including a pure test, a start in register0,
and a twelve-state single-register table requiring a nonzero paid
control margin. Every emitted gate reaches both selected finalizers.

The primary-table contraction checks840 U21 checkpoints against870 U22
steps, alongside the inherited672 U32-to-U22 checkpoints. Direct raw
oracles check144 complete residual/output identities,72 signed. All
six inherited native rewrites are replayed in every fixture. New field
projection checks192 complete graph identities and both finalizers;
range-only and all-unit corrections check192 assignments each, again
with both finalizers and half signed. Off-zero nonpositive lifted
fields are recorded rather than silently treated as positive solutions.

A separate literal register interpreter produces269 halted histories
across65 tables, including the actual universal table, with832 rows:
290 increments,193 positive decrements,165 zero decrement branches,
66 positive pure tests and118 zero pure tests. Independently evaluated
scalar formulas agree with every emitted outer register, all three
required outer residuals and the joined AND. These are finite outer
histories; no full huge Pell witness was numerically materialized.
The checker also covers both weak range signs before dyadic typing,
540 negative-transport digit cases,145 checksum-one negative-index
exclusions and six rejected source/mode mutations.

The proof establishes an unbounded-duration, fixed-arity universal
polynomial; the finite checks audit the literal compiler and its stated
interfaces. They do not replace the primary strong-universality theorem
or the native positive-extension theorem.

Author receipt generation and a separate fresh replay pass. The384 weak
range checks include192 negative range units and318 nondyadic radices;
all seven local links resolve. No parent source or receipt was changed.

An independent full proof/source/primary-dependency review and fresh replay
pass with no remaining findings. The reviewer checked50 ledgers and, with
an independent executor,480 graph/unit correction assignments(240 signed)
in both finalizers and160 raw SOS identities. Separate checks covered480
weak range margins(240 negative units,366 nondyadic radices),243 physical
halted paths/426 rows with243 wrong-final rejections, and1,000 negative-index
population cases. A further typed-boundary enumeration covered189,024
assignments over six tables and D=8,16:192 exact counter transports and104
complete one-row paths passed, with no negative transport solutions. These
are bounded algebra/outer-history checks, not materialized full Pell zeros.

A second independent full proof/source/native-dependency and primary-source
review, with a separate fresh replay, also passes without findings. Its
own register interpreter, literal executor and packing formulas checked682
halted histories/1,498 rows across170 increment/decrement/test programs,
including both pure-test branches and nine positive-margin cases with12
states on one register. Raw outer equalities, the range-unit slack shift,
joined AND, injective control labels and strict digit margins all passed.
No author run/packing helper or full numerical Pell tuple was used. Source
and receipt are unchanged after the two independent reviews.
