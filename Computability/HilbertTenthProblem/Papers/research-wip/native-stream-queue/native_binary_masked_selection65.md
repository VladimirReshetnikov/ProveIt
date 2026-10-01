# Complete binary AND64/65 and eight selected fields in118/120

The [shared-input successor63](native_binary_masked_selection63.md) saves
one addition in each schedule, giving AND63/64 and selected-source117/119.
The [complete matrix compiler](group_complete_matrix_compiler.md) uses
its prescribed exclusive119 variant with all external predicates paid.
The schedules and proof below remain the parent construction.

The existing binary selector kernel gives an exact bitwise-AND relation
in **65=33M+32A**, with **22 strictly positive auxiliary witnesses** and
**16 equations**. A four-bit prefix admits zero inputs, zero output,
empty unpadded words and arbitrary truth-pattern omissions. The component
also proves its own binary length power. If the length bound is not a
relation argument, **64=32M+32A** defines unrestricted bitwise AND with
22 positive auxiliaries and15 equations.

One kernel can check all eight selected-source fields of the
[four-register matrix interface](group_four_register_history.md) together.
This batch costs **120=57M+63A**. The general batch uses30 positive
auxiliaries and24 equations. Under the actual four-register digit margin
and mutually exclusive selection, a variant uses only **23 positive
auxiliaries and17 equations**, at the same120 operations. Using the
unrestricted AND component instead gives **118=55M+63A**, with30/23
auxiliaries/equations in the general version and **23 positive auxiliaries,
16 equations** in the version for the four-register interface. These118
versions retain the dyadic cell geometry as an external hypothesis.

The AND predicate is a complete arithmetic component. Its interpretation
as eight cellwise selected-source products still assumes certified history
digits, Boolean cell selectors and the common cell geometry. Those
remaining conditions, regular control and the connection to the physical
duration are not free. No complete universal bound is claimed.

## 1. Complete AND projection and positive domains

Supply positive parameters `P,Hhat,Mhat,Zhat`. Mathematically decode

    H=Hhat-1, M=Mhat-1, Z=Zhat-1.

The exact projection of the65-operation source is

    P=2^ell for some ell>=0,
    0<=H,M<P, Z=H AND M.                              (1)

In particular `P=1,H=M=Z=0` is admitted. AND here specifies the relation;
it is not an arithmetic instruction in the source. The hats are relation
arguments, not uncharged conversions of external integers. In the later
batch, affine substitution into the padded formulas removes the need to
construct global hats as separate registers.

Compute seven instructions

    q=16*P;
    scaled_A=16*Hhat; padded_A=scaled_A-4;
    scaled_B=16*Mhat; padded_B=scaled_B-6;
    scaled_Z=16*Zhat; F3=scaled_Z-8.                  (2)

Equivalently the last three outputs are `16H+12`, `16M+10` and `16Z+8`.
Both q and the computed F3 are strictly positive before using any equation:
q>=16 and F3>=8. Supply only positive `F0,F1,F2`, and append the unchanged
[four binary selectors56](native_controller_binary_selector56.md) at these
q,F0,F1,F2,F3. Its kernel scale `n2` is literally aliased to the computed q;
its seventeen positive core coordinates plus `odd_half,bound_beta` are
retained. Finally compute two sums and compare

    F1+F3=padded_A,       F2+F3=padded_B.              (3)

The output selector F3 is a computed register, so no witness or comparison
for it is needed. All twenty-two supplied auxiliaries are

    F0,F1,F2,
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y_aux,
    odd_half,bound_beta.

The source is acyclic; in particular its input histories use distinct
names from the inherited kernel registers.

## 2. Why the padding gives the full positive converse

The selector theorem proves q is a power of two, all four positive fields
partition its binary positions, and F0 contains the units bit. Since
q=16P and P is a positive integer, `P=2^ell` with ell>=0.
Interpreting the four classes as `00,10,01,11`, the two sums in (3) are
exact binary input words and F3 is their AND. Their lower four bits are

    padded_A: 1100,       padded_B: 1010,       F3: 1000.

Thus the low-first truth labels are `0,2,1,3`. The higher bits say exactly
`Z=H AND M`; the selector bounds give `H,M<P`. This proves soundness
without an assumed truth table or assumed input length.

Conversely take any tuple in (1). Form the two padded words `16H+12` and
`16M+10` in exactly ell+4 bits, and let F0,F1,F2,F3 be their four truth
classes. The prefix supplies a bit in every class, so all four Fi are
strictly positive. F0 has its units bit, and the fields partition
`q-1=16P-1`. The AND field is exactly `16Z+8`, agreeing with the computed
F3. The full positive converse of selector56 now supplies all nineteen
kernel/outer auxiliaries. Equations (2)--(3) hold. This inherits that
packet's parametric Pell witness map at the actual newly packed index;
it does not rely on materializing a bounded sample of enormous Pell
coordinates.

The literal ledger is

    selector56:                 29M+27A;
    q and three padded words:    4M+ 3A;
    two input-port sums:         0M+ 2A;
    total:                      33M+32A =65.            (4)

The selector contributes fourteen comparisons and (3) contributes two.
All fixed-numeral products, including each multiplication by16, are paid.
This is a comparison-system count; no sum of squares is included.

### The unrestricted64 version

Delete `q=16*P` from (2) and remove P from the relation parameters.
The four existing checksum additions now compute the scale itself:

    bs_sum01=F0+F1;
    bs_sum012=bs_sum01+F2;
    bs_Q=bs_sum012+F3;
    q=bs_Q+1.                                        (4a)

Evaluate these after F3 and before every q-dependent packing or kernel
gate. The old checksum register bs_q is renamed q; its comparison
`bs_q=q` is deleted. This gives the exact projection on positive
Hhat,Mhat,Zhat

    Zhat-1 = (Hhat-1) AND (Mhat-1),                    (4b)

with **64=32M+32A**,22 positive auxiliaries and15 equations. No new
arithmetic is required: the four additions were already in selector56.
All other gates and comparisons retain their original formulas.

The positive domain is valid before any equation. The three supplied
fields F0,F1,F2 are positive and computed F3>=8, so (4a) gives q>=12.
The selector theorem then makes q a power of two, hence q>=16. Thus
q=16P for some power of two P as a conclusion of the proof. The earlier
padding argument gives (4b). Conversely, for any nonnegative H,M,
choose a power of two P larger than both and form the padded truth
classes at q=16P. Their checksum is exactly that q, so (4a) computes it.
The same complete positive Pell extension supplies every auxiliary.

This refinement also gives a bijection with the previous unrestricted64
source that supplied q. At every old positive zero its checksum equation
forces q to equal (4a); erase that coordinate. Conversely, every new
positive tuple reconstructs a positive old q by (4a). The deleted
checksum residual is identically zero and every remaining old residual
after this substitution is the new residual. Thus the two maps are
inverse on the full positive solution sets, including noncanonical Pell
witnesses. The bounded65 source and its positive domains are unchanged.

## 3. A binary mask selects a whole cell

Let B=2^b with b>=1 and P=B^t with t>=1. Let

    H=sum_j h_j B^j,       0<=h_j<B,
    S=sum_j s_j B^j,       s_j in{0,1}.

Then

    (B-1)S=sum_j s_j(B-1)B^j

has either b zero bits or b one bits in each binary cell, with no carry
between cells. Consequently

    H AND ((B-1)S) = sum_j s_j h_j B^j.                (5)

This is the precise selected-source product needed in the matrix trace.
It holds for unbounded t and b; no fixed-t matrix expansion occurs.
Ordinary multiplication H*S is a convolution and is not substituted for
(5). Nor does (5) hold for arbitrary odd B: with B=3, digits h=(1,2) and
s=(1,0), its left side is `7 AND 2=2`, while the selected digit word is1.

The120-operation batch source itself recovers P as a power of two. Thus if
an external certified geometry already says `P=B^t`, B>1 and t>=1,
prime factorization also recovers B=2^b. Binary geometry need not be
assumed independently in its soundness proof. Its completeness statement
still concerns the intended dyadic geometry.

## 4. Eight selected products through one kernel

Use positive parameters P,B, four positive histories H0,H1,H2,H3, eight
positive selector hats Shat_i, and eight positive output hats Zhat_i.
Decode `S_i=Shat_i-1` and `Z_i=Zhat_i-1`. In the physical shear order of
the four-register packet, the source-history indices are

    j(i)=(1,1,0,0,3,3,2,2).                            (6)

Define the concatenated numbers

    Hb=sum_(i=0)^7 H_(j(i))*P^i,
    Mb=(B-1)*sum_(i=0)^7 S_i*P^i,
    Zb=sum_(i=0)^7 Z_i*P^i.                            (7)

Use a single padded AND at scale P^8, on Hb,Mb,Zb. All three numbers
are nonnegative already from the positive supplied domains, even without
digit typing: each is a sum of nonnegative terms, and B-1>=0. Hb is
strictly positive. Therefore its computed output selector `F3=16Zb+8`
is always positive, as needed to invoke the selector theorem.

For the general batch, supply eight positive bound coordinates beta_i and
compare

    Zhat_i+beta_i=P+1,       i=0,...,7.                (8)

These enforce exactly `0<=Z_i<P`; conversely the needed witnesses are
`beta_i=P-Z_i>0`. Together with the full AND theorem, this is an exact
arithmetic relation on the displayed positive parameters:

    P is a power of two,
    0<=Hb,Mb<P^8, Zb=Hb AND Mb,
    0<=Z_i<P for every i.                              (9)

The source alone does not assert the missing individual history and
cell-selector digit conditions.

Now assume the intended common cell geometry and digit semantics:

    P=B^t, B=2^b, b,t>=1,
    H_j=sum_k h_j(k)B^k, 0<h_j(k)<B,
    S_i=sum_k s_i(k)B^k, s_i(k) in{0,1}.               (10)

The selectors in this general version need not be mutually exclusive.
Each H_j and `(B-1)S_i` is below P. Hence both input concatenations in
(7) have eight disjoint blocks of `log2(P)` bits. Equation (9) says their
bitwise AND equals the concatenation of their eight blockwise ANDs.
The paid bounds (8) ensure Z_i are the actual base-P output chunks.
Uniqueness of base-P expansion and (5) therefore give exactly

    Z_i=sum_k s_i(k)h_(j(i))(k)B^k, for all eight i.   (11)

Conversely, given (10)--(11), both concatenated inputs are below P^8,
their AND is Zb, and every Z_i<P. The padded AND positive converse and
the explicit beta_i above supply every auxiliary of the batch. Thus
(11) is certified uniformly in the unbounded number of physical steps,
conditional only on the explicitly remaining geometry and digit typing.

The output bounds cannot be omitted. Take B=2,t=2,P=4, all four
histories H_j=3 (both binary digits1), S0=0,S1=1 and all other selectors
zero. The actual
outputs are `(0,1,0,...,0)`, whose concatenation is4. The false outputs
`(4,0,0,...,0)` have the same concatenation and positive hats, so the
global AND alone accepts them. The first bound in (8) would require
beta_0=0, which is forbidden. This is a typed mask/history example,
not just a formal equality between unrelated packed numbers. In particular
all history digits meet the strict bounds in (10).

## 5. The literal120 schedule

The following shared power and repunit instructions cost5M+3A:

    P2=P*P; P4=P2*P2; P8=P4*P4;
    J2=P+1; P2plus1=P2+1; J4=J2*P2plus1;
    P4plus1=P4+1; J8=J4*P4plus1.                      (12)

Then `J8=1+P+...+P^7`. Exploit the repeated history slots in (6):

    Hb=(1+P)*(H1+P^2*(H0+P^2*(H3+P^2*H2))).          (13)

Its literal Horner schedule costs4M+3A, reusing J2 and P2. Horner-pack
the eight selector hats in radix P, subtract J8, compute B-1, and
multiply by B-1; this forms Mb in8M+9A. Horner-pack the eight output
hats and subtract J8; this forms Zb in7M+8A.

Append the65-operation padded AND directly with

    q=16*P8,
    padded_A=16*Hb+12, padded_B=16*Mb+10, F3=16*Zb+8.

These are the algebraic substitutions of the hatted padding formulas.
They cost the same seven gates; no three extra global hats are formed.
The eight bounds (8) each cost one addition, since P+1 is already J2.

| Part | M | A |
|---|---:|---:|
| Powers and J8 |5|3|
| Repeated history packing |4|3|
| Expanded selector-mask packing |8|9|
| Output packing |7|8|
| Eight positive output bounds |0|8|
| One padded AND |33|32|
| **Total** | **57** | **63** |

The auxiliaries are the22 retained AND auxiliaries and eight positive
bounds, for30. The comparison count is16+8=24. Every listed supplied
scalar is positive; signed computed registers inside the Pell core
retain exactly their original domain conventions.

### The conditional118 version

Replace the bounded AND65 by the unrestricted AND64 from Section2.
In the actual batch schedule this deletes `q=16*P8` and the now-unused
instruction `P8=P4*P4`. Compute q by the four existing checksum additions (4a), moved before
q-dependent packing, and delete the checksum comparison. Every other
instruction and comparison remains. The literal cost is **118=55M+63A**,
with30 positive auxiliaries and23 equations. The same positive erasure/
reconstruction bijection as Section2 applies to its former supplied q:
computed F3=16Zb+8>=8 makes the reconstructed q positive on every
positive tuple, before using any equation.

Its exact scalar projection is `Zb=Hb AND Mb` together with (8).
It no longer proves that P is a power of two, nor bounds Hb,Mb by P^8.
Under the already stated dyadic cell geometry and typed inputs (10),
those input bounds hold mathematically, and the same chunk-uniqueness
argument proves all eight equations (11). Conversely, the unrestricted
AND theorem supplies a sufficiently large positive q; for example
q=16P^8 is a valid witness choice. That witness construction is not an
exponentiation gate in the source. Thus the selected-source interpretation
has the same conditional hypotheses (10) while saving two products.

## 6. One bound suffices with the four-register margin

For the actual matrix interface, strengthen (10) to

    B>=16, 0<h_j(k)<B/2,
    at most one of the eight selector bits is1 at each k.         (14)

This includes its B=4q^2 and history digits `0<X<2q^2=B/2`, since q>=4.
Retain all the batch arithmetic, but replace the eight bounds by one
positive beta and the single comparison

    sum_(i=0)^7 Zhat_i + beta = P+1.                  (15)

Seven additions form the sum and one adds beta, still8A. Hence the
schedule is again **120=57M+63A**, now with **23 positive auxiliaries**
and **17 equations**.

Soundness needs only positivity: (15) implies

    sum_i Z_i=P-7-beta<=P-8<P.

Each Z_i is nonnegative, so each is below P, and the same unique-chunk
proof gives (11). Completeness uses (14). At every cell, the sum of
selected digits is at most B/2-1. Therefore

    sum_i Z_i <= (B/2-1)*(P-1)/(B-1) < P/2.

Since P=B^t>=16, the explicit witness

    beta=P-sum_i Z_i-7

is strictly positive and satisfies (15). This strengthened margin is
needed: replacing (8) by (15) without (14) would restrict the general
component incorrectly. The mutual exclusion and digit margin themselves
are not proved by this new equation.

The same replacement applies to the118-operation version: use (15)
instead of its eight bounds. This gives **118=55M+63A**,23 positive
auxiliaries and16 equations. Its scalar projection includes the stronger
bound `sum_i Z_i<=P-8`. The exact selected-source interpretation and
full positive converse follow under (10),(14), by precisely the preceding
soundness and margin arguments. All six64/65 and118/120 schedules are
implemented and independently audited in the adjacent source.

## 7. Remaining obligations and evidence

The118/120 batches discharge the eight selected-source products of the
four-register trace through a literal uniform arithmetic relation. It
does not discharge the typing of the four histories or the eight
Boolean cell selectors, their mutual exclusion, the regular macro
controller, or the shared physical duration in `q=2^t` and
`P=(4q^2)^t`. Here q denotes the physical duration power from the
four-register packet; the selector kernel's q is a separate, local
variable. For120, the derived fact that P is dyadic does not identify its
exponent with a function of the other exponent. For118, even that dyadic
fact remains part of the external geometry. The ordinary-input
loader is unchanged and has not been included in118 or120. In particular
adding these local ledgers is not an established universal bound.

The [checker](native_binary_masked_selection65.py) and
[receipt](native_binary_masked_selection65.json) retain and audit every
actual selector56 gate. They expand all fourteen imported residuals
with the usual auxiliary-norm correction, and independently expand each
new port and bound residual. All six schedules have their claimed
acyclic dependencies, counts and positive witness lists.

It exhausts21,845 input pairs through binary length seven, including
P=1, and checks the prefix, all positive truth classes, packed index
parity and exact population. Another341 truth partitions check the
reverse projection. There are1,152 general batch fixtures with arbitrary
independent Boolean selectors; changing one bounded output rejects the
batch. Another960 fixtures check the exclusive-selector variant and
its strictly positive global bound. The explicit carry-alias and odd-
radix examples check two hypotheses that cannot be silently removed.
These are finite exact audits. The unbounded converse follows from the
proved selector56 extension and the mathematical arguments above.

Before the checksum refinement, independent root full proof/source/default
review passed for all six original variants. A separate final review of AND64/65 passed with1,024 independent
complete residual identities and37,449 candidate-triple projection checks,
of which exactly1,365 were the required AND tuples. Another independent
full proof/source/default review of all six variants passed with6,144
arbitrary-positive assignments checked against manually expanded residuals
and all cost, witness and comparison counts. Its1,536 independent bit-string
fixtures also verified the exclusive-selection identity and positive global
bound. All reviewers accepted the strict-digit carry counterexample and
the explicitly retained geometry/typing hypotheses. No findings were
reported; these finite audits supplement the parametric proofs above.


## 8. Checksum refinement and exact polynomial compilation

The unrestricted sources now define q by (4a), removing one supplied
coordinate and one equation while retaining their arithmetic counts.
The source checker compares all three prescribed-scale circuits and their
comparison lists against frozen hashes; AND65 and both120 variants are
unchanged. For each unrestricted source it independently maps all surviving
selector residuals, including the auxiliary-norm correction, back to their
original indices. The omitted checksum residual is identically zero.
Another768 positive supplied assignments compare every register and every
surviving residual against the previous source after reconstructing q.
These are polynomial/source checks; the positive zero-set bijection is
the argument in Section2.

For completeness, literal sums of squares now have these costs:

| Unrestricted relation | Comparisons | M | A | Polynomial operations | Exact degree |
|---|---:|---:|---:|---:|---:|
| AND64 |15|47|61|108|28|
| General batch118 |23|78|108|186|112|
| Exclusive batch118 |16|71|94|165|112|

Each E-equation system pays E residual subtractions, E squarings and
E-1 additions. The checker constructs those actual schedules and verifies
their full polynomial values and degrees on weighted, offset polynomial
inputs. The first Pell-norm residual has degree14 for AND64 and56 for
either batch; all other residuals have lower degree. Its highest form is
`w^2*s^4*k^2*q_top^6`, where the scale's highest part is

    q_top=F0+F1+F2+16Zhat             for AND64,
    q_top=16Zhat_7*P^7               for either batch.

These are nonzero polynomials in the supplied coordinates. Their squared
highest forms prove the exact degrees28 and112, independently of the
finite checks. The supplied domains and the conditional history/selector
interpretation are unchanged by sum-of-squares compilation. These are
component polynomial costs, not complete universal polynomial bounds.

The checksum refinement passed independent root proof/source review and
a separate full proof/source/default review. The latter checked1,536
positive substitutions against every surviving original residual, the
positive reconstructed q, all new ledgers, prescribed-scale hashes, and
the unique highest form giving SOS degrees28/112. The author's final
default replay passed as well. No findings were reported.
