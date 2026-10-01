# A second fixed program parameter gives the sparse compiler504 operations

The [literal source](residue_affine_sparse_program_radix504.py) makes a parameter
tradeoff from the [505-operation control-code compiler](residue_affine_sparse_control_codes.md).
Its default complete polynomial has **504=177M+327A**, **67 positive witnesses**,
**seven comparisons**, and degree **at most5160**. Its certificate costs
484=170M+314A. There are now **two fixed positive program parameters E,C**, in
addition to the ordinary positive input x. The [receipt](residue_affine_sparse_program_radix504.json)
records the complete emitted default schedule, literal counts and exact checks.

For a universal U21 program recipe, fix E=3^e as before and independently
choose a power of two C such that

    C>=64,       C>E.                                  (1)

Conditions(1) specify the permitted fixed program recipes; they are not extra
unpriced polynomial constraints. No representation claim is made on other C
slices. C stays fixed when x varies. The actual U21 table, prime assignment, ordinary
input prefix and paid chronology are unchanged. On every valid fixed slice(1),
the positive-zero projection represents exactly the parent's accepted-input
relation. This is not a one-program-parameter improvement: the uniform total
degree counts C as a variable, and rises from5091 to5160. It is also not a
same-coordinate positive-zero theorem. The general established75/87 frontier
is unaffected.

## 1. Guarded source change and fixed-C identity

The505 source has

    h=E+x+eta,       B=64h,       eta>0.

Replace precisely these definitions by

    h=x+eta,         B=C*h.                            (2)

The source removes the private E+x addition, changes the h row's first input
to x, and changes the paid radix multiplication's first input from64 to the
new parameter C. Every other source row, comparison, unit factor and supplied
witness is retained. The guard requires the complete canonical505 packet with
its default control plan, in the chosen native form and shared/unshared packing
recipe. It rejects other configurable code plans, even though some could be
handled by stronger recipe hypotheses.

This restriction matters at the new minimum h=2. The default codes are in
[0,63], hence below B>=128. The505 configurable interface instead allows codes
up to191; that broader plan guard is not reused here.

The active metadata sets `radix_multiplier='radix_program'`, explicitly lists
both fixed program parameters, and exports the radix coefficient. Historical
parent dictionaries remain provenance. The new `pack_path` requires C as an
explicit argument and constructs h and B from(2); it does not reuse a parent
packer that silently fixes64.

For an exact algebraic comparison, let G_C be the parent's complete polynomial
with its radix numeral64 replaced by an arbitrary fixed integer C. Its original
height definition remains E+x+eta_old. On arbitrary integer assignments,
substitute

    eta_old=eta−E.                                     (3)

Then the two h values, B values, every surviving source register, every
residual, every unit factor and both complete finalizers are identical. This
holds even for signed C and signed coordinates; it is a polynomial identity
for each specialization, not a semantic claim for those assignments.

The inverse affine map is eta=eta_old+E. For positive old coordinates it is
positive. Formula(3), however, can be nonpositive for positive new coordinates.
Moreover G_C is generally not the original505 polynomial G_64. Thus neither
this identity nor its positive forward direction proves equality of the new
and505 supplied positive zero sets. Soundness below is direct, and completeness
uses fresh packing at the fixed chosen C.

## 2. Soundness before radix typing, including h=2

Fix positive E,C,x satisfying(1). Before equations, h=x+eta>=2 and B=C*h>=128.
In the actual table pmax=19, and the complete radix-multiplier requirements are

    C>=max(4,edge_count+1,state_count+2,3*pmax+1).

Here edge_count=36 and state_count=21, so C>=64 suffices. In particular

    B−1>2(pmax−2),       B−1>2(h−1),
    0<E<C<B,            0<x<h<B−1.                    (4)

These are the strict numerical hypotheses needed in the
[terminal-bound proof, Section2](residue_affine_sparse_terminal537.md).
The original h>=3 bound is not needed: (4) proves the two pretyping inequalities
directly at h=2.

For clarity, the inherited positive computed scale is

    P=V+YI_hat+YD_hat+beta>=3,
    U=W+J,       V=U+sum_(p>2)(p−2)Z_p,
    N_P=P−(B−1)J.

All unhatted selector, quotient and selected words are nonnegative. At a zero
of either emitted finalizer, the ordinary residuals vanish and each individual
unit is ±1. Thus N_P=±1. It excludes J=0, and the computed positive bound gives

    J<=U<=V<P,       W,Z_p,YI,YD<P.

The exact remainder comparison and (4) give R,S<P; the range mask
(h−1)J is also below P. Class masks are at most P+1 while the repunit sign
is unsettled. Hence the packed words obey the same bounds as in the
[computed-scale proof, Sections2–3](residue_affine_sparse_scale538.md):

    0<=H,Z<P^48,       0<=M<2P^48<Q=B*P^64.

All padded native ports are legitimate positive ports. The local native norm,
rank, shifted-index and exponent arguments recover a dyadic native scale
before assuming the sign of the old native product. Therefore B and P are
powers of two. The negative repunit sign would make a power of two congruent
to−1 modulo B−1; the same Mersenne argument excludes it since B>=128.
Consequently N_P=1, P=B^T and J=1+B+...+B^(T−1), with T>=1, and the full native
AND relation follows.

Because C is a fixed power of two and h=B/C is a positive integer, h is dyadic
as well. It may still equal2. The rest of the proof therefore uses h>=2
explicitly rather than importing the parent's later h>=4 conclusion.

The unchanged joined lanes type all selectors, quotient/remainder digits and
selected actions. Edge_count<B makes the edge partition one-hot. The range
lanes give w,rho,sigma in[0,h−1]; U has digits w+1<=h, and V has digits
(p−1)(w+1)<B. The remainder equation is carry-free because both2h−2 and pmax−2
are below B. It recovers the exact increment, decrement, positive-test or
zero-test local graph. None of these estimates needs h>=4.

## 3. Exact chronology and ordinary input

Write C_payload and N_payload for the decoded current and following payload
words, to distinguish them from the fixed parameter C. Their T base-B digits
are positive and at most pmax*h<B, so

    0<C_payload<P,       0<N_payload<P.

The paid transport comparison is unchanged:

    B*N_payload+E=C_payload+P*F,       F>0.             (5)

Using E<B from(1), its upper bound gives

    0<P*F<=B(P−1)+(B−1)−C_payload<BP.

Thus 0<F<B. Comparing canonical digits in(5) recovers the initial payload E,
every current/following adjacency and the final payload F. The bounded
injective default control codes recover the same initial loader, intermediate
states and halt state as in505. Their maximum63<B is guaranteed by(1)–(2),
and no control equation was used in the preceding native bootstrap.

The loader is a nonempty contiguous prefix with no body-to-loader return.
If it has ell rows, its final output is E*2^ell<B, since that output is a typed
following digit. In particular 1<=ell<B−1. Also1<=x<h<B−1 by(4). The unchanged
paid prefix-count comparison gives ell congruent to x modulo B−1, hence ell=x.
The remaining selected rows are exactly the actual U21 execution from that
loaded payload. This proves soundness for every positive zero on a valid
fixed(E,C) slice, without a positive old height slack.

## 4. Completeness with C fixed independently of x

Take any finite accepted U21 prime-payload execution from E with exactly x
loader doublings. Keep C fixed as in(1). For each selected local graph,
construct the usual nonnegative quotient and remainder digits w,rho,sigma.
Choose a dyadic h strictly greater than x and all these digits. Then

    eta=h−x>0,       B=C*h

is dyadic, and all local digits fit the same range masks. This choice is
possible for every finite accepted run, regardless of its length or magnitude;
C does not need to grow with x or with the run. Pack the edge selectors, prime
selections and action selections in base B, with P=B^T and J=(P−1)/(B−1).
They satisfy the joined AND and every local graph by construction. The exact
chronological control and payload identities telescope, and the initial x
loader rows supply a nonnegative count quotient.

The new positive global slack is

    beta=P−V−YI−YD−2.

Here V<=(pmax−1)hJ and YI+YD<=V, because the increment and decrement selections
are disjoint. Therefore

    beta>=((C−2(pmax−1))*h−1)J−1
         >=((64−36)*2−1)*1−1=54>0.                   (6)

This proves the required slack directly, with no old height assumption. The
explicit packer uses precisely this bound. Finally apply the parent's complete
native extension theorem to the legitimate dyadic scale and actual packed AND;
the same positive computed-field and normalized/coupled native extensions exist.
Finite checking of outer histories does not materialize those Pell coordinates.

This constructs a complete positive zero from every finite accepted run. Together
with Section3 it proves equality of the represented accepted-input relation with505
on all fixed recipes(1). For the strongly universal slice E=3^e, choose for example
C=2^max(6,bit_length(E)); this is an effective fixed program recipe satisfying(1).
The parameter C is an additional supplied program coordinate, not an extra input
encoding or a freely varying existential witness.

## 5. Literal costs, degree and verification

|Native form, shared packing|Certificate|Comparisons|Witnesses|Polynomial|Degree bound|
|---|---:|---:|---:|---:|---:|
|Normalized norm units|481=168M+313A|9|67|507=177M+330A|5418|
|Coupled index units|484=170M+314A|7|67|504=177M+327A|5160|

The unshared schedules cost646=247M+399A and643=247M+396A respectively,
with the same corresponding degree bounds. Both product and SOS schedules are
emitted, and every gate reaches the chosen complete output. Each schedule saves
one addition from the matching505 predecessor schedule; multiplication by C
remains a charged multiplication.

Uniformly over all three parameters E,C,x and the witnesses, B now has degree2.
The coupled factor bounds are827,1926,448,66,1032,380,380,3, totaling5062. The
largest ordinary residual bound remains49. The product bound is therefore5160;
the same-cost SOS bound is10124. The uncoupled product/SOS bounds are5418/9316.
These use the same guarded main-norm source cancellation as the parent. They
are upper bounds, not claims of exact polynomial degree. If C is specialized
to a numeral before measuring degree, the parent's degree dictionaries are
recovered; that is distinct from the uniform bound reported here.

Run `python3 residue_affine_sparse_program_radix504.py`; `--write` regenerates
the receipt. Four form/packing ledgers include256 complete fixed-C register,
residual and finalizer identities,128 signed. There are128 positive parent
forward-map checks and33 positive off-zero assignments whose formal old height
slack is nonpositive. Four actual halted U21 outer histories with235 rows pass
the paid comparisons, scale, joined AND and input packing. Sixty-four endpoint
contexts include h=2, and13 malformed caller or invalid recipe cases are rejected.
The source guard, actual liveness and explicit-C packer are also checked.

Author scratch tests separately executed eight U21 outer histories with484 rows
and68 pretyping endpoint contexts. These are algebraic and outer-history checks,
not full native Pell zeros. Twelve additional author packs at C=128,256,1024
cover705 rows and pass all outer comparisons, repunit and joined AND.

The independent full proof/source/dependency review and fresh replay passed
without findings. Its separate literal executor/manual fixed-C specialization
passed384 complete register, factor, residual and both-finalizer identities,
192 signed, including75 positive assignments with nonpositive formal old
slacks. Eight independent degree/opcode/closure audits covered both native
forms, packing recipes and finalizers, including recovery of parent degree
dictionaries after specializing C. A separate register-counter interpreter
produced six halted U21 histories with357 rows, then12 explicit fixed-C outer
packings with714 packed rows;320 weak-repunit endpoint contexts included h=2.
All five local links and whitespace checks passed. This is finite algebraic
and outer-history evidence, not a full Pell fixture.

Root independently read the complete source/proof and passed a fresh replay.
Its separate literal executor checked384 complete fixed-C output and retained-
register identities on192 assignments,96 signed, across four contexts. Using
the parent literal payload interpreter and this packet's packer, it also
checked56 outer packs with14630 rows at two valid C values for each of28
halted U21 histories;49 packs had C>64. Those latter checks do not claim an
independent interpreter or packer. No findings remained; the trio is frozen.
