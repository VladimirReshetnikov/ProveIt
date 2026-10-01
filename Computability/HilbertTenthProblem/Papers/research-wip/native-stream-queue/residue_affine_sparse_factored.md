# Factoring prime and action masks in the sparse universal compiler

The [complete literal source](residue_affine_sparse_factored.py) lowers the
[674-operation prime-payload compiler](residue_affine_sparse_universal.md)
to **551 = 193M + 358A**, with **67 positive witnesses**, **8 comparisons**
and product degree at most **10052**. Its certificate has 528 operations.
The [receipt](residue_affine_sparse_factored.json) includes the entire
551-operation polynomial schedule. This saves 123 operations and 14
witnesses in that route; it does not improve the separate U9 or Korec411
bounds.

The fixed U21 table, register primes, ordinary positive input and program
recipe are unchanged. For every recursively enumerable set of positive
integers, a fixed positive program parameter E = 3^e makes positive zeros
exist exactly on that set. The loader remains a fully paid chronological
prefix. Its count equation is not a standalone three-gate exponential
predicate. The improvement factors the local arithmetic into prime and
action selections, and shares a remainder correction. It introduces no
new unit-sign relaxation.

## 1. Inherited machine and input interface

The parent records the exact literal U21 and its primary attribution to
[Korec, *Small universal register machines*, Main Theorem (a3) and Section 7](https://www.cs.cmu.edu/~cdm/resources/Korec1996-small-universal-RM.pdf).
It uses primes (5,3,2,7,11,13,17,19) for registers 0 through 7. At a valid
program slice E = 3^e, the paid prefix performs exactly x doublings,
producing E*2^x and therefore the initial counter vector (0,e,x,0,...,0).
The deterministic body is the same total residue-affine map of modulus
223,092,870, accepted on its halt-control class with any positive payload.
The loader is a separately paid branching prefix; it is not asserted to
be part of that deterministic residue map.

There are 36 edges: two loader edges and 34 body edges. Each edge has a
prime p and one of four kinds I, D, T, Z. I multiplies the payload by p;
D is a positive decrement; T is a positive pure test; Z is a zero branch.
The parent's exact local representations use w,rho,sigma >= 0:

|Kind|Current payload|Next payload|Remainder condition|
|---|---|---|---|
|I|w+1|p(w+1)|rho+sigma=0|
|D|p(w+1)|w+1|rho+sigma=0|
|T|p(w+1)|p(w+1)|rho+sigma=0|
|Z|pw+1+rho|pw+1+rho|rho+sigma=p−2|

The zero row represents residues 1 through p−1 exactly. In particular,
p=2 requires rho=sigma=0. The parent selects a quotient for each of 23
exceptional coefficient pairs. The new compiler instead selects seven
prime classes and two action classes.

## 2. Factored local graph

Write E_e for the nonnegative edge-selector words and J=sum E_e. Let W,
R,S encode w,rho,sigma. Every such supplied word is a positive hat minus
one. Define the computed word

    U = W+J.                                                (1)

The prime 2 always occurs because both loader edges use it. For each
occurring prime p>2, let G_p be the sum of its edge selectors and supply
one selected word Z_p. The prime lanes will enforce

    Z_p = U AND ((B−1)G_p).

Define another computed word, with nonnegative coefficients,

    V = U + sum_(p>2) (p−2)Z_p.                             (2)

After typing, U has digits w+1 and V has digits (p−1)(w+1) at a row
whose selected prime is p. Supply action-selected words Y_I,Y_D and use
I_sel and D_sel for the increment and positive-decrement selector sums:

    Y_I = V AND ((B−1)I_sel),
    Y_D = V AND ((B−1)D_sel).                              (3)

For the zero selector Z_sel and positive-test selector T_sel, the exact
linear identity

    Z_sel = J−I_sel−D_sel−T_sel                           (4)

can reuse the two action sums. The builder compares its literal cost with
direct zero-edge summation. On U21 it saves nine additions.

The new current and following payload words are

    C = U+V−S−Z_sel−Y_I,
    N = U+V−S−Z_sel−Y_D.                                  (5)

Retain the literal remainder comparison

    R+S = sum_(zero edges e) (p_e−2)E_e.                   (6)

At an I row, equation (6) gives S=0 and Y_I=V; hence (5) gives w+1
and p(w+1). At D it gives the reverse pair; at T both values are p(w+1).
At Z, S=p−2−rho and both action words vanish, giving pw+1+rho.
Thus (5) has precisely the four local graphs in Section 1.

There is also an exact signed correction identity, before any equations
or positivity assumptions. In a scalar row let

    delta = rho+sigma−(p−2)[kind=Z].

The new C and N equal the corresponding raw parent expressions minus delta.
Those raw expressions include +rho on every branch, before equation (6)
forces rho=0 on I, D and T.
Consequently the payload transport residual changes by −(B−1)delta.
This explains why the retained remainder comparison permits the new
formula. It is not a same-tuple identity between the complete native
polynomials: their mask lanes and auxiliary coordinates differ.

## 3. Complete packed source and bootstrap

Let b be the edge count, k the number of occurring primes greater than 2,
and g=k+2 the number of selected words including Y_I,Y_D. The default has
b=36,k=7,g=9. Positive hats represent all E_e,W,R,S,Z_p,Y_I,Y_D. There
are also positive final payload F, height slack eta, global slack beta
and loader quotient hat d_hat. Set

    h=E+x+F+eta,
    B=C_B*h,
    P=(B−1)J+1,
    range_mask=(h−1)J,                                    (7)

where the fixed dyadic multiplier C_B is at least
max(4,b+1,number_of_body_states+2,3*p_max+1). On U21 it remains 64.
All fixed multiplications are paid.

The retained global comparison is strengthened to include computed V:

    J+V+W_hat+R_hat+S_hat+sum Zhat_p
          +Y_I_hat+Y_D_hat+beta=P.                        (8)

The remaining four outer comparisons are (6), exact control transport,
exact payload transport and the paid loader count:

    B*following_control=current_control+(m+1)P,
    B*N+E=C+P*F,
    load_word=(B−1)(d_hat−1)+x.                           (9)

Here m is the body-state count; the loader state is 0, body states are
1 through m, and halt is m+1. The source uses the actual edge targets and
has no accepting state's outgoing edge.

One prescribed native AND joins the following lanes in base P:

    (E_e,J,E_e)                      for each edge,
    (U,(B−1)G_p,Z_p)                 for each prime p>2,
    (V,(B−1)I_sel,Y_I), (V,(B−1)D_sel,Y_D),
    (W,range_mask,W), (R,range_mask,R), (S,range_mask,S).   (10)

There are b+g+3 lanes, 48 by default. If a is the least power of two at
least this number, use the paid native scale Q=B*P^a; a=64 on U21. The
folded prescribed native ports remain 16Q,16H+12,16M+10,16A+8.

All positive parameters and hats give nonnegative J,W,R,S and selected
words. Thus U,V and all lane inputs/outputs are nonnegative before
constraints. Equation (8) excludes J=0, because that would make P=1
while several positive hats remain. It gives J>=1, P>=B, and strict
bounds below P for U=W+J, V, every supplied word and every selector.
The selector-class masks are at most (B−1)J=P−1; the range mask is
strictly below P. Thus the packed words H,M,A are below P^(b+g+3)<=P^a<Q.
The complete native theorem applies without an assumed digit type.

It yields dyadic Q and H AND M=A. Since B and P are positive factors of
Q, both are powers of two; h is also dyadic. The identity P−1=(B−1)J
with J>=1 then gives P=B^T and J=1+B+...+B^(T−1), T>=1, by the same
repunit divisibility proof as in the parent.

The selector lanes and sum E_e=J give exactly one edge per time row:
each E_e is a bitwise subset of J and b<B prevents carrying in that sum.
The three range lanes give 0<=w,rho,sigma<h. Therefore U=W+J has digits
w+1<=h<B, with no carry. Prime lanes select these digits exactly, so V
has digits (p−1)(w+1)<B. The two action lanes then select those V digits
exactly. This order is necessary: the action split uses V only after its
computed prime coefficients have been shown carry-free.

Both sides of (6) are carry-free: their digits are at most 2h−2 and
p_max−2 respectively, below B. Hence the row remainder condition holds.
Only now use (5) as positive payload words. The local graph gives their
digits in [1,p_max*h], strictly below B. Endpoints E,F are below h; all
control labels are below B. Base-B uniqueness in (9) proves exact
chronological payload and control adjacency, initial state/payload and
final halt.

The initial control forces a nonempty contiguous loader prefix, with no
body return to 0 or premature halt. If its length is ell, its last payload
is E*2^ell<B. Thus 1<=ell<B−1. Also 1<=x<h<B−1 by (7). Reducing the
loader comparison modulo B−1 gives ell=x. This is the parent's paid
input proof, with both strict bounds derived from the new source.

## 4. Positive converse

Take a genuine finite accepted payload run, including exactly x loader
steps. Its local w,rho,sigma are nonnegative. Choose dyadic h strictly
larger than E+x+F and every occurring w,rho,sigma, and set B,P,J as in
(7). Pack the actual selectors, prime selections of w+1, and action
selections of (p−1)(w+1). Then every supplied hat is positive, including
zero words; eta=h−E−x−F is positive.

The prime classes are disjoint, so sum Z_p<=U. The I and D classes are
disjoint, so Y_I+Y_D<=V. Moreover

    U+V <= p_max*h*J,
    R+S <= (p_max−2)J.

The slack required by (8) satisfies

    beta=P−J−V−W−R−S−sum Z_p−Y_I−Y_D−g−3
        >=(B−2*p_max*h−p_max+1)J−g−2 > 0.               (11)

Indeed C_B>=3*p_max+1 and h>=4 make the coefficient in parentheses at
least 3*p_max+5. There are at most p_max−1 distinct occurring primes;
therefore g<=p_max, and (11) is at least 2*p_max+3>0. This proves a
strict positive extension uniformly, rather than merely a large-radix
heuristic. The loader quotient hat is positive because its geometric sum
minus x is a nonnegative multiple of B−1.

All five outer comparisons and all lanes now hold. The inherited complete
native helpers supply positive native witnesses; strong normalization and
coupled-index normalization may reconstruct private witnesses. Conversely,
every positive zero gives the genuine run proved in Section 3. Thus each
form below has exactly the same accepted outer input/program relation as
the parent, with fresh native extensions as needed. An all-coordinate
positive bijection with the parent or an identical full polynomial on
arbitrary assignments is not claimed.

The unchanged primary U21 theorem and E=3^e recipe now prove universality
on ordinary positive x. Arbitrary positive E still has the stated payload
semantics; the represented-set assertion only requires the valid recipes.

## 5. Literal ledgers and verification

The builder shares selector packing, repeated quotient lanes, action
lanes, and the three repeated range masks. It compares direct fixed linear
forms with bounded suffix schedules and compares the two versions of (4).
No optimal-circuit claim is made. Both this sharing and an explicit
unshared packing are emitted and compared on signed assignments. All
retained gates reach the final polynomial output.

|Form|Certificate|Comparisons|Witnesses|Final polynomial|Degree bound|
|---|---:|---:|---:|---:|---:|
|raw SOS|520=178M+342A|21|74|582=199M+383A|1564|
|positive-scale SOS|520=178M+342A|20|73|579=198M+381A|1564|
|six-field SOS|520=178M+342A|14|67|561=192M+369A|3488|
|normalized norm product|525=183M+342A|10|67|554=193M+361A|10562|
|coupled-index product|528=185M+343A|8|67|551=193M+358A|10052|

The default seven factor bounds are 1614,3752,873,129,2008,742,742.
Their sum is 9860 and the maximum retained residual bound is 96, giving
9860+2*96=10052. The same-cost coupled SOS has bound 19720. These are
propagated upper bounds with the inherited guarded norm cancellation,
not exact-degree claims. With b edges and g selected words, witnesses
number b+g+29 raw and b+g+22 coupled; lanes number b+g+3.

Run `python3 residue_affine_sparse_factored.py` to replay the receipt;
`--write` regenerates it. The checker includes signed complete raw
source/SOS identities against a separately evaluated original native core,
all native rewrite correction audits, full shared/unshared polynomial
identities, local signed remainder-correction identities, typed class/action
lanes and wrong selected outputs, and differential payload/counter-vector
histories with wrong-input rejection. The case with no exceptional prime is
included. These finite algebra and outer-history checks do not materialize
full native Pell witnesses or replace the complete proof.

The author writer and fresh replay pass. The saved checks cover 25 ledgers,
160 complete raw identities (80 signed), 600 complete shared/unshared
identities (300 signed), and the inherited native correction audits in all
five contexts. Differential execution across 31 tables gives 176 halted
histories and 750 chronological rows, with 162 wrong-input rejections.
There are also 3,072 exact scalar remainder corrections, 896 typed
prime/action graphs and 2,688 rejected wrong selected outputs. The inherited
paid-prefix and random-access residue-map checks pass unchanged. All three
local links resolve.

Franklin's independent full proof/source/fresh-replay review passes with no
findings. Across five additional tables, including prime 23, missing action
kinds and no exceptional prime, his own executors check 240 complete
raw/native-oracle SOS identities (120 signed), 400 complete shared/unshared
outputs (200 signed), 600 positive pretyping cases and five rejected J=0
cases. His independent interpreter and packer check 60 halted histories
with 258 rows, plus 60 signed packed remainder corrections and strict
global-slack bounds. All three local links resolve. This is finite algebra
and outer-history evidence, not a full native Pell-witness fixture.

Root's independent full proof/source review and fresh replay also pass.
An additional interpreter and manual packer, without the author's path or
packing helpers, checks189 halted histories and795 chronological rows
across21 new tables, including prime23. All five outer equalities and the
packed AND hold;179 changed ordinary inputs fail the retained count while
preserving the other four outer comparisons. No full native Pell tuple is
claimed by these outer-history fixtures.
