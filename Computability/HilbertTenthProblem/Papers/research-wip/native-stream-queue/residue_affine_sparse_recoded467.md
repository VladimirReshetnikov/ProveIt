# Direct two-program U21 recoding reaches 467 operations

The complete [emitted source](residue_affine_sparse_recoded467.json) costs
**467=171M+296A**, with **67 positive witnesses**, seven comparisons and
uniform total degree **at most5160**. Its certificate costs447=164M+283A.
It saves four multiplications while adding one addition relative to the
actual [470-operation two-program parent](residue_affine_sparse_shared470.md).
The positive integer zero sets agree on identical supplied coordinates on
valid fixed program slices. The full polynomials have an explicit correction
identity; they are not identical off zero.

The fixed recipe remains E=3^e from the inherited U21 compiler, with a second
fixed program parameter C that is dyadic, C>=64 and C>E. The ordinary input
is x>0, the height is h=x+eta and the radix is B=C*h. All 67 witnesses remain
positive. E and C stay fixed while x varies. This is a direct reconstruction
from the actual470 source. No positive-coordinate map to a one-program
source or improvement of the separate universal84 bound is claimed.

## 1. Exact code choice and paid expressions

There are 36 edges, in the authenticated U21 order; the two loader edges
come first. Write E_i=edge_i=edge_i_hat−1. The current state is0 at the
loader,1 through21 in the body, and22 at halt. For body instruction q set

    c(q)=w_(p(q))+4*[q is an increment]+d_q,
    (w_2,w_3,w_5,w_7,w_11,w_13,w_17,w_19)
      =(0,1,2,3,8,9,17,11),
    d_9=1, d_11=16, d_12=32, d_13=32, d_14=1, d_18=16,

with all other d_q zero, c(0)=0 and c(22)=14. The resulting codes are

    0,1,15,21,9,17,13,11,5,18,8,25,41,32,10,3,12,4,24,2,6,7,14.

All23 codes are distinct and their maximum is41. In particular every code
is below B>=128 before any native or control equation is used. This is the
necessary stronger guard at h=2; the old generic configurable-code limit191
would not suffice for this interface.

Let J=sum E_i, L=E_0+E_1, I be the increment-edge sum, G_p the prime-p
edge sum and A_q the source-state-q edge sum. The exact current-control word is

    C_new=sum_(p>2) w_p*G_p+4*(I−L)+sum_q d_q*A_q.

For each actual edge i with target state t_i, subtract the following paid
basis contributions from c(t_i):

    J +4*(E_2+E_6+E_8+E_11)+(E_5+E_8+E_9)
      +31*(E_18+E_19)+(E_24+E_25).

Grouping equal remaining coefficients and adding the basis gives N_new.
Each basis selector vector is verified against its actual already-paid
producer. The full current and next words are expanded into all36 supplied
selector hats, including the constants caused by E_i=edge_i_hat−1.
No Boolean assumption enters these integer-polynomial identities.

Compared with the parent's code assignment, only q2,q7,q14 and halt change:

    C_new−C_old = G_19−47*(E_24+E_25),
    N_new−N_old = E_2+E_10−47*E_20−49*E_31.

The control residual becomes

    r_new=B*N_new−(C_new+14P),

where P is the unchanged positive computed packing scale. The parent's
residual uses its old words and halt code63.

The common base is recomputed as the ancestor closure of the actual unit
product and the five non-control residuals. It has388 rows. In particular,
control-named pair sums now used by the prime and population expressions
remain in that base; their costs are not deleted as private control work.
The newly scheduled control uses64 rows instead of67. It also retains the
already-paid identity G_3+2G_5=(G_3+G_5)+G_5, removing its private scalar
product. Adding the15 remaining finalizer rows gives467 live operations.

## 2. Full positive-zero equivalence on the actual two-program recipe

The actual full finalizers are

    F_old=U*(1+sum_(j!=1) r_j²+r_old²)−1,
    F_new=U*(1+sum_(j!=1) r_j²+r_new²)−1,
    F_new−F_old=U*(r_new²−r_old²).

Here U and the other five actual residuals have the same complete producer
cones. The correction holds over every commutative ring. At a positive
integer zero of either polynomial, the positive integer1+sum r_j² must
be1 and U must be1. Thus all six residuals vanish. This first step does
not separately assume the signs of the factors inside U.

Now apply only the pre-control part of the
[two-program native and range proof, Sections2–3](residue_affine_sparse_program_radix504.md).
Its literal ports and required comparisons are unchanged, by the full base
identity. With h>=2 and C>=64, one has

    B>=128, B−1>2*(19−2), B−1>2*(h−1), 0<E<C<B.

The positive computed P and the remainder equation give the same weak
repunit and packed-field bounds. The local native norm/rank argument first
recovers dyadic B and P without using control chronology or assuming the
repunit sign. The Mersenne congruence then excludes the negative repunit
unit. Hence

    P=B^T, J=1+B+...+B^(T−1), T>=1,

and the complete native AND relation types every selected edge, prime,
action and range digit. There is exactly one edge per time row. This order
of proof is inherited unchanged at h=2; no larger height is presumed.

Both current and next control words now have T canonical base-B digits.
All old codes lie in[0,63] and all new codes lie in[0,41], strictly below B.
For either injective code system the equation

    B*N=C+c(22)*P

is equivalent, by uniqueness of base-B digits, to initial state0, matching
target/current states in successive rows, and final state22. It follows
that the old and new control residuals vanish on exactly the same typed
edge words. This reasoning uses only bounded injectivity of the new codes;
no old generic builder's default-plan restriction is treated as a theorem
about this newly emitted source.

At a new full positive zero, the old control equation therefore holds on
the same supplied coordinates. Every other residual and U already agree,
so the old full polynomial vanishes. The converse uses the same argument
starting with an old zero. This proves equality of the entire supplied
positive zero sets on each valid fixed(E,C) slice, retaining all native
witnesses. The inherited ordinary-input and completeness theorem therefore
transfers without fresh witness maps. It does not assert a positive inverse
between the original one-program and two-program height interfaces.

## 3. Uniform degree and source evidence

The fresh [helper](residue_affine_sparse_recoded467.py) authenticates ten
inert source/proof files, reconstructs all36 edges from the literal21-row
table and fixed prime list, checks all23 codes, and emits every row of the
complete source. All388 base rows, all72 native rows, the two height/radix
rows and the other19 finalizer rows remain literal. Every supplied port
and emitted operation is live. The parent packet remains unchanged in
memory. No predecessor helper or builder is imported or executed.

The control words are degree1 and the new residual has degree at most3,
because B has uniform degree2 when C is counted as a supplied variable.
The guarded main-norm expansion is

    X²+2acX+2GX+2acG+G²−4ac²−3c².

At the actual paid boundaries, the propagated degrees of X,a,c,G are
312,379,68,380. This gives the main-norm upper bound827. Repropagation
through the entire new source gives native product bound5062 and outer
sum-of-squares bound98, hence5160. The uncorrected syntactic bound5227
is also recorded. These are uniform upper bounds, not exact degrees.

The receipt additionally records32 signed full-source correction checks
and236 typed edge-word examples, including a word traversing each of the
36 edges. At bases128 and256 each example checks both old and new control
encodings. These are finite algebra and chronology diagnostics, not
materialized native Pell witnesses or complete accepted U21 histories.

The helper uses the standard library, rejects duplicate JSON keys and
noninteger JSON numbers, binds its own bytes and the emitted source into
the receipt, preserves checks under optimization, and uses type-sensitive
canonical JSON comparison. Creating a receipt requires an unused path.
Fresh normal and optimized exact replays from `/` pass with
`--root ABS_WIP --expect ABS_RECEIPT`. The independent review is recorded
separately. No global circuit minimum or new computation substrate is claimed.
