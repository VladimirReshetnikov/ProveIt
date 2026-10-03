# Post correspondence as a positive affine-matrix trace

This scoped alternative-substrate result does **not** improve
[complete75](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md). It supplies an
exact finite-trace skeleton for Post correspondence (PCP), an honest
expansion of its selected weighted fields, and an effective obstruction
to bounded-imbalance simplifications. The accompanying
[checker](matrix_pcp_trace.py) and [receipt](matrix_pcp_trace.json) test
the formulas against direct string concatenation and dense matrix products.

The useful distinction is that matrix dimension is not the number of
arithmetic operations needed to verify an arbitrary matrix word. Two
variable-slope accumulators are already necessary in this direct encoding;
their selected weighted histories are substantial additional relations.

## 1. Source contract and exact matrix representation

Post's original result concerns nonempty words over two letters and asks
whether some nonempty common sequence of tiles has equal concatenations.
Its undecidability is the motivation for the construction below; it is not
a fixed-program ordinary-input Diophantine interface. See
[Post, 1946](https://www.ams.org/journals/bull/1946-52-04/S0002-9904-1946-08555-9/S0002-9904-1946-08555-9.pdf).
The published five-pair reduction and its matrix-mortality consequences
are in [Neary, STACS 2015](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2015.649).
The different four-pair claim in the older arXiv version is not used.

Let the letters have digits 1 and 2 in radix 3. For a word w let

    a(w)=3^|w|, c(w)=ordinary base-three value of w,
    e(w)=a(w)+c(w).

The leading sentinel 1 makes e injective, including e(empty)=1, and

    e(vw)=a(w)e(v)+c(w).

For tile i=(u_i,v_i), put a_i=a(u_i), c_i=c(u_i),
b_i=a(v_i), d_i=c(v_i). The fixed nonnegative matrix

    M_i = [ a_i   0   c_i ]
          [  0   b_i  d_i ]
          [  0    0    1  ]

acts on (U,V,1)^T by the two append updates. A sequence i_0,...,i_(h-1)
is a PCP match exactly when

    M_(i_(h-1)) ... M_(i_0) (1,1,1)^T = (z,z,1)^T

for some z. This is a diagonal-reachability formulation of PCP, not a
claim that these upper-triangular matrices themselves are mortal. The
matrix product and the common sequence of choices remain to be certified.

## 2. A conditional eleven-operation trace

Fix A=max_i(a_i,b_i), a positive duration h, and an independently supplied
common geometry Q=B^h. At each time t supply the same selected tile i_t
for both lanes, and bounded positive history digits U_t,V_t and endpoint
z, all at most K. Define

    H_U = sum U_t B^t,       H_V = sum V_t B^t,
    P_U = sum a_(i_t) U_t B^t,
    P_V = sum b_(i_t) V_t B^t,
    C_U = sum c_(i_t) B^t,   C_V = sum d_(i_t) B^t.

These six identities are hypotheses about the supplied fields, not free
Diophantine constraints. In particular P_U and P_V contain selected
products of an unbounded history digit with a finite-table slope.

The source equations are

    B(P_U+C_U) = H_U+zQ-1,
    B(P_V+C_V) = H_V+zQ-1,
    B = AK+A+beta,                         beta>0.

They characterize exactly U_0=V_0=1, the selected append updates, and the
common endpoint U_h=V_h=z. No additional equality test for the two final
words is needed.

Proof: in one lane the first equation has residual

    1-U_0 + B sum_(t<h) (a_(i_t)U_t+c_(i_t)-U_(t+1)) B^t,

where U_h=z. Because 1<=U_0<=K<B, reduction modulo B forces U_0=1.
Each remaining coefficient lies between 2-K and AK+A-2, hence has
absolute value less than B. Repeated
reduction modulo B therefore forces every coefficient to vanish. The
other lane is identical. Conversely the equations telescope for every
genuine trace; choose K at least every history digit and endpoint, and
then any beta>0 supplies the paid margin. All six aggregate fields and
all displayed existential coordinates are strictly positive, since
h>0 and each tile word is nonempty.

The literal schedule is

| Computation | M | A |
|---|---:|---:|
| Shared E=zQ and G=E-1 | 1 | 1 |
| P_U+C_U, B times that sum, H_U+G | 1 | 2 |
| P_V+C_V, B times that sum, H_V+G | 1 | 2 |
| AK, AK+A, AK+A+beta | 1 | 2 |
| Total | 4 | 7 |

Equalities and copying registers are free under the repository convention.
The margin is paid, but the digit-bound relation with K is still a
separate hypothesis. The schedule cannot be combined with a Pell kernel
until that relation and common geometry have actually been implemented.

The margin cannot be replaced by the bare statement that history digits
are less than B. With B=11, append words `11`, `1`, and the false history
(1,2,8), the two step errors are (11,-1). Their base-B evaluation is zero.
The claimed packed equation holds although neither step is correct.
This counterexample uses the actual slopes (9,3) and offsets (4,1) of
nonempty PCP words, and every supplied history digit is positive and <B.

## 3. Paying for the selected arithmetic, but not its masks

An explicit branch split shows how much work the aggregate fields hide.
For each of m tiles define

    S_i = sum [i_t=i] B^t,
    U_i = sum [i_t=i] U_t B^t,
    V_i = sum [i_t=i] V_t B^t.

The selector fields must be one-hot at every common time; U_i and V_i
must be the correspondingly selected bounded histories. Those digit
typing and synchronization predicates are still unpaid.

Use directly

    H_U=sum U_i,       T_U=sum a_i U_i + sum c_i S_i,
    H_V=sum V_i,       T_V=sum b_i V_i + sum d_i S_i,
    BT_U=H_U+zQ-1,     BT_V=H_V+zQ-1.

For nonnegative branch coordinates the literal circuit costs

    (4m+4)M+(6m+1)A = 10m+5.

The four groups of m constant multiplications cost 4mM; the two T
sums cost (4m-2)A; the two H sums cost (2m-2)A. The common endpoint,
two transports and paid margin cost 4M+5A. Multiplication by fixed
numerals has been charged, including redundant coefficient-one gates
in this generic schedule; no optimality claim is made.

Absent tiles make some branch coordinates zero. Strict positivity can
be obtained without separately decoding all 3m coordinates. Supply

    Uhat_i=U_i+1, Vhat_i=V_i+1, Shat_i=S_i+1.

Compute T_U from its hatted weighted sum minus the fixed numeral
sum_i(a_i+c_i), and similarly for T_V. Keep the two uncorrected sums
`Hhat_U=sum Uhat_i` and `Hhat_V=sum Vhat_i`. Instead of separately
subtracting m from each, change the shared endpoint register to

    G=zQ-(m+1).

Then `Hhat_U+G=H_U+zQ-1` and likewise for V. Its fixed subtraction
costs exactly as much as the previous `zQ-1`; only the two T corrections
cost new additions/subtractions. The exact positive-coordinate schedule is

    (4m+4)M+(6m+3)A = 10m+7.

The two T registers and the two Hhat sums are positive for a nonempty typed trace.
The computed register G may be negative; it is an arithmetic intermediate,
not a supplied positive witness. No inequality for G is added. The fixed
numeral m+1 is free under the same convention as the original fixed1.
The digit predicate must interpret each hatted field as its value minus
one; that external predicate does not become free because its arithmetic
aggregate has this cheap correction. The checker compares both circuits
with the aggregate source, including sequences omitting most tiles, and
tests the positive adapter on arbitrary fields whose computed G is negative.

For m=5 the positive subtotal is **57=24M+33A**. Adding even a compatible
42-operation power/kernel component would give 99 before the remaining
typing, input and controller costs. This is a warning about this literal
decomposition, not a lower bound for PCP or matrix encodings. The present
42-operation kernel has not been integrated with this trace at all.

## 4. Effective bounded prefix imbalance is an obstruction

Here a bound D means a supplied bound on

    | |u_(i_0)...u_(i_(t-1))| - |v_(i_0)...v_(i_(t-1))| |

at every tile boundary of the proposed solution. It does not mean bounded
deciphering delay of either morphism. The distinction matters: PCP can
remain undecidable for morphisms with bounded deciphering delay, whose
equality language is regular but not effectively obtainable. See
[Karhumaki and Saarela, 2010](https://dmtcs.episciences.org/523/pdf).

For an explicit finite D, the PCP solutions respecting this bound form
an effectively constructible regular language. Its states are the empty
residual or a nonempty unmatched word of length <=D on one of the two
sides. On a tile, append its top word to the top residual, its bottom
word to the bottom residual, and cancel their longest common prefix.
If both sides remain nonempty, reject permanently: the first differing
symbols can never be corrected by later appends. If the one remaining
residual is longer than D, reject. Otherwise store it. The empty state
is both the initial and accepting state; a used-at-least-one-tile flag
excludes the empty sequence.

There are at most

    1 + 2 sum_(j=1)^D 2^j

residual states over this alphabet. By induction the stored residual is
exactly the unmatched suffix of the two accumulated words. This proves
both directions of the recognition claim. A supplied regular restriction
on tile sequences is handled by the finite product automaton, and
emptiness is decidable by finite graph search.

Consequently a total effective reduction from arbitrary halting questions
cannot supply both a finite D and a proof that every yes-instance has a
matching sequence within that bound. This also applies when the instance,
regular restriction and D depend computably on the input. Leaving D as
an unbounded existential parameter avoids this obstruction but restores
the unbounded unmatched-word geometry.

The particularly tempting shared-slope case a_i=b_i for every tile has
D=0 at every boundary. It has a solution exactly when some tile has
u_i=v_i; with a regular restriction, the accepted sequences are precisely
those using only individually equal tiles. Thus replacing the two slopes
by a common slope does not preserve PCP universality.

The bounded-imbalance condition is substantive even for one fixed tile
set. For tiles (`11`,`1`) and (`1`,`11`), the sequence 0^n1^n is a match
and has maximum imbalance n. Every fixed-D automaton omits some such
solutions. The theorem does not claim that unbounded imbalance alone
implies undecidability; this particular example is simple.

## 5. Remaining contract and validation boundary

The ordinary raw input x does not appear in this construction. A published
reduction that changes tile words with the input changes compiler numerals;
it does not provide the fixed-index contract of complete75. Encoding x as
the sentinel ternary word e(w) would be a variable recoding, and cannot
be silently identified with ordinary x. A successful continuation needs
an explicit paid fixed-program input relation, selector/regular-control
certificate, bounded digit types, and common finite power geometry.
Common-endpoint acceptance is paid above once these obligations are met.

The checker performs three independent comparisons: literal string
concatenation versus dense 3x3 products, the three arithmetic DAGs versus
those endpoints, and the finite residual automaton versus direct prefix
lengths and string equality. It also exhausts arbitrary small bounded
histories rather than only examples produced by the recurrence, and
checks the carry-omission counterexample and unbounded-imbalance family.
The receipt records exact counts. None of these finite checks proves a
universal compiler; the parametric trace and automaton proofs above give
the stated general results.

Independent scoped proof/source reviews passed without findings. Cross-review
found the shared endpoint correction that reduces the positive branch
schedule from10m+9 to10m+7; the original author independently checked the
improved source. A further600 arbitrary-field comparisons, including159
negative intermediate endpoint registers, agreed with separately expanded
formulas. Default replay checks the stored receipt as well as all invariants.

Run:

```sh
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/matrix_pcp_trace.py
```
