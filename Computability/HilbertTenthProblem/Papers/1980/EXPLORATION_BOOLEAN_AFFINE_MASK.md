# Compile any Boolean local relation into one affine masked field

For a fixed relation on k Boolean inputs, the number of forbidden patterns
need not determine the number of arithmetic operations. All of its clauses
can be absorbed into fixed integer coefficients of one affine expression
and one fixed bit mask. This uses the chosen convention that fixed numerals
are free. It does not make the bit-mask predicate itself free.

This is a general local compiler and a conditional packed-word theorem,
not a complete universal certificate or an improvement on the universal
bound of89. Input typing, neighbor alignment, the mask implementation,
positive-domain wrappers, and the raw input/acceptance interface remain
separate obligations. The generic Life instance is locally more expensive
than the existing specialized one-helper formula.

## 1. Construction and exact scalar equivalence

Let R be any subset of {0,1}^k. Enumerate its forbidden tuples as
p_0,...,p_(m-1). For Boolean z=(z_1,...,z_k), define

    u_j(z) = sum_(i:p_ji=0) z_i
             + sum_(i:p_ji=1) (1-z_i) - 1.

This is the number of coordinates in which z differs from p_j, minus one.
Consequently u_j is in [-1,k-1], and u_j=-1 exactly when z=p_j.
The condition z in R is therefore equivalent to every u_j being
nonnegative. Pick a power of two A>=2 with A/2>k-1 and set

    G = A^m,
    B = 2G,
    F(z) = G + sum_(j=0)^(m-1) A^j u_j(z),
    M = sum_(j=0)^(m-1) (A/2) A^j.                 (1)

All of A,B,G,M are fixed numerals for the chosen relation. B is a power
of two. Expansion gives the affine expression

    F(z) = c0 + sum_i ci z_i,
    c0 = G + sum_j A^j (popcount(p_j)-1),
    ci = sum_j A^j (1-2p_ji).                     (2)

For every Boolean tuple, 0<F(z)<B. Indeed, with
T=sum_(j<m) A^j=(G-1)/(A-1),

    G-T <= F(z) <= G+max(k-1,0)T < 2G.

The lower bound is at least1 since A>=2. The last strict inequality
follows from max(k-1,0)<A-1. It also covers m=0 directly, when F=1,
B=2, M=0. Arity zero is allowed and has the same direct interpretation.

If z is allowed, each u_j lies in [0,k-1], strictly below A/2. There
are no carries in (1), so every digit's masked high bit is zero. The
guard G is above all tested digits. Thus F(z) AND M=0.

If z is forbidden, choose the first j with u_j=-1. All earlier raw
digits are nonnegative and below A/2, so none produces an incoming
carry. Normalization at j therefore produces the digit A-1 and a borrow
into later digits. That digit has its high bit set, so F(z) AND M is
nonzero. Later borrows cannot change this lower digit. Hence

    z in R  iff  F(z) AND M = 0.                 (3)

The guard in (1) matters: it keeps even a rejected cell's complete value
strictly positive. Borrowing never reaches a neighboring packed cell.

## 2. Exact composition of aligned Boolean planes

Let z^(0),...,z^(N-1) be Boolean tuples, let q=B^N, and define

    J = 1+B+...+B^(N-1),
    Zi = sum_(t<N) z_i^(t) B^t,
    Fword = c0 J + sum_i ci Zi,
    Mword = M J.

Ordinary distributivity gives

    Fword = sum_(t<N) F(z^(t)) B^t.

Since 0<F(z^(t))<B for every cell, including rejected cells, this is
the actual base-B expansion. No carry or borrow crosses cell boundaries.
Therefore

    0<Fword<q,
    Fword AND Mword=0  iff  every z^(t) belongs to R.         (4)

Equation (4) assumes the Zi are already Boolean words with matching cell
positions. It does not establish those assumptions. For example, the
one-forbidden-pattern relation p=(1,0), A=4 has F=4-z0+z1 and M=2.
Untyped values z0=z1=100 still give 0<F=4<B=8 and F AND M=0.
Thus a bound on F and its mask do not generally type the input planes.

## 3. A positive-coefficient variant

If the all-zero tuple is forbidden, put it last in the clause ordering.
Each variable coefficient in (2) then has a final term +A^(m-1), which
strictly dominates the absolute sum of all its earlier terms. Thus every
ci>0. Also c0=F(0)>0 by the scalar bound. No typing hypothesis is needed
for these fixed coefficient signs.

For nonnegative supplied Zi and positive J, this gives an independent
bootstrap: Fword<q implies Zi<q for every i. Boolean typing still needs
its own proof. For a quiescent Boolean cellular automaton, complementing
the output coordinate makes the all-zero tuple forbidden: zero inputs
produce actual output zero, whereas complemented output zero represents
actual output one. This provides the positive coefficients. If the
original output word Y is already supplied, forming J-Y costs one
subtraction; choosing the complemented word as a primary variable moves
its interpretation into the neighbor and interface obligations.

## 4. Cost and concrete rules

With the k aligned Zi and J supplied, direct evaluation of (2) costs at
most k+1 multiplications and k additions. Forming Mword costs one further
multiplication. These are upper bounds, before removing trivial zero or
unit coefficients. They do not include constructing J, typing Zi,
implementing the mask, extracting neighbors, or loading the input.

| Local relation | k | Forbidden patterns | A | Cell radix B | Affine evaluation | Repeated mask |
|---|---:|---:|---:|---|---|---|
| Rule110, three inputs and output | 4 | 8 | 8 | 2^25 | 5M+4A=9 | 1M |
| Life, eight neighbors, center and output | 10 | 512 | 32 | 2^2561 | 11M+10A=21 | 1M |

The same counts and radices apply when the output is complemented and
zero is ordered last. The latter versions have all coefficients positive.
The large B in the Life row is a fixed numeral, not a charged power chain.
Multiplication by that numeral, wherever needed, is still charged.

The existing one-helper Life formula evaluates its local field in nine
operations, so this generic table does not improve that local count.
Its different tradeoff is the elimination of Boolean helper planes and
its applicability to arbitrary local truth tables. Whether that tradeoff
helps the complete certificate depends on geometry and mask packing.

There is no conflict with
`EXPLORATION_LIFE_AFFINE_MASK_OBSTRUCTION.md`: that obstruction concerns
affine expressions in the aggregate neighbor count, center and output.
Here the eight named neighbors have separate fixed coefficients. Replacing
them by their sum would remove precisely the information used here.

## 5. Verification and scope

`../verification/explore_boolean_affine_mask.py` is a standalone exact
compiler and checker. Its adjacent JSON records:

- all278 Boolean relations of arities0 through3, in two clause orders;
- 4,244 scalar assignments, with a separate direct clause evaluation and
  explicit inspection of the first negative digit;
- 4,164 packed small-relation cases;
- all139 applicable positive-coefficient orderings;
- complete Rule110 and Life truth tables in both output conventions;
- 256 four-cell packed cases for each of those four concrete instances.

An independent proof review covers the strict field bounds, first-negative
digit, packed composition, coefficient signs and untyped-plane caveat.
A separately implemented exhaustive check covers the same278 relations,
2,122 scalar assignments and16,658 ordered two-cell cases, as well as
all139 positive-coefficient variants. These finite checks corroborate
the general argument; they are not its universality or interface proof.

The result makes local truth-table complexity a fixed-numeral choice.
It does not remove the arithmetic cost of the number of input planes or
the need for a sound, complete, finite computation certificate.
