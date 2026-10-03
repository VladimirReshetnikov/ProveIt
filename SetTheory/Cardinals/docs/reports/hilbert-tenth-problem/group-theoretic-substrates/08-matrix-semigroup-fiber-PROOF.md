# Exact fibers of the fixed matrix construction

Authored 2026-10-03. This is a focused consequence of the existing 114-tile,
229-generator construction and its canonical paired polynomial interface.
It changes neither construction and makes no novelty claim.

## 1. Counting convention and immediate infinitude

For a word w over Sigma, put T_w = Phi(w#)^(-1). Let N_w(r) count tile
sequences s of length r satisfying

    w# h(s) = g(s) X#.

By the source marker lemma, N_w(r) is exactly the number of generator
factorization WORDS of diag(T_w,P) of length 2r+1. By the paired-interface
bijection it is also exactly the number of natural roots of F_r(T_w;x).
Factorization words, rather than distinct resulting matrices, are counted.
Different tile sequences give different generator words because the
literal generators are pairwise distinct; the one-hot selectors also
make their canonical polynomial roots different.

Write c(v#) for the copy tiles spelling v followed by the separator tile.
Its h and g words both equal v#. If s solves the equation, then, for every
k>=0,

    s_k = c(w#)^k s

also solves it: both sides of the original equality are simply preceded
by (w#)^k. Thus the same target has factorizations at inner lengths

    r = |s| + k(|w|+1),

and generator lengths 2r+1. These words are distinct because their lengths
are distinct. Consequently EVERY representable encoded word target has
an explicitly infinite unbounded factorization fiber. This holds for
arbitrary accepted w, not only well-formed machine inputs. It is stronger
than merely saying that an unbounded finite-fold guarantee was not proved.
It does not say that any one fixed-arity polynomial F_r has infinitely many
roots: each fixed-r fiber still has at most 114^r roots. The infinite set
is the disjoint union of the canonical fibers over r.

Appending c(X#)^k to a witness also preserves the equation. In particular,
w=X has exactly the witnesses c(X#)^k, so its generating function is
1/(1-z^2), including the empty tile witness and the one-generator product C.
No well-formed U15 input equals X, and its initial state A is not the halt.
The empty word cannot rewrite to X under these nonempty-sided rules.

## 2. Exact factorization generating function for a halting live input

The following also applies to any accepting live configuration, not just
the tape encoder's initial state A. Suppose its deterministic machine run
has H moves before the halting configuration. Write its live words as

    v_0=w, v_1, ..., v_H=[l J 1 r],
    n_j=|v_j|,  m=|l|+|r|,  B=binomial(m,|l|).

Here H counts machine moves only; J1->X and cleanup are additional rewrites.
Set

    r_* = sum_{j=0}^{H-1}(n_j-1)
            + (m+4) + sum_{a=1}^m(a+3) + 2,
    d = H+m+2.

Empty sums are zero. Then the EXACT ordinary generating function is

    sum_{r>=0} N_w(r) z^r
      = B z^(r_*) /
        [(product_{j=0}^H (1-z^(n_j+1)))
         (product_{q=4}^{m+4} (1-z^q)) (1-z^2)].             (A)

The denominator has d+1 factors, with repetitions retained.

### Proof: every witness has the asserted unique decomposition

Only the separator tile contains #, and all tile sides are nonempty.
The correspondence equation therefore uniquely parses a solution into
complete separator-terminated blocks, with no trailing nonseparator
suffix. The successive bottom and top words form a rewriting history
from w to X, allowing copy-only steps.

Every rule left side contains exactly one machine state or X. Every
reachable word has exactly one such marker. A block partitions its bottom
word into disjoint tile sides, so it can contain at most ONE rule tile.
With no rule tile it is exactly the unique all-copy block c(v#). With one
rule tile for u->u', it is uniquely the copies of the context, that rule
tile, the remaining context copies, and #. It realizes precisely one
actual rewrite. Conversely every such rewrite/copy block is admissible.

Before J1->X, the simulation invariant forces the one deterministic
machine history. It has no repeated configuration: a repeated live word
would force a deterministic cycle and prevent this run from halting.
After J1->X, the word is [l X r]. A tape erasure removes the rightmost
remaining letter on the left or the leftmost remaining letter on the
right. Exactly m erasures are needed, and then the mandatory [X]->X step.
Their left/right schedules are exactly the B choices of |l| left deletions
among m positions. Even if neighboring bits coincide, left and right
rule tiles are different. These schedules therefore give distinct
rule-block sequences; merging at a later word does not identify them.
All cleanup edges decrease length. Thus, after removing copy loops, the
reachable graph is a finite acyclic graph.

For each genuine history, insert k_j>=0 copies of the all-copy block at
each visited word, including before the first rewrite and after reaching
X. These choices are independent and injective: separator parsing tells
which complete blocks have a rule tile, recovers the genuine history,
and counts the intervening copy blocks. This remains true even without
assuming distinct word strings at different stages. In particular,
repeated configuration lengths cause repeated denominator factors, not
collisions between witnesses.

A rewrite u->u' applied in a source word of length n costs n-|u|+2 inner
tiles: context copies, one rule tile, and one separator. Every machine
rule has |u|=3, so its cost is n_j-1. The J1 rule has |u|=2 and source
length m+4, hence cost m+4. The m tape erasures have source lengths
m+3,m+2,...,4 and |u|=2, so their costs are those same lengths. The final
[X]->X costs 2. This proves the common minimal core length r_*.

An all-copy block at a word of length n costs n+1. Every history has the
live lengths n_0,...,n_H, followed by cleanup lengths m+3,m+2,...,3,1.
Thus every one of its B genuine histories has exactly the same multiset
of copy-loop weights appearing in (A). Geometric series for the k_j,
followed by addition over the B disjoint histories, prove (A).

For any fixed genuine history w_0->...->w_d=X, independently of the exact
simplification, the injective construction already gives the lower bound

    N_w(r) >= [z^(r-r_*)] product_{j=0}^d (1-z^(|w_j|+1))^(-1).

Equation (A) proves this lower bound is multiplied by exactly B here.

## 3. Exact support, quasipolynomials, growth, and inversion

The loop weights always include 2 (at X), 4 (at [X]), and 5. For m=0,
the halt word has length 4 and gives weight 5; for m>=1 the cleanup passes
through length 4 and gives it. No visited word has length 0 or 2, so
there are no loop weights 1 or 3. Consequently

    N_w(r)>0  iff  r in {r_*, r_*+2} or r>=r_*+4.            (B)

Indeed the nonnegative combinations of 2 and 5 are exactly
{0,2} union {n>=4}; adding the other weights changes no support. Thus r_*
is the minimum inner length, N_w(r_*)=B, and the corresponding generator
lengths are 2r_*+1, 2r_*+5, and every odd length at least 2r_*+9.

Let a_1,...,a_(d+1) be the denominator weights in (A), and let
A=product_i a_i and L=lcm_i a_i. Every pole is a root of unity. Moreover,

    sum_i a_i - r_* = 2H+m+5 > 0,

so (A) is proper. Partial fractions express its coefficients, for EVERY
r>=0, as finite sums of polynomials in r times roots of unity to the rth
power. Thus N_w is an exact quasipolynomial of period dividing L. Its
long initial zero interval is included; no finite correction is needed.
The only pole of order d+1 is z=1 because the weights include 4 and 5.
All other pole orders are at most d. At z=1 the leading coefficient is
B/A, since (1-z^a)/(1-z) tends to a. Therefore

    N_w(r) = B r^d/(d! A) + O(r^(d-1)).                     (C)

Equivalently r may be replaced by r-r_* in its leading term. Each residue
class has the same positive leading coefficient. This is polynomial,
not exponential, growth for this fixed accepted input, with an exponent
that depends on its actual halting history.

For the cumulative count C_w(R)=sum_{0<=r<=R} N_w(r),

    C_w(R) = B R^(d+1)/((d+1)! A) + O(R^d).

For the generalized inverse R_w(M)=min{R:C_w(R)>=M}, as M tends to infinity,

    R_w(M) = (((d+1)! A/B) M)^(1/(d+1)) + O(1).

These are counts/ranks of factorization words or their canonical paired
roots, not counts of distinct matrices. The relevant generator-length
threshold is 2R_w(M)+1. These conditional formulas do not give a total
algorithm to determine whether an input halts: H and its accepting run
are available only after acceptance has been established.

## 4. The actual released accepting tape

The released witness ell=011, r=empty has w=[110A0], H=7, m=5, |l|=0,
B=1, d=14, and r_*=94. Its exact generating function is

    z^94 / [(1-z^2)(1-z^4)(1-z^5)(1-z^6)(1-z^7)
             (1-z^8)^2 (1-z^9)^2 (1-z^10)^6].            (D)

The weights have product 8,709,120,000,000 and lcm 2520. In particular,

    N_w(r) = r^14 / 759,246,199,455,744,000,000,000
               + O(r^13).

At z=-1 there are 11 vanishing factors; every root other than 1 and -1 has
order at most 7. Hence all nonconstant-period terms have degree at most
10: the coefficients of degrees 14,13,12,11 in the quasipolynomial are
independent of the residue class. This follows from pole counts alone;
no uncomputed full quasipolynomial is claimed to have been tabulated.

At r=94,...,106 the exact counts are

    1,0,1,0,2,1,3,2,6,5,14,7,19.

## 5. Independent finite checks and limits

`check_fibers.py` is newly authored standard-library Python. It reads
only the copied, hash-pinned literal JSON data and saved witness; it imports no source
or paired-interface Python. It enumerates ALL literal bottom-word tile
segmentations in reachable fixture graphs, checks the unique-copy/
one-rule block property, and compares direct coefficient recurrence
against (A). Fixtures are the actual accepting input, [01J110] (six
cleanup histories), and [J1] (no tape erasures). The separate zero-step
word X is also checked.

It additionally verifies 33,544 bounded stutter witnesses have no tile
sequence collisions, and checks 12 sample witnesses by literal full 4x4
matrix multiplication and independently constructed canonical polynomial
selectors/state parts. Every squared-residual sum is zero, with exactly
17r+4 residuals and 130r natural auxiliary slots. `CHECKS.json` records
these outcomes. These finite tests supplement, rather than prove, the
all-length assertions above. The original source and paired proof packets
remain unchanged.

An independently authored graph checker in `audit/independent_check.py`
verifies 226 fixtures and 31,366 coefficients; normal and Python -O outputs
agree. `audit/REVIEW.md` records the independent proof review. Both checkers
use only the local pinned data files.
