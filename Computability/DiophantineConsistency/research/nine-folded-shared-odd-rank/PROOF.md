# Exact sharing of the odd rank in the folded nine-positive equation

The immediate frozen parent is `research/nine-folded-minimal-reflection/`.
This sibling preserves its entire polynomial, not merely its zero set.
Every assignment of its nine integer variables, in particular every strictly
positive assignment, has the same output as the corresponding parent.
All fixed ports and native calibration dependencies remain unchanged.

| Complete tuple | Live operations | Exact total degree |
|---|---:|---:|
| original31 | 405 = 237 mul + 150 add + 18 sub | 1,191,570 |
| compact54-sharp | 413 = 241 mul + 154 add + 18 sub | 1,316,546 |

## 1. The exact stored source registers

In both complete parent graphs the source rank is literally defined as

    R=RankPlusOne-1.

RankPlusOne is an existing source register feeding that subtraction. Its
name here describes a checked arithmetic value; the identity does not
rely on the meaning of a machine, binomial coefficient, or source code.
The parent's odd index is computed using two binary gates:

    TwiceRank=2*R, B1=1+TwiceRank.

The entire consumer inventory of TwiceRank consists of the single B1
addition. Replace those gates by

    B1_new=R+RankPlusOne.

This takes one binary addition with both operands already stored. No new
variable, numeral, positivity condition, arithmetic division, or implicit
operation is introduced. The scalar2 leaf remains live elsewhere in each
source circuit; only the private multiplication is removed.

## 2. Universal polynomial and whole-output identity

For every integer rplus, and more generally in every commutative ring,

    1+2*(rplus-1)=(rplus-1)+rplus.                    (1)

The independent checker expands both actual B1 schedules with the sole
free cut at the literal RankPlusOne node and compares all coefficients.
It also verifies the unchanged literal subtraction defining R.
Consequently B1_new equals B1_parent for every assignment, without any
source or sign assumption.

Every other parent node is retained, with precisely the same operator and
its mapped operands. Induction over the full acyclic schedule, using (1)
at the changed B1 node and literal equality at every other node, proves
pointwise equality of the complete integer output. The finite checker
accounts for every parent and child node and checks the complete private
consumer inventory. This is a complete structural proof, not a comparison
of finitely many numerical evaluations.

The strict positive domain and all fixed leaves remain unchanged.
Accordingly both directions of the parent's ordinary zero/refutation
equivalence transfer by the identity witness map. In particular its
positivity-first margin argument, reflected parameter G=A*(F-1)+F,
signed Pell folding, odd actual B1=2R+1 in completeness, finite matrix
periods and positive auxiliary witnesses apply unchanged. The original31
and compact54-sharp bindings remain distinct complete coherent tuples;
no individual port substitution or identification of different K values
is performed.

## 3. Degree and complete finite certificate

Since the entire polynomials are identical, their exact total degrees
are unchanged. The checker independently repeats the complete centered
norm identity, literal degree bounds and actual-coefficient nonzero leading
homogeneous witnesses of the parent. The unique dominant summand remains

    4*Omega^4*(V^2-a)*(G*H)^2.

Its exact degree is66*d+14*r+8*Wmax+54, where d=deg A, r=deg R.
For the two complete sources these are1,191,570 and1,316,546.
Nonzero evaluations of the highest homogeneous form modulo three primes
certify attainment over Z. The larger syntactic bounds1,599,032 and
1,766,808 remain separately reported.

Both whole native tuples and every fixed leaf are recomputed and compared
with the authenticated incoming source and earlier complete payloads.
Normal and optimized Python independently check the complete node map,
all literal operators and operands, norm and rank identities, operation
counts, topology/liveness, exact degree and rejected corruptions. No parent
emitter or Lean process is executed. No new native calibration, Lean,
internal-ZFC theorem or global optimum is asserted. All frozen parents,
common documents and canonical pages are preserved.
