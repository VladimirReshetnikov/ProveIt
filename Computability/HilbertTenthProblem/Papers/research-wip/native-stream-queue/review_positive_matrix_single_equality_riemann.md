# Independent review of the strictly positive matrix equality transfer

**PASS, with no correction requested.** The lift preserves every selected
signed word action on coordinate differences. Its application to the
accepted fixed seven-dimensional Gram interface yields a fixed strictly
positive eight-dimensional alphabet with one common row sum, a complete
14 = 5M + 9A positive input-column loader, and exactly one terminal
equality of evolving coordinates. It does not supply a fixed-arity
Diophantine certificate for the unbounded selected word.

## 1. Exact lift, positivity and word order

For every original row, its absolute row sum is at most kappa-1.
Therefore each entry M_ij+kappa is at least one, and the final-column
entry kappa-sum_j M_ij is also at least one. The bottom row is constantly
kappa>=1. A top row sums to

    sum_j M_ij+r*kappa+kappa-sum_j M_ij=(r+1)*kappa,

which is also the bottom-row sum. The same kappa and C work for every
letter in the finite alphabet, including the all-zero family.

Subtracting the bottom row from each of the top rows proves

    D L_sigma=[M_sigma | -M_sigma*1]=M_sigma D.

The top-left and bottom-left kappa terms cancel exactly. Iterating this
identity preserves the same ordered product on both sides. It introduces
no transpose, reversal, inverse, denominator or length-dependent scale.
The chronological convention with the most recent letter on the left
is consistent with the displayed product in the note; the identity also
holds for any other consistently named ordered word product.

For an arbitrary integer v, a sufficiently large positive integer h
makes the lifted input (v+h*1,h) strictly positive and gives decoder
value v. The general statement correctly does not charge an arithmetic
implementation of choosing h. Every positive input remains strictly
positive under every lifted letter. Its first signed coordinate is zero
if and only if the first lifted coordinate equals the last one.

This proves a quotient action through D, not a homomorphism preserving
full matrix products or inverses as lifted operators. The common
all-ones direction has eigenvalue C and a two-letter product has C^2.
The author's retained warning about full-operator identities is correct.

## 2. The inherited universal input interface

The Gram note's precise theorem supplies one finite seven-dimensional
signed alphabet, independent of the program and ordinary input, and
acceptance u A_w v(x)=0 for every recursively enumerable positive set
through its fixed program numerals. Its scalar-zero proof requires the
inherited torsion-free group and its prescribed generator alphabet;
the new transfer leaves that alphabet and all its selected words intact.
No inference from undecidability alone is used.

The fixed row replacement Q has determinant one because u_1=1, and its
inverse is integral. Conjugating each letter therefore preserves its
ordered products, while the first coordinate of Qv is

    f=2a+2c-4=2(r^2+1)^2>0.

The remaining coordinates are exactly (b,c,a,b,c,1). The specified
program numerals alpha=12*2^(p+1), beta=12*2^p are compiled constants in
the accepted interface. The alphabet is fixed across both p and x;
no varying exponentiation is treated as a free input operation.

For the strictly positive lift the fixed choice h=1 is sufficient.
Decoding (f+1,b+1,c+1,a+1,b+1,c+1,2,1) gives precisely Qv. Thus the
same word accepts exactly when coordinates 1 and 8 are equal. The
empty word has difference f>0 and cannot accept, so no hidden
nonemptiness condition is required.

## 3. Complete fourteen-row loader

Let eta=r-1, s=r^2 and u=s+1 as in the source table. The four shifted
outputs simplify directly to

    a_hat=(r-1)^2+2=a+1,
    b_hat=(r-1)(r^2+1)+3=b+1,
    c_hat=(r^2+1)^2-a_hat+4
          =r^4+r^2+2r+2=c+1,
    f_hat=2(r^2+1)^2+1=f+1.

All are positive for r>=1. Literal output copies and the fixed entries
2 and 1 need no additional arithmetic. The five multiplication rows
are 1, 4, 6, 8 and 10; the remaining nine operations are additions or
subtractions. In particular alpha*x is paid, and neither the doubling
nor a final shift is omitted. Every row and each supplied input
alpha,beta,x feeds an output. There are no auxiliary witnesses.

The internal subtraction v-a_hat is charged and allowed. Its presence
does not weaken the comparison with the capped theorem: that theorem
allows any totally computable specified initial vector, so this finite
loader is already admissible as initialization. The distinction lies
in the unbounded-coordinate equality at acceptance.

The prior 13-operation column plus four separate shifts indeed gives
a valid 17-operation reference. The displayed sharing reduces it to 14
without claiming either number to be a minimum or the complete cost of
an unbounded computation history.

## 4. Contraction and the exact equality boundary

After dividing by the common C, every matrix is row stochastic and
each entry is at least 1/C. Removing the matrix whose every entry is
1/C leaves a nonnegative matrix with row sum theta=1-1/kappa. Its
rows send a real vector into the interval between theta times that
vector's minimum and maximum. The removed part contributes the same
scalar to every coordinate, so oscillation contracts by theta.
Induction gives the stated normalized bound for every switching word.
The empty word is treated separately, including the case kappa=1.

Stochasticity makes normalized minima nondecreasing and maxima
nonincreasing. Their difference tends to zero, and the initial positive
minimum remains a positive lower bound. This proves a common positive
limit along each infinite switching word.

For M=[1], kappa=2 and C=4, the stated L has rows (3,1) and (2,2).
Their difference is (1,-1), so the raw coordinate difference of the
state remains exactly one from (2,1). The terminal equality never holds
at a finite time. Its normalized difference is 4^(-t), and convergence
to a positive common limit makes the coordinate ratio tend to one.
The example therefore refutes replacing exact equality by arbitrary
approximation, as claimed.

The prior capped theorem admits nonnegative polynomial updates with
finite fixed threshold/congruence predicates, including parameters
computed effectively from the ordinary input. A comparison between
two unbounded evolving coordinates is outside that exact predicate
class. Since the present interface contains a nonrecursive ordinary
input language, a total faithful replacement solely inside the capped
class would contradict its terminating decision procedure. Finite
extra control or an effectively chosen large cap cannot remove that
contradiction. This is the stated interface obstruction, not a theorem
that every positive-matrix problem is undecidable.

## 5. Scope, retained boundaries and evidence

The author's two numbered remarks correctly retain the false inference
from approximation to exact equality and the false extension to full
lifted matrix identities. No new wrong or unproved claim arose in this
review, and no correction was requested. The open question correctly
keeps selected-word certification, chronology, endpoints and ordinary
input binding unpaid. No numerical universal alphabet, optimal
matrix dimension or universal arithmetic saving is asserted.

I read the complete author note and receipt, Gram lines 1--232, the
complete capped theorem, group-commutator lines 185--235 and 246--346,
and the complete Markov lift note. The latter confirms the stated
comparison with signed Fourier coordinates and a rational duration
scale; the new lift has positive integer states with an exact signed
difference decoder. External group embedding and existing universal
alphabet proofs are inherited at their stated interface, not re-audited
against outside literature.

The companion metadata binds the frozen author pair, verifies the four
author dependency byte/span pins, and records my narrower substantive
read spans. It also parses the fourteen displayed operations only for
binary syntax, names, dependencies, liveness and the arithmetic ledger.
The explicit polynomial simplifications above are hand derivations;
no saved source array is evaluated or symbolically propagated.

No scientific helper or arithmetic sample program was run. No supplied,
archived, committed, predecessor or frozen code was executed or imported;
no source degrees were propagated or universal matrices materialized.
Only original byte/span and structural metadata were computed, with
all review artifacts confined to /tmp.
