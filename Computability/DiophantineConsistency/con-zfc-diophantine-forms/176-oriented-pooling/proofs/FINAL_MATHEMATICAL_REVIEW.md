# Mathematical and monic-certificate review

## Scope and reviewer role

This note records an AI-assisted review within the present collaboration.
The reviewer developed the general oriented and joint-pooling arguments,
then reviewed the separately implemented partition compiler and monic
elimination checker. A different reviewing agent independently audited
the inherited raw-index bound and the literal P216 port identities.
This is not external human refereeing or an end-to-end proof-assistant
verification.

The reviewed mathematical claims are the ordinary integer zero-existence
equivalences, the declared variable domains, exact degrees, actual variable
dependence, and the certificate mechanism. No consistency decision or
global simplicity theorem is inferred.

## Arithmetic theorem and partition forms

The all-five-base theorem is sound under its stated retained frame and
canonical-pair hypotheses. Zero bases have T=-1 and coefficient n=0;
they are omitted from the proof-only clearing product. Negative and unit
bases are handled without assuming their requested indices nonnegative.
All active fractions n*d^2/T have the common sign of A. The strict
bound 68*b^(12*b+1)<W^(6*b+2)<=W^W is valid for W>=258 and
b=floor(sqrt(W-1)). No coprimality of different denominators is needed.

The joint theorem correctly replaces the initial canonical-pair premise
by the inherited bound on the classified raw indices. Writing a raw pair
as epsilon*(X_nu(A),Y_nu(A)) is valid for both signs of A, including
index zero. The orientation residues are epsilon and epsilon*nu modulo
A-1. Thus the common-sign integral sum simultaneously forces epsilon=1,
nu=k and the exact power outputs. The bound

    C^2*o + sum |n|*d^2 <=188*b^(12*b+2)<W^(6*b+2)<=W^W

has ample stated margin. It remains valid when the selected fusion uses
fewer bases or requests. The new numerator is the literal sum of the
fourteen unique orientation errors; its equality with the transformed
parent row is a separate exact retained-row identity, which the source
auditor checked.

The partition compiler uses three logically distinct cases correctly:

- A single block uses E-z*T. At n=0 this is vacuous after existentially
  choosing z, because T=-1. At n!=0, the single-denominator square-error
  proof recovers its powers. It does not need an extra factor n.
- A multiple-base block uses the oriented weights n. This licenses
  zero or mixed-sign bases and the same common-sign argument.
- The specifically emitted consecutive-base alternative omits the weights
  only for q,q+1. This is justified directly under the retained frame and
  canonical-pair hypotheses, before the source's sign bootstrap. If both
  bases are nonzero, they have the same sign, and
  sign(T_n)=sign(A*n) makes their reciprocal denominators have a common
  sign. If q=0 or q=-1, the zero-base denominator is T=-1, so its E/T
  contribution is an integer. Subtract that contribution, omit the zero
  base from the proof-only clearing product, and apply the small-error
  argument to the remaining nonzero block. Thus no prior assertion that
  q or q+1 is nonzero is needed; the resulting power conclusions can
  themselves support the subsequent bootstrap.

In P210_joint (and P208_joint), orientation is fused specifically with
the UNWEIGHTED t block. This is valid because the retained horizon already
gives t>=16 independently of orientation. Consequently T_t and A-1 have
the same sign. The fusion authenticates all fourteen pairs and F=t^t
first; the other four single blocks, or the two oriented paired blocks,
are interpreted afterward. Fusing an unweighted block of unknown sign
would require an additional argument; no such unsupported profile is
among the reviewed emissions.

The stated restoration maps are integral on zeros: exact powers make
the original congruence quotients integral, and canonical pairs make the
orientation quotient integral. These semantic replacements preserve
existential zero existence. They are not claimed to be polynomial
bijections on all ambient integer tuples.

## Monic elimination: exact coordinate theorem

Reviewed `build.py`, `verify.py`, the curated `PROOF.md`, and the nine
curated equation certificates. The method is correctly attributed to the
existing acyclic monic-elimination approach, including repository report152.

Every removed variable has a distinct selected source row
epsilon*x+R=0, epsilon=+/-1, with no occurrence of x in R. The checker
authenticates the row as an actual polynomial in the relevant pooled
source DAG, not merely by its label. Its dependency traversal rejects
cycles. The recursive restorations are therefore integer polynomials in
the retained coordinates. They make every deleted row zero identically;
substitution into all remaining residuals proves an exact bijection of
integer zero sets. No rational division, root choice, or lost sign
condition is involved.

The checker imports neither the search program nor the producer. It
reconstructs every source node under the recursively authenticated
substitution and verifies the resulting residuals and final sum of
squares by structural identity. This is sufficient for exact polynomial
substitution; no probabilistic identity test is being used.

The exact-degree certificate is valid: propagated degrees are upper
bounds, and a nonzero modular value of a top homogeneous residual form
proves that the corresponding integer polynomial is nonzero. The
sum-of-squares output attains twice the maximum residual degree over the
integers. Primality of the evaluation modulus is unnecessary for this
nonvanishing implication.

The nonzero derivative certificate is also valid. At a supplied point
the checker recomputes all partial derivatives modulo the stated modulus.
A nonzero residue for each derivative proves that every independent
coordinate actually occurs in the collected integer polynomial, rather
than merely appearing in an expression that might cancel.

The coefficient-norm calculation supplies a conservative upper bound.
The largest circuit literal (384) is not the expanded polynomial's
coefficient height. No full expanded-support count or exact expanded
height should be claimed for these circuits. Circuit operation counts
refer to nodes reachable from the output, not all stored provenance
nodes. The proof and metric names distinguish these quantities.

## Performed finite check and conclusion

A fresh run of the separately implemented curated checker passed for
all nine selected polynomials:

| Integer variables | Exact degree |
|---:|---:|
|194|6|
|147|8|
|135|12|
|121|16|
|115|24|
|111|32|
|105|64|
|97|256|
|90|32768|

All five corruption controls per polynomial were rejected (45 rejected
mutations). The machine receipt `../verification/ELIMINATION_REVIEW.json` binds
these claims to the exact reviewed equation SHA-256 values. A preceding
broader development run passed eighteen profiles with ninety rejected
mutations; only the curated receipt is needed for this release review.

No gap was found in the reviewed new arithmetic argument, partition
interpretations, or exact monic-certificate mechanism. The conclusion
continues to depend on the explicitly identified inherited raw-anchor
theorem and C222/ZF/ZFC refutation calibration. Those unbounded imported
dependencies are not re-proved by the finite checker. Search optimality,
global minimum variable count, and literature-wide priority are outside
the proved scope.
