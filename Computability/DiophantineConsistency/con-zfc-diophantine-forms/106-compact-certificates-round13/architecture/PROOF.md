# New architectures for the direct proof certificate

This packet proves four arithmetic transformations. The common-radius majorant and forward Pell quotients improve the main round 13 construction. Negative CRT moduli and factorial-separated labels are valid alternatives, but their measured standalone variants do not beat the radius construction. None of the arguments asserts the consistency of ZFC or a newly kernel-checked end-to-end formalization.

The benchmark builders are self-authored copies of the round 13 direct builder, not executed upstream programs. Their counts are frozen comparisons against the earlier 2799-variable source; later factoring and forward-quotient improvements in the main direct packet supersede those counts.

## A common radius replaces the duplicated upper row circuit

Let E and F be the natural arithmetic circuits obtained by splitting the fixed signed row polynomial into nonnegative polynomial sides. Their leaves are natural row inputs and constants in {0,1,2,3,4}. Fix a natural radius R at least 4 which bounds every row input. Assign a syntactic exponent h to each node:

- An input receives h=1.
- Constants 0 and 1 receive h=0; constants 2,3,4 receive h=1.
- An addition receives h=max(h_left,h_right)+1.
- A multiplication receives h=h_left+h_right.

Then every node value is at most R^h. This follows by induction on the finite DAG. At an addition, each summand is at most R^d, so their sum is at most 2R^d, which is at most R^(d+1). At a multiplication, multiply the two induction bounds. The zero constant causes no exception because 0 is at most R^0=1.

Consequently, D=max(h(E),h(F))+1 gives E+F at most R^D. If one only needs separate bounds on E and F, the final +1 is unnecessary. Either convention is valid if the implementation and certificate agree.

For the short-beta source use

R = 4 + N + x + y + m + M0 + U.

The row index is at most N. The three labels are bounded by m. The two accumulator coordinates are less than y and can be majorized by y. All remaining local coordinates are at most U. Every external row input is one of the displayed summands. Thus the induction hypotheses hold, and R also dominates N and every binomial lower argument, including U+1, m+1 and y.

Take a fixed power of two Dhat at least D and put K=R^Dhat. Then K bounds the row values and all range cutoffs. K is a polynomial, not a variable exponent: if Dhat=2^s, s successive squaring gates compute K. No new Pell power graph is introduced. Set T=K! and use the existing positive CRT compiler. Each prime dividing 1+(i+1)T exceeds K, so the decoded row equality follows exactly as before. Since all range factorials divide T, ordinary CRT proves completeness of the factorial-free binomial certificates.

The independent earlier source gives D=6,893,164, while its negative-CRT group source gives D=6,891,818. Both are bounded by 2^23=8,388,608. Thus 23 ordinary squaring gates replace the entire duplicated upper row DAG. The exact source used by the main construction is allowed to have a different smaller audited D, provided it remains at most 2^23.

The completeness order is unchanged: choose a finite proof and its labels, then the carrier, then the obligation stream, then a sufficiently large beta scale y and code x, then U, then R,K,T and finally the CRT representatives. The radius includes x,y,M0, but they are fixed before R is chosen. There is no circular requirement on the obligation stream.

## Every indexed Pell congruence has a forward witness

For A at least 2 define the canonical Pell sequences by

X_A(0)=1, Y_A(0)=0,
X_A(j+1)=A X_A(j)+(A^2-1)Y_A(j),
Y_A(j+1)=X_A(j)+A Y_A(j).

Both coordinates are nonnegative. If B is at least A, simultaneous induction on j gives X_B(j) at least X_A(j) and Y_B(j) at least Y_A(j), because all coefficients in these two recurrences increase with the parameter. Also Y_B(j) is at least j, by induction using X_B(j) at least 1 and B at least 1.

For a target Pell index k greater than zero, the existing completeness construction sets X=X_A(k), Y=Y_A(k), h=2kY, U=X_A(h), V=Y_A(h). Here Y is at least k, hence h is at least 2 and U is strictly greater than X_A(1)=A. It chooses a natural B satisfying B congruent to A modulo U and B congruent to 1 modulo 4Y, and sets S=X_B(k), R=Y_B(k). The index in S and R is the original target k, not the auxiliary h.

Since 0<=A<U, the residue equation B mod U=A implies B>=A. Parameter monotonicity now gives S>=X, and the elementary index bound gives R>=k. Therefore the same valid completeness witness has natural quotients q_B,q_S,q_R with

B = A + U q_B,
S = X + U q_S,
R = k + 4Y q_R.

The existing fourth congruence B congruent to 1 modulo 4Y is already forward because B>=2. Thus all indexed-Pell congruences can be encoded by one-sided quotient equations. Conversely, each such equation implies its original congruence, so replacing the equations restricts the certificate and preserves soundness immediately. Completeness is supplied by the canonical witnesses just proved to have the required orientations. This does not claim every old auxiliary witness is forward.

Source verification: the inert file PellMatiyasevic_reference.lean, lines 761–807, contains the target-index completeness construction. It is from Mathlib commit 4dc43842a11f257ffba2a611c943a133a65cb4b2, blob db9c757dd7cac29260397150fd190d72715ea3f8. The SHA256 and permanent URL are recorded in PELL_SOURCE_PIN.json. The source is included under its Apache 2.0 license. It was read, never executed.

## The power residue also has a forward quotient

Let A>=n>=1, and write

F_j = X_A(j) - (A-n)Y_A(j).

The ordinary integer recurrence is F_0=1, F_1=n and F_(j+1)=2A F_j-F_(j-1) for j>=1. We claim F_j>=nF_(j-1)>=0 for every j>=1. The base case is equality. Assuming the claim,

F_(j+1)-nF_j = (2A-n)F_j-F_(j-1)
>= [n(2A-n)-1] F_(j-1) >= 0,

because n(2A-n)>=n^2>=1. Induction gives F_j>=n^j, including j=0.

Set T=2An-n^2-1>0. Modulo T, both F_j and n^j satisfy the same recurrence and have the same first two terms: the recurrence error for n^j is -T n^(j-1). Hence F_k is congruent to n^k modulo T. Its nonnegative difference from n^k yields a natural q with

X_A(k) + nY_A(k) = A Y_A(k) + n^k + Tq.

The positive power graph already forces A>n. Indeed its last norm is A^2=1+W^3(W+2)Z^2 with W=n+k>=2 and A>=2; Z=0 would give A=1, so Z>=1 and A>W>=n. Thus the oriented power-output equation loses no canonical completeness witness. As with the indexed-Pell orientations, the converse follows by forgetting the quotient sign and applying the inherited exact power graph.

The recurrence inequality itself also covers A=n=1, although that case is not used by the Pell graph. Positive-power specialization does not cover n=0 or k=0; the direct construction separately proves every call has positive base and exponent.

## Negative factorial moduli separate a product from a conjunction

Fix a bounded row relation of the form

(there exists j<h with C_j=0) and R0=0,

where each C_j and R0 is a sum of squares of integer polynomials and is therefore nonnegative on natural arguments. Write H0=product_j C_j. Let K>=4,N and suppose K bounds each C_j and R0 throughout the intended bounded row box. Also require K to dominate every range-certificate lower argument. Set

T=K!, D_i=(i+1)T-1 for 0<=i<N, B=product_i D_i.

The empty product is 1. Every D_i>=23 and D_i is congruent to 3 modulo 4. Also gcd(D_i,T)=1. For i<j, any common divisor of D_i,D_j divides (j-i)T, hence divides j-i; since j-i divides T, the common divisor is 1. Thus the D_i are pairwise coprime.

A positive integer congruent to 3 modulo 4 has a prime divisor p congruent to 3 modulo 4. Applying this to D_i gives such a p. Since p does not divide K!, p>K.

Use the same binomial range certificates B divides choose(A_j,u_j+1), the index certificate B divides (C+1)T-1, and replace the row congruence by

H0(C,A)^2 + R0(C,A)^2 congruent to 0 modulo B.

To decode row i, choose the prime p just described. The binomial identities decode A_j modulo p to some w_j between 0 and u_j. The index equation gives C congruent to i modulo p because T is invertible. Over the field with p elements, -1 is not a square, so a^2+b^2=0 forces a=b=0. Therefore H0(i,w) and R0(i,w) vanish modulo p. Primality forces one C_j(i,w) to vanish modulo p. Both that C_j and R0 are nonnegative and at most K<p, so they are literally zero. This proves the required row relation.

Conversely, choose bounded valid row witnesses. Ordinary CRT supplies encoded columns and index modulo each D_i. The selected valid branch gives H0=0 and the other residuals give R0=0, so the norm congruence holds. The falling-factorial product vanishes for every encoded column. Its factorial denominator divides K!, which is coprime to B, so cancellation proves the binomial divisibility. For N=0 the row obligation is vacuous and every congruence modulo B=1 holds.

The product B has a finite arithmetic expression. Put

Q=(1+(N+1)T)^N+2, L=TQ+1.

Then

B = (T^N N! choose(Q+N,N)) mod L.

The numerator is product_(j=1..N)(TQ+jT), which reduces modulo L to product_(j=1..N)(jT-1)=B. For N>=1, B<=(NT)^N<Q<L. For N=0, B=1,Q=3,L=3T+1>1. Therefore the remainder is exactly B in every case.

This alternative does not justify a sum of three arbitrary squares modulo p: for p=3, 1^2+1^2+1^2=0. It also cannot use arbitrary positive moduli: modulo 5, 1^2+2^2=0 is a nontrivial zero. The construction deliberately bounds the individual branch sums of squares and R0, and uses a binary norm only to separate their product from R0. A fully nested binary norm could instead separate every leaf, but is unnecessary here.

## A factorial base recovers multiplicities without coefficient heights

Let m be natural and M>=1. Suppose max(m-1,0)! divides M. For distinct labels 1<=j<k<=m, put g_j=1+jM. If d divides g_j and g_k, then d is coprime to M and divides (k-j)M, so d divides k-j. But 1<=k-j<=m-1, hence k-j divides max(m-1,0)! and therefore M. Thus d=1. The g_j are pairwise coprime and all exceed 1.

For any two finite multiplicity families a_j,b_j, equality of product_j g_j^(a_j) and product_j g_j^(b_j) implies a_j=b_j for every positive label. Choose a prime divisor of g_j. Pairwise coprimality makes its valuation zero in every other g_k; taking its valuation in the equality and cancelling its positive valuation in g_j proves the claim. The factors need not themselves be prime.

Truth label 0 has g_0=1 and is deliberately invisible, exactly as required by the Horn flow balance. For m=1 any positive M works, including M=1. For m=0, no positive label can occur on the rule side, whereas the target factor 1+M is greater than 1, so the target equality is impossible. M=0 must not be allowed: then every factor is 1 and no multiplicity information survives.

Consequently the obligation accumulator can use M=m! for m>=1 instead of a coefficient-height carrier. Telescoping gives the global product equality; pairwise coprimality recovers the Horn balance independently of the proof length N. Completeness first chooses the proof and m, then M=m!, then the obligation stream and its beta code. Reusing a later CRT factorial whose bound contains the initial accumulator M+1 is not valid: it would impose a circular and generally impossible size constraint.

A fixed positive M with no label-dependent restriction is unsound. The single rule (1,0)->M+2 has no derivation of target 1, but satisfies the one-row accumulator identity with initial state 1+M and final state 1, since 1+(M+2)M=(1+M)^2. For M=1 this is the collision 4=2*2 between labels 3 and two copies of label 1.

The native factorial carrier is not a variable-count improvement in this compiler. Against the rounded-radius positive-CRT comparison, it adds one factorial and one binomial graph, replaces one carrier power with five powers, and costs 200 natural variables. This is a proved alternative certificate, not a new minimum.

## Formal and experimental boundaries

All proofs use finite arithmetic induction, integer polynomial identities, prime factorization, and the Chinese remainder theorem, with the stated Pell graph as an existing dependency. They can be formalized in ZFC, so no soundness step assumes the arithmetic inputs are externally standard. In a nonstandard model, the finite sequences, primes, factorials, and inductions are interpreted internally in the same theorem. The fixed arithmetic DAG and its emitted polynomial are ordinary externally finite syntax.

Finite tests and exact sparse-polynomial replays verify implementation fidelity, not the all-input mathematical claims. The proof-calculus calibration to ZFC refutability remains the main direct packet's pinned calibration. The final conclusion is conditional only on those explicitly inherited arithmetic and calibration theorems, never on Con(ZFC).
