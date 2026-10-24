# Independent review: residue-separated root mergers

Reviewed against ProveIt snapshot cfbf118b4ad9b2c651fe96b571d9415261766328 and the ten archives currently in docs/incoming. This is an internal AI-assisted mathematical review, not a formal kernel proof or external peer review.

## 1. Primitive two-root merger

For integers a, delta, r with delta nonzero, put A=4a+1. Then

    exists tau,y in Z: tau^2=A and delta*y^2=r

is equivalent to

    exists t in Z:
      G=(delta*(t*(t+1)-a)-r)^2-A*delta*r=0.

In fact the equivalence preserves all a,delta,r coordinates. For completeness take t=(tau+2y-1)/2, integral because tau is odd. Conversely x=2t+1 is nonzero and the exact identity

    16G = [delta*(x^2+A)-4r]^2-4*A*x^2*delta^2

gives the rational root

    tau=[delta*(x^2+A)-4r]/[2*x*delta].

Its square is A, so tau is integral by rational-square-root integrality. Since A=1 modulo 4, tau is odd. Thus y=(x-tau)/2 is an integer and direct substitution gives delta*y^2=r. No positivity, separation inequality, or Pell descent is needed. This primitive form is smaller than the expanded quartic norm and contains no division in its definition.

## 2. Three-root residue separation

Let A,B,R be integers with A=B=1 modulo 4. Define

    a=A, b=4B, c=16R,
    F8(x;a,b,c)=((x^2-a-b-c)^2-4*(a*b+a*c+b*c))^2
                  -64*a*b*c*x^2.

If an integer x satisfies F8=0, then A,B,R are integer squares. Conversely, if A=tau^2, B=d^2, R=z^2, all signed sums tau+2d+4z are odd and give zeros. Therefore supplying x=2t+1 gives an exact existential merger of the three square conditions.

Proof: over the complex numbers F8 is the product over all eight signed sums of the three square roots. A zero therefore gives a rational signed sum of sqrt(A),2sqrt(B),4sqrt(R). Group its nonzero terms by their square classes in Q*/Q*2. Distinct square classes are linearly independent over Q, for example by averaging the corresponding characters of a finite multiquadratic Galois group. Thus the coefficients in every nontrivial class would have to sum to zero.

For terms in a fixed square class, write the radicands as d times integer squares, with signed squarefree d. Since A and B are odd, their squarefree parts and unscaled integer coefficients are odd. Their scaled coefficients consequently have 2-adic valuations 0 and 1. The coefficient belonging to 16R has valuation at least 2 whenever it shares either class; if it shares neither class it is the sole term of its class. A sum with a unique least 2-adic valuation cannot vanish. Thus no nontrivial class occurs. All three radicands are rational squares. As integers they are integer squares; removing the factors 4 and 16 shows B and R themselves are integer squares. Negative radicands and R=0 are covered: a nonzero negative square class cannot occur, and the zero term is already a square.

The argument does not assume positivity of A, B, or R. It also does not require R to be odd. The condition B=1 modulo 4 serves two purposes: it supplies an odd square coefficient in the second root, and makes its restored root suitable for a coordinate 2p+1.

## 3. Application to the auxiliary Pell equation

Use Q=I^2, delta=Q-1, r=Q*V^2-1 and R=delta*r. The third recovered square is z^2=delta*r. If Q is not 1, set y=z/delta in Q. Then

    Q*V^2-(Q-1)*y^2=1.

When Q>=4, the adjacent-coefficient Pell descent already supplied in package69 makes y integral. When Q=0 the equation is simply y^2=1 and integrality is immediate. Thus Q=I^2 and Q!=1 suffice; no preliminary claim Q>1 or c!=0 is necessary.

The retained ordinary strong row I^2=Delta*(f^2-1), together with the unconditional Delta>1, excludes Q=1 because an integer greater than 1 cannot divide 1. It does not by itself exclude Q=0, hence the explicit zero case above matters to proof order.

For the shared positivity guard put

    B=4*(G*Z-(s^2-G-Z+1)^2-1-p1^2-p2^2)+1.

Its odd recovered square root d restores p3=(d-1)/2 and the exact old equation

    G*Z-(s^2-G-Z+1)^2-1-p1^2-p2^2-p3*(p3+1)=0.

Completeness sends old roots tau,y,2p3+1 to

    x=tau+2*(2p3+1)+4*delta*y,
    t=(x-1)/2.

All other source coordinates are unchanged. This is an existential projection equivalence; it need not be injective on the merged root coordinates.

## 4. Necessary boundaries and negative controls

* If delta=0 is allowed without a separate source exclusion, the norm loses the auxiliary equation. For Q=1,V=2,A=B=1,x=3, the three-root norm is zero but Q*V^2-(Q-1)y^2=1 is impossible.
* If the second radicand lacks the odd residue condition, cancellation can reappear. A=1, B=-12, Q=4,V=0 gives R=-3, so the two scaled irrational roots are equal: 2sqrt(B)=4sqrt(R). Their cancellation leaves x=1, a norm zero although neither B nor R is a square.
* General sums of three radicals cannot be decoded just because their radicands are distinct. The present proof uses the full residue/valuation separation, not merely inequality of radicands.

## 5. Prior-art scope

The inspected incoming collection already contains two-root mergers scaling the auxiliary root by I and proving radicand inequality modulo I^2; it also contains four-root separation and small-rational-residue methods. These particular odd-carrier/2-adic constructions were not found in the inspected primary proofs. This is a repository-relative observation, not a literature-wide priority claim.

The current active fixed-root-elimination candidate already contains fourteen-positive-variable 73/342 and 75/293 operation/degree tradeoffs. Porting the universal local norm-unit guard to those blank-input sources would duplicate that active work.

## 6. Audit of the supplied literal packets

`independent_graph_audit.py` parses the literal polynomial expressions with a restricted AST; it imports no builder. The copied parent file and coefficient binding were separately compared byte for byte with the originals extracted from the pinned incoming archive. Its parent SHA-256 is `0ec2ef40f57d6d2b1a18a27e11dda1a06faa67fb97fe66b23576ab0680298698`.

All six compressed coefficient payloads pass their compressed and raw byte hashes, exact bit counts, minimal encoding checks, and total size 615883 bytes. The beta and two determinant scales also match their exact power-of-two recipes. The other three native integers remain the unchanged source tuple; byte authentication is not a new semantic proof of that compiler.

All retained parent polynomial abbreviations and surviving residual rows match literally. New variables are exactly the intended projections: remove tau,y_gap and add t_parity; the fifteen-variable construction also removes pair_pos3. Exact symbolic identities verify the centered shift, parent first-root and auxiliary restorations, and the actual three-root primitive polynomial (the full conjugate norm divided by 256).

Independent safe multivariate degree propagation and dense univariate arithmetic modulo 1000000007, using the authentic coefficient bytes reduced modulo that prime, confirm every recorded exact degree. In particular the intended deliverables are:

| Literal | Variables | Residual degrees | Exact polynomial degree |
| --- | ---: | --- | ---: |
| centered16_sos | 16 | 14,14,44,60 | 120 |
| parity15_unit_product | 15 | 14,14,176 | 204 |

The actual nonzero top coefficients on the recorded line are 738307154 and 85468886, respectively. They are exact attainment witnesses, not Monte Carlo degree estimates. The finalizers are sound over unrestricted integers: a sum of squares vanishes exactly when every residual vanishes; in a product of factors 1+4r equal to 1, each integer factor is a unit and its residue excludes -1.

The root-merger and graph auditors both pass normally and under Python `-O`. Their receipts distinguish exact symbolic identities and exact degree certificates from finite diagnostics. The latter include explicit counterexamples to dropping either a needed residue or the nonzero denominator condition.
