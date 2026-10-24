# Independent review of the two new certificate interfaces

Status: accepted as conditional mathematical interfaces, not as new ordinary-polynomial consistency endpoints. No Lean/Rocq compilation was performed. The reviewer read the theorem texts, their TeX counterparts, the inherited directed-signal language proof and the inherited odd-prime controller argument. The independent checker imports neither author checker nor builder. Finite computations below supplement, and do not establish, the universal arguments.

## 1. Inert-prime CRT closure

The stated equivalence is valid for n >= 1, m >= 1, natural external parameters and natural certificate coordinates U,A_j,c. Use the usual convention binom(A,k)=0 for 0 <= A < k. This convention should be made explicit when importing a graph representation: a partial binomial graph restricted to A >= k would need enlarged CRT representatives in completeness and a corresponding explicit domain statement.

The decisive soundness points all hold:

1. H = e(n,U,...,U;x)+f(n,U,...,U;x)+n+U+1 strictly exceeds the absolute value of every local residual for i<n and coordinates <=U. Nonnegative coefficients and natural parameters are essential to that monotonicity argument.
2. A common divisor of 4T(i+1)-1 and 4T(j+1)-1 divides j-i, since it is coprime to 4T. It consequently divides H!, and therefore is one. No primality claim about the composite moduli is needed.
3. Every prime factor exceeds H. Each modulus is positive and 3 mod 4, so at least one of its prime factors is 3 mod 4. A prime with that property is chosen separately for each index, then used simultaneously for all leaves.
4. The nested binary norm, unlike a flat sum of three or more squares, forces every leaf to vanish over that field. The index leaf recovers c=i modulo the prime. The binomial leaf multiplied by (U+1)! recovers some coordinate in [0,U]. Polynomial congruence and the strict absolute bound then recover exact equality.
5. Completeness works modulo the full composite moduli: their coprimality with (U+1)! makes the binomial denominator invertible. CRT supplies natural representatives; no appeal to a field for this direction is required.
6. The product identity is exact, not a heuristic remainder: (4T)^n n! binom(Q+n,n) is congruent to the positive product, which is strictly less than Q and hence the remainder modulus. The restriction n>=1 avoids the ambiguous 0^0 boundary. H>=2, so all moduli are positive.

The graph expansion must preserve domains, strict bounds, DAG sharing and every residual. Its unexpanded factorial/binomial/power language is not itself an ordinary Diophantine equation. Interface savings of m-1 bounds and m+1 congruence tests are credible comparison counts, not a final variable saving. The five-versus-eighty-nine local-coordinate distinction likewise does not prove eighty-four fewer variables after final flattening.

## 2. Fixed input and affine absorption

The radix boundary lemma is valid for B>=2, m>=1, 0<=D<B^m with a nonzero top digit, and a recovered nonnegative native C<B^N. From C=D+B^m V and V integral one obtains V>=0, the exact low-digit prefix, and N>=m. Conversely the prefix supplies the integral quotient. Thus a too-short cyclic word cannot evade the boundary condition.

The replacement alpha=q-F-D-B^m V is an affine substitution, since B,m,D,beta are fixed and q=beta J+1. It preserves variable count, residual count and upper bounds on degree in an all-integer lifted system. It is bijective onto the boundary-constrained old solutions, provided alpha was an independent coordinate and *every* old occurrence, including every positivity guard, is replaced. The current Markdown explicitly says unrestricted alpha and both texts retain the guards. The reviewed 42-integer architecture has explicit positive-product guards; it does not rely solely on alpha's quantifier domain.

Important restriction: this is not automatically a zero-cost substitution in a positive-coordinate polynomial. Replacing positive alpha by positive V does not imply reconstructed alpha>0. The independent checker contains a concrete counterexample to that invalid generalization. The optional V+1 convention only addresses positivity of the new quotient, not loss of the old alpha restriction. For all-integer lifted sources with substituted guards, no such gap remains.

## 3. Constant-size initializer and shifted controller

The initializer matching argument is valid. To the left of the fixed first-symbol tile only L blanks or a seam can occur; to the right of the fixed delimiter only R blanks or a seam can occur. Horizontal periodicity cannot close a phase cycle across L->D->R without seams. Between the nearest seams the fixed block determines exactly one head, the selected input, and blank margins. The inherited directed-signal argument then enforces a genuine computation until a finish/reset row; temporal periodicity supplies a subsequent reset. Conversely finite halting computations permit arbitrarily large independent margins and absorbing-halt padding. Empty input is correctly represented by one blank symbol.

The tile-count formula is consistent with the recipe: ns working tiles, s(|SR|+|SL|) receiving tiles, 4s ordinary/halt/finish tiles, 2s+3 initializer tiles, two resets, nine seams and one forbidden tile. Since |SR|,|SL|<=n+1, n=s=5 gives at most 130 tiles. This is conditional on a total five-working-state/five-symbol machine with one additional halt state. It is not a supplied universal machine or ZFC-refuter instance.

The translated Boolean controller proof is valid under its explicit hypotheses: lambda is an odd prime, T is a power of lambda, T>C0=d lambda, B is a unit modulo C0 T, and the complete stated orbit identity holds. Subtracting either zero or B ensures a nonzero residue modulo lambda; its residue b modulo C0 is nonzero and invertible modulo T. Summing b consecutive additive orbit coordinates produces b+C0[b z0+b(b-1)/2], which gives the claimed target. Translation by B^a is invertible. The extra position a+1 is distinct from the orbit because lambda-1>1. The assumption lambda does not divide B-1 is stronger than this subset-coverage subargument needs, but is harmless and may be needed by other native unit conditions.

For sufficiently large independently padded width w and height h, the available terminal gap T+k-a exceeds w+1, so the positive translates used in the native proof do not wrap. Taking a>=m freezes the prescribed prefix. The inherited rank-effect unit and canonical slack/parity conclusions still require verification for the regenerated coefficient tuple. The generic shifted subset lemma cannot replace that new arithmetic-controller certificate.

## 4. Remaining obligations and independent diagnostics

No fatal proof gap was found in the two stated conditional interface theorems. The principal unresolved endpoint obligations are honestly identified: materialize a small universal transition table with an exact constructive input compiler, provide the actual finite refuter input, regenerate all four coefficient ports coherently, verify the new arithmetic controller and carry conditions, and measure the resulting input-dependent coefficient bitlength. For the CRT route, implement exact graph expansion and compare the resulting polynomial frontier. Neither route establishes a new small Con(ZFC) equation at this stage.

The independent checker verifies 36 exact product cases, 2,030 anisotropy pairs, binomial range recovery over six inert primes, one composite CRT fixture, 50,652 boundary cases, and nine subset-coverage cases using a subset dynamic program rather than the author's constructive controller implementation. Negative controls reject the flat three-square norm and the loss of a positive alpha domain. These are regression diagnostics, not proofs or an endpoint kernel certificate.

Reproduce: python review/interfaces/check_independent.py from the wave10 package root. SHA256SUMS records the reviewed source snapshots and independent artifacts, so later source edits require re-review.
