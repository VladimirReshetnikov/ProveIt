# Exclude direct-Q cancellation at the ten-gate auxiliary cut

For the independent-variable outputs

    V=cTf−c−Rf²,  Q=Delta²*i²*c⁴,  S=Delta*f²−Q,

the declared paid interface requires at least ten arithmetic gates, without protecting Q's construction or S's final subtraction. The existing7M+3A schedule attains ten. This is a local producer-cut theorem: it is not an optimality theorem for the whole universal84 polynomial, different paid ports, coordinate changes, or altered outputs.

The new step excludes the last direct-Q cancellation case. Its central structural lemma permits arbitrary extra paid monomials and uses no multiplication-count claim. The proof then returns to the original paid interface before making any product-count contradiction.

## 1. Exact model and inherited reduction

Let R0 be the rational polynomial ring in the independent variables Delta,c,i,f,T,R. Original paid ports are these six variables and precisely c² and Delta*c². Constants and scalar multiples may be free. A binary scalar-weighted sum costs one addition; multiplication of two nonconstant expressions costs one multiplication. Arbitrary linear combinations are free only in the explicitly identified multiplication-only contradictions.

The pinned frontier and proper-pivot proofs reduce any hypothetical circuit of at most nine gates to exactly5M+4A. Exactly one addition has a monomial value; it genuinely cancels terms and produces Q up to nonzero rational scalar. Normalize that output to U=Q. The other three addition outputs are nonmonomial. The pinned mixed-cut theorem gives a four-multiplication lower bound for V and W=Delta*f² from the original paid ports with arbitrary linear combinations free.

The no-i-monomial-products successor excludes every counted multiplication output that is a nonzero monomial containing i. It also records the following specialization criterion, restated in Section4 below. No five-product lower bound for V,W is assumed.

Put

    P=f²−Delta*i²*c⁴, so S=Delta*P.

P is primitive and linear in Delta, hence irreducible in R0. V is primitive and linear in T: its coefficient cf and its constant term −c−Rf² are coprime. Thus V is irreducible as well. The two irreducibles are not associated. V has three noncollinear exponent vectors, with distinct T/R multidegrees (1,0),(0,0),(0,1).

## 2. Structural facts with arbitrary paid monomials

In this section, supply any additional finite set of monomials for free, including Q if desired. Inputs still contain no nonmonomial polynomial. There is no restriction on the number or depth of multiplications. Scalar aliases do not count as new additions.

Between addition gates, each wire is a monomial times a product of nonnegative powers of earlier addition outputs. This follows immediately by induction through multiplication gates. A nonmonomial irreducible factor cannot disappear under multiplication in R0.

### Two additions producing V

One addition can produce only a monomial times a power of a binomial, whose support is collinear. It cannot produce V. With two additions, call their outputs g,h. Irreducibility and the absence of a monomial factor force V to be a scalar multiple of h itself. Write

    V=m*g^r+n*g^s,

where m,n are nonzero scalar monomials and r,s are nonnegative integers. If both exponents are positive, g divides V, impossible because the first addition g is a binomial and cannot be associated to V. If both are zero, the result has at most two terms. Therefore, after swapping operands,

    V=m*g^k+n,  k≥1.

For k≥2, the binomial power has k+1 distinct collinear monomials. Adding n either introduces another monomial, changes one coefficient, or cancels at most one term. A three-term result for k=2 or3 remains collinear; for larger k too many terms remain. Hence k=1. The first binomial groups exactly two monomials of V, and its outside monomial divides their common monomial divisor. In particular g and h are independent of Delta and i. This conclusion holds regardless of which additional monomials were supplied.

V and S cannot both be computed with at most two additions. V would use the second addition and its first binomial would be i-free by the preceding argument. Neither that binomial nor V contains the irreducible factor P. Products of those outputs and monomial inputs therefore cannot produce S. Consequently at least three additions are required, even with arbitrary paid monomials.

### Three-addition separation lemma

**Lemma.** Suppose a circuit whose inputs are monomials computes V and S using exactly three additions, and all three addition outputs are nonmonomial. Then two addition outputs are i-free values in a two-addition construction of V. The third is a nonzero scalar multiple of P or Delta*P.

Write the three addition outputs in chronological order as g,h,k. Irreducibility forces V itself, up to scalar, to be one of these addition outputs. It cannot be g. To obtain S, at least one addition output on a product path to S must contain its unique nonmonomial irreducible factor P. That output divides S, so its value is a scalar P or Delta*P. It is different from the addition giving V. These facts leave precisely the placements below.

**Case A: h is V and k supplies S's core.** The two-addition result makes g,h independent of Delta and i. Each operand in k is a monomial times powers of g,h, and thus has one fixed (Delta,i) multidegree. P and Delta*P each have two distinct such multidegrees. The operands must occupy different multidegrees; cancellation between them cannot remove unwanted terms within either multidegree. Each operand must therefore be a monomial. In particular no nonmonomial factor g or h is used in this last binomial construction. The asserted separation holds.

**Case B: g supplies S's core and k is V.** Reduce modulo P and invert c and i, so that

    Delta=f²/(i²c⁴).

Every paid monomial, including an extra paid Q, becomes a scalar Laurent monomial. V is unchanged and still has three noncollinear terms. The first addition g becomes zero. Write h=m*g^r+n*g^s. If either exponent is positive, h reduces to zero or one Laurent monomial. The final addition k would then reduce to at most two Laurent monomials, a contradiction. Therefore r=s=0: h is a binomial of monomials and does not use g in its expression.

If either operand of k contains a positive power of g, that operand vanishes in the quotient. The sole remaining operand is a Laurent monomial times a power of the Laurent binomial h, with collinear support; it cannot equal V. Thus neither operand uses g. The actual, pre-quotient construction of V uses only h and its final addition, so the two-addition result makes both values i-free. This proves separation in this case. The quotient is used to exclude dependencies, not to replace the original paid interface in a multiplication bound.

**Case C: h supplies S's core and k is V.** Write h=m*g^r+n*g^s.

If both exponents are positive, the nonmonomial g divides h. Since h has only the nonmonomial irreducible factor P, g vanishes modulo P. Then both g,h vanish there and k has at most two Laurent monomials, contradicting V.

If both exponents are zero, h is an independent binomial of monomials. In the quotient by P, any operand of k using h vanishes; the remaining operand has collinear support as a monomial times a power of the first binomial g. Thus neither operand uses h. V is formed by g and k alone, and the two-addition result again gives the stated i-free values. This includes direct formation of S as W−Q when Q is supplied.

It remains that exactly one exponent is positive: h=m*g^r+n with r≥1. The two monomials of g are distinct. If they have the same nonzero T/R multidegree, all r+1 terms of m*g^r have nonzero T/R multidegree and a single additional monomial cannot cancel them all. If their T/R multidegrees differ, those r+1 terms have distinct T/R multidegrees; at most one is (0,0), since all original monomial exponents are nonnegative. The extra monomial can cancel at most one other term. For r≥2 at least one forbidden multidegree remains. For r=1 a cancellation removing the unwanted multidegree leaves only one monomial, whereas h has two surviving monomials. The same argument applies if m adds a positive T/R multidegree. Hence g must be independent of T and R.

Now both g and h are T/R-free. Each operand of k, a monomial times powers of g,h, has one T/R multidegree. Their sum has at most two, while V has three. This last subcase is impossible.

Cases A–C exhaust the placements and prove the lemma. No count of multiplications was used. In particular, none of the former seven-product conclusions is being transferred to an enlarged paid interface.

## 3. Apply the lemma without changing original gate values

Return to the hypothetical original5M+4A circuit. Delete the addition U=Q and make its polynomial Q an extra paid monomial input in a separate relaxed circuit. Redirect exactly its former uses. Every surviving gate still computes the same polynomial as before. The relaxed circuit has the other three nonmonomial additions and computes V,S; it has at least three additions by Section2, so none of those three can be discarded as irrelevant to both outputs.

The separation lemma therefore identifies their polynomial values: two are i-free V-grouping values, and the remaining one is a scalar P or Delta*P. This is a conclusion about the values of those same three gates in the original circuit.

From this point onward, restore the original circuit and original paid ports. Q is no longer a free input; it exists only when U is computed. The extra-paid-Q relaxation is used solely to identify addition values. It is never used in the following multiplication-count arguments or in the final chronological argument.

## 4. No multiplication output can vanish at i=0

Let P0 be the rational scalar span of the original paid monomials

    1, Delta, c, i, f, T, R, c², Delta*c².

Before U, write Q=A+sum beta_j*g_j, where A is in P0 and the g_j are preceding multiplication outputs. The coefficients are rational scalars. Since Q is outside P0, some coefficient is nonzero.

If a multiplication output g occurring after U vanishes at i=0, delete that product there. The latest nonzero product coefficient in Q's specialized relation deletes a second, earlier multiplication. This leaves at most three products for V,W from the original specialized paid ports, contradicting the inherited four-product bound.

If g precedes U, vanishes at i=0, and Q is outside `P0+span_ℚ{g}`, the same relation has a nonzero coefficient on a product other than g. Delete g first, then eliminate the latest other product coefficient. The remaining relation uses only earlier surviving products, whether the second product was originally before or after g. This gives the same contradiction. These are the exact scalar-span specialization steps proved in the pinned no-i successor.

Consequently any surviving nonzero product output vanishing at i=0 must precede U and satisfy

    Q in P0+span_ℚ{g}.

Because Q is outside P0, this gives g=alpha*Q+A0 for some nonzero rational alpha and A0 in P0. Specialization forces A0 to vanish at i=0. The intersection of P0 with the ideal generated by i is exactly the scalar span of i, so

    g=alpha*Q+beta*i.

If beta=0, g is an earlier scalar alias of Q. Redirecting U to g removes U's addition and yields the already excluded circuit with at most5M+3A. Thus beta is nonzero. We have forced

    g=i*h,  h=beta+alpha*Delta²*c⁴*i,  alpha*beta != 0.       (4)

h is irreducible: it is primitive and linear in i with nonzero constant rational term. It divides g and is not a factor of any monomial.

Every irreducible factor of a computed polynomial must originate in a paid input or an addition output in its ancestor cone, because multiplication only combines existing factors. Apply this elementary factor-origin observation to h. Original paid inputs are monomials. The fourth addition U is Q, also a monomial. The other three addition values have just been classified: two are i-free, so cannot contain the positive-i-degree factor h; the third is P or Delta*P up to scalar. h does not divide Delta, and cannot divide P, which is monic in f while h is independent of f. Thus no allowed origin exists for h. Equation(4) is impossible.

We conclude that **no counted multiplication output in the original circuit is a nonzero polynomial vanishing at i=0**, not merely that none is a monomial. An identically zero product is redundant in the normalized nonconstant-multiplication model and may be removed; it cannot rescue a five-product circuit.

## 5. The original circuit cannot first acquire quadratic i-dependence

This final argument uses the original circuit, in which Q is not paid. Original inputs have i-degree0, except the supplied i itself, which has i-degree1. The classified original addition outputs are i-free, or have i-degree2: the latter are U=Q and the S-core addition P or Delta*P.

Since the circuit outputs Q, some gate first attains i-degree at least2. It cannot be an addition of two earlier expressions of i-degree at most1. Hence this first gate is a multiplication. Every addition preceding it must be i-free, because either of the two possible i-dependent addition values would already have i-degree2.

There cannot be an earlier i-dependent counted multiplication. If there were, choose the first one. Its previous multiplication outputs and addition outputs would be i-free; the only available i-dependent operands would be scalar aliases of the original input i. Its product would therefore be divisible by i, contradicting Section4. This reasoning charges all actual computations and uses no arbitrary free linear combinations.

Thus, before the first gate of i-degree at least2, the only i-dependent values are scalar aliases of the original i. The first degree-at-least2 product must use such an operand and is again divisible by i. Section4 excludes it. This contradiction rules out the hypothetical5M+4A circuit, and hence every at-most-nine-gate circuit at the declared paid interface.

## 6. Attainment and boundaries

The existing mixed schedule is

    f2=f*f;
    cT=c*T; Rf=R*f; inner=cT−Rf; V=f*inner−c;
    root=i*(Delta*c²); Q=root*root;
    W=Delta*f2; S=W−Q.

It uses7M+3A=10, with Delta*c² already paid. Therefore ten is the exact local cost in the stated relaxation and in the corresponding actual binary arithmetic model, where this schedule is available. Its existing complete84 source and degree are unchanged.

The lower bound does not cover additional computed paid ports, different output cuts, zero-set-only replacements, valid-compiler relations between the independent variables, positive coordinate transformations, or changes elsewhere in the full source. It supplies no universal84 optimality claim. This successor contains no new executable helper, full-source array, finite search, numerical compiler zero or historical replay.

## 7. Inert proof dependencies

The new structural lemma and its use are written out above. The reduction to the remaining5M+4A direct-Q case and the original-paid-port V,W four-product lower bound remain the following authenticated inherited results:

| Proof | SHA-256 |
|---|---|
| [Mixed auxiliary cut](complete84_auxiliary_mixed_cut.md) | `b16bcf8b4013345d25a5d2bbb0598ae2caaaeaa31a529e00af7ea4647d78d7f2` |
| [Nine-gate frontier](complete84_auxiliary_nine_gate_frontier.md) | `ae4925e8bf330fcd1a5d1c0f529e982f0c5df018690a7ef81e4ca27cc5ad4cd2` |
| [Proper-pivot exclusion](complete84_auxiliary_proper_pivot_exclusion.md) | `027c1945025f4bf1e6b9d585ba2befe1af697239787928226b0fd10f868fdf20` |
| [No i-containing monomial products](complete84_auxiliary_no_i_monomial_products.md) | `4d98a15d3eb9ec8beb989149d0b93d5f44fd3094fe31994b8c850891ff0dae59` |

These files were read as inert mathematical text. No frozen predecessor Python was run or imported and no repository or predecessor file was edited.
