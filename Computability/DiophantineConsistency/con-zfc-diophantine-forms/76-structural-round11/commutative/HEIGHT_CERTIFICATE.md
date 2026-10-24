# Finite coefficient height replaces pairwise coprimality

## The arithmetic lemma

Let N be a natural number and let p_i,q_i,c_i be nonnegative integers, i<N. Write

 A(X)=product_i (1+c_i X),
 B(X)=(1+X) product_i (1+p_i X)(1+q_i X),
 R=2 product_i ((1+p_i)(1+q_i)+c_i).

For every integer M>R,

 A(M)=B(M) if and only if A(X)=B(X) in Z[X].

Proof. Both A and B have nonnegative coefficients. Their coefficient sums are A(1) and B(1). The factor D_i=(1+p_i)(1+q_i)+c_i is at least both 1+c_i and (1+p_i)(1+q_i). Therefore A(1)<=R/2 and B(1)<=R. Every coefficient of A-B has absolute value at most R, hence strictly less than M. If A-B were nonzero, let k be its least nonzero coefficient index. The equality (A-B)(M)=0 divided by M^k would imply M divides its nonzero coefficient a_k, impossible when 0<|a_k|<M. The converse is evaluation.

This is a bounded-height integer-root argument, not a probabilistic polynomial identity test and not an assertion that distinct labels yield coprime evaluated factors. In particular, M need not be divisible by any label difference, factorial, or interval of integers.

## Exact recovery of label multiplicities

For positive j, the linear polynomial 1+jX has the unique rational root -1/j. The factors for distinct positive labels have distinct roots. Equality A=B therefore implies, for every positive j,

 #{i:c_i=j} = [j=1]+#{i:p_i=j}+#{i:q_i=j}.

Zero labels contribute factors1 and disappear. One can prove the multiplicity statement by repeatedly evaluating at -1/j and dividing by the factor; no irreducibility theorem for high-degree polynomials is needed.

Conversely, these balances imply the polynomial identity. Composing with the round10 single-conclusion Horn-flow theorem gives derivability of target1. For the same calibrated numerical C222 calculus, existence is therefore equivalent in ZFC to a ZFC refutation. No soundness assumption about ZFC or Con(ZFC) is used in this equivalence.

## Two-register certificate

Take natural numbers S_0,...,S_N and R_0,...,R_N and M>0, satisfying

 S_0=M+1, S_N=1, R_0=2, M=R_N+1,
 S_(i+1)(1+c_i M)=S_i(1+p_i M)(1+q_i M),
 R_(i+1)=R_i((1+p_i)(1+q_i)+c_i),
 Horn(p_i,q_i,c_i).

Every factor is positive. Starting from S_0>0, the first update forces all S_i>0, so multiplying and cancelling internal S_i proves A(M)=B(M). The second update gives the exact height product R_N above. Consequently M>R_N and the arithmetic lemma yields the multiset balances and a derivation of1.

Conversely, choose a finite proof tree of1 and list its expansions in any order in which each selected node is an open obligation. This choice is needed only for constructing witnesses, not for soundness. Fix the list, compute R_N, choose M=R_N+1, and let S_i be the product of 1+jM over currently open positive-labelled obligations. Expanding a node labelled c_i replaces its factor by the two premise factors, giving the first update. The initial and final products are M+1 and1. The R_i are the prefix height products. All variables are natural. N=0 cannot satisfy the endpoints, since R_N=2 implies M=3 and S_0=4!=1.

The order of existential choices is important: first the finite rule list, then R_N, then M, then the obligation accumulators. No bound on an expression that already depends on M is used to choose M. This avoids the circular scale error that would arise from bounding M by a code containing its own accumulator.

## Literal local polynomial

Let H(p,q,c;w_1,...,w_17) be the inherited nonnegative degree50 branch-shared Horn polynomial. It is a product of twelve sums of squares, and has zeros exactly at the padded C222 Horn rules. Put M=M0+1 and define

 E=S'(1+cM)-S(1+pM)(1+qM),
 F=R'-R((1+p)(1+q)+c),
 L=H+E^2+F^2.

Over naturals, L=0 is precisely the Horn condition and the two updates. The local witnesses are p,q,c and the seventeen Horn witnesses:20 in total. Its exposed parameters are S,S',R,R',M0. E has degree5, F degree3, and H has degree50, so L has exact degree50. Exactness follows because H is nonzero of degree50, whereas the added squares have degree at most10.

Compared with round10, the three witnesses enforcing p,q,c<=m are gone, the parameter m is gone, and the entire interval-divisibility bounded-universal block is gone. An extra accumulator and its beta-code are introduced. Both old and new global schemas have five outer natural parameters. This is a source-level improvement; the full compiled witness count has not been measured and no global variable reduction is asserted.

## One bounded-universal block

For natural x,y,i let beta(x,y,i)=x mod(1+(i+1)y). Use outer parameters N,x,z,y,M0. The fixed quantified source is

 beta(x,y,0)=M0+2,
 beta(x,y,N)=1,
 beta(z,y,0)=2,
 beta(z,y,N)=M0,
 forall i<N, exists w in N^20:
 L(beta(x,y,i),beta(x,y,i+1),beta(z,y,i),beta(z,y,i+1),M0;w)=0.

Here M=M0+1=R_N+1. Simultaneous finite beta encoding exists: choose y larger than both finite sequences and divisible by N!, so the moduli 1+(i+1)y are pairwise coprime; the Chinese remainder theorem gives independent x and z with the SAME y. The common multiple here is used solely in the existential completeness proof of ordinary beta encoding, not as a separately checked predicate or a second bounded block. It is unrelated to M.

All mod operations are supplied through the pinned remainder-graph representation. The single bounded-universal block is eliminated by the pinned constructive bounded-forall representation, and the remaining existential polynomial is passed to the quartic compiler. The supplied Lean file specifies these operations but has not been elaborated. The resulting ordinary polynomial has not been materialized or counted. This module is not presented as a completed smaller Diophantine equation; the completed new object is the literal local polynomial and the fully proved global source equivalence.

## Necessary controls

Without M>R, numeric product collisions need not preserve labels. At M=1, 1+3M=(1+M)^2, so label3 can mimic two label1 occurrences. A Horn system containing only the rule with premise1 and conclusion3 has no derivation of1, yet N=1, p=1, q=0, c=3, S_0=2, S_1=1 gives an unchecked accumulator certificate at M=1. Its height register ends at10, so the new bound rejects it. The coefficient bound, not mere largeness or primality of M, is the proved safeguard.

Without the Horn condition, the arithmetic certificate does not certify any logic. Without single-conclusion rules, flow balance is unsound. Without positivity of factors and S_0, internal zeros could defeat telescoping. These conditions are retained.

## Degree reduction by nonnegative selectors

The twelve Horn branch SOS polynomials have degrees2 (truth), ten degrees4, and one degree8 (bundle). Number them in inherited JSON order h0,...,h11, with h9 the bundle. Products of nonnegative branch polynomials are nonnegative.

A single new selector r gives a21-local-witness degree20 variant. Partition into groups [0,1,2,3], [9,4], [5,6,7], [8,10,11], whose product degrees are14,12,12,12. Let G_i be each group product, g(r)=product_{i=0}^3(r-i), and l_i(r)=product_{j!=i}(r-j). Replace H by

 g(r)^2 + sum_i G_i l_i(r)^2.

All terms are nonnegative. A zero forces r in{0,1,2,3}; then only the selected summand can survive, and l_r(r)!=0. Thus existence of r is equivalent to at least one original h_i vanishing. The exact degree is20 because the unique degree14 group contributes degree20 and the other summands have degree at most18.

The recommended degree-oriented variant instead uses three Boolean selectors b0,b1,b2. Use eight groups [9],[1,2],[3,4],[5,6],[7,8],[10,11],[0],[]; the empty group has value1. For0<=i<8 let chi_i(b)=product_k (b_k if bit_k(i)=1 else1-b_k). Replace H by

 sum_k [b_k(b_k-1)]^2 + sum_i G_i chi_i(b)^2.

Every term is nonnegative at all integer selector values. A zero forces all three bits to be0 or1. Exactly one chi_i then equals1, with all others0, so the selected G_i must vanish. The unused empty group cannot be selected. Conversely a vanishing original branch permits selecting its group. The six degree8 group products multiplied by squared degree3 indicators give exact total degree14. Their degree14 homogeneous parts cannot cancel: each is the common nonnegative monomial b0^2 b1^2 b2^2 times the nonnegative, nonzero leading homogeneous form of a product of SOS polynomials. Thus the local E^2 and F^2 terms of degrees10 and6 do not change degree14.

This yields23 local natural witnesses, exactly the prior affine source count, while reducing its local degree50 to14 and removing its second bounded-universal block. The five exposed state/parameter coordinates are not included. This is not a final consistency-equation variable or degree claim. All three variants have literal JSON, matching uncompiled Lean constructors, and independently authored finite checks.

## Optional four-parameter source form

The outer M0 coordinate can be eliminated exactly. Set h=beta(z,y,N), substitute h for M0 everywhere, and retain only the outer natural parameters N,x,z,y. The endpoint equations become beta(x,y,0)=h+2, beta(x,y,N)=1, and beta(z,y,0)=2; the old equation beta(z,y,N)=M0 is now an identity. In the bounded block, use L(beta(x,y,i),beta(x,y,i+1),beta(z,y,i),beta(z,y,i+1),h;w)=0. The four-parameter source is equivalent to the five-parameter source: restore the uniquely determined M0=h in one direction, and use the old endpoint equality in the other.

The local polynomial and its20/21/23 local witnesses do not change. The graph composition for everyStep now requires a fifth remainder graph for h, whereas the five-parameter form passes M0 as a coordinate. Thus four outer parameters do NOT imply fewer final Diophantine variables or a smaller compiled circuit. This is a source-level tradeoff only, not a counted compiler improvement; no additional generated constructor is supplied.
