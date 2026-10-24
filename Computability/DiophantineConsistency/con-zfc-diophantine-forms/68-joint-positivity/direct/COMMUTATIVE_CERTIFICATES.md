# Commutative refutation certificates

## Status

The theorem below is a proved mathematical replacement for ordered proof traces. It is not, by itself, a fixed ordinary Diophantine equation: the finite support, coordinate equality and variable powers in the corollaries must still be eliminated. No final variable count or compiler claim is made.

## Single-conclusion flow theorem

Let F be any set and R any set of rules. A rule r has a finite multiset P(r) of premises and exactly one conclusion c(r). A rule with an empty premise multiset is an axiom. Let D be the least subset of F closed under all these rules. For f in F write e_f for its unit vector in the free abelian group Z^(F), and define

    v(r) = e_c(r) - sum_{p in P(r)} e_p.

For a target t, the following conditions are equivalent:

1. t belongs to D.
2. There are finitely supported nonnegative integers n(r) such that sum_r n(r) v(r) = e_t.
3. There are finitely supported nonnegative rational numbers q(r) such that sum_r q(r) v(r) >= e_t coordinatewise.

The inequality includes all coordinates, not only the target coordinate. Repeated premises are counted with multiplicity.

### Proof

(1 implies 2.) Unroll a finite derivation to a tree. Give each rule instance its number of occurrences. Every non-root node contributes once positively as a conclusion and once negatively as a premise of its parent. Only the root survives. Axioms contribute positively and have no negative premises.

(2 implies 3.) Immediate.

(3 implies 1.) Suppose t is not in D. Sum the finitely many coordinates in the support of the certificate that lie outside D. For every rule r, if c(r) is outside D then at least one of its premises is outside D, because D is closed. Hence its contribution to this sum is at most zero. If c(r) is inside D, its contribution is minus the number of outside premises, also at most zero. Nonnegative q(r) preserve this inequality. The asserted coordinatewise lower bound instead forces the sum to be at least one, since t is outside D. Contradiction.

This is a proof in ZFC using separation only over a finite support; no model of ZFC or assumption of Con(ZFC) is used. More constructively, for a given finite support of rules, form its finite closure from its zero-premise rules. If the target were outside that closure the same argument would contradict the certificate. Saturating this finite closure supplies an actual finite proof DAG.

## What removes the danger of circular proofs?

The single-conclusion hypothesis is essential. With a single rule having premise a and TWO conclusions a,t, the flow vector is e_t, although neither a nor t is derivable from no axioms. The theorem does not extend to arbitrary Petri nets. Multiple premises, repeated premises, self-loops, and cycles are harmless when there is exactly one conclusion.

Nonnegative coefficients are also essential. In the system having only the rule with premise t and conclusion a, the signed combination -v(r)=e_t-e_a is not a proof of t. More strongly, add the axiom a: its vector plus -v(r) equals e_t, despite t remaining underivable.

## Application to the numerical C222 calculus

Take F=N, include an empty-premise rule for every allowed axiom instance and for truth code 0, the modus-ponens rule with premises a,I(a,b) and conclusion b, and the generalization rule with premise b and conclusion A(a,b). Choose t=1. The pinned C222-to-ZF and constructible-choice bridges from round 9 identify t in D with a finite ZFC refutation. Consequently ZFC proves:

    Con(ZFC) iff there is no finite nonnegative commutative flow certificate for target 1.

This drops the entire stack, instruction order, endpoints, and proof ranks. Axioms and inferences remain exactly those of the calibrated source. It does not require that every natural number be a decodable formula.

## Carry-free arithmetic specialization

For a proposed finite certificate, define signed balances h_j by

    sum_r n(r) v(r) - e_t = sum_j h_j e_j,

and let L = 1 + sum_r n(r)(1 + |P(r)|). Then |h_j| <= L. For any natural base B > L,

    sum_j h_j B^j = 0 iff every h_j = 0.

Proof: if k is the least index with h_k nonzero, division by B^k and reduction modulo B show B divides h_k, impossible when 0 < |h_k| < B. Thus the exact integer equation

    sum_r n(r) [B^c(r) - sum_{p in P(r)} B^p] = B^t

with B>L is equivalent to the flow identity. This is an exponential finite-sum formulation, NOT yet an ordinary fixed polynomial. Both the variable powers and the variable-length sums are genuine remaining compilation obligations.

A second exact encoding assigns each formula j a distinct prime p_j and writes

    product_r p_c(r)^n(r) = p_t * product_r product_{p in P(r)} p_p^n(r).

Unique factorization proves equivalence without a carry bound. Producing the formula-to-prime graph and unbounded product in one fixed polynomial is not free, and no claim that this encoding is smaller is made.

## Architectural comparison

Round 9 stores a chronological sequence of whole stacks; local verification must decode the stack and every global step. The present theorem stores only a multiset of primitive rule instances. Local verification no longer needs a stack pairing equation, and global verification needs one multiset balance rather than path continuity or well-foundedness. The mathematical simplification is substantial, but a smaller completed Diophantine polynomial has not yet followed from it.

## Safe next target

Implement a finite-multiset compiler specialized to unary-conclusion polynomial Horn rules. It must simultaneously (a) certify every represented rule instance; (b) aggregate exactly its premise/conclusion labels; and (c) compare aggregates collision-free. An encoding satisfying only (b), an unbounded finite list of variables, or an equation with variable exponents is not a completed answer to the original problem.

## Uniform two-premise rule and explicit local polynomial

Because truth code 0 is derivable, work modulo its free coordinate: put e_0=0. Pad every axiom with premises (0,0) and every generalization with second premise 0. All rules then have exactly two slots. The flow theorem still holds for target1: in soundness the nonderivable-coordinate functional ignores0; in completeness discard true leaves or cancel them against free truth axioms.

Let H(v,a,b,c,u) be the same explicit nonnegative axiom-selector polynomial as round9 (including truth factor v^2). Define

    R(p,q,v;a,b,c,u)
      = (p^2+q^2+H(v,a,b,c,u))
        * (q-I(p,v))^2
        * (q^2+(v-A(a,p))^2).

Then existential vanishing over natural a,b,c,u says exactly that (p,q)->v is an axiom, modus ponens, or generalization rule, with the indicated padding. The single local polynomial contains no stack. `build_horn_rule.py` gives every literal operation, by adapting the authored round9 axiom-code construction; it imports no upstream executable code. It has367 binary operations, versus382 for the stack transition. Flattening produces81 natural wires plus4 local witnesses,82 quadratic residuals, and a quartic sum of squares with2,979 monomials. These are LOCAL counts only; three formula-label coordinates are exposed in addition to the85 witnesses. The full polynomial for global consistency is not constructed here.

For projected balances h_j, j>=1, use weights W(j)=B^j-1. The exact compressed condition is

    sum_r n_r [W(c_r)-W(p_r)-W(q_r)] = W(1).

The resulting polynomial in B has nonzero-coordinate coefficients h_j and constant coefficient -sum_{j>=1}h_j. A safe bound is B > 3N+1, where N=sum_r n_r: the total absolute contribution is at most3N+1, including the target. The least-nonzero-digit argument applies. Do not reuse the sharper B=max(2,N) unprojected bound here without accounting for the free zero coordinate and the new constant coefficient.
