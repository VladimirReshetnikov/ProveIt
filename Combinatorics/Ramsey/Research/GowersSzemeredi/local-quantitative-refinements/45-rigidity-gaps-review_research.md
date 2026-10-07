# Internal AI review of the applications and research programme

This is an internal mathematical cross-check by an AI agent during article preparation, not an external or human peer review. It checks the initially supplied `ap:rectified-holes` subsection and all of `sections/research.tex`, and records a new refinement developed during that review. It does not certify that every proposed research question is open in the published literature. The review used the paper's explicit mathematical hypotheses and inspected the supplied verifier; finite evidence was not substituted for proof.

## 1. Rectified holes: the mathematical claim checks out

The exact complement identity is

    epsilon = delta*(1-delta) + (u^3-E(K))/m^3,
    delta = u/m.

A Freiman 2-isomorphism preserves every counted quadruple, in both directions. Therefore the three largest energies for an u-point torsion-free set produce the three smallest possible defect values in this rectified-hole class:

1. `epsilon_0`;
2. `epsilon_0 + 4*(u-2)/m^3`;
3. `epsilon_0 + 8*(u-3)/m^3`.

These are distinct precisely in the claimed range `u>=5`, since `0 < u-2 < 2*u-6`. The classification of the first two levels transfers directly from the proved ordered-energy theorem; the third statement is a sharp lower bound, not a classification of all third-level holes.

The normalization is correct:

    (u^3-M_u)/m^3 = delta^3/3 - delta/(3*m^2).

For the three example holes, all points lie in `[0,u]` and all pair sums in `[0,2u]`. Consequently a cyclic order `m+u > 2*u` suffices to preserve all equalities; the text's stronger condition `m+u > 2*u+2` is valid. It is sufficient, not asserted necessary. The complements are nonempty under that condition.

`J_u` was already defined globally in the introduction; adding its local definition in this proof improves readability. The current application proof now gives the local definitions of both `H_u` and `J_u`. An initial concern that `J_u` was wholly undefined was resolved by checking the introduction.

Minor exposition: the phrase “asymptotic to delta^3/3” means as the hole cardinality `u` tends to infinity, since the exact additional lower bound is `delta^3*(1-u^(-2))/3`. Making that limiting variable explicit would remove ambiguity. No rectification is deduced from energy alone, correctly.

## 2. A proposed open constant gap was already resolvable

The initial research text asked whether the asymptotic puncture-repair leading constant lay strictly between 1 and 2. The coupled remainder already answers this. The issue was reported, then developed into the stronger finite theorem now labelled `co:puncture-refined`.

Let `C` be the canonical closest coset, `K=C\A`, `x=|A\C|/m`, `k=|K|/m=delta-x`, and `zeta=1-E(K)/|K|^3`. The essential budget is

    eta >= x + k^3*zeta.

In the final result-first presentation, the superseded factor-two theorem/proof has been removed. The sharp theorem has both labels `co:puncture` and `co:puncture-refined`; the independent sharpness construction follows as `co:puncture-scale`, with no circular proof dependency.

The new theorem assumes outer defect `epsilon<1/9`, `delta>0`, and

    0 <= s=eta/delta^3 < 1/9.

This improves the earlier repair theorem's sufficient condition `s<=1/16`. The outer envelope gives `delta<tau(1/9)<1`. For `0<=y<=eta`, put

    z(y)=(eta-y)/(delta-y)^3.

The derivative

    z'(y)=(-delta+3*eta-2*y)/(delta-y)^4

is strictly negative, because `3*eta=3*s*delta^3 < delta/3`. Thus every relevant inner defect is at most `s<1/9`, and the inner coset theorem applies.

The repaired distance inside this fixed outer coset is bounded by

    F(x), where F(y)=y+(delta-y)*tau(z(y)).

Writing `k_y=delta-y` and `b_y=tau(z(y))`, exact differentiation gives

    F'(y)=(1-b_y^2-k_y^(-2))/(1-2*b_y) < 0.

The positivity of the denominator and `k_y<1` justify strictness. Another AI agent independently rechecked this algebra. Hence the finite bound is

    Delta_C(A) <= delta*tau(s)
               = (tau(s)/s)*eta/delta^2
               <= (1+2*s)*eta/delta^2,

where `Delta_C` minimizes only over nonempty proper subcosets of the canonical `C`. The case `s=0` is handled separately and gives exact repair. No division by zero occurs.

The final simplified multiplier is justified by `b=tau(s)<1/4`:

    tau(s)/s = 1 + s/(1-b)^2 <= 1+(16/9)*s <= 1+2*s.

## 3. Equality and exact attainment in the new theorem

For positive `s`, strict decrease of `F` forces `x=0` in any equality case. The exact complement identity then gives `zeta=s`; equality in the inner coset envelope classifies the missing set as `K=D\J`. Thus equality is exactly

    A=(C\D) union J,
    nonempty subgroup cosets J properly contained in D properly contained in C,
    index of the subgroup of J in the subgroup of D at least 9.

Both necessity and sufficiency are supplied in the final proof. The subgroup index condition is the already proved inner envelope equality condition. The statement does not claim that the outer coset minimizes distance among all punctured outer cosets; it explicitly fixes the canonical `C`.

For every integer outer index `r>=10` and integer `u>=8`, take an ambient cyclic group `H` of order `r*(u+1)`, a subgroup `L` of order `u+1`, and

    K=L\{0}, A=H\K,
    m=(r-1)*(u+1)+1.

Then `delta=u/m<1/(r-1)<=1/9`, and

    eta=(u^2-u)/m^3 < delta^2,
    epsilon=delta*(1-delta)+eta < delta < 1/9.

The canonical outer coset is `H`. The inner parameter is

    s=(u-1)/u^2 <= 7/64 < 1/9,
    tau(s)=1/u.

The exact repair cost is one point, so `Delta_H(A)=1/m=delta*tau(s)`. The nonintegrality obstruction showing that no zero-edit punctured-coset representation exists is proved in `co:puncture-scale`. The expansion `tau(s)/s=1+s+O(s^2)`, together with these attained parameters tending to zero, settles the best uniform asymptotic leading constant as exactly 1. The theorem does not claim that every real parameter is attained.

The corresponding research question now concerns the maximal validity range and stronger bounds for unavailable subgroup indices or intermediate attainable energies. It no longer presents the leading constant as open.

## 4. Factor-one pointwise question and verifier scope

At initial inspection, `code/verify_cosets.py` asserted only

    m*v*(m-v) <= 2*(m^3-E(A)),

for difference multiplicity `v`. It did not include the proposed factor-one inequality. The research text's claim that the supplied checks included that diagnostic was therefore inaccurate. This was reported, and the claim has been removed from the research text. Any later verifier extension should be described according to its actual checks.

The lower bound of 1 on a possible universal pointwise constant is valid at positive defect: take `A=H\L`, where `L` is a subgroup of finite `H` of index `r>=3`, and choose `d` in `H\L`. Then

    q(d)=(r-2)/(r-1),
    q(d)*(1-q(d))=(r-2)/(r-1)^2=epsilon.

The phrase “differences outside its hole subgroup” should specify `d in H\L`; differences outside `H` have zero overlap and do not supply positive-defect equality. This wording clarification was reported. No universal proof or counterexample to factor one was obtained in this review. The present factor-two proof must not be treated as establishing it. In particular, finite success alone would not settle the proposed question.

## 5. Other research questions and wording checks

- The second candidate third-energy model `{0,2,3,...,m-1,m+1}` has the stated ordered deficit `2*m-6`: the prefix has deficit `m-3`, and exactly its `m-3` difference-one pairs fail after the endpoint is appended. The model is a legitimate candidate in the open equality classification.
- The two-point set in `Z/3Z` has energy 6, defect 1/4, and normalized coset distance 1/2 to the full group and either singleton contained in it. It correctly demonstrates failure of uniqueness at the endpoint.
- The bounded-Schur question should use “positive real dilates of finitely many integer terminal perturbations,” not literally “integer dilates,” because the domain consists of arbitrary positive real sets and dilation by an irrational number preserves the hypothesis.
- The spectral-support question “Must an extremizer involve at least two opposite character pairs?” is already answered affirmatively by the paper's exclusion of the single-pair class. It should instead ask whether two pairs suffice, or for the minimum possible number of pairs. This was reported for correction.
- The interval for `c_4^{odd}` has the stated approximate width, and the text correctly treats the five-point example as a lower-bound witness rather than an optimizer.
- The weighted question correctly asks for explicit normalization; the support cardinality alone cannot bound weighted energy.
- The cyclic-transfer question correctly retains a Freiman 2-isomorphism hypothesis, rather than treating an arbitrary choice of representatives as rectification.
- The global-propagation discussion does not claim that a local constant improvement yields a new Szemeredi bound.

No further mathematical contradiction or elementary resolution was identified in the remaining proposed questions during this review. This statement is limited to the internal mathematical audit, not an exhaustive literature search.

## 6. Verification and scope of edits

The reviewer's changes were restricted to the new nested-hole theorem in `sections/cosets.tex`, its corresponding question in `sections/research.tex`, and the two internal review files. Other suggested wording changes were reported to the coordinating author. The coordinating author assigned the new finite verification checks to a separate agent; this review does not claim those new checks had already passed at the time of derivation.

A standalone two-pass LaTeX compilation of the final coset section succeeded, producing 12 pages with no warnings, undefined references, or overfull/underfull boxes. Final article assembly and visual inspection remain separate from this mathematical review.
