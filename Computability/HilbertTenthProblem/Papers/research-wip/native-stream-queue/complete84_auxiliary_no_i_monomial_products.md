# No i-containing monomial product at the remaining nine-gate frontier

For the existing auxiliary interface

    V=cTf−c−Rf²,  Q=Delta²*i²*c⁴,  S=Delta*f²−Q,

**a circuit with at most nine gates cannot have any counted multiplication output that is a nonzero monomial containing i.** This strengthens the necessary conditions on the remaining direct-Q cancellation case. It does not exclude every nine-gate circuit or supply a new circuit. The complete84 upper construction is unchanged.

## 1. Model and authenticated premises

Work over the rational polynomial ring in the independent variables Delta,c,i,f,T,R. The only additional paid ports are c² and Delta*c². Constants and scalar multiples are free in the inherited lower-bound relaxation. A counted multiplication multiplies two nonconstant expressions; a scalar-weighted binary sum costs one addition. Arbitrary scalar linear combinations are free only in the multiplication-count contradiction below.

The [nine-gate frontier](complete84_auxiliary_nine_gate_frontier.md) proves that any circuit using at most nine gates must have exactly5M+4A, with a unique useful monomial-valued addition U on the path to Q. It also proves that a circuit with three additions needs at least seven multiplications. The [proper-pivot exclusion](complete84_auxiliary_proper_pivot_exclusion.md) leaves only U proportional to Q. Normalize that nonzero rational scalar freely and write U=Q.

The [mixed-cut proof](complete84_auxiliary_mixed_cut.md) proves that V and W=Delta*f² jointly require at least four multiplications from precisely the original paid ports, even with arbitrary linear combinations free. No extra power of c, pivot, quotient or coefficient is added to that interface here.

Let P0 denote the rational scalar linear span of

    1, Delta, c, i, f, T, R, c², Delta*c².

List multiplication outputs chronologically as g1,...,g5. Before any point in the circuit, every available expression lies in the scalar linear span of P0 and the earlier multiplication outputs. Additions preserve this statement, and each multiplication introduces its own output. Therefore, immediately before the addition U,

    Q = A + sum_(j=1)^r beta_j*g_j,                 (1)

where A belongs to P0, every beta_j is rational, and g1,...,gr precede U. Since Q is not in P0, at least one beta_j is nonzero. These are scalar coefficients, never variable-dependent weights.

At the specialization i=0, Q becomes0, V is unchanged, and S becomes W. A multiplication output known to specialize to zero can be deleted and all its uses replaced by literal0. Also, if j is the largest index with a nonzero coefficient in a surviving specialized relation, that relation solves for g_j using only specialized paid ports and earlier surviving product outputs. Replacing its later uses by this scalar linear combination deletes that multiplication too. This uses division only by a nonzero fixed rational and is permitted in the multiplication-only relaxation.

## 2. An earlier proportional-Q product is already impossible

Suppose a multiplication output g_t preceding U is a nonzero rational multiple of Q. Redirect every use of U to the already available scalar multiple of g_t and delete U's addition. The circuit still computes all three outputs with at most five multiplications and three additions. This contradicts the inherited three-addition bound; fewer than three additions are already excluded for V,S.

Thus any multiplication output proportional to Q that is relevant to the remaining argument must occur after U. This exception is excluded by alias removal, not by asserting linear independence between proportional monomials.

## 3. Three chronological cases

Assume some counted multiplication output g_t is a nonzero monomial with positive i exponent. It specializes to zero at i=0.

**Case1: g_t occurs after U.** Choose j maximal with beta_j nonzero in(1). Then j≤r<t. Delete g_t by replacing it with0. It does not occur in(1), so the specialized relation independently deletes g_j using earlier products and the paid span. These are two distinct multiplications.

Now suppose g_t precedes U. Section2 excludes g_t proportional to Q. Distinct monomials are linearly independent, so

    Q is not in P0 + span_ℚ{g_t}.                  (2)

Here span_ℚ means rational scalar linear span. Equation(2) is not multiplication of Q by g_t. It implies that in(1) some beta_j with j≠t is nonzero. Choose the largest such index j. First delete g_t using its zero specialization. Its term disappears from the specialized relation, which becomes

    g_j|_(i=0)
      = −(A|_(i=0) + sum_(k<j, k≠t) beta_k*g_k|_(i=0))/beta_j.   (3)

**Case2: j<t.** The deleted g_t was later than g_j, possibly depending on it. Replacing g_t by0 first removes that later value and all its uses. By the choice of j, no other product later than j occurs with nonzero coefficient in(3). Thus(3) deletes g_j using only earlier surviving outputs. No later computation is introduced into an earlier node.

**Case3: t<j.** The zero product g_t has already been replaced by0 in the operands of g_j and all intervening computations. Those substitutions preserve their specialized polynomial values. Equation(3) again expresses g_j using only earlier surviving products, so its multiplication is deleted chronologically.

These cases exhaust the relative positions: U is an addition and cannot be the same gate as g_t, and j≠t by construction. No assumption is made about the multiplicative depth, dependencies between g_t and g_j, or whether g_j is monomial. A product that becomes constant or zero elsewhere only reduces the remaining count further.

In every case the specialized circuit computes V and W using at most5−2=3 multiplications from the original specialized paid ports. All other computations remain charged; free additions in this argument do not grant any new paid polynomial. This contradicts the four-multiplication lower bound for V,W. The supposed g_t therefore cannot exist.

## 4. Exact conclusion and optional extension

Any surviving at-most-nine-gate circuit in this model must have5M+4A, form Q directly at its unique useful monomial-valued cancellation addition, and have **no nonzero i-containing monomial among its multiplication outputs anywhere in the circuit**. The statement concerns polynomial identities in the declared independent variables, not positive-zero identities, valid-compiler coefficient relations, or arbitrary other interfaces.

It does not exclude i-dependent **nonmonomial** multiplication outputs. Their cancellations may still be relevant to the unresolved direct-Q case. No ten-gate optimality theorem or nine-gate impossibility follows here.

The same deletion argument yields a limited optional lemma: any later multiplication output vanishing at i=0 gives the Case1 contradiction; an earlier output g vanishing there gives the Case2/3 contradiction whenever `Q ∉ P0 + span_ℚ{g}`. This is a criterion, not a classification of all such nonmonomial g. The monomial theorem above uses distinct-monomial independence to establish the criterion, with the proportional-Q exception handled separately.

## 5. Provenance and scope

This is a proof-only successor. It emits no new source array, operation saving, numerical compiler fixture or bounded-search certificate. The predecessor proof texts were read as inert data and the following bytes were hashed; no predecessor program was executed or imported. No repository file or frozen predecessor was changed.

| Inert dependency | SHA-256 |
|---|---|
| [Proper-pivot Python](complete84_auxiliary_proper_pivot_exclusion.py) | `ff8f5126e6e04f9c09f47763624e4a4f2d20cb19df42646f43ae7fa9a28fa8d0` |
| [Proper-pivot receipt](complete84_auxiliary_proper_pivot_exclusion.json) | `1147fab5fb69fcecf3b77c982118af147f5938bc57c786ebed64317c26217793` |
| [Proper-pivot proof](complete84_auxiliary_proper_pivot_exclusion.md) | `027c1945025f4bf1e6b9d585ba2befe1af697239787928226b0fd10f868fdf20` |
| [Mixed-cut proof](complete84_auxiliary_mixed_cut.md) | `b16bcf8b4013345d25a5d2bbb0598ae2caaaeaa31a529e00af7ea4647d78d7f2` |
| [Nine-gate proof](complete84_auxiliary_nine_gate_frontier.md) | `ae4925e8bf330fcd1a5d1c0f529e982f0c5df018690a7ef81e4ca27cc5ad4cd2` |
