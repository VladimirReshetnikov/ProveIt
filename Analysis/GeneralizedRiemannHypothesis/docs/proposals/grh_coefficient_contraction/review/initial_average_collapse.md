# Initial gauge average collapses to one root of unity

## Status and novelty boundary

This is a new paper-level theorem derived from the first-column source contracts. It has not been compiled in Lean. The relevant source files are identical at commits `d417d0b5b08edd4f5f67224fd310add7f1618ca0` and `1a59f50680e470fb5269bbe70c06f974c95ad930` (local `git diff` checked).

The newer `grh_diagonal_sweep_proposal` already supplies deterministic sweeps, the diagonal-only budget, exact ranks, endpoint cardinalities, and asks whether the unused reflected initial-node coset can be removed. Those are assumed available here. The result below remains nontrivial **after that redundant coset is removed**: all the other initial averages collapse to a fixed scalar times a root-or-zero function. The initial coefficient budget becomes 1, instead of the product of all initial group cardinalities or their rank-sensitive bounds. It also solves the twist-independent-normalization issue by an explicit CRT argument.

## Source facts

Paths below are relative to `Analysis/GeneralizedRiemannHypothesis/Lean/grh/src/`.

* `New/Determinant/AuxiliaryForms/PathData.lean:63–125`: write I for the product of the chosen-place ideals, Q for the twist-place product, b=`D.natB`≥1. The grid ring is R=O/(I^b Q), the false triangle ring R0=O/(I Q), and the true triangle ring B=O/I^b. Q is coprime to I by the source's disjoint chosen/twist places.
* `GridFirstColumns.lean:399–413`: `firstPointDatum` is precisely the indicator that every edge matrix reduces to its standard inclusion over R0 (false half) or B (true half).
* `GridFirstColumns.lean:620–644`: `LevelCosets` has a coset at every node `(z,0,i)`, i<m; false node levels are trivial, true node levels are the kernels of reduction to B. Its family is anchored at both i=m endpoints and has true initial gauge `diag(g_false,0,1)`. The true initial coset is unused.
* `PathData.lean:390` proves surjectivity of the GL reduction to B. Thus true quotient cosets are exactly GL(B), not merely an injection into it.
* `GridFirstColumns.lean:563–583`: the edge characters are trivial on the true reduction kernels. Hence the character weight descends to the product of true quotient groups. `edgeCharProd_mul` supplies its multiplicativity; its values have finite order.
* `GridFirstColumns.lean:647–670`: the existing average is equivariant; 691–720 supplies support and the existing coarse root-count bound. 781 onward supplies its period identity with a scalar independent of the twist.

The standard edge inclusions have left inverses by definition; no property of arbitrary edge matrices is postulated.

## A general weighted orbit lemma

Let a finite group G act on a set X on the right, let e∈X, and let χ:G→C^× be a finite-order character. Put H=Stab(e). For x∈X define

    A(x)=sum_{g∈G} χ(g) 1_{x·g=e}.

If the transporter is empty, A(x)=0. Otherwise choose g0 with x·g0=e. The transporter is g0 H, so

    A(x)=χ(g0) sum_{h∈H} χ(h).

The character sum is |H| when χ|H=1 and zero otherwise: translating by h0∈H gives S=χ(h0)S, and C has no zero divisors. Consequently A(x)/|H| is either 0 or a root of unity. This does not assume χ is trivial on H and does not require choosing representatives uniformly in x. In particular it yields the universal root-count budget 1.

The same statement holds with left actions after reversing the coset convention. It is purely finite algebra.

## The actual first-column gauge group

For m≥1 let a_i be the false rank and b_i the true rank. Define

    G_theta = (product_{0≤i<m} GL_{a_i}(R))
              × (product_{1≤i<m} GL_{b_i}(B)).

The omitted true initial slot is precisely the previously identified redundant coset. The action on observed edge tuples is induced by

    S_i -> g_{i+1}^{-1} S_i g_i,

over R0 on the false half and B on the true half, with both g_m=1 and

    g_true,0 = diag(g_false,0 mod B, 1).

The edge-character product defines a character χ_theta on this group, because true representatives differ by kernels on which the source's edge characters are trivial. The original average is

    firstPathDatum_theta(S) = d * A_theta(observed(S)),
    d = |GL_{b_0}(B)|.

Here d is independent of theta. No assertion that the other node gauges are independent of their adjacent edges is being made.

## Stabilizer theorem: all residual freedom is a fixed congruence kernel

Let E be the tuple of standard inclusions. Its stabilizer in G_theta is exactly

    H_theta = product_{1≤i<m} ker(GL_{a_i}(R) -> GL_{a_i}(R0)),

with every other gauge coordinate equal to 1.

Proof. Stabilizing the false standard edge means

    E_false,i * (g_false,i mod R0)
      = (g_false,i+1 mod R0) * E_false,i.

Starting from g_false,m=1 and multiplying by a left inverse of E_false,i, descending induction forces every g_false,i mod R0=1. The same descending induction on the true half forces every true interior gauge to be 1 and diag(g_false,0 mod B,1)=1. Thus g_false,0 reduces to 1 in both R0 and B. The map

    R -> R0 × B

is injective: `(I Q) ∩ I^b = I^b Q` because Q and I are coprime and b≥1. Hence g_false,0=1 over R. The remaining false gauges may be any element of the indicated reduction kernel; each such family does stabilize all observed standard inclusions. This proves both inclusions and the claimed product decomposition.

This proof is stronger than a generic stabilizer bound: the stabilizer is explicitly identified, independently of S. Every nonempty transporter is a coset of exactly this group.

## The stabilizer cardinal is independent of the twist

Let A=O/I and T=O/Q. CRT gives compatible ring isomorphisms

    R ≅ B × T,       R0 ≅ A × T,

under which reduction is `(B→A) × id_T`. Applying GL in rank a_i gives

    ker(GL_{a_i}(R)→GL_{a_i}(R0))
       ≅ ker(GL_{a_i}(B)→GL_{a_i}(A)).

Therefore

    h = product_{1≤i<m} |ker(GL_{a_i}(B)→GL_{a_i}(A))|

is a positive integer independent of theta. The original average's multiplicity is C=d h, also independent of theta. This argument requires no assertion about the norm or number of elements of Q. If the earlier proposal removes the unused true initial slot first, simply take C=h.

## Main consequence

Define

    normalizedFirstDatum_theta(S) = firstPathDatum_theta(S) / C.

Then every value is 0 or a root of unity, so `IsSumOfRootsOfUnity 1` holds. Dependence on the first-path edges and the existing covariance follow by scalar multiplication, and support follows because C≠0. Hence

    IsPathDatum 1 (TwoGridPath.first m).edges normalizedFirstDatum_theta.

If the source first-period identity is `P_theta = K * gridPeriod(firstPathDatum_theta)`, with K independent of theta, its normalized version is

    P_theta = (K C) * gridPeriod(normalizedFirstDatum_theta).

The new scalar K C is still independent of theta. This is multiplication by the known positive integer C; it never divides by an unproved nonzero period or by K. The definition involving division by C causes no hidden coefficient-denominator problem: the orbit lemma proves that its values are algebraic units or zero before any arithmetic bounds are applied.

### An endpoint-only comparison scalar

There is a sharper simplification of the particular first-column comparison scalar in `exists_diagonalPeriodForm_transposedChain_eq`. Let

    h_i = |ker(GL_{a_i}(B)→GL_{a_i}(A))|,   0≤i<m.

The source's explicit scalar witness at `GridFirstColumns.lean:96–98` is

    kappa_i = |GL_{a_i}(R0)| / |GL_{a_i}(R)| = 1/h_i.

Surjectivity of GL reduction follows from the local surjective ring reduction, as used in that source proof; equivalently use CRT and the nilpotent ideal reduction B→A. The source comparison scalar is the product of kappa_i. Its product with our full normalization C=d*product_{1≤i<m}h_i is therefore

    alpha_normalized = d/h_0.

Every interior congruence-kernel factor cancels, leaving a scalar depending only on the common bottom space and the two fixed untwisted residue rings. The same result holds if the redundant true initial slot was removed earlier: its d has already entered the comparison scalar, and our remaining normalization is the product over i≥1. This endpoint-only formula is an optional strengthening; the budget-1 theorem needs only the already proved twist independence.

Combining with the **already proposed** exact diagonal budget gives final coefficient budget

    |R|^(m r + t m^2),

with no initial endpoint factor `|R|^A`. The terminal summation still has its own tuple factor `|R|^B`; this result does not remove it. Thus the known endpoint-sensitive full finite-sum factor improves from `|R|^(A + m r + t m^2 + B)` to `|R|^(m r + t m^2 + B)`. No final global exponent improvement is claimed without checking other factors.

## Lean integration and scope

### Why the fixed normalization is not paid back as a height or denominator cost

The scalar in `FirstPath.exists_isPathDatum_first` is existential and independent of the twist. Replacing the initial datum by its quotient by C changes that scalar alpha to C alpha; the restriction map and its surjectivity are unchanged. `SpanningForms.lean:412–420` retains this scalar only as part of an unbounded existential coefficient beta in the period identity. No norm or valuation estimate of alpha or beta is subsequently required.

At `SpanningForms.lean:682–690`, the proof chooses a nonzero scalar s so that

    s beta = dualHook * (epsilon N),     epsilon∈{0,1}.

When beta≠0 it takes s=dualHook*N/beta. Thus, if compatible homogeneous transport choices multiply beta by C, s is divided by C. More generally the proof works for any new existential beta by its same formula; no homogeneity claim about the chosen transfer witnesses is needed. If beta=0 the existing separate branch takes s=1 and epsilon=0, with no cancellation. The arithmetic conclusion at lines696–727 is expressed solely in terms of `dualHook * epsilon * (N Xi)`, and Xi is the period of the newly normalized datum. Its coefficients have already been proved roots of unity or zero, so the original denominator-clearing N still suffices. The lower datum budget improves its archimedean estimate. The freely chosen nonzero rescaling s preserves the spanning claim, as in the original proof.

Consequently the integer C is genuinely removed from the auxiliary coefficient estimate, rather than silently moved to a later norm bound. This point is specific to the source's existential rescaling interface; it would not be valid in a theorem requiring a predetermined integral input normalization.

The safe first port can retain the existing average and all current period/covariance lemmas, prove the orbit-fibre theorem, and normalize once. This removes `card_levelCosets_le` from the actual bound dependency and changes the initial `IsPathDatum` budget to 1. A second port can define the coefficient as an equivariant orbit section, with the orbit lemma recovering the old average as a compatibility identity; this is where quotient-representative bookkeeping may disappear. Net line savings need a clean Lean implementation and must not be inferred from the numerical budget gain.

Required new infrastructure is specific and checkable: (1) compatible CRT for the three moduli, (2) GL preservation of the product ring decomposition, (3) the anchored-chain stabilizer proof, (4) the finite character-sum lemma. All are elementary algebra; no new theta identity, seesaw, convergence theorem, or norm/cardinality assumption is used.

For the first Lean port, the cardinal-independence proof can be shorter than formalizing the full GL product decomposition. Reuse `exists_triangleGLCard_eq_mul_levelIndex`: its fixed kappa_i satisfies `|GL(R0)| = kappa_i |GL(R)|`. Surjectivity of GL reduction and finite-group fibre counting imply `kappa_i |ker| = 1`. Compare this identity with the trivial twist to deduce equality of kernel cardinalities. The CRT/intersection argument is still needed for joint injectivity at the common initial node, but the group-cardinality part can reuse source infrastructure.

The source has m=2*varrho+2≥2. A generic theorem stated for m≥1 avoids a spurious m=0 exception: when m=0 there are no initial coset slots and the original coefficient already equals 1.
