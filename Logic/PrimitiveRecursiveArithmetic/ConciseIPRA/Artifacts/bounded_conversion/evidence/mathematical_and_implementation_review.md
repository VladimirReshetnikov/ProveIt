# Independent audit: bounded local conversion

## Verdict and scope

I independently reviewed the argument now in Section 2 of `../ipra_bounded_conversion.tex`, the six finite packet traces in `bounded_conversion_trace.json`, and the implementation now in `../code/checker.py`. I found no mathematical counterexample or missing inference in the claimed equivalence. The proposed seven-family calculus is sound and complete for exactly the same **raw open sequents** as the eight-rule native kernel with one-term crossed transport and direct equation progress.

The result is a written mathematical proof, supported by executable checks of the finite traces and an inspection of the implementation. It is not a Lean/Rocq formal verification. It does not establish a new global checker minimum, a minimum depth bound, or fewer primitive rule families than the incoming six-rule weak-head presentation.

The narrow substantive claim is justified: the equivalence needs only bidirectional, one-step computation at counter-spine depth at most three in the **left endpoint of an equation**. No global normal-form operation or normalization theorem is used in the primitive inference mechanism or in the completeness argument.

## 1. Structural lemmas do not assume general substitution admissibility

The variable-only rule V is not stable under replacing a source variable by an arbitrary term. The proof must not silently assume such stability. It does not need it.

Prove the following first by induction on finite derivations:

* Weakening by additional formula assumptions.
* Injective renaming of free numerical variables, together with alpha-renaming of bound variables.
* Cut on a formula assumption.

An injective renaming preserves being a literal variable, being literal zero, the equation/compound root distinction, the two redex patterns, and counter-spine depth. In a cut step under E or I, first alpha-rename the eigenvariable away from the cut proof and added context. Weaken and rename the proof of the cut formula into that branch, and apply the induction hypothesis. No arbitrary substitution into a derivation occurs. Raw term substitution inside V, computation, and the binder rules is a syntactic operation, not the disputed structural substitution theorem.

## 2. The dependence order is acyclic

The safe order of derived rules is:

1. Structural weakening, injective renaming, and cut.
2. Symmetry, using a fresh variable supplied by a dummy D theorem.
3. Conversion on the right endpoint, using symmetry around primitive left conversion.
4. Direct equation progress, then the equation-cases rule with independent branches.
5. The packet and arbitrary one-term crossed transport.
6. The two computation axioms and the missing equation-case introduction at literal witness zero.
7. Rule-by-rule equivalence with the native kernel.

In particular, the packet does not use general equality transport, arbitrary substitution into proofs, induction on compound formulas, predecessor, coverage, or the general parity equations.

## 3. Symmetry is valid even in an empty numerical scope

The theorem D_(x,y)(0=0) follows from I at witness zero: its progressive branch has goal 0=0, discharged by Refl. Open it at a fresh b. The major b=b for V follows by Refl. Apply V to this major and the given equation s=t, using source b and replacement b. The conclusion is t=s. Freshness guarantees that the conclusion contains no b, so E exports it.

This explains why no pre-existing numerical parameter is needed. It also explains why right-endpoint conversion is available before the packet: reverse the equation, use primitive left-endpoint conversion, then reverse again.

## 4. Direct progress and equation cases use literal equations only

For a literal equation E(y), use I at witness zero on D_(x,y)E(y), with x unused. Its premise is exactly E(z) |- E(Sz). Eliminate the resulting D formula to export its Q_y E(y) hypothesis. Thus direct equation progress is derived.

If E(0) and E(Sv) have been proved independently of an induction hypothesis, weakening adds E(v) to the latter proof. Direct progress yields Q_y E(y), and Q yields E(r) at any raw term r. All passive parameters remain fixed. In the packet construction, the fresh variable v for this induction is separate from the fresh variable z of the surrounding paired introduction; r=P(Sz) is merely a later instance in that already established closure.

## 5. The packet calculations fit the bound

Use the matrix

    Pi(x,y) = C(y,0,C(P(y),x,h(x)))
               = C(y,0,C(P(y),t,r)).

Here x and y are chosen fresh from the original context, s, t, r, and the passive parameters of the term template h. Every internal iterator binder is alpha-renamed away from these variables before expansion.

The two endpoints have the following explicit reduction depth lists:

| Row | Depths | Reduced equation |
| --- | --- | --- |
| 0 | 0 | 0=0 |
| 1 | 0,1,2,1,0 | h(x)=r |
| 2 | 0,1,2,3,2,1,0 | x=t |

The payloads x, h(x), t, and r are opaque throughout these computations. Their sizes and internal structure do not increase the required counter-spine depth. In particular, no contraction is required inside h(x).

At the successor row used to introduce the packet at witness s, one root contraction on each endpoint gives

    F(P(Sz)),  F(v) := C(v,s,h(s))=C(v,t,r).

F(0) is obtained by inverse endpoint conversions from s=t. For a fresh v, F(Sv) is obtained by inverse endpoint conversions from h(s)=r. Equation cases supplies F(P(Sz)); inverse root conversions restore Pi(s,Sz). The local I assumption is unused. Consequently this branch is valid whether the raw witness s selects case mode or, when s is literally zero, progress mode.

After opening the packet at fresh b, Refl and inverse conversions provide Pi(b,0), so Q supplies rows one and two. Their finite conversions give h(b)=r and b=t. Rule V, with source b and replacement t, gives r=h(t). Since b is fresh for t, r, and the passive parameters of h, the exported equation contains no b. E therefore discharges the packet correctly.

This derives arbitrary crossed one-term transport from its two original equation premises.

## 6. The literal-zero witness repair is correct

Suppose the old case rule supplies a branch

    Gamma, B(0,0) |- B(0,Sz)

for an equation matrix B. Set a=I(0,0;u.0). The raw term a is not literally zero, while a=0 follows from Refl and one inverse conversion.

Under Gamma,B(a,0), derived equation transport gives B(0,0). Cut in the supplied old branch to obtain B(0,Sz). Symmetry of a=0 and derived equation transport give B(a,Sz). Rule I at raw witness a now selects case mode and concludes D_(x,y)B.

The old proof branch is inserted by formula cut; it is not modified by an arbitrary term substitution. This distinction is essential because V does not have a direct general substitution lemma.

## 7. Choose the native comparison basis explicitly

For the cleanest proof, compare directly with the native eight-rule basis:

    Hyp, I0, IS, crossed one-term Tr, QE, DE, DI by cases,
    QI by equation progress.

All eight have now been recovered. General transport through compound formulas need not be reproved before establishing this equivalence; it can be inherited afterwards from the native kernel. This avoids introducing an unnecessary formula-induction argument into the critical dependency chain.

For the reverse inclusion, native computation and congruence prove every allowed endpoint conversion, in either direction. V is an instance of native crossed one-term transport, using the source variable as the template hole. The selected introduction is either native DI by cases or native witnessed equation progress. Refl is already a native derived rule. Induction on the new proof gives the reverse inclusion on every raw open sequent.

Once the ordinary readings and numerical syntax remain unchanged, the established native-iPRA interpretation and both identity-graph round trips transfer unchanged. This is stronger than equiconsistency alone.

## 8. Implementation inspection

The inspected checker implements the stated calculus faithfully.

* `contract` descends only through iterator counters. The certificate depth is an exact integer in 0,...,3; Boolean depths are rejected.
* `raw(redex,n)` checks every redex child before any zero computation erases a body or seed. Out-of-scope variables cannot be hidden by an erasing step.
* Conversion changes only the left equation endpoint. The supplied redex and its computed reduct determine the two directions; no normalization is performed.
* V checks that its source index is an actual free variable in the current numerical scope, validates the replacement and raw minor term, and performs substitution with `drop=0`, preserving the numerical context.
* In DE, the goal and old context are shifted by one, while Q of the supplied two-variable body correctly retains the newest numerical variable as the existential witness. This enforces the eigenvariable condition syntactically.
* In DI, substituting the witness at index one removes the existential binder while preserving the universal variable at index zero. The case assumption is the shifted zero instance; the progressive assumption is the uninstantiated equation body. The successor instance uses `drop=0`, retaining the new eigenvariable.
* Raw formulas and all initially retained hypotheses are validated. Intermediate formulas are produced by scope-preserving operations or validated auxiliary bodies. A malformed proof field may be ignored for a hypothesis or reflexivity leaf, which is harmless because that leaf already proves its goal.

This inspection is a correctness argument for the current source, not a claim that future changes are automatically covered. Preserve the inspected source hash in the deliverable's manifest.

## Recommended wording

> We give a seven-rule raw-term presentation equivalent to the native calculus on every open sequent. It replaces automatic weak-head normalization by certificate-directed computation, with every primitive conversion confined to the left endpoint and counter-spine depth at most three. The equivalence is proved in writing, and the finite packet calculations and implementation are checked separately. This is a reduction in the trusted evaluation mechanism; no absolute size minimum or minimum depth is claimed.

