# One orientation of quantifier commutation is sufficient

## Result

In the accepted native classical calculus, write `Box_i X = Q_i(X)` and
`Diamond_i X = not Box_i(not X)`. Keep the normality row rho2, the symmetry
row rho6, the classical propositional fragment supplied by dominated rho8,
and theorem-only generalization.

For each unordered pair of distinct natural labels, choose exactly one
orientation `(a,b)`. Retain rho4 only in the chosen orientation, for every
natural formula code X:

    Box_a Box_b X -> Box_b Box_a X.

Then **every omitted rho4 instance is derivable at exactly its original
native code**. In particular, retaining only instances with a<b gives the
same native theorem set as the unrestricted calculus. Equality cases are
instances of the propositional identity theorem. The result does not
require well-formed formula codes or constructor injectivity.

This is a new derived interface checked against the currently inspected
repository. It is not a claim of priority in modal logic; it is an explicit
native-calculus reduction with a machine-oriented proof certificate.

## Explicit finite derivation

Let A=Box_a, B=Box_b, d_a=Diamond_a, d_b=Diamond_b. The retained rho6 says

    d_i Box_i X -> X.                                      (counit)

Taking its instance at not X, using classical contraposition and
eliminating double negations, gives

    X -> Box_i d_i X.                                      (unit)

The normality row and closed-theorem generalization give monotonicity of
Box_i. Classical contraposition then gives monotonicity of d_i. As a
consequence, from a closed theorem `d_i U -> V` one derives
`U -> Box_i V`: compose the unit with the Box_i image of that theorem.
This is an admissible theorem transformation, and never generalizes an
open premise.

Fix an arbitrary code X and put Y=B A X. Use the retained orientation only
at the matrix not Y. Classical contraposition and the two double-negation
transports under boxes give

    d_b d_a Y -> d_a d_b Y.

Then the following chain consists of derived theorems:

    d_b d_a Y -> d_a d_b Y
                -> d_a A X       [d_a monotonicity of rho6(b,A X)]
                -> X.            [rho6(a,X)]

Apply the preceding admissible theorem transformation first for b, then
a. The results are

    d_a Y -> B X,
    Y -> A B X.

Substituting the definition of Y proves

    B A X -> A B X,

which is exactly the missing orientation. No quantifier-renaming lemma,
semantic completeness theorem, or substitution rule for the full native
theory appears in this argument. Every displayed parameter can denote any
natural code, including the native zero alias `I(0,0)=0`.

## Checked certificate

`ordered_commutation.py` generates a 600-node finite Hilbert DAG and
validates every inference using the pinned, inherited `hilbert.py` reader.
The only axiom schemas used are K, S, double-negation elimination, rho2,
rho6, and the single orientation of rho4. The first three are exactly the
already available classical propositional interface supplied by the
accepted dominated-rho8 derivation. All GEN nodes have closed premises.
The result and DAG are `ordered_commutation_result.json` and
`ordered_commutation_dag.json`.

This is an executable finite symbolic certificate, not a new Lean/Rocq
kernel theorem. Its interpretation as a finite family of native numerical
proofs is justified by the compositional code constructors; syntactic AST
equality only supplies sufficient instances of numeric equality and does
not assume the constructors are injective at zero.

## Consequence and precise limit for AX optimization

The restricted rho4 calculus has the same native theorems as its parent:
its axioms are parent axioms, while the finite derivation above recovers
all missing rho4 leaves. Therefore every inherited source-level and ZFC
calibration theorem transfers once a source actually enumerates the
restricted family together with all the other required rows.

This does **not** justify imposing a<=b on the existing entire AX command.
The other schemas share a and b. For example, the accepted equality
reflexivity proof uses rho1(r,x) with r=f(x,x)>x and the merged equality
binder f. Such instances are excluded by a global a<=b restriction. The
current argument only removes redundant orientations of rho4; it does not
replace the missing other rows or prove that the existing gated seed
bundle survives an ordered-pair restriction.

Similarly, no state saving follows just from fewer axiom instances. A
machine benefit requires a concrete source construction and complete
physical allocation/runtime/startup checks. None is claimed here.

## Provenance

Inspected revision: ead95b5b336818a53c89b8c3d5249822e0570939 of
https://github.com/VladimirReshetnikov/ProveIt.

Native formulas and normality/symmetry rows:
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean`.
Classical propositional interface:
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` and the
accepted `candidate-k218/alternatives/dominated/proof.md` calibration.
Inherited proof checker:
`Computability/BusyBeaver/Research/ZFC/k218-ks-mixed-commutation/hilbert.py`,
SHA256 63396d6ec0b98744b8b4502c316fbdb7fdb018dcda1dbaed0d2e612e5351b7cc.
