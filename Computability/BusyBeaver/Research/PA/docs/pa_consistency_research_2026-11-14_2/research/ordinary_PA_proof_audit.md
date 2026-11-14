# Independent ordinary-proof audit of the PA194 baseline

Snapshot: ProveIt 567266818aaeceb0f3a8f82debf303c8d84bddaf.

## Verdict

The ordinary PA proof in `PA/docs/pa194_conpa_2026-11-13/report/calibration.tex`, with its retained `reference/original_pa195_calibration.tex`, is a coherent inherited mathematical dependency. I found no counterexample or invalid inference in its diagonal replacement, equality-interface recovery, finite binary comprehension, or exact proof-store invariant. This is **not** a claim of a freshly checked end-to-end Lean theorem. The repository explicitly reports that endpoint still open, and its standard Lean calculus/clock theorem concerns the numerical calculus before PA calibration.

The user's requested PA-provable equivalence does not require iPRA internalization or a new Lean proof. Do not conflate the stronger uncompleted repository goal with failure of the ordinary mathematical argument.

## Strongest proof chain

1. Original PA196 has a PA-refutation compiler into its numerical calculus (the internal nonhalting -> Con(PA) direction). The relevant numerical constructors are I(A,B)=4p(A,B), M(a,b)=4p(a,b)+1, U(a,B)=4p(B,a)+2, E(a,b)=4p(a,b)+3. Code 0 is truth; code 1 is M(0,0).
2. Replace primitive equality vacuity by the diagonal theorem Gamma(B)=B -> U(B,B). All labels occurring in decoded B are < B, including bound labels; code zero is separately true.
3. Recover reverse membership congruence and neighborhood equality using finite, primitive-recursive proof templates. This supplies precisely the interfaces used by the original refutation compiler. I verified by repository search that direct uses of `equalityVacuity` outside its definition are in `Logic/Reverse.lean`, `Logic/Neighborhood.lean`, and their arithmetic certificate copies; the text correctly targets these.
4. Separate Gamma from its bundled gate. The two axiom presentations are propositionally interderivable, with primitive-recursive translations preserving exact conclusion codes. Command selectors must account for ten pushes (versus nine previously).
5. For the reverse translation, interpret M(s,z) as the zth bit of s. Full PA gives finite comprehension for every arithmetic formula, with a uniform syntactic proof supplier using one induction-schema instance. This is proof construction, not uniform truth/reflection.
6. Annotate every visible formula t,h and every canonical live Cantor-stack element with a PA proof of its translation. Check every command algebraically. Any halt at t+h=1 (or the appropriate modified test) yields a PA proof of code 1, whose arithmetic interpretation is refutable.
7. Exhaustive command scheduling must use a halting word valid from every incoming store, because the scheduler carries its store between trials. Positive, exact source-to-tape segment simulations plus full blank startup establish equivalence for the literal binary table in PA.

## Details checked

### Diagonal reverse congruence

Fix distinct labels a,b and a family chi(t) equal to M(d,t), M(t,d), or M(t,t). Initially, in the first two families require d != a. Put C = E(a,b) -> (chi(b) -> chi(a)), phi = not C and c = code(phi). All a,b,d are below c. Pointed separation at (a,a,c) gives not Q. Its second matrix conjunct, using phi -> not chi(a), gives S -> U(a, M(c,a) -> not chi(a)). The inherited negative-specialization lemma uses only direct membership rewriting, the equality witness and membership vacuity; it gives S -> (M(c,b) -> not chi(b)). Assuming phi and P, one gets M(c,a), then M(c,b) by E(a,b), contradicting chi(b). Hence phi -> (S -> not P). Necessitate this **closed theorem** at c and use Gamma(phi) to derive phi -> Q; not Q yields C by classical logic. No undischarged-assumption generalization occurs.

When a=b, reverse congruence is propositional. When d=a, direct rewriting moves M(a,b) or M(b,a) to M(b,b), and the previously established diagonal case moves M(b,b) to M(a,a). These are all the exceptional cases.

For neighborhood equality, z0=code(E(a,b)) is fresh. Gamma(E(a,b)) lifts the bidirectional rewrites to a common binder z0. Equality witnesses plus membership vacuity specialize the membership-only neighborhood matrices to any new z != a,b; commutation supplies vacuity of the antecedent at z. This does not assume the removed equality-vacuity rule.

### Finite bit soundness

Let Bit(s,z) := exists u,v [s=(2u+1)2^z+v and v<2^z]. PA proves Bit(s,z) -> z<s and hence not Bit(x,x). It proves bounded binary comprehension for arbitrary arithmetic formula theta by induction on the bound: keep s or add 2^n according as theta(n) is false or true. A fixed proof template with theta syntactically substituted yields a primitive-recursive proof supplier; PA verifies its lines uniformly in the formula code.

For a guarded separation instance c!=a,b and phi=T(c), when a!=b use matrix (Bit(x_a,z) or z=x_b) and phi[z/x_b], bounded by x_a+x_b+1. When a=b the inner binder changes both occurrences, so the first antecedent is Bit(z,z), which is false. The correct matrix is only (z=x_b) and phi[z/x_b]. The retained proof handles this subtle collision correctly.

### Constructor and stack aliases

I(0,0)=0 is a real alias. The soundness translation uses a fixed PA proof of T(I(A,B)) iff (T(A)->T(B)); it does not falsely assert literal syntax equality at zero. Cantor p(0,0)=0 is also real. Canonical stack tail strictly decreases at every positive code; popping zero returns truth with its fixed proof and pushing zero onto zero adds no live annotation. Both t and h must be annotated for the original Shift test t+h=1. All these points are handled by the baseline article.

### Physical internalization

A finite universal symbolic contract can support a PA proof only after its interpretation has been justified: table rows are primitive recursive, run-length self-loops by induction, and register-file excursions by induction on unary blocks/finite file. The accepted contracts need exact endpoints and positive durations, not merely an alternative 'halts or reaches next frame'. Under Con(PA), T+1 annotated command boundaries yield a run longer than any alleged T-step halt; determinism excludes the halt. This avoids needing an inverse parser for arbitrary intermediate tapes.

## New logical observation and source opportunity

Splitting G=not(V->Q) into two separately supplied heads V and not Q is propositionally conservative, exactly as splitting Gamma was. It potentially saves an implication-construction macro. But the existing trailing guard only clears the top: naively dropping the combining cons leaves an invalid membership-vacuity V on the stack when c=a or c=b. A correct implementation must guard both emitted heads, for example by moving the shared guard before the two-result emitter and emitting fixed zero placeholders when disabled. This changes stack selection ranks and needs an all-store proof compiler.

There is a modest guard weakening for the separation head alone: not Q(a,b,c) is PA-valid also at c=a != b. There the first separation-matrix conjunct is Bit(s,z)->(phi(z)->Bit(s,z)), a tautology, while the second requires only a subset of phi. A singleton of the distinguished b suffices when phi(b), and empty set otherwise. Thus c!=a is needed by V, not by separation. The c!=b condition remains essential: at c=b and true phi the point condition would demand self-membership Bit(s,s).

These are mathematically safe avenues, not a claimed sub-194 machine. Omitting V completely has no known completeness proof; diagonal vacuity alone cannot silently replace arbitrary membership vacuity.

## Transfer lessons from the other suggested projects

ConciseIPRA's value here is the method of replacing full interfaces by derived minimal ones and proving explicit proof translations. Its shorter checker cannot simply replace PA's checker: the current upper calibration uses full induction for arbitrary formula comprehension. The ZFC work contributes contextual folds, exact startup, protected-tail/all-store scheduler reasoning and positive simulation contracts. Equiconsistency with ZFC does not supply Con(PA) calibration.
