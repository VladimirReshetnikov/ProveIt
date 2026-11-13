# Independent audit of raw guarded deterministic introduction and fusion

## Scope

I reviewed `mathematical_reduction/raw_guarded_bootstrap.tex` against the incoming guarded-core specification and the incoming evaluation-discharge calculus. I found no mathematical gap in the bootstrap as currently stated, provided the accompanying pure-equational predecessor construction proves its advertised identities. The observations below are important to retaining a noncircular proof.

## Exact matcher deletion

Delete the literal naming-matrix branch from the incoming deterministic selector and keep only newest parameter, or 0 in empty scope. This is a genuine change beyond the incoming parameter-introduction archive: that archive already has unconditional newest selection, but on fully normalized counter-aware recursors. The present theorem keeps the raw iterator language and raw substitution of the guarded system.

The packet

    A(r) = D_{x,v}(C(v,0,C(r,0,Sx)) = C(v,0,r))

is canonical. `A(0)` is uniformly provable at any selected witness. In the proof of `D_{a,r} A(r)`, the outer compound introduction allocates fresh newest z, so the inner introduction of `A(Sz)` selects z and has an unconditionally true successor row. Heredity applies to this WHOLE recipe, not to an arbitrary finished proof of `A(Sz)` under an unrelated parameter order.

In the clause language there is no Q-valued intermediate formula. To get `A(St)`, open the outer D, retain `[A(0); r.A(r)]`, regenerate `A(0)` in that extended scope, Use at `St`, and discharge the dummy opening. Open `A(St)` at b, use its true zero row and row 1, and obtain `Sb=St`. The equational predecessor then gives b=t.

## Hereditary replacement

The hereditary donor is regenerated at each leaf of a fixed receiving proof. Receiving numerical scopes remain unchanged, so all newest-witness tests remain unchanged. This justifies cut with hereditary donors without assuming numerical weakening or cut for arbitrary finished restricted proofs.

The equational-source embedding is strong enough: its induction hypothesis quantifies over ALL term substitutions on the source proper subproof. Thus the guarded induction construction may regenerate the source step at 0 and at Sw. It does not substitute terms into a finished target derivation. This is the essential reason the arithmetic bootstrap precedes naming without circularity.

## Three-family raw fusion

The evaluator has two arithmetic cases and identity fallback:

    rho_{s=t}(I(0,s;u.h)=r) = (r=t)
    rho_{I(c,a;u.h)=t}(I(Sc,a;u.h)=r) = (r=h[t/u])
    rho_E(F) = F otherwise.

With guarded Eq/D formulas, an explicit initial universal-reflexivity clause R, deterministic root-mode introduction, Use, and evaluate-and-discharge, the full guarded calculus can be recovered first at the level of hereditary proof families.

### The correct dummy major

The incoming dummy `D(0=0)` is NOT a canonical guarded formula. Replace it by

    Theta = D_{x,y}(I(y,0;u.0)=I(y,0;u.0)).

Its introduction uses the deterministic witness, whose coordinate x is unused. Its successor row is proved by Use of R at the corresponding iterator term. No evaluation or computation theorem is used in this proof. This fact requires the explicitly counted R clause; do not state it for arbitrary contexts lacking R.

### Recovering Open and Eval

For ordinary Open, take the given D major and use a freshly regenerated Theta as the auxiliary branch formula E. Since E is compound, the evaluator selects identity and exports the intended F. Do not weaken a finished copy of the original D major into its own branch.

For either arithmetic Eval, use Theta as major and regenerate the two hereditary equation-premise families inside its fresh branch. Evaluate-and-discharge yields precisely the desired arithmetic conclusion. This construction initially proves Eval for hereditary inputs; arbitrary finished proof weakening remains unavailable until later structural completeness has been established.

### Recovering equality and computation

The two computations follow from Eval on reflexivities. Joining follows with the zero frame J_s=I(0,s;u.0): use `s=t` and Refl(J_s) to get J_s=t; use `s=r` and that equation to get t=r. Symmetry and transitivity follow.

To obtain term transport from s=t and h(s)=r, use J=I(0,s;u.h) and K=I(S0,s;u.h). Eval and the zero computation give K=h(s), hence K=r by joining. Zero Eval gives J=t, and successor Eval gives r=h(t). These proof families are uniform in the actual receiving scope.

### Full formula transport

Induct on D-depth of the formula template. Equations follow from term transport. For F(v)=D_{x,y} B(v,x,y), open F(s) at the actual newest b and reintroduce F(t) at that same b.

If B is a guarded equation, its source zero row B(s,b,0) is a computation theorem. The retained source clause therefore gives B(s,b,Sz) without using the target progress hypothesis. Equation transport gives B(t,b,Sz), which is the required progressive target.

If B is compound, the target case assumption B(t,b,0) is transported to B(s,b,0) by the induction hypothesis. Use of the retained source clause gives B(s,b,Sz); transport back gives B(t,b,Sz). The conclusion does not mention b, so the derived Open discharges it.

All target introductions in this proof use either an unused witness coordinate or the just-opened newest b. There is no invocation of arbitrary-witness introduction or naming. Thus full transport is available before the arithmetic/name bootstrap, and the three-family composition is noncircular.

## Executable-scope qualification

The strict guarded checker has a separate numerical `scope` parameter; its clause context and numerical scope are correctly independent. The incoming compact raw three-family checker instead uses `len(g)` as its scope counter. For ordinary closed certificates, every binder adds one local clause and one numerical parameter, so the two counts coincide on reachable runs. An implementation or completeness argument must preserve that invariant. Arbitrary hypothetical context extension in hereditary metatheory should not silently be equated with numerical scope extension. The clearest new checker can expose numerical scope separately; a shorter checker can retain the old count only with an explicit compilation argument for binder-generated contexts.

## Validation status

These are written metatheoretic arguments, not a new Lean proof. Finite certificate execution validates examples and the implementation's local rule checking; it does not mechanically establish successor injectivity or bi-interpretability. The inherited Lean equivalences supply the existing scalar/native/iPRA bridge once the new comparison theorem has been proved.


## Final assembled-paper review

The final review found two side conditions requiring explicit wording: hereditary donors retain their hypotheses after deletion of the distinguished receiving assumption; the equation-induction eigenparameter is fresh for all fixed invariant parameters. Both corrections were incorporated into the paper. No other concrete mathematical error was identified in that review. This is written review, not proof-assistant verification.
