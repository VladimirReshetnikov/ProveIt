# Independent audit of the target-directed calculus T

Audited source: `math_work/target_closure.tex`; inspected implementation: `checker_work/target_checker.py`. The comparison calculus R is the incoming `ipra_uniform_progress/sections/new_theory.tex`.

## Verdict

The written equivalence proof is sound as stated. No circularity was found in the induction bootstrap, full transport proof, numerical substitution repair, or either elimination simulation. The result is exact equality of consequence relations on the full common Eq/Q/D language, not merely equality of standard numerical models or closed arithmetic consequences.

This establishes a local refinement of the R presentation. It does not beat the already existing witness-sensitive seven-rule checker in the matched implementation comparison and must not be described as a global minimum.

## Dependency check

1. I0 plus primitive equation transport derives reflexivity, symmetry, transitivity, and numerical congruence.
2. Dummy-witness DI followed by DE and Hyp derives QI. Its witness coordinate is unused, so the opened Q can be exported without violating DE freshness.
3. Literal target S(a) supplies direct progress Q E, E(a) |- E(Sa).
4. Literal target W(t)=I(0,t;u.0) is always nonsuccessor-headed. QE therefore takes E(0) to E(W(t)); I0 and equation transport give E(t). This anchored interface is proved before numerical substitution or compound transport.
5. QI plus the anchored interface derives contextual equation induction.
6. Numerical substitution is then admissible. Its only special case is an old nonsuccessor variable target becoming a successor after substitution: the translated minor is E(0), and the already-derived anchored interface supplies the new target. Literal successor targets remain successors under substitution.
7. Full transport is an external structural induction. Atomic Q uses direct progress; compound Q uses direct anchored QE; D uses the corresponding interface according to its strictly smaller matrix. No appeal to the same formula's transport appears recursively.

All parameter freshness requirements can be met by alpha-renaming. In the orbit simulation, the induction counter is fresh for Q E, E(a), a, n, and every passive parameter of E; a and n are held fixed throughout the induction.

## T to R

- Atomic successor target: use R's derived one-step interface, itself obtained from its orbit rule and the proved equality A(a,1)=Sa.
- Atomic nonsuccessor target: use R's orbit rule at source 0 and initializer t, then I0 and atomic transport.
- Compound target: use the same orbit specialization, then R's previously established full transport to remove the I0 redex. The report correctly identifies this dependency rather than assuming primitive compound transport.

All other rules coincide literally.

## R to T

- Compound orbit QE: T's compound rule can target the exact required term A(0,n), with the same zero minor.
- Atomic orbit QE: under Q E and E(a), equation induction gives E(A(k,a)). The base is I0; the step uses direct progress at A(k,a) followed by IS and equation transport. Instantiate k=n, then transport along A(n,a)=A(a,n). The latter commutativity theorem uses only already-derived equation induction.

The induction invariant E(A(k,a)) remains a literal equation. No induction on a quantified or compound formula is introduced.

## Full-language bridge

The target section accurately retains the old progressive/conditional root-sensitive reading. Its maps F and J match the incoming R theorem. In particular, P pads equations to compound formulas before a native binder is translated, and J preserves compound roots. The incoming R proof establishes both composites using homogeneous binder congruence and atomic closure normalization before extending ordinary logical macros to all mixed formulas. Thus the T/R identity comparison transfers both formula composites and the inherited actual-equality, whole-domain numerical identity graphs.

Homogeneous congruence must remain qualified: a progressive closure of an equation need not agree with a conditional closure of an equivalent compound formula.

## Implementation inspection

The changed `use` branch in `target_checker.py` first validates the target term and derives a Q major. It chooses `target[1]` exactly when the matrix is an equation and the well-formed target is a successor constructor; otherwise it chooses zero. The zero term short-circuits before indexing, and every nonzero well-formed target is a list. The required minor and returned target instances match the mathematical rule exactly.

The de Bruijn operations and all remaining rules are inherited unchanged from the matched R checker. DE opens x while keeping y under Q; DI removes x using a lifted witness and then opens y at a fresh variable. These binder positions agree with the declared y-at-0/x-at-1 convention.

## Separate compact-core clarification

For the lexical checker based on `len(a) % 2 == u`, the falsy exact-int/list inputs for u are precisely integer 0 and the empty list. A logical DI packet uses u=0 for progress at an equation matrix and u=[] for cases at any matrix. Compound matrices have odd arity and therefore use cases also at u=0. Nonzero integers and nonempty lists are truthy and enter the computation branch instead of DI. Accordingly this compact kernel retains Choice-DI with both choices at every witness; it is not the guarded, root-deterministic T/R calculus or the witness-sensitive W calculus. Its public Eq/Q/D grammar remains unrestricted.
