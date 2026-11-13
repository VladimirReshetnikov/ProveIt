# Independent review of the final guarded-register package

Reviewed on 12 November 2026:

- `output/ipra_guarded_register_2026-11-12/report.tex`
- `checker_work/guarded_j/checker_j.py`
- `analysis_mathematics/guarded_register.md`

The reviewed version is the **pure guarded** calculus: bodies are state-free
or literally successor-headed, and the only primitive arithmetic equations
are B and R+. Neither conditional Load nor Increment is primitive.

## Verdict

No critical mathematical gap or checker defect was found in this review.
The claimed whole-domain bi-interpretability is supported by the written
argument, conditional on the explicitly identified, pinned native-core
prerequisite. The report correctly distinguishes a written proof from new
proof-assistant verification and a matched checker improvement from the
requested corpus-wide minimization, which remains unmet.

This verdict is a mathematical/code review, not a machine proof of the
bi-interpretation or checker correctness. It does not turn finite tests
into a universal soundness proof.

## Arithmetic and formation

1. The state-free-or-successor-headed restriction is closed under
   capture-avoiding substitution. Substitution for an outer parameter cannot
   introduce the current bound state into a previously state-free body;
   the literal successor head survives substitution. The induction applies
   recursively to all nested J occurrences.
2. R+ with constant update g=t directly gives J(1;u.S(t))=t. Crossed
   transport of this equation along itself derives t=t. Thus the pure
   version has no residual dependency on the removed Load rule when
   establishing reflexivity.
3. The constant-instruction equations for f, W's three-cycle, and the
   definitions of Z, G, C and P have the stated endpoint equations. These
   derivations use B, R+ and equality only. In particular W cubed fixes
   zero while removing three successors; that is precisely the property
   used in G and C.
4. Conditional Load is admissible for a successor-headed body through
   successor injectivity, and for a state-free body through transport in
   f(S(n),-). Conditional Increment is admissible for a state-free body
   through f(n,0)=S(n); a successor-headed zero instruction produces the
   designated contradiction, from which selector transport gives every
   equation. Neither argument needs coverage or the later logical bridge.
5. The guarded iterator compiler uses the literal successor-headed body
   H(u)=S(C(u,a,S^2(h(P^2(u))))). Its invariant
   A(k)=S^2(P^2(A(k))) is a literal equation. R+ and the selector endpoints
   prove the successor step under that invariant. QI and QE therefore
   establish both initialized-iterator equations before coverage, general
   disjunction or a characteristic equality test is invoked.
6. The report correctly keeps passive parameters fixed during that
   induction and uses a fresh iteration variable.

## Logic and the ordinary realization

The native simulation preserves the six non-computation rules literally,
and the newly proved iterator equations simulate the other two. The logical
macro interface is schematic in arbitrary numerical terms; it does not
presuppose that a guarded J term already is a scalar-I term.

The appendix's gates and formula selector have the required endpoint
equivalences. Its implication and existential encodings use the base and
successor rows; the conjunction encoding accesses the two parity rows at
1 and 2. The numerical-cases construction supplies the coverage needed for
disjunction and universal elimination. The selector recursion decreases
maximum binder depth as stated.

The separate ordinary first-order realization explicitly includes both
coverage and (0=1)->bottom. This resolves the singleton-model problem that
would arise if an ordinary theory with independent bottom were claimed to
need neither. The native calculus still has only eight primitive patterns;
its designated contradiction and DI rule carry these roles in that
presentation.

## Interpretation composites

The reverse interpretation uses the fixed primitive-recursive update
C(h(u),S(u),P(h(u))). It maps the defined successor J(n;0) to the ordinary
successor by equation induction. B and R+ are sound under this reading.

After the native bridge, the source proves the unconditional reverse
recurrence. For a state-free instruction, this proof uses its now-derived
numerical coverage; for a positive instruction, R+ suffices directly.
Literal-equation induction proves uniqueness for every fixed recurrence.

The report applies external structural induction to each body with its
state variable free, then uses recurrence uniqueness for the enclosing J.
It expressly avoids substituting an equality under a binder that captures
the state variable or assuming an intermediate translated J body still
satisfies the guard. This supplies both term composites; the native logical
equivalences and structural induction supply both formula composites.
The domain and equality are unchanged, so the identity-graph claim follows.

## Strict checker

The `term` validator first validates both children of every J, and then
checks that replacing the bound state by zero while keeping all outer
indices fixed leaves the body unchanged, or that its literal head is a
successor. An ill-typed integer body that fails the first condition may
raise an indexing exception in the second condition; this is rejection
under the documented acceptance convention, not acceptance of bad syntax.

Both `j0` and `js` validate the **whole constructed J term**. The `js`
constructor wraps its supplied g in S(g), so its main body is guarded, while
the recursive validation still checks every J within g. It returns exactly
the R+ equation and has no hidden equation premise.

All remaining rules preserve the previous scoping invariant:

- simultaneous substitution preserves guards and the correct one-based
  indices;
- DE's reused D matrix has the correct y/x indexing under Q plus the fresh
  numerical scope;
- `subst(f,(0,),1)==f` holds exactly when the fresh parameter does not occur;
- DI's two simultaneous replacements and QI's successor replacement use
  the required outer shift;
- hypotheses arise only from already validated/formally constructed
  contexts;
- exact-integer validation excludes booleans, negatives and floats;
- the public goal is validated in the empty numerical scope.

No unchecked route for introducing an unguarded body was found. Induction
on successful evaluation gives the well-scoped, guarded, derivable-result
invariant stated in the report. Conversely each ideal finite rule tree has
the described certificate, subject to the separately stated finite Python
resource limits.

## Claim boundary and minor editorial point

The report states the 1041 / 1181 / 3467 matched measurement, its control,
and the much smaller existing compact profiles separately. It expressly
does not claim the requested global lower-envelope improvement or absolute
minimality. The source-retrieval threshold is disclosed rather than treated
as an exhaustive normalized-program lower-bound proof.

The equality-rules paragraph is correct but unnecessarily retraces two
unhelpful symmetry instances; the author already plans to shorten it to
the successful instance (major s=s, minor s=t, identity template). No
mathematical repair is needed there.

Packaging note: the suggested symmetry-paragraph simplification was applied
to the delivered report. No mathematical change was required.
