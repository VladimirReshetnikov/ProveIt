# Addendum: primitive recursive verification versus hidden evaluation

## Verdict

The proposed stronger distinction is correct for the **mathematical verifiers on unbounded finite syntax**, with ordinary execution-resource limitations abstracted away:

1. Verification of a bounded-local-conversion certificate is primitive recursive.
2. Acceptance by the particular inherited weak-head checker, on its interface allowing explicit open-sequent contexts, is not primitive recursive.

The second statement already holds on a family with one fixed context, one fixed conclusion, a single QE instruction, and only the closed numerical term hint varying.

This is a genuine mathematical distinction between these two verification mechanisms. It is not a claim that ordinary iPRA verification was previously non-primitive-recursive. The earlier raw native kernel already has a primitive recursive proof relation. It also does not establish a source-size minimum or prove that every normal-form-based certificate format has a non-primitive-recursive verifier.

## 1. Exact interface reduction

Let C(y,a,b)=I(y,a;u.b), with u unused, and define the fixed equation matrix

    B(y) := C(y,0,0) = C(y,0,1).

The inherited weak-head checker leaves B(y) unchanged, because each outer iterator has the neutral variable y as its counter. Thus B is a permitted normalized matrix, and Q_y B(y) is a permitted closed context formula.

For any closed, well-scoped raw numerical term t, use the certificate:

    variables = 0
    context   = [Q_y B(y)]
    goal      = 0=1
    proof     = [qe, B, t, null, null].

Its matrix and goal pass syntax validation. Its term hint t is checked as raw syntax, so it need not be normalized. The goal is neither an initial hypothesis nor a reflexive equation; hence the checker reaches the QE branch.

That branch first checks whether the normalized substitution instance B(t) equals the goal 0=1. Weak-head evaluation of a closed numerical term exposes zero if its denotation is zero, and exposes a successor if its denotation is positive. Consequently,

    normal(B(t)) = 0=0,  if value(t)=0;
    normal(B(t)) = 0=1,  if value(t)>0.

In the positive case, the remaining premises succeed immediately: the major Q_y B(y) is in the retained context, and B(0) normalizes to 0=0, which is reflexive. The `null` proof fields are therefore legitimate leaves under the supplied implementation. In the zero case the required endpoint comparison fails.

Thus this exact certificate is accepted if and only if t denotes a positive number. The final executable experiment, including nontrivial iterator terms denoting both zero and a positive number, is recorded in `normalization_boundary.json`: twelve terms, each checked in ordinary and optimized Python, for twenty-four CLI executions. These examples check the encoding and branch behavior, not the universal non-primitive-recursiveness theorem.

The fixed context is inconsistent in the ordinary arithmetic interpretation: its closure would imply B(1), which is 0=1. This does not invalidate the reduction. An open-sequent checker is permitted to receive inconsistent assumptions, and the result concerns the complexity of recognizing this particular certificate, not whether the fixed sequent has some proof. Indeed the sequent already has a proof independent of t.

## 2. The universal nonzero predicate is not primitive recursive

Use any standard primitive recursive coding of finite raw terms. The following elementary syntactic functions and predicates are primitive recursive:

* being a well-scoped term with at most the one free variable x;
* producing the raw numeral S^n(0);
* capture-avoiding substitution of that numeral for x;
* building the certificate displayed above.

Assume, for a contradiction, that the inherited verifier's acceptance predicate A were primitive recursive. Define the Boolean predicate

    U(e,n) = A(certificate(t_e[S^n(0)/x]))

when e codes a valid unary raw term t_e, and U(e,n)=0 on invalid codes. The reduction proves

    U(e,n)=1  iff  value(t_e(n))>0.

Therefore U is a primitive recursive universal nonzero predicate for all unary scalar terms.

Now put d(n)=1-U(n,n). It is a primitive recursive Boolean numerical function. By the already established scalar-iterator representation theorem, there exists a unary scalar term t_d computing d on all natural numbers. Let e_d be its code. Then

    U(e_d,e_d)=1
        iff d(e_d)>0
        iff 1-U(e_d,e_d)>0
        iff U(e_d,e_d)=0,

a contradiction.

Only the existence of a scalar term for each unary primitive recursive function is required. **No primitive recursive universal compiler hypothesis is needed** for this diagonal argument. A primitive recursive compiler could also be supplied, but it would add an unnecessary proof obligation.

Accordingly, even the one-QE fixed-context slice of the inherited acceptance relation is not primitive recursive. Any total algorithm recognizing exactly that idealized acceptance relation has a non-primitive-recursive characteristic function.

## 3. Why bounded local verification is primitive recursive

The new verifier contains no operation that evaluates an arbitrary iterator term to a normal form. Its nonrecursive work consists of finite syntax checks, variable-index arithmetic, equality and membership tests on finite trees, raw substitution and shifting, and at most one explicitly selected contraction at counter-spine depth at most three. Each operation is primitive recursive on finite syntax codes.

The recursive proof check is controlled by the supplied proof tree. Every recursive `prove` call receives a proper child proof field of the current proof. There is no call that manufactures a new proof obligation and searches for a certificate, repeats a proof branch according to the numerical denotation of a term, or loops until an iterator reaches a normal form. Thus the number of proof-node visits is bounded by the number of nodes in the finite input certificate.

Intermediate syntax can grow, so a bare statement that proof depth is bounded would be too quick. Here that growth is also primitive recursively bounded. A raw substitution replaces finitely many occurrences of one variable by a finite supplied term; its tree-size growth has a fixed primitive recursive bound in the sizes of the input trees. Shifting preserves tree shape. A one-step iterator contraction is one such substitution. Context extension and every other rule construction have fixed primitive recursive size bounds as well.

Choose one monotone primitive recursive bound H that dominates the finite collection of per-step operations, including their output sizes and loop bounds. If N bounds the input size and initial numerical indices, then iterating H at most N times bounds every intermediate state of a proof traversal. The function

    H^0(N)=N;  H^(k+1)(N)=H(H^k(N))

is primitive recursive in (k,N). A depth-first traversal with its explicit stack, bounded by the input proof size, can therefore be simulated by primitive recursion. This yields a primitive recursive characteristic function for acceptance or rejection of finite certificates.

The same argument permits malformed inputs: syntax and field-shape checks are primitive recursive and reject them. It also permits early hypothesis/reflexivity success and arbitrary unused proof fields. Those do not introduce semantic computation.

## 4. Exact strength of the conclusion

This gives a useful additional theorem beyond equivalence of provable sequents:

> The bounded-local-conversion presentation has a primitive recursive certificate relation. The inherited weak-head verifier on its open-sequent interface does not. The latter implicitly performs semantic computations whose complexity is not bounded by a single primitive recursive function of the certificate code; the former requires those computations to be exposed as finite proof steps.

This is a tradeoff between verification and proof representation. The local format can require longer certificates. No claim is made that it recognizes the same raw certificate strings as the weak-head program; it proves the same raw sequents through the established equivalence theorem.

The result does not imply that the local proof relation is elementary or polynomial time. Those stronger bounds have not been proved here. Nor does it show that the local checker has fewer source tokens, AST nodes, or bytes than the global frontier.

## 5. Necessary idealization concerning executable Python

The theorem concerns the mathematical algorithms implemented by the two sources, with unbounded finite syntax, integers, and recursion. Literal CPython execution imposes a recursion limit and can exhaust memory; its parser may also impose input-size restrictions. Those implementation limits reject some mathematically valid certificates and can truncate the evaluation relation.

Consequently, do **not** state that the exit-status predicate of a fixed, resource-limited CPython process is itself proved non-primitive-recursive. Use wording such as "the idealized weak-head verification relation" or state the unbounded-syntax convention once. The same convention is already necessary whenever these finite implementations are called complete proof checkers for an infinite theory.

## Recommended report placement

Place this theorem after the raw-sequent equivalence and before the source measurements. It gives the operational simplification a precise mathematical meaning, while keeping it separate from the unmet global source-size objective.
