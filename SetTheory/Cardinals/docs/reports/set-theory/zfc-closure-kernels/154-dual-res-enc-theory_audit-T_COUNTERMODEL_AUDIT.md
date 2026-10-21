# Independent audit of the full T+B countermodel

## Finding

I find the countermodel in `formalism_work/t_countermodel.md` sound for the
**complete literal seed-K numerical calculus** after replacing its original
rho6 row by T, by its apparent dual B, or by both:

\[
 T(a,A)=Q_aA\to A,\qquad
 B(a,A)=A\to Q_a\operatorname{Ex}_a A.
\]

The proof establishes inside ZFC that the changed calculus cannot derive
its designated code F=1. This is stronger than a logical-row
non-derivability example. It addresses the private-label/matrix-code coupling
of the actual K emitter, all allowed parameter collisions, and all retained
numerical rules. Subject to consistency of ZFC, the resulting theory cannot
have its consistency provably equivalent in ZFC to Con(ZFC).

The proof is mathematical, not fully formalized in Rocq. I independently
checked its semantics and added a source AST checker that binds its formulas
to the archived native definitions. No remaining mathematical gap was found.

**Scope:** This countermodel retains the original primitive positive-equality tag. It does not apply to the later negative-equality system `Eq = Neg(J)` with dual B, whose translated fragment has a separate positive calibration proof.

## 1. Exact source binding

The audited source is the `K221F` seed calculus in the repository's
`k225-formal/rocq/rocq-extension/coq/221` directory, together with its pinned
`K230L.Codes230` and `K230S.KCode230` dependencies. The K220 and K219 sources
retain this calculus.

`audit_t_native.py` independently parses prefix applications and parentheses
in the literal Rocq terms. It expands only the named relative-negation,
existential, vacuity, and seed helpers. It compares the resulting trees to
the formulas used below. Its receipt, `audit_t_native_receipt.json`, records
these source hashes:

| File | SHA-256 |
|---|---|
| Codes222.v | `e87e59a8f444bb037374bc68985d2c5eee15505354f6235ffaafc5cf587772b4` |
| Codes230.v | `ab41044fd2feb34cf595c6ea2d174c768c2c6cde14204d03dbee77c37d8f618e` |
| KCode230.v | `2a5fd8a170dedfd732347e0da969230cfc9321d3d8f71729711f5cf3b12f045e` |
| Thm222.v | `4f6fea9deab56bc70f33f09fc399362d159ee73333a1ccb8b0fbb38c686c8f0f` |
| Enum222.v | `1ca83534d485355410f8879877157644a9d0888e86a437660942ff0300e787e8` |

The check passes for all seven inherited rho definitions in use, growG,
vrel, nks222, bundle222, all twelve complete inductive rule clauses, the
constructor declarations, and the enumerator's gate. This is a check of
literal syntax and source coverage, not an automated proof of soundness.

## 2. Numerical decoding and coordinate freshness

The actual pairing is
\(P(a,b)=\operatorname{tri}(a+b)+b\), with the four constructors
\(I=4P\), \(R=4P+1\), \(Q=4P+2\), \(E=4P+3\).
The arithmetic inequalities \(a,b\leq P(a,b)\) show that every field of a
positive code n is at most \(\lfloor n/4\rfloor<n\). All positive numerical
codes therefore have a well-founded recursive interpretation, including
codes that would be unusual in an ordinary presentation of logic.

Code zero requires an explicit clause. Set its truth value to true. This
respects the only constructor equation at zero, \(I(0,0)=0\), because
true implies true. Hence material implication is the semantics of I(a,b)
for every pair of numerical arguments, including the exceptional zero pair.
The `W_true` rule is sound.

By induction on positive code n, every atomic label and every bound label
appearing in its decoded formula is strictly below n. Thus the matrix with
numerical code c does not mention coordinate c at all. Its truth at either
time is independent of that coordinate. This includes c=0, which is
constant true, and c=1=R(0,0), which has only label zero. No renaming or
ordinary first-order substitution theorem is used here.

The same arithmetic gives \(RCode(a,b)=4P(a,b)+1>\max(a,b)\), including
a=b=0. Its residue is always one modulo four. These two facts are exactly
what the merged equality row requires in the proposed model.

## 3. Set construction and accessibility relations

Inside ZFC let \(\kappa=\omega_1\), \(D=V_\kappa\), and
\[
 S_j=\{\omega\cdot\alpha+j:\alpha<\omega_1\}\quad(j\in\omega).
\]
Every ordinal in S_j is countable and hence belongs to D. Ordinal division
by omega shows the S_j are pairwise disjoint. Each is unbounded in rank
below omega_1. For B in D and distinct a,b, choose z in S_a above the rank
of B; then z is neither a member of B nor a member of S_b. The S_j are
ambient sets, and are not claimed to be elements of D.

Elements of D have countable *rank*, and can have large cardinality. The
argument needs closure under singletons, transitive closure, and countable
rank segments, not countability of the underlying sets. These closures
follow from the definition of V_omega_1.

Worlds form the set \(\{0,1\}\times D^\omega\). At time zero, R and E have
ordinary membership and equality semantics. At time one, every E is false,
R(0,0) is true, and every other R(i,j) is true exactly when
\(v(i)\in v(j)\) or \(v(i)\in S_j\). The designated F=R(0,0) is false at
time zero by Foundation and true at time one.

Q_n varies coordinate n over D. It preserves time for n=1 modulo four;
otherwise it also permits advancing from time zero to time one. All these
relations are reflexive. Their coordinate factors commute, and their time
factors are either identity or the same reflexive two-point order. Hence
they commute, including when the two quantifier labels coincide.

There is no circularity in satisfaction. For each code, the required
complement, intersection, or universal inverse image is a subset of the
set of worlds. Recursion on the numerical code gives a set-valued
satisfaction function. All model objects and this recursion are available
in ZFC without assuming the existence of a model of ZFC.

## 4. Complete retained-row audit

Write \(N(A)=A\to F\) and
\(\operatorname{Ex}_a A=N(Q_aN(A))\). The literal rows and their reasons
for validity are as follows.

| Source row | Literal formula | Verification |
|---|---|---|
| rho1 | \(\operatorname{Ex}_a E(a,b)\) | Initially, reset coordinate a to the original value of b; for a=b it is already equal. Terminally the outer N is true. |
| rho2 | \(Q_a(B\to C)\to(Q_aB\to Q_aC)\) | Ordinary universal distribution over the successor relation. |
| rho3 | \(E(a,b)\to(R(c,a)\to R(c,b))\) | Actual equality initially; false equality antecedent terminally. |
| rho4 | \(Q_aQ_bC\to Q_bQ_aC\) | Commuting successor relations, with no distinct-label assumption. |
| rho5 | \(E(c,a)\to(R(c,b)\to R(a,b))\) | Actual equality initially; false equality antecedent terminally. |
| growG | \(E(c,a)\to(E(c,b)\to Q_{RCode(a,b)}E(a,b))\) | The numerical binder is fresh for a,b and preserves time. |
| rho8 | \((((C\to U)\to A)\to((A\to C)\to(B\to C)))\) | Material-implication tautology. If C is true the consequent is true; if C is false the row reduces to \(A\to(A\lor\neg B)\). |
| vrel | \(R(a,b)\to Q_cR(a,b)\), c distinct from a,b | Initial membership is contained in terminal membership; both relations depend only on a,b. |

The vrel argument also covers a=b=0: the initial antecedent is false, and
the terminal atom is the constant true exception. The exception cannot
occur in either atom R(c,a), R(c,b) of the subset guard, because the source
gate excludes c=a and c=b.

Modus ponens is sound by the uniform I constructor law established above.
Theorem generalization preserves validity at all worlds. This accounts for
all three non-axiom constructors `W_true`, `W_mp`, and `W_gen` as well as
every retained axiom constructor in `Thm222.v`.

T is valid by reflexivity. For B, suppose A is true at (0,v). From any
initial Q_a successor, coordinate a can be reset to its value in v, giving
an initial existential witness for A. At any terminal successor Ex_a A is
automatically true because F is true. Terminal starting worlds satisfy B
for the same reason. This proof permits arbitrary nested quantified A and
does not assume a conventional first-order interpretation.

The original rho6 is excluded for a precise reason: at a terminal world
its antecedent \(\operatorname{Ex}_a Q_aE(0,0)\) is true, while its final
unnegated E(0,0) is false. Therefore the new model does not inadvertently
validate the original calibrated calculus.

## 5. Literal K expansion and the terminal-world check

The parser verifies exactly the following terms, with the symbol chi
standing for the *actual code c* rather than an independently chosen code:

\[
\begin{aligned}
r&=R(b,c), &s&=Q_c(R(c,a)\to R(c,b)),\\
w&=Q_b(\chi\to N(Q_b(\chi\to N(r)))),\\
u&=Q_a(s\to w),\\
h&=Q_b(r\to N(Q_a(\chi\to N(u)))),\\
\mathrm{nks222}&=Q_c(h\to N(w)),\\
\mathrm{bundle222}&=N(V\to\mathrm{nks222}).
\end{aligned}
\]

At terminal worlds N is constantly true. It follows directly, in order,
that w, u, h, and the complete bundle are all true there. Every terminal
branch introduced while computing w, u, h, and the outer seed existential
is therefore a true test. The subset guard s is the only surviving place
where extra terminal tests can matter initially.

This observation justifies eliminating those terminal branches; it does
not use terminal worlds as existential witnesses. In particular,
\(h\to N(w)\) is true terminally, so its failure, required by the initial
outer relative negation, must occur at time zero.

For distinct a,b, freeze other coordinates and put x=v(a), y=v(b), C=v(c).
Freshness of c yields a relation chi_0(x,y) independent of C. Direct
Boolean expansion gives

\[
\begin{aligned}
 W(x,C)&=(\exists y\,\chi_0(x,y))\to
                  (\exists y\in C\,\chi_0(x,y)),\\
 U(y,C)&=\forall x\,[s_0(x,y,C)\to W(x,C)],\\
 H(C)&=\forall y\in C\,\exists x\,[\chi_0(x,y)\land U(y,C)],\\
 \mathrm{Seed}_0&=\exists C\in D\,[H(C)\land W(v(a),C)].
\end{aligned}
\]

I independently checked the quantifier scopes in this expansion against
the literal tree. In particular, the inner Q_a of u removes its dependence
on the surrounding input coordinate. The draft's symbolic Boolean checker
is useful corroboration, but the displayed identities and terminal checks
are the proof for arbitrary domains.

## 6. Full matrix-code case analysis

### Private label c not congruent to one modulo four; a distinct from b

The Q_c in s permits a terminal test. Select z in S_a outside v(b) and S_b
and assign it to coordinate c. The terminal R(c,a) is true from its marker,
whereas R(c,b) is false. These atoms cannot be the special R(0,0) by the
gate. Thus s_0 is false for every input and output assignment, and U is
always true.

If the seed has no chi_0 output, use C=empty. Otherwise choose an output y
of the seed and use C={y}. The seed then both meets its request and
supports the only container member. This applies to every non-membership
matrix, regardless of internal modal structure.

### Private label c congruent to one modulo four; a distinct from b

Here the numerical decoder forces chi to be the *single atomic formula*
R(i,j). This is the essential use of the private-label/matrix-code coupling.
Its initial meaning is ordinary membership, and Q_c preserves time, so
s_0(x,y,C) is exactly x subseteq y.

If this atom depends on at most one of a,b, an empty or singleton container
works. For an output predicate, take empty if no output satisfies it,
otherwise a singleton of one witness; W then holds at every input. For an
input predicate, take empty if the seed does not satisfy it, otherwise
any singleton; in the latter case every positive input has an output and
the seed supports the sole member. Constant predicates are included.
Repeated endpoints i=j make the atom false initially by Foundation.

The only remaining endpoint arrangements are (i,j)=(b,a) and (a,b):

* For chi_0(x,y) meaning y in x, define
  \(T_0=\mathrm{seed}\), \(T_{n+1}=\bigcup T_n\), and
  \(C=\bigcup_{n<\omega}T_n\). Thus seed is a subset of C and C is
  transitive. Each y in C is supported by {y}. If x is a subset of such y,
  then x is a subset of C; any nonempty x has a member in C, exactly its
  required output. The rank of C is at most the seed's rank, so C is in D.
* For chi_0(x,y) meaning x in y, choose a countable limit
  \(\beta>\operatorname{rank}(\mathrm{seed})+1\) and set
  \(C=V_\beta\setminus\{\varnothing\}\). The seed has output {seed} in C.
  Every y in C is nonempty and hence supported by some x in y. For any
  x subseteq y, rank(x) is at most rank(y), so the limit property gives
  {x} in V_beta and hence in C. This is the required output containing x.
  Finally C is in D because beta+1 is still countable.

All endpoint coincidences of an atomic matrix fall into these cases.
Neither argument asserts that D satisfies full K or full ZFC.

### Coincident input and output labels

If a=b, treating the two appearances as independent coordinates would be
invalid. The literal s is instead a universal identity, hence true. At
time zero w has no free occurrence of the common coordinate, and u=w.
Let p be the resulting unary matrix truth predicate. If p has no witness,
choose C=empty. Otherwise choose C={y} for one witness y. Then w=u=true.
Every member of C has a p-witness, so h=true as well. This verifies the
physical-coordinate case directly, for all residues of c.

Code zero and code one introduce no omitted case. Zero is constant true;
one is F, initially false. The source gate returns code zero whenever c=a
or c=b, so these disallowed private-label collisions are also covered by
`W_true` rather than being silently included in the K argument.

## 7. Internal soundness and scope of the conclusion

The model, assignment space, numerical satisfaction function, axiom
verification, and induction on finite proof trees can all be constructed
within ZFC. Every axiom is true at every world; both inference rules
preserve this property; F is false at an initial world. Therefore ZFC
proves each of Con(C_T), Con(C_B), and Con(C_T+B).

If ZFC is consistent, it cannot also prove any of these consistency
statements equivalent to its own consistency, by the second
incompleteness theorem. This rules out the specific proposed T and dual-B
replacements under the user's equiconsistency requirement, even though the
user allows nonstandard numerical semantics and arbitrary junk codes.

The audit does not address other quantifier fusions, new propositional
rows, altered native coding, or modified K guards. Those changes require
their own calibration or countermodel. No state reduction is claimed by
this negative result.
