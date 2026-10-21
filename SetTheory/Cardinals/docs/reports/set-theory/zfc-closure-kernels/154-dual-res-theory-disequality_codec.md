# Disequality atoms and a parity-only contradiction detector

## Exact change of formalism

Keep native implication, membership, quantification, relative negation,
truth, and falsum:

\[
I(a,b)=4P(a,b),\quad R(a,b)=4P(a,b)+1,\quad
Q(a,b)=4P(a,b)+2,\quad F=1,\quad N(A)=I(A,F).
\]

Interpret the remaining primitive constructor as **disequality**:

\[
J(a,b)=4P(a,b)+3\quad\text{means}\quad v_a\ne v_b.
\]

The equality formula used by the logical rows is now

\[
E'(a,b)=N(J(a,b))=I(J(a,b),F).
\]

Replace every old equality constructor in rho1, rho3, rho5, and G by E'.
There are six such builder occurrences in the native AX emitter: one each
in rho1, rho3, and rho5, and three in G. No other logical row, the membership
vacuity/seed-K bundle, or theorem rule changes. In particular, primitive tag
3 codes remain legitimate arbitrary formula parameters; they are not
silently treated as malformed or prohibited input.

Call the resulting numerical theory `Cneq`. Then

\[
\mathrm{ZFC}\vdash
\operatorname{Con}(Cneq)\leftrightarrow\operatorname{Con}(\mathrm{ZFC}).
\]

This is a formalism calibration. It does not by itself certify any compiled
source or transition table.

## Soundness and the parity detector

In any set-coded model of ZFC, interpret each positive native code by its
outer residue and recurse on its smaller formula fields. Code 0 denotes
truth, respecting I(0,0)=0. Interpret J as actual disequality, R as the
model's membership, Q as universal quantification, and I as material
implication. Foundation makes F=R(0,0) false. Therefore E' is exactly actual
equality under every assignment, and every changed logical row has the same
truth conditions as its old counterpart. All unchanged rows and bundle
instances remain valid. MP and GEN preserve global validity.

Every odd code is either a membership atom R(a,b) or a disequality atom
J(a,b). Neither is globally valid. Assign the same object to both labels:
membership is then false by irreflexivity, and disequality is false by
identity. The argument includes coincident labels. Consequently a sound
theorem enumerator may halt on **any odd cached code**, and every such halt
implies inconsistency of ZFC. Completeness is preserved because F=1 is one
of those odd codes.

This claim is stronger than merely saying all odd codes are false under
some specially selected assignment: for each possible odd theorem there
is a refuting assignment in every ZFC model, which contradicts the global
theorem invariant.

## Full logical completeness still holds

The existence row should be emitted in its simplified form

\[
\rho'_1(a,b)=N(Q(a,J(a,b))).
\]

Indeed the literal replacement of old rho1 is

\[
\operatorname{Ex}_a E'(a,b)
=N(Q(a,N(N(J(a,b))))).
\]

The unchanged rho6 and rho8 prove double-negation introduction and
elimination for every numeric formula. From any theorem A->B, GEN and
rho2 give Q_a A->Q_a B, and classical contraposition gives N(B)->N(A).
Applying these facts in both directions proves the equivalence of the two
displayed rows. This argument uses neither rho1 nor equality nor K, so
there is no circular existence or specialization assumption. Consequently
the simplified row may replace the literal translated row in every
completeness and soundness argument below.

Define a named-formula translation tau' exactly like the baseline tau,
except

\[
\tau'(\operatorname{Weq}(a,b))=E'(a,b).
\]

The core propositional derivations in `CD222.v` and `Prop222.v` use rho8
and rho6, so they are unchanged. In particular, explosion and double
negation elimination are available for every numeric formula code,
including raw J atoms.

The proofs in `G222.v` are uniform in the equality formula. Replacing
`weq(a,b)` by E'(a,b), the changed G and rho1 rows give the same derivations
of:

* reflexivity E'(a,a);
* the special helper E'(a,b) -> Q_R(a,b) E'(a,b);
* the Euclidean equality row E'(c,a) -> (E'(c,b) -> E'(a,b)).

The existential monotonicity and specialization steps use only
propositional logic, rho2, rho6, MP, and GEN. They never require that the
equality formula itself have a particular outer code tag.

The unchanged bundle supplies all membership-vacuity instances. Therefore
the induction in `Interp222.lprov224_thm222` transfers with tau' in place
of tau: every theorem of `lprov224` translates to a theorem of Cneq. The
existing theorem `L224E.lprov_th` is a purely named-formula theorem and does
not mention the numerical equality constructor. Composing them yields

\[
\operatorname{lprov}(A)
\Longrightarrow Cneq\vdash\tau'(\operatorname{th}(A)).
\]

There is an especially useful simplification. `th` replaces **every**
Weq atom by `Eind`, whose definition contains only membership, implication,
negation, and quantifiers. A structural induction thus gives

\[
\tau'(\operatorname{th}(A))=\tau(\operatorname{th}(A))
\quad\text{for every named formula }A.
\]

So the final full-first-order interpretation has exactly the same numerical
formula codes as before. Although the intermediate equality axioms are
recoded, the interpreted theory used for the K/ZFC bridge is unchanged.

## The K/ZFC completeness chain requires no new code-renaming lemma

`Complete222.v` uses the interpreted proof predicate

\[
Q(A)\quad\Longleftrightarrow\quad
\text{the calculus proves }\tau(\operatorname{th}(A)).
\]

The preceding section gives the same logical closure for that identical
predicate, now using Cneq proofs. The private seed code is

\[
c_\phi=\tau\bigl(\operatorname{th}
   (\neg\neg\operatorname{tr}_{\eta}\phi)\bigr).
\]

It is numerically unchanged, as is the emitted seed/vacuity formula at
roles 1 and 3. Its bound c_phi>3 and private-label freshness are therefore
the old syntactic lemmas verbatim. No assumption is made that recoding an
arbitrary native formula preserves the matrix/private-binder identity.
That potentially troublesome recoding is unnecessary because the actual
interpreted seed matrices contain no primitive equality atoms.

The remaining steps of `Complete222.v` use only this logical closure and
the unchanged seed instances. They give

\[
\mathrm{ZFC}\vdash\bot
\quad\Longrightarrow\quad Cneq\vdash1.
\]

More precisely, the old finite-proof transformation through the ordinary
K0 theory is reused with the new native logical derivations substituted.
It is effective and its proof is formalizable in ZFC. Conversely, assuming
Con(ZFC), the completeness theorem provides a set-coded ZFC model and the
soundness argument excludes a Cneq proof of 1. These establish the stated
internal consistency equivalence.

## Four-leaf NIP test

With the repository's structured break/continue semantics, use

\[
\left\langle \mathrm{CD}_5,
 \left\langle
  \left\langle\mathrm{CD}_5,\mathrm{CC}_2\right\rangle,
  \mathrm{CH}
 \right\rangle
\right\rangle.
\]

On input h=0, the outer decrement's break is consumed and the macro returns
normally. On positive odd input, repeated pairs of decrements eventually
leave one unit: the first decrement succeeds, the second fails, its pair
consumes the break, and CH executes. On positive even input, each successful
pair of decrements repeats the whole macro; eventually the first decrement
sees zero and returns normally. Each repeat decreases h by two, so all
nonhalting branches terminate. The complete contract is:

* odd h: halt;
* even h: normal return with h=0;
* every register other than 5 is unchanged.

The existing NIP pop follows the normal return. Scratches 6 and 7 are still
zero, so its original unpair/pop contract applies exactly. This replaces
the old constant-one setup plus equality test plus halt, twelve primitive
occurrences, by four occurrences. Source-DAG and machine-state savings
must still be measured and independently checked.

## Proof-enumerator calibration and bootstrap caveat

The original NP=3,D=3 bootstrap, with current/cache/stack zero, remains
sound. Logical row leaves have implication tags; the GEN leaf has a
quantifier tag; the gated bundle has an implication tag or is truth zero.
They are all even. Thus the existing proof-block cleanup NIPs do not
prematurely halt merely because equality formulas were recoded. On a
compiled contradiction proof, an earlier odd-code halt is acceptable and
the final proof of code1 still triggers NIP. The unchanged command coding
and enumeration reachability proofs therefore transfer.

The earlier all-register-permutation bootstrap theorem **must not be
applied unchanged**. Under this codec code3=J(0,0) is false, so placing an
initial three in current-theorem register1 or cache register5 violates the
invariant (cache3 would immediately satisfy the new halt predicate).
An initial stack3 is still safe: 3=P(2,0), and code2=Q(0,0) is a theorem.
The prior prefix argument remains available for placements of the two
threes outside registers1 and5. The original seed needs no modification.

## Optional combinations

The approximate inverse-detachment theorem becomes more permissive: its
decoder must be exact only on I and Q codes, and can behave arbitrarily on
both odd tags. Q-theorem elimination and ordinary MP are globally sound;
the two odd antecedent cases are impossible. This does not assert that the
previous inverse-command source becomes smaller automatically.

Also the fixed-role seed lemma can now use roles1 and3 without any
additional K gate. Both possible colliding matrix codes are false: F and
J(0,0). The false-matrix expansion gives w=u=true and an empty-container
existence statement (or a tautology when the container/output binders
coincide). These are exactly the roles already used by Complete222, so this
optional fixed-role variant needs no new alpha translation.

## Swapping the two odd tags

The same approach permits

\[
J(a,b)=4P(a,b)+1,\qquad M(a,b)=4P(a,b)+3,\qquad
F=J(0,0)=1,\qquad E'(a,b)=N(J(a,b)).
\]

Now M is membership and J is disequality. The logical rows use E', all
membership occurrences in the vacuity/seed-K bundle and congruence rows
use M, and the simplified existence row is still N(Q(a,J(a,b))). The
parity detector and code0 truth convention are unchanged. Every odd atom
is again refuted by a diagonal assignment in any ZFC model.

The numerical translation tau must now use M for named membership, so
the final interpreted seed codes are recomputed. Its strictly smaller
field bounds and direct private-code freshness proof are unchanged in
form. The G helper binder can use M(a,b), which exceeds both endpoint
labels. Alternatively it may retain the numeric function 4P(a,b)+1 as
its fresh binder: the logical proof only uses that function as a variable
label and requires the same strict endpoint bounds, not that the number
encode the membership predicate.

There is no hidden need to derive membership irreflexivity merely from
the new definition of F. The current `Complete222.v` endpoint uses
`K0_ZFc_inconsistent`, whose source K0 consists of equality axioms and K
schemas; it does not use K0IR. Propositional explosion comes from rho6 and
rho8 independently of the atomic meaning of F. The final `TB_to_thm`
step is an application of a translated negation to its positive theorem,
which yields the same F=1. Thus the complete K0/ZFC proof chain transfers
after the numerical constructor substitutions. Foundation is used in the
ZFC-model soundness argument to refute membership atoms, as before.

Both raw diagonal codes1 and3 are false in this swapped variant too, so
the optional unconditional fixed-K roles1,3 and the bootstrap restriction
remain exactly as above.

## Verification scope

The proofs above are ordinary mathematical proofs, checked against the
literal baseline Rocq interfaces. They are not a claim of a newly compiled
Rocq endpoint. A concrete candidate additionally requires literal source
binding, the six equality-builder replacements, the exact four-leaf NIP
tree, complete command/source simulation, and the binary-table certificate.
