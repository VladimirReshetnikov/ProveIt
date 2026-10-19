# Exploratory appendix: restricted equality vacuity for the K230 schema

## Status and precise result

This is a **conditional ordinary external argument**. Its explicit premise L
is the uniform logical interpretation stated in section 1, supplied by the
earlier ordinary proof in `research_sub237_round2/vacuity_reduction/`.
Those finite Hilbert replays do not themselves establish the entire uniform
theorem, and this appendix does not formalize L in Rocq. It also uses ordinary
first-order completeness. It is not a new Rocq theorem, a changed enumerator
proof, or a new machine endpoint. The published K230 proof still uses full
equality vacuity in `Comp_Prop230.v:thm_B6a` and `lprov_thm`.

Let H_K(kappa) retain the exact K230 numerical rules, rho1--rho8, full
membership vacuity, and exact gated K core. Replace only the equality-vacuity
component by

    Eq(a,b) -> All(kappa(a,b), Eq(a,b)).

Assume kappa(a,b) differs from a and b whenever a differs from b. Its value
on the diagonal may be arbitrary. The helper must be available for every
(a,b); keeping it in the original c!=a,b bundle supplies this by choosing
any enabled c. In the opposite consistency direction, every emitted helper
must satisfy the stated condition. A c-dependent implementation must check
that obligation for all emitted instances, not just one convenient witness.

Assuming L, the argument below gives

    Con(H_K(kappa)) <-> Con(StandardZFC)

in the same external classical metatheory as the previous ordinary proof.
The proof does **not** translate an equality-containing matrix while keeping
its former native code. It first restricts source use to equality-free
matrices, then passes to a membership-indiscernibility quotient. This extra
quotient is the missing bridge between the earlier CP/GIC argument and K.

## 1. What is already available, independently of set axioms

The earlier logical certificate supplies the following theorem for the
retained logical rows, membership vacuity and the restricted helper:

* Primitive symmetry is derivable from old rho7 and the diagonal helper.
* The two-sided membership-indiscernibility formula E(a,b) satisfies the
  entire comparison Tarski calculus's equality laws, including fresh
  equality vacuity and existential equality.
* Replacing comparison Eq(a,b) by E(a,b), preserving Rel, implication and
  each quantifier label, translates comparison derivations into H_K
  derivations. Negation translates to implication into F=Rel(0,0).
* This interpretation is proved by induction on the substitution-free
  proof rules. It does not assume native alpha-conversion or a substitution
  rule. The E auxiliary-binder transport was proved separately.

These statements use no CP, GIC or K axiom. Hence the logical part applies
unchanged to H_K. This fact alone does not calibrate its set theory.

## 2. An equality-free named comparison theory

Use the named syntax of `Logic.v`: Wel, Weq, Wim, Wn, Wal. Here Wn has its
ordinary logical meaning; its numerical encoding is implication into F.
For every named formula p containing no Weq and no atom Wel(0,0), put

    c(p) = encode230(Wn(Wn(p))).

Let S_R contain the universal closures of

    KCore(1,3,c(p),Wn(Wn(p)))

for every such p, as well as IR = All(0, Wn(Wel(0,0))). Its underlying logic
is full ordinary first-order logic with equality.

The exact repository encoder lemmas give

    c(p)>3,
    D(c(p)) = Wn(Wn(p)),
    fr(c(p),p) = false.

The first property enables both source gates. The numerical encoding of
the displayed KCore is literally `kcore(1,3,c(p),c(p))`, the core component
of the actually emitted bundle. Projection uses only the retained classical
logic. Its universal closures follow by the source's closed-theorem GEN.

The logical interpretation of section 1 fixes every such named KCore
because its skeleton and matrix contain no equality. It therefore also
fixes its actual native matrix code and private binder. The interpretation
of IR has native form All(0,F->F), a theorem. Consequently

    Con(H_K(kappa)) -> Con(S_R).

Ordinary first-order completeness supplies a nonempty homogeneous model
A=(A,R) of S_R, with actual identity interpreting comparison equality.
This is a model of the comparison theory, not an assertion that primitive
equality in an arbitrary H_K interpretation is identity.

Only the direction “bundle implies KCore” is used. The published converse
`KBundle_core_equiv`, which reconstructs both old vacuity components, is
unnecessary here.

## 3. A real syntax subtlety: Std_tr is not equality-free

One cannot simply say “restrict `ordinary_code230` to equality-free ordinary
matrices.” The pinned `Std_tr.v` translates bottom to

    botw = Wn(All(0,Eq(0,0))),

which introduces equality even when the ordinary matrix has no equality
atom. A standalone equality-free adapter must remove this occurrence too.

Use the same hygienic named translation, except that bottom becomes

    bot_R = Wn(All(2, Rel(2,2)->Rel(2,2))).

This is a closed, equality-free false formula in every ordinary structure.
It contains no Wel(0,0). The bottom branch's internal binder may shadow an
outer binder named 2 harmlessly, since bot_R is closed. All other clauses
can be exactly those of `Std_tr.tr`, including its implication-to-bottom
negation abbreviation.

Call the resulting translation `tr_R`. Give its free roles the actual
source names

    output 0 -> 3, input 1 -> 1, parameter 2+k -> 2k+5,

and its ordinary quantifiers the same positive even names
`bname(qd(body))=2*qd(body)+2`. The usual depth argument separates nested
ordinary binders, and the odd free names cannot be captured by them.

For an equality-free ordinary matrix psi, structural induction proves:

1. p=tr_R(source_names,psi) is equality-free and has no Wel(0,0).
2. Its free names occur only among the images of the free variables of psi.
3. Under a named assignment s, its truth is the truth of psi under the
   assignment n |-> s(source_names(n)).

The bottom case follows from the definition of bot_R; the remaining cases
are the standard named-translation induction. Thus p is a permitted S_R
matrix, and its *own* code c(p), chosen after this translation, is available.
No equality expansion is performed after c(p) has been chosen.

## 4. Exact KCore extraction and all relevant binder interactions

Fix an equality-free ordinary psi(y,a,q), put p=tr_R(source_names,psi), and
take its S_R instance. Ordinary double-negation equivalence removes the
matrix's two negations. Because every occurrence is an ordinary formula
context, this preserves the KCore truth under all assignments.

The exact named formula is

    Ex_c ((p -> R(3,c)) AND
      All_3 (R(3,c) ->
        Ex_1 (p AND
          All_1 (KSubset(1,3,c) -> KRequest(3,c,p))))).

Interpret its outer private c as C, label 3 initially as x, label 1 initially
as a, and the odd parameter labels as q. The translation induction and
fr(c,p)=false allow the private-coordinate update without changing p.

The source's repeated binders then give exactly:

* The root conjunct is psi(x,a,q) -> R(x,C).
* All_3 chooses a member u of C.
* Ex_1 supplies some support input v with psi(u,v,q).
* The following All_1 shadows this support input and ranges independently
  over every request input a'. It must not be identified with v.
* KSubset is All_c(R(c,1)->R(c,3)). This inner c intentionally shadows the
  outer container coordinate, yielding a' subset u. The outer C is restored
  on leaving that subformula.
* KRequest is All_3(p -> Ex_3(p AND R(3,c))). It means that each satisfying
  output can be replaced by an output in C for the same a', hence the usual
  witness request W_psi(a',C).

The last equivalence is ordinary logic: forall z(P(z)->exists y Q(y)) is
equivalent to (exists z P(z))->exists y Q(y) when z has no free occurrence
in the existential consequent. The inner Ex_3 binds the output occurrences
there. No source-level renaming or specialization was assumed to reach
this model; these are standard operations in the homogeneous model A.

Unused parameter names may numerically coincide with c. They do not affect
the argument, because the precise matrix freshness property eliminates the
private update on every free occurrence. The active labels 1 and 3 cannot
collide with c because c>3. Only these enabled, distinct-role instances are
used in this lower direction; no assertion about discarded a=b instances
is needed.

It follows that A satisfies every equality-free instance of the ordinary
KPrime output-root schema, with arbitrary finite parameters, and IR.

## 5. The additional quotient supplies equality-containing matrices

Define on the set A:

    x ~ y iff
      (forall z, R(z,x) iff R(z,y)) AND
      (forall z, R(x,z) iff R(y,z)).

This is an equivalence relation. It is a congruence for R in both arguments:
if x~x' and y~y', then R(x,y) iff R(x',y'). The outgoing half proves the
first-coordinate replacement; the incoming half proves the second.

Let B=A/~, with [x] R_B [y] iff R(x,y). This is well-defined and nonempty.
Its equality is actual equality of equivalence classes. IR passes to B:
a loop [x] R_B [x] would imply R(x,x), contrary to IR in A.

For every ordinary formula phi, define phi^~ by replacing each equality
atom x=y by the displayed, equality-free formula for x~y. Choose its bound
variables capture-avoidantly, or use the ordinary de Bruijn syntax. Preserve
membership, bottom, Boolean operations and quantifiers. Then phi^~ contains
no equality, and for every assignment s in A,

    B, [s] |= phi    iff    A, s |= phi^~.                 (Truth lemma)

Proof is structural induction. The equality and membership cases are the
definitions; Boolean cases are immediate. In the quantifier case every
class has a representative, so quantification over B corresponds to
quantification over A. No global choice of representatives is required.
In particular the truth of phi^~ is invariant under replacing parameters
by ~-equivalent parameters.

The ordinary KPrime core has no equality outside its matrix. Its support,
subset, membership and witness clauses therefore commute with this
translation, modulo ordinary capture-avoiding binder bookkeeping:

    (KPrime(phi))^~ = KPrime(phi^~).

This can also be checked directly in the prose schema of section 4. The
subset clause quantifies over all A representatives; surjectivity makes it
equivalent to the subset clause over all B classes. The support and request
witnesses project to classes, and all universal inputs/outputs lift to
representatives. The two independently scoped input binders remain
independent in both structures.

Since A satisfies KPrime(psi) for every equality-free psi, it satisfies
KPrime(phi^~). The truth lemma now gives B |= KPrime(phi) for **every**
ordinary phi, including equality-containing matrices. Thus B is a model
of full KPrimeOrdIR.

This quotient is only a preprocessing step to obtain the full ordinary K
theory. It is not claimed to be extensional or well-founded. The repository's
separate KQuot development performs the further interpretation needed for
ZF; its hypotheses now hold because B satisfies full KPrimeOrdIR.

## 6. Consistency conclusion and reverse direction

The chain proved above is

    Con(H_K(kappa))
      -> Con(S_R)
      -> an ordinary model A of equality-free K + IR
      -> a quotient model B of KPrimeOrdIR
      -> Con(KPrimeOrdIR)
      -> Con(StandardZFC).

The last implication is exactly the published external K calibration.

Conversely every retained row is an old K230 row. Every new helper is
derivable in old K230: use full Eq-vacuity in the off-diagonal fresh case;
on the diagonal use old logical Eq reflexivity, GEN and propositional logic,
even if kappa(a,a)=a. Project the unchanged K core and membership-vacuity
components, derive the helper, and reassemble the changed bundle. MP and
GEN are unchanged. Therefore an H_K refutation would be an old K230
refutation, and the published K230 consistency direction gives

    Con(StandardZFC) -> Con(H_K(kappa)).

## 7. Implementation boundary

This establishes a general ordinary consistency argument, not a literal
derivation of the deleted primitive Eq-vacuity schema. It also does not show
that `Complete230.v` compiles after a one-line axiom edit. At least the
following new formal pieces are required for a Rocq endpoint:

1. A reduced native proof relation and the general E logical interpretation.
2. The equality-free tr_R adapter, including its bottom replacement.
3. The equality-free named K extraction, with the same actual private code.
4. The quotient truth lemma and equality-free-K to full-K model transfer,
   plus the chosen formal completeness interface; alternatively a fully
   syntactic interpretation implementing these same obligations.
5. Source/enumerator binding, runtime, startup and machine proofs for the
   modified emitter.

The already verified 230-state endpoint and any 229-state backend fold of
its unchanged theory do not depend on this extension. No state count or
machine reduction is inferred here.

## 8. Finite regression checks

`python -O check_quotient_bridge.py` independently checks the elementary
semantic constructions on all 530 binary structures of sizes 1, 2 and 3.
It checks 237,218 instances of the quotient truth lemma, all 69 irreflexive
quotients among those structures, and the closed membership-only bottom.
Separately, on all size-1 and size-2 binary relations and all possible
two-argument matrix truth tables, it compares the literal named KCore with
the ordinary output-root formula in 1,028 cases. The actual repeated binder
labels and negative conjunction/existential encodings are used.

The script imports no source generator. Its explicit checks remain enabled
under Python's `-O`; `quotient_bridge_checks.json` records the receipt and
hashes. These are finite regression checks, not a proof of L, general
first-order completeness, the uniform truth lemma, or the consistency claim.
