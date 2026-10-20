# Native-code audit of the seed-request K family

This note concerns a source that retains the eight logical rows, the original
whole-bundle gate `c!=a,b`, membership vacuity, and K224's calibrated equality
helper. The actual matrix and private variable label are both the natural
number c. Root/conjunction permutations do not alter the argument below.

## 1. Decoding is exact before any semantic simplification

The pinned total decoder D sends0 to the closed tautology

    (forall0 0=0) -> (forall0 0=0),

and1 to R(0,0). It does not decode every implication uniformly: a numerical
implication whose consequent is1 is decoded as genuine named negation; the
special code0 is decoded as the displayed tautology.

For the emitted K_s expression all intentional negations have literal
consequent1, so `D_wn` applies. Every other implication has a consequent
known different from1. It is a quantifier, negation, existential or positive
compound code, except for R(b,c) and R(c,b); these two membership codes differ
from1 because the unchanged gate excludes b=c. The antecedent/consequent
pair also cannot be(0,0), since at least one argument is positive. Therefore
`D_wim` applies at every intended genuine implication. The atomic and
quantifier identities `D_wel`, `D_weq`, and `D_wal` apply unconditionally.

`audit_native_decoding.py` checks these uniform syntactic side conditions
against the actual generated arithmetic-expression trees. It is deliberately
limited to the constructor interface. Its checks do not establish any machine
semantics or any consistency theorem.

Thus the decoder gives the claimed named K_s formula for every enabled
natural triple, rather than merely for matrix codes selected for the lower
consistency direction. In particular, there is no substitution of a more
convenient matrix code for the actual c.

## 2. Private-code freshness, including c=0 and c=1

`KDecodeFresh.v` proves `D_private_fresh`: c has no free occurrence in D(c)
for every natural c. For positive c the stronger code-label bound says every
name in D(c) is strictly below c. For c=0 the decoder's special tautology is
closed even though it has a bound occurrence of0. For c=1 the decoded matrix
is R(0,0), whose sole name is strictly below1.

Consequently using c as the private container binder is valid in all enabled
cases. The gate supplies c!=a,b independently of this matrix freshness.
No argument needs the false assertion that c never occurs at all in D(c)
when c=0.

## 3. Distinct active roles a!=b

Use the pinned abstraction

    abstract_matrix(a,b,q) = q with output role b mapped to its first
    de Bruijn variable, input role a to its second, and all other names to
    parameters.

For q=D(c), the environment lemmas in `KDecodeAbstract.v` identify every
matrix insertion, output binder, input binder, membership occurrence and
subset occurrence with this ordinary two-role matrix. The hypotheses are
exactly a!=b, c!=a,b and free freshness of c in q. These are all available.

The decoded source therefore is an ordinary K_s instance, with the original
finite tuple of other names as parameters. K_s is interpreted in the same
constructible set theory as the upstream K family by the proof in
`seed_request_k.md`. Codes0 and1 cause no additional exception in this case.

## 4. Coincident active roles a=b

Do not apply the distinct-role abstraction lemma here. Keep c!=a from the
gate. Fix the other free names and write psi(x) for the matrix q evaluated
with its sole active name a assigned x. Renaming only locally bound variables
for readability gives

    W(C) = ((exists x psi(x)) -> exists x (psi(x) and R(x,C))).

In the emitted subset test both endpoints are the same active name, so it
becomes forall z(R(z,p)->R(z,p)), a tautology. In H, the support existential
and subsequent universals repeatedly bind that same name. They shadow the
outer member u, rather than retaining u as one of two independent matrix
roles. Its exact ordinary simplification is

    H(C) = forall u (R(u,C) -> ((exists x psi(x)) and W(C))).

There are two cases. If no psi witness exists, choose an empty C. Then W is
vacuous and H has no members to check. If a psi witness x exists, choose any C
containing x (an ordinary singleton suffices). Then W holds, and every guarded
H clause uses the same true existence statement and the same W. Thus the
decoded K_s instance is valid in the upper interpretation.

The case split is on `exists x psi(x)`. Reusing the old output-root diagonal
proof's split on the value of psi at the original environment would be
incorrect for the changed root. The request has quantified over that role.

## 5. Existential-premise and contrapositive request forms

Let B(C)=exists b(phi(b,a,q) and R(b,C)). Since c!=b and this occurrence binds
the output name b, B(C) has no free b. Capture-free ordinary first-order
reasoning gives

    forall b(phi(b,a,q)->B(C))
       <-> ((exists b phi(b,a,q))->B(C))
       <-> (not B(C)->not exists b phi(b,a,q)).

These transformations apply both in H and at the K_s root. They remain valid
at coincident active roles by the explicit diagonal argument above.

At b=0, do not claim freshness simply by expanding numerical N as an
implication to the raw atom R(0,0). The proper route first uses `D_wn` and
`D_wex`, so the displayed formulas have genuine named negation/existence,
then uses the unchanged relative-falsity/IR bridge from the upstream proof.
That bridge is already required for the original machine. This approach
adds no new primitive vacuity assumption for the raw falsity atom.

## 6. Lower consistency and equality interpretation

An arbitrary finite ordinary K_s refutation is put in the same named form as
K224: input name1, output name3, distinct positive parameter names and
capture-free bound names. Interpret primitive equality first using K224's
membership-indiscernibility translation theta. For a matrix f, set

    psi = theta(f),  pp = not not psi,  c = enc(pp).

The padded code satisfies c>3. All names in pp are below c, so c is fresh
after the equality interpretation, including all auxiliaries it introduced.
Choose the comparison K_s instance with private binder c and matrix
`not not f`. Ordinary K_s allows this fresh binder choice. Its outer template
contains only membership, implication, negation and quantifiers, so applying
theta gives the same K_s template with matrix pp. Its native code is exactly
the emitted expression with actual matrix/private input c, and the gate is
enabled at(1,3,c).

The root/conjunction permutations and each request form can be proved or
undone in the ordinary comparison logic before theta is applied. Their
translation uses the retained derived logical calculus, not a silent
renumbering of native formula codes. The helper calibration is unchanged.

This supplies the comparison's theory instances. The retained logical proof
translation supplies its logical axioms and preserves MP and theorem GEN.
The upstream K0-to-StandardZFC calibration and the K_s-to-K0 proof then give
the lower consistency direction. As in K224, this is an effective argument
on finite proofs, not only a claim about standard external models.

## 7. Exact limits

This audit supplies the ordinary mathematical native-calculus comparison.
The selected 223-state source is independently bound to the literal formula
by `audit_ks223_emitter.py`: its exact 77-macro symbolic execution and finite
all-register bisimulation pass, as recorded in `ks223_emitter_audit.json`.
The polished final proof is `theory223.tex`. This note does not itself certify
a compiler's context-sensitive state sharing. Complete enumeration, exact
startup and the unbounded binary runtime are separate certificates in the
released packet. No new kernel-checked theorem is asserted.

Primary dependencies are the pinned k230-rocq files `KDecoder230.v`,
`KDecodeFresh.v`, `KDecodeAbstract.v`, `KDecodeDegenerate.v`, `KDecodeCore.v`,
`KDecodeBundle.v`, and the K224 restricted-equality-helper calibration.
