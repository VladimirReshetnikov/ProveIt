# Backward crossed replacement: equivalence proof and optional source restriction

Research note for the current task. Repository snapshot examined:
`36d37fc1071fe289371f6bcd7dcfa0eac593a5a6`.

## 1. Scope and attribution

The native scalar kernel has numerical terms

    t ::= x | 0 | S(t) | I(n,a;v.h)

and formulas formed by equations, `Q_y A`, and `D_{x,y} A`.
Only `v` is bound in the body `h` of an iterator. The two computation
axioms are

    I(0,a;v.h) = a,
    I(S(n),a;v.h) = h[I(n,a;v.h)/v].

The native kernel's one-template crossed transport is

    s=t,  H(s)=r
    ------------- Tr
       r=H(t).

Its remaining rules are hypothesis, the two computations, QE, DE,
introduction of D by numerical cases, and introduction of Q by progress
for a literal equation. The repository proves this kernel equivalent to
the presentation with full formula transport and bi-interpretable with
full first-order iPRA.

The existing `template_free` proposal replaces Tr by the FORWARD rule

    s=t, u=r  /  r=Rep_s^t(u).

The rule considered below is its goal-directed counterpart. It is not
the preceding rule with only its printed direction changed: in a backward
checker the second premise is deterministically COMPUTED from the goal
and the major equality.

## 2. Replacement operation

`Rep_t^s(u)` is a single top-down traversal of a term `u`. At a node
identical to `t`, replace the whole node by `s` and stop at that node. At
any other node preserve its constructor and traverse its term children,
including an iterator body. The operation does not revisit an inserted
copy of `s` and performs no arithmetic normalization.

Replacement is capture avoiding: rename an encountered binder fresh for
the free variables of `s` and `t` before traversing its body. Equivalently,
a de Bruijn implementation shifts both free comparison term `t` and
replacement `s` when descending beneath a binder. Matching a bound
variable against a free source variable is forbidden.

The operation is total by structural recursion on the ORIGINAL `u`, even
when `s` contains `t`. It is replacement of all currently matching
outermost occurrences, not repeated rewriting and not bottom-up matching
against nodes newly created by the traversal.

## 3. Proposed rule and its soundness

The new primitive rule is

    Gamma |- s=t       Gamma |- Rep_t^s(u)=r
    --------------------------------------- BRep
                  Gamma |- r=u.

Let B be the eight-rule native kernel with Tr replaced by BRep.

**Soundness lemma.** Every BRep instance is one instance of Tr.

Proof: The occurrences of `t` actually replaced in `u` are pairwise
disjoint. Replace precisely these occurrences by a fresh variable `v` to
form a capture-safe template `H(v)`. Then

    u = H(t),        Rep_t^s(u) = H(s)

as literal syntax up to alpha renaming. The two BRep premises are `s=t`
and `H(s)=r`; Tr concludes `r=H(t)`, namely `r=u`. If no occurrence is
replaced, H is a constant template. No equation induction, computation,
or semantic equality decision is used.

This argument is for the ONE-SIDE CROSSED rule as written. It does not
establish completeness of the different full-formula rule
`s=t, Rep_t^s(A) / A`.

## 4. Equality algebra derived from I0 and BRep alone

Put `J(a)=I(0,a;w.0)`, choosing `w` fresh.

**Joining.** From `s=t` and `s=r`, BRep with its target-side term `u=t`
concludes `r=t`, because `Rep_t^s(t)=s` at the root. This holds even when
one term contains the other.

**Reflexivity.** Join two copies of the computation equation `J(a)=a`
to obtain `a=a`.

**Symmetry.** Join `s=s` and `s=t` to obtain `t=s`.

**Transitivity.** Given `s=t` and `t=r`, first reverse the former to
`t=s`, then join `t=r` and `t=s` to get `s=r`.

These are derivations under an arbitrary retained context, using no
logical connective, successor computation, or induction.

## 5. Exact marking

Count one node for a variable, zero, successor, and iterator constructor;
count all nodes in an iterator's body. For a fixed template H(v) and
terms s,t choose

    N = 1 + |H| + |s| + |t|,
    K = I(0,s;w.S^N(0)),

with w fresh. The node count of K is strictly larger than that of H.
The computation axiom gives `K=s`.

**Exact-marking lemma.** Every occurrence of K in H(K) is one of the
copies inserted at a designated occurrence of v. Consequently

    Rep_K^s(H(K)) = H(s),
    Rep_K^t(H(K)) = H(t).

Proof: An occurrence of K not equal to an inserted copy would either be
disjoint from all inserted copies, strictly inside an inserted copy, or
strictly contain an inserted copy. In the first case its nodes would all
come from H, which has fewer nodes than K. In the second its size would
be smaller than K. In the third it would be larger than K. Each case
contradicts identity with K. Renaming bound variables preserves size;
below a binder compare against the correspondingly shifted/renamed K.
The traversal therefore replaces precisely the designated copies and
stops at each.

The marker is used by the proof compiler, not by the trusted checker.
There is no marker-recognition test, supplied path, occurrence mask, or
template parameter in BRep.

## 6. Arbitrary selected congruence and transport

Assume `s=t`. By I0 and the derived equality algebra obtain

    s=K,        t=K.

For the first equation use the symmetry of `K=s`; for the second join
`K=s` with `s=t` and reverse the result.

Apply BRep to major `s=K`, target-side term `u=H(K)`, and minor
`H(s)=H(s)` supplied by reflexivity. Exact marking gives

    H(s)=H(K).

In the same way major `t=K` and reflexivity of H(t) give

    H(t)=H(K).

Symmetry and transitivity yield `H(s)=H(t)`. This is congruence for an
arbitrary term template, with any number of designated occurrences and
with occurrences below arbitrarily many iterator binders. Fixed copies
of s or t elsewhere in H remain fixed, even when naive global
replacement would change them.

Now given `s=t` and `H(s)=r`, derive `H(s)=H(t)` and join it with
`H(s)=r` to obtain `r=H(t)`. This is precisely Tr.

**Exact-sequent equivalence theorem.** For every native context Gamma
and native formula A,

    Gamma |-B A    iff    Gamma |-Native A.

Proof: Translate derivation trees by induction. BRep is a native Tr
instance by Section 3. In the other direction replace each Tr occurrence
by Sections 4--6. All other rules and all term/formula syntax are the
same. The translated premises have exactly the same sequents as the
original premises, so eigenvariable conditions are preserved. Markers
introduce no free variable absent from the original equality premise;
their body variable is bound and chosen fresh. Only internal intermediate
terms grow. The construction does not rely on substitution being
primitive or already admissible for B.

Thus the full first-order bridge, equiconsistency, whole-domain
interpretations, actual equality, both formula round trips, and identity
numerical composites transfer from the existing native kernel. This is
stronger than merely identifying closed equational theorems.

## 7. Optional restriction: the source s may not be literal 0

Let B-minus retain the other seven kernel rules but permit BRep only
when its major's left-hand term s is not the literal constant 0. This
restriction also preserves all native sequents. The proof is longer
than in the unrestricted case and uses the logical rules.

### 7.1 Reflexivity, arbitrary symmetry, and restricted joining

Reflexivity is still obtained from two copies of `J(a)=a`, whose source
J(a) is a compound term. Joining with a common left side s is available
whenever s is not literal 0.

For arbitrary symmetry of `u=r`, choose a closed numeral M with more
nodes than u. The computation major `J(M)=M` is allowed. No occurrence
of M lies in u, so `Rep_M^{J(M)}(u)=u`; BRep applied to this major and
the minor `u=r` concludes `r=u`. This includes symmetry of `0=r`.

### 7.2 A common nonzero-syntax anchor for all provably zero terms

Set `c=I(0,0;v.0)`. It is a compound term and `c=0` is I0.

For every term p the constant-iterator identity

    I(p,p;v.p)=p

is derivable before using transport. To see this put
`E(y) := I(y,p;v.p)=p`, with y,v fresh for p. Its base E(0) is I0.
Its successor instance E(Sz) is IS because the body ignores v. QI by
progress, with an unused induction assumption, gives Q_y E(y), and QE
at target p gives the identity. Numerical cases are an alternative.

If `p=0` is given and p is not literal 0, BRep with this major, `u=c`
and `r=p` has exactly the preceding identity as its minor, since

    Rep_0^p(c) = I(p,p;v.p).

It concludes `p=c`; symmetry gives `c=p`. If p is literal 0, `c=p` is
already the computation equation. Therefore every term proved equal
to zero is provably equal to the one nonzero-syntax anchor c.

### 7.3 Full joining and transitivity

The only missing joining instance has premises `0=t` and `0=r`.
Reverse each premise, apply the anchor lemma, and obtain `c=t` and
`c=r`. Joining at the allowed nonzero source c concludes `r=t`.
Together with restricted joining this gives arbitrary joining and hence
transitivity exactly as in Section 4.

### 7.4 Congruence when both endpoints are nonzero syntax

The marking proof of Sections 5--6 now applies whenever neither s nor t
is literal 0: its two BRep majors are `s=K` and `t=K`, so both are
allowed. All auxiliary equality algebra is available by 7.1--7.3.

### 7.5 Congruence between a fresh variable and zero

Suppose the context supplies `b=0`, where b is a variable fresh for a
template H(v). Put

    L = Rep_0^b(H(0)).

Then also `L=Rep_0^b(H(b))` as literal syntax: replacing all zero leaves
by the variable b erases the distinction between the designated zero
copies and designated b copies. The variable b itself contains no zero
leaf. This fact holds under binders with capture avoidance.

Use BRep twice with the allowed major `b=0` and the reflexive minor
`L=L`. Taking u=H(0) gives `L=H(0)`; taking u=H(b) gives `L=H(b)`.
Full joining yields `H(0)=H(b)` (reverse if needed).

### 7.6 A fresh name for zero

Use `C(y,a,d)=I(y,a;v.d)` and the matrix

    E(x,y) := C(y,0,x)=C(y,0,0).

At witness x=0 the matrix is reflexive for every y. Hence DI by cases,
whose local assumption may be unused, proves `D_{x,y} E(x,y)`.
Open it at a fresh b. The opened closure is Q_y E(b,y).
The base E(b,0) follows from the two zero computations and full equality
algebra. QE at S0 gives E(b,S0). The two successor computations reduce
its sides to b and 0; equality algebra therefore derives `b=0`.

No congruence or full transport is used in this naming argument: all
comparisons are chained at the roots of whole computation equations.

### 7.7 Completion at a zero endpoint

Given `0=t` with t not literal 0 and a desired template H, open the zero
name of 7.6 at b. In that local context `b=0`, so transitivity with
`0=t` gives `b=t`. Both b and t are nonzero syntax; 7.4 gives
`H(b)=H(t)`. Section 7.5 gives `H(0)=H(b)`, hence
`H(0)=H(t)`. This conclusion contains no b, so DE discharges the name.
If t is literal 0, reflexivity suffices. A zero right endpoint is handled
by symmetry of the premise and of the conclusion.

All term congruence is now available. Joining congruence with the minor
premise recovers Tr; Section 3 then recovers every unrestricted BRep
instance. Therefore B-minus, B, and the native kernel prove exactly the
same sequents.

### 7.8 Combination with the witness-selected introduction

The restriction also works with the seven-rule presentation in the report,
where the single D-introduction uses progress precisely when its matrix
is a literal equation and its witness is syntactically 0.

First derive QI by an unused existential coordinate, witness 0, and DE.
No equality transport is used. This suffices for the common-anchor
argument above. The only other use of introduction in the source-minus
proof is the zero-name formula E(x,y)=C(y,0,x)=C(y,0,0). At witness 0,
the selected introduction chooses progress, but its successor instance
is reflexive, so the local induction assumption can be unused.

Thus the common-anchor and zero-name arguments recover all congruence
before general case introduction is needed. Only after that recovery,
derive the missing atomic case introduction at witness 0 through the
nonzero-syntax alias c=I(0,0;u.0). Weakening, fresh renaming, and cut are
admissible by direct derivation induction, justifying use of the original
case derivation under its transported assumption. The dependency order
is noncircular. Both restricted presentations derive exactly the native
sequents; neither is separately implemented in this archive.

## 8. Scope of novelty and claims

At the pinned snapshot I searched the article and artifact text for
backward/backwards replacement, reverse replacement, goal-directed
replacement, and related formulations. The closest proposal is
`Artifacts/template_free`, documented in Chapter 2's section
"Replacement with no template". It states the forward rule
`s=t,u=r / r=Rep_s^t(u)` and uses the oversized marker in the forward
orientation. Its test named `replacement_target_is_not_rewritten`
checks that an inserted term is not revisited; it is not the new
backward rule. I found no statement of BRep as above.

The defensible novelty claim is therefore narrow: a deterministic
goal-directed equality premise with no supplied template, together
with an exact-sequent completeness proof and the optional harmless
literal-zero source restriction. The marker technique and the entire
native/iPRA bridge are inherited, explicitly attributed mathematical
ingredients. This is not a claim of historical priority outside this
repository, a smallest calculus, or a measured source-size record.

The existing current coordinatewise compact envelope is 251 significant
tokens, 275 AST nodes, and 502 normalized bytes, attained by three
different programs (Chapter 11, "The coordinatewise envelope"). The
present equivalence theorem by itself says nothing about beating these
figures. A matched complete checker must be measured separately.

## 9. Suggested implementation regression examples

1. Root joining with nested/overlapping s,t: top-down root matching must
   stop immediately.
2. Reflexivity at 0 and at a term containing bound state variables.
3. Symmetry and transitivity from unrelated variables as hypotheses.
4. The template `H(v)=I(v,s;w.s)`: a marker-based derivation must replace
   only the designated first argument, leaving the fixed copies of s.
5. Marking and replacement beneath two nested iterator binders with an
   outer free parameter and a different bound state variable.
6. An inserted replacement s that contains its target t: the traversal
   must not recurse into s.
7. Reject replacement of a bound variable by matching it to a free
   variable in the major equality.
8. If the restricted variant is implemented: symmetry of `0=t`, joining
   `0=t,0=r`, the anchor identity, and zero-endpoint congruence with
   fixed zero occurrences in the template.

Finite regression runs test implementation behavior; the universal
mathematical result is the proof in Sections 3--7 and is not yet a
Lean or Rocq formalization.
