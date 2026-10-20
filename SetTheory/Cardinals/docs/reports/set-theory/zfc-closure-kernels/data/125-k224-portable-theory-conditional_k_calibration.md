# Conditional K has the consistency strength of ZFC

## Main theorem

Work in classical first-order logic with genuine equality and one binary
relation R. Let Kc be the schema

    forall a,x (phi(x,a,q) -> exists C (R(x,C) and H_phi(C))),

where

    H_phi(C) := forall u (R(u,C) ->
        ((exists p phi(u,p,q)) and
         forall p (Sub(p,u) ->
           ((exists y phi(y,p,q)) ->
            exists y (R(y,C) and phi(y,p,q)))))),
    Sub(p,u) := forall z (R(z,p) -> R(z,u)).

The matrix phi and its finite tuple of parameters q are arbitrary. Let Ku
be the original unconditional output-root schema

    forall a,x exists C ((phi(x,a,q) -> R(x,C)) and H_phi(C)).

Let IR be forall x not R(x,x). Then

    Con(Kc + IR) <-> Con(Ku + IR).

By Elliot Glazer's calibrated theorem for Ku+IR, both sides are equivalent
to Con(StandardZFC). The new part proved below is a uniform first-order
interpretation of Ku+IR in Kc+IR. It uses two markers and a hereditary
domain. It does not derive a raw empty object, does not assume raw
extensionality, and does not invoke Choice.

The source-level root changes from

    Ex_k(And(Imp(m,Rel(b,k)),H))

to

    Imp(m,Ex_k(And(Rel(b,k),H))).

Here H is the SAME emitted support-and-closure formula as before. After
the elementary Ex-And fusion, the new root is

    Imp(m,Neg(All_k(Imp(Rel(b,k),Neg(H))))).

Its constructor count equals the fully fused unconditional root, but its
subexpressions and therefore possible compiler sharing differ.

## 1. Raw singleton and pair constructions

Use the unambiguous convention

    Sing(y,p) := R(y,p) and forall z (R(z,p) -> z=y).

Thus the SECOND argument p is a container with exactly the one member y:
the input p={y} represents the output y. This is the argument order of
upstream `raw_singleton y p`.

### Lemma 1 (singletons)

Kc proves forall a exists p Sing(a,p).

Proof. Take phi(y,p): y=a, with a as an ordinary matrix parameter. For
any seed input, the specified output a satisfies the matrix. Kc gives a
container containing a. Support says every member equals a. QED.

### Lemma 2 (pairs)

Kc+IR proves that every a,b have an exact pair container c:

    R(a,c) and R(b,c) and forall z (R(z,c) -> (z=a or z=b)).

Proof. Choose r with Sing(a,r). Since R(a,r), IR implies r!=a. Use

    phi(y,p) := (p=r and y=a) or (p=a and y=b),

with seed input r and specified output a. The resulting C contains a.
Since Sub(a,a), its closure applies at input a, which has output b. Any
output at this input equals b, because a!=r. Hence C contains b. Support
restricts all members of C to a or b. QED.

Singleton uniqueness used below concerns the element selected by ONE
container: Sing(y,p) and Sing(z,p) imply y=z. It does not assert that two
containers with the same members are equal. Raw extensionality is never
used.

## 2. Two fixed markers and a hereditary domain

Choose any object t; this uses only the nonempty-domain convention. Choose
s with Sing(t,s). Then t!=s by IR. For the rest of the argument keep these
two objects fixed.

Define

    Q(x) := R(t,x) and R(s,x).

Call a raw set T admissible if

    Adm(T) := forall u (R(u,T) ->
        (Q(u) and forall v (R(v,u) ->
            (v=t or v=s or R(v,T))))).

Define the first-order domain formula

    D(x) := exists T (R(x,T) and Adm(T)).

All these are finite first-order formulas with parameters t,s. The
definition of D is not recursive: Adm uses only Q and R, never D.

### Lemma 3 (elementary domain facts)

1. D(x) implies Q(x).
2. Neither t nor s lies in D.
3. If D(u), R(v,u), and v is neither marker, then D(v).
4. If e is an exact pair {t,s}, then D(e). In the induced D-structure it
   has no members.

Proof. Item 1 follows by applying Adm(T) to x. Item 2 follows from IR:
Q(t) entails R(t,t), and Q(s) entails R(s,s). For item 3, a witness T for
D(u) also contains v, and the same T witnesses D(v). For item 4 choose a
singleton T={e}. Every member of e is a marker, so Adm(T) holds. Neither
marker belongs to D, so e has no D-members. QED.

The interpreted relation is simply R restricted to the definable domain
D, and interpreted equality is genuine equality restricted to D. No
quotient is needed at this stage.

## 3. The key closure lemma

### Lemma 4 (forming a new tagged object)

Suppose Q(C), and suppose every member of C other than t,s belongs to D.
Then D(C).

Proof. Apply Kc to the finite formula

    psi(y,p) := Sing(y,p) and (D(y) or y=C),

using specified output C and any singleton input p_C={C}. The root premise
holds through y=C. Obtain T containing C with H_psi(T).

Support shows that each u in T satisfies D(u) or u=C. Hence every u in T
satisfies Q(u), either by Lemma 3 or by the hypothesis Q(C).

Now let u belong to T and let v belong to u, with v different from t,s.
If D(u), Lemma 3 gives D(v). If u=C, the assumed member condition gives
D(v). Choose a singleton p_v={v}. Since v belongs to u, Sub(p_v,u). The
formula psi(v,p_v) holds, so closure for T supplies z in T with
psi(z,p_v). Both Sing(v,p_v) and Sing(z,p_v) hold; therefore z=v. Hence v
belongs to T.

We have proved Adm(T), and C belongs to T. Thus T witnesses D(C). QED.

This argument is the reason that no collection of arbitrarily chosen
domain witnesses is needed. It applies the conditional closure schema
once more to a formula containing the already defined first-order D.

## 4. Transferring an arbitrary conditional instance

Choose p_t,p_s with Sing(t,p_t) and Sing(s,p_s). Because t!=s,

    p_t != p_s,  not D(p_t),  and not D(p_s).

Indeed, Q(p_t) would require its only member t to equal s; similarly for
p_s. Equality of p_t and p_s would force t=s.

Let phi(y,p,q) be an arbitrary formula of the interpreted D-structure.
Write phi^D for its ordinary first-order relativization: each universal
quantifier becomes forall z(D(z)->...), each existential quantifier becomes
exists z(D(z) and ...), while R and equality are unchanged. Its parameter
tuple is assumed to lie in D, as usual for an interpretation.

Suppose D(a), D(x), and phi^D(x,a,q). Define the RAW matrix

    Psi(y,p) :=
        (p=p_t and y=t)
        or (p=p_s and y=s)
        or (D(p) and D(y) and phi^D(y,p,q)).

Its remaining parameters include t,s,p_t,p_s and q. Since Psi(x,a) holds,
Kc supplies C containing x, with support and closure for Psi.

### Both markers belong to C

Because D(x), Q(x) holds. Hence Sub(p_t,x) and Sub(p_s,x). The request at
p_t has the witness t. Any Psi-witness at input p_t must equal t: the
second branch is excluded by p_t!=p_s and the third by not D(p_t).
Consequently t belongs to C. Likewise s belongs to C. Thus Q(C).

### C belongs to the interpreted domain

Support says that every u in C is a Psi-output. If u is not t or s, only
the third branch is possible, so D(u). Lemma 4 now gives D(C).

### Interpreted support

If D(u) and u belongs to C, u is neither marker. Its raw supporting input
therefore satisfies the third branch of Psi. Hence some p in D satisfies
phi^D(u,p,q), as required by the interpreted support clause.

### Interpreted subset closure

Suppose D(u), u belongs to C, D(p), and every D-member of p belongs to u.
Then Sub(p,u) holds in the raw structure. To see this, let v belong to p.
If v is a marker, Q(u) puts v in u. Otherwise Lemma 3 gives D(v), and the
interpreted subset premise puts v in u.

If there exists y in D with phi^D(y,p,q), then Psi(y,p) holds. Raw closure
supplies z in C with Psi(z,p). Since D(p), p is neither p_t nor p_s; thus
the third branch holds. We get D(z) and phi^D(z,p,q), which is exactly the
interpreted witness request.

We have established the entire relativized conditional instance at a,x.
Since phi and its finite parameters were arbitrary, the induced D-structure
satisfies Kc. It also satisfies IR and, by Lemma 3, has an empty object e.

## 5. Recovering the unconditional schema and consistency

Within any nonempty classical structure, Kc plus an empty object implies
Ku. For a fixed matrix, a,x, split on phi(x,a). If true, Kc provides C with
the required seed and closure. If false, use an empty C: the seed implication
and every guarded clause of H_phi(C) are vacuously true.

Thus D interprets Ku+IR in Kc+IR. The reverse consistency direction is
immediate because Ku implies Kc by retaining its witness whenever the root
premise holds. Hence the theories are equiconsistent.

Every construction above uses a fixed finite number of schema instances
depending effectively on the input matrix. Relativization is recursive on
formula syntax. The proof therefore gives the usual effective finite-proof
translation, formalizable in ZFC; it is not merely an argument restricted
to standard matrices in a chosen external model. A fully serialized proof
assistant development remains additional work.

## 6. Native source obligations

The theorem above calibrates an ordinary classical first-order theory. A
changed literal numerical source still requires its own exact binding to
that theory, its finite proof-enumerator correctness, runtime simulation,
and blank initialization. The useful facts for this binding are:

- Keep all eight old logical rows and both full atomic-vacuity families.
- Keep the old private-code gate and the identity k=m=c, unless a separately
  justified encoding is used.
- The new root is obtained by moving the seed implication across the fresh
  container quantifier. For every enabled emitted old instance, the old
  ordinary/named formula implies the conditional one. The existing private-
  freshness and coincident-role lemmas therefore support the upper direction;
  they should be applied explicitly rather than assumed as code identities.
- For the lower direction, the existing safe encoder uses output label 3,
  input label 1, and padded matrix/private code c>3. Its distinct-role
  translation can be adapted to the changed outer root. The resulting
  ordinary instances are exactly Kc, which the interpretation above calibrates.
- The new root remains an implication whose consequent is a positive
  existential code. It cannot be numerical 0 or F=1. Conjoining the vacuity
  bundle preserves nonzero and nonhalting-code status.

The exposed source compiler may choose an unfused or fused negative encoding.
The separate `fusion_certificate.json` proves the elementary double-negation
removals in the retained numerical logical basis. A conditional-root variant
needs its own appropriately instantiated cancellation certificate; the
ordinary Kc interpretation is independent of which equivalent negative
encoding is used.

## 7. Attribution and mathematical scope

Elliot Glazer's K230 theory, its original closure/support mechanism, and its
calibration to StandardZFC are the starting point. The source is
`elliotglazer/k230-rocq` at
`3142e4dd980f0be12f4abb636c4ae2528afc17eb`, especially
`coq/settheory/{KPrimeCore,KPrimeTheory,KUpperConsistency}.v`.
The present derivation contributes the two-marker hereditary interpretation
for conditional seeding. We make no priority claim about the general use of
tagged domains or relative interpretations. No state reduction follows from
the theorem until the complete compiler and machine are measured.
