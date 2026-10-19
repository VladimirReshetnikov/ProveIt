# E639: using the descriptor as its class code

Status: side result paused when the user redirected the main investigation to
Elliot Glazer's 230-state repository. This records the ordinary mathematical
argument; no new proof-assistant or Turing-machine endpoint is claimed.

The seven equations, ordered nine-symbol signature, four-variable capacity,
four-bit opcode format, and query `Q(d)=d` are exactly those of the inherited
E663 packet, except that the three class arguments `V(b,d)` in its closure
equation are replaced by `b`. In symbols, use

    R_b(x,y) = p_eps(P(y,P(x,b)), b).

The equation node counts become 14,6,9,12,12,17,74: 144 in total.
The complete packet is 43 + (8+4*144) + 12 = **639 bits**.

## Completeness of the new descriptor convention

Fix arbitrary finitely many raw parameters p0,...,p(m-1). Let
`L=P(p0,P(p1,...P(p(m-1),d)...))`, with L=d if there are none.
Given a class code c, put

    b = P(P(c,c), P(L,P(L,L))).

The NAND-class equation and the Boolean reduct from Sh1 give, for every
environment s and in every model of the first six equations,

    p_eps(s,P(L,P(L,L))) = 1,
    p_eps(s,b) = N(N(p_eps(s,c),p_eps(s,c)),1) = p_eps(s,c).

No assumption that the class d is false enters this identity. This is essential:
the upper model is allowed to make class d false, but lower extraction cannot
assume that for an arbitrary equational model.

The native stream `P(y,P(x,b))` has consecutive coordinates

    y, x, P(c,c), L, L, p0, p1, ... .

Therefore build c first to represent the desired pure membership formula with
y at index 0, x at index 1, and parameter pi at index 5+i, ignoring slots 2--4.
Under k binders these free coordinates shift by k. The unchanged native
Head/Tail equations prove those coordinate identities inductively. The Boolean
identity then makes b represent the very same formula while carrying the
parameter stream it needs. This supplies every finite matrix with every finite
parameter tuple, so the earlier extraction of raw EPSC still applies.

## The truth equation is still forced

The unchanged outer Boolean closure term F satisfies

    not d AND F(d,r,e,f,a,b0,c,u,v) = not d AND r.

For the new convention choose `b*=P(d,P(d,d))`. Its class is identically true by
the NAND-class equation, so the closure's first predicate r equals 1 at this
descriptor, regardless of the other chosen inputs. Thus `d=F` implies d=1,
as in E667. The old descriptor `P(k,d)` is no longer needed.

## Upper-model construction and the descent check

Use the inherited E692/E667 countable free tagged carrier with constructors
P,A,Q, its native selector interpretation, and its literal stack equations.
For any descriptor b, decode class b as a finite pure membership formula on the
stream `P(y,P(x,b))`. Every fixed raw parameter it references is a head of a
proper P-tail subtree of b, or the default d. Quantifiers add only bound inputs;
selectors inspect their own finite syntax. Thus the changed descriptor obeys
the same proper-subtree parameter descent as the old descriptor. It does not
introduce a self-evaluation or truth predicate in the raw model.

The existing weighted recursion is consequently unchanged:

    w(Q(b)) = w(b)+1,
    w(P(b,z)) = w(b)+w(z)+2,
    w(A(b,z)) = w(b)+w(z)+3.

Choose the raw value of Q(b) as a hull when R_b is locally subset bounded and
as an unbounded input otherwise; choose P(b,z) as the indicated output/support
witness and A(b,z) as the separating member. All descriptor parameters have
already received raw values, and the above weights order the remaining
witness dependencies. Define W and the free member-choice slice W(x,d) exactly
as in the inherited proof (class d is false in this constructed upper model).
The identical Boolean closure verification proves all seven modified equations.

Thus every countable raw-EPSC model yields a separating E639 model, while every
separating E639 ground-term model yields a raw-EPSC model. Equational
soundness/completeness and the inherited ordinary EPSC/ZFC calibration give

    ZFC proves: E639 does not derive Q(d)=d iff Con(ZFC).

Native Head/Tail still show that Q(d)=d collapses the entire carrier: for all
x,s, x=V(P(x,s),d)=V(P(x,s),Q(d))=V(s,d). This is why the same query works.

This is an equiconsistency/model-construction comparison, not a same-model
claim for E663 and E639. The representation convention changes.

## Evidence and provenance

Run `python3 -B build_e639.py` in this directory. Its independent decoder
roundtrips the AST and rejects all 639 strict truncations plus three malformed
controls. It also checks the four assignments of the descriptor Boolean
identity, 1218 native coordinate instances, and the inherited 512 Boolean
cofactor/truth-forcing cases and 256 closure cases. These finite checks validate
the indicated syntax/identities; the unbounded argument is given above.

The inherited script `inherited_e667.py` is copied without modification from
commit 0128d662fd's `docs/incoming/ZFC235_Construction_2026-10-19.zip`, inner path
`zfc235-research-20261019/formalisms/build_e667.py`. The E663 baseline hash is
checked before transformation. Its article, E692 compatibility proof and raw
EPSC calibration dossier remain the inherited foundations; attribution is
retained beside this file. No bit count here charges a binary proof interpreter
or its blank initializer.
