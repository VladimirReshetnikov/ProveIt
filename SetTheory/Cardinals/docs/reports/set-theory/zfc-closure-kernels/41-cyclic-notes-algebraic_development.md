ARCHIVE NOTE: This is a development or independent audit record. The final
article.tex/article.pdf and README.md are authoritative for the delivered
status and runnable archive commands. Some original workspace paths and
earlier-stage comments are retained as provenance. The final U14 source
and its 10,182-node wrapper are included under data/.

# Cyclic algebraic compression for a ZFC consistency search

New work in this session, 17 October 2026. Internal research notes for the
parent report. The mathematical results below are ordinary proofs; there is
no claim that the new algebraic frontend has been compiled to a binary TM.

## Outcome and novelty boundary

The pinned ProveIt tree already discusses Andréka–Németi's three-modal/Df3
route, its 18 expanded equations, and the missing-reflexivity error in the
paper's abbreviated modal presentation. Repeating that suggestion would not
advance the project. The new result here is an equational-validity reduction
from the usual Df3 signature (join, complement, and three closures) to a
9-equation signature (join, complement, one closure, and a cyclic rotation).
This reduction has a complete elementary proof, a fully serialized basis,
a complete reference rewrite-certificate kernel, and exact syntax counts.
An additional 8-equation presentation combines complement and rotation into
one unary operation. It has a larger basis in tree nodes and is a tradeoff.

| Presentation | Nonleaf term constructors | Equations | Sum of both-side tree nodes |
| --- | ---: | ---: | ---: |
| Published Df3 basis | 5 | 18 | 127 |
| Same basis with redundant idempotence removed | 5 | 15 | 112 |
| New cyclic basis E9 | 4 | 9 | 75 |
| New combined-unary basis E8 | 3 | 8 | 90 |

Nodes count operation occurrences and variable leaves. Equation separators,
variable encodings, target term, decoder, arithmetic, initialization, and
TM implementation are excluded. E9 saves 52/127 = 40.94% against the 18-row
presentation, or 37/112 = 33.04% against the fair 15-row control. These are
syntax measurements, not state-count improvements.

## 1. Exact E9 basis

Use a binary operation + and unary operations n,c,r. Write n(x) as -x and
omit parentheses for compositions (rightmost operation applies first).
Variables in the following equations are universally quantified.

1. B1: x+y = y+x.
2. B2: x+(y+z) = (x+y)+z.
3. B3: -(-(x+y)+-(x+-y)) = x.
4. C1: x+cx = cx.
5. C2: c(x+y) = cx+cy.
6. C3: c(-cx) = -cx.
7. R1: r(x+y) = rx+ry.
8. R2: rrrx = x.
9. M: crcx = rcrrcrx.

B1--B3 are the Boolean basis used in the cited Df3 presentation. The final
row is the shorter form of c(r c r^2 x) = r c r^2(c x): compose it on the
right with r^2, using r^3=identity, to recover that commutation equation.
Conversely, compose the commutation equation on the right with r to obtain M.

### Closure lemma

C1 says x <= cx. From C3 applied to -cx,

    c(-c(-cx)) = -c(-cx).

But C3 at x gives c(-cx)=-cx. Substitution and Boolean double negation turn
the displayed equality into c(cx)=cx. Thus idempotence need not be stored as
an additional equation. Also c1=1 by extensivity, and C3 at 1 then yields
c0=0. C2 gives additivity and hence monotonicity. Therefore c is a normal
additive extensive idempotent closure whose range is closed under complement.

### Rotation lemma

R2 makes r a bijection with inverse r^2. R1 says it preserves join. A
bijective join homomorphism is an order isomorphism: if rx <= ry, applying
r^2, which also preserves join, gives x <= y. Hence r preserves least and
greatest elements, meets, and the unique Boolean complement. In particular
r(-x)=-rx. We do not need to store this last equation separately.

Define

    c0 = c,  c1 = r c r^2,  c2 = r^2 c r.

Each is a conjugate of c by a Boolean automorphism, so each satisfies the
four usual Df3 closure equations. M says c0 c1=c1 c0. Conjugating this identity
by r and then by r^2 gives c1 c2=c2 c1 and c2 c0=c0 c2. Every E9 algebra
therefore has a Df3 reduct with these three operations.

## 2. Conservative equational-validity reduction

For Df3 terms, define tau by leaving variables, +, and complement unchanged
and mapping f to c, g to r c r^2, and h to r^2 c r. For every equation e,

    E18 proves e  iff  E9 proves tau(e).

The forward semantic implication follows from the reduct above. For the
reverse, take any Df3 algebra A with operations f,g,h. On B=A^3 define

    r(a0,a1,a2) = (a1,a2,a0),
    c(a0,a1,a2) = (f(a0),g(a1),h(a2)),

and use coordinatewise Boolean operations. The three conjugates of c are
(f,g,h), (g,h,f), and (h,f,g), respectively. All E9 equations hold, since f,g,h
commute pairwise. Assign each original variable x the diagonal triple
(a_x,a_x,a_x). A structural induction on t gives

    first_coordinate(tau(t)^B) = t^A.

Thus a counterexample to e in A lifts to a counterexample to tau(e) in B.
The diagonal is generally NOT a subalgebra: c(a,a,a) need not be diagonal.
Only the displayed coordinate identity is used.

For completeness, equational validity and provability can be connected here
without appealing to a black-box semantic theorem. Take the term algebra and
quotient by the congruence generated by contextual instances of the equations.
The quotient satisfies every defining identity, and two terms have the same
class exactly when a finite rewrite zigzag connects them. If an equation is
valid in every algebra, it holds in this quotient and has such a zigzag.

There is also direct proof transport in the reverse direction. Map an E9
term to a triple of Df3 terms, making Boolean operations coordinatewise,
interpreting c by (f,g,h), and r by coordinate permutation. Each E9 axiom
maps coordinatewise to an E18 axiom or a reflexive equation. For example M
maps to fgx=gfx, ghx=hgx, and hfx=fhx (up to renamed variables). Equational
inferences translate componentwise. A proof of tau(e) yields a proof of e
in coordinate zero. Fixed finite proofs of the reduct identities give the
forward syntactic transport. No formal PA certificate package is claimed
for these proof transformations in this deliverable.

### Do not transport nonlogical premises naively

If E18 plus a source theory T proves e, one cannot simply infer that the
product construction satisfies tau(T) in every coordinate. The other two
coordinates cyclically relabel f,g,h. Arbitrary T need not be invariant under
that relabeling. The correct application below translates a single designated
equation in the PURE algebraic basis. This avoids that premise issue.

## 3. One invariant generator, with an important typing distinction

Let p be one distinguished constant. For every one-generator Df3 equation e,

    E18 proves e iff E9 + {r(p)=p} proves tau(e).

The product countermodel above uses diagonal p, so satisfies the added ground
equation and retains every source counterexample. The reduct gives the other
direction. This may shorten the compiled target by eliminating terminal
rotations at p.

The extra equation is GROUND. It must never be treated as the schema r(x)=x
or allow uniform replacement of p by an arbitrary term. That schema forces
r=identity, identifies all three derived closures, and destroys the intended
reduction. The code deliberately matches literal p for this optional rule.

A pure E9 alternative is to replace the generator by P=p+rp+r^2p. R1/R2 make
P invariant, and the diagonal countermodel evaluates P to the original
diagonal p. This avoids the extra ground axiom but adds target syntax. Both
options need measured comparison after the actual target is available.

## 4. A finite target for Con(ZFC) using the proved pairing theorem

Let U be a fixed finite relational first-order theory, for example a precise
finite NBG presentation whose consistency is equivalent to Con(ZFC). First
replace multiple sorts by unary predicates if necessary. For exposition take
a single binary relation R and write A_U for the conjunction of its axioms.

For a membership structure, let

    Sing(s,x) := forall v (v in s iff v=x),
    PairSet(t,x,y) := forall v (v in t iff v=x or v=y),
    KP(z,x,y) := exists s exists t
      [Sing(s,x) and PairSet(t,x,y) and PairSet(z,s,t)].

For parameters d,e, interpret the original domain by x in d and the original
binary relation by

    R_e(x,y) := exists z (z in e and KP(z,x,y)).

Let psi_U be the pure-membership sentence

    exists d exists e [exists x (x in d) and A_U relativized/interpreted as above].

Every membership model of psi_U yields a nonempty U-model by satisfaction
induction. Conversely, from any set-coded U-model (A,R), choose a sufficiently
large limit ordinal lambda so that A, the set of Kuratowski pairs coding R,
and all required finite codes belong to V_lambda. The actual membership
structure on V_lambda satisfies psi_U. It is closed under finite unordered
and ordered pairing and its Kuratowski projections satisfy the concrete
pairing axiom pi+ used by Andréka--Németi. V_lambda need not model ZFC.

Consequently, ordinary ZFC proves

    Con(U) iff Sat(pi+ and psi_U).

The publication explicitly says that it only gives a weaker version of its
general Theorem 2.2. We do NOT rely on an unimplemented use of that theorem.
Instead use the displayed, proved Theorem 5.4 with empty T, and the standard
three-variable reduction f, whose property is that pi entails the sentence
(chi iff f(chi)). Since pi+ implies pi,

    proves_d h(f(not psi_U))
      iff pi+ entails not psi_U
      iff not Con(U).

Translate that one-letter modal formula to its Df3 term q_U(p), where p is
the one atomic formula and modalities become f,g,h. Put

    t_U(p) := tau(q_U(p)),   top(p) := p + -p.

Then

    E9 proves t_U(p)=top(p) iff not Con(U).

Thus the finite theory consisting of the nine E9 identities and the one
ground disequation t_U(p) != top(p) is equiconsistent with U, and therefore
with ZFC for the fixed calibrated U. A fair E9 rewrite search from t_U to top
has non-halting equivalent to Con(ZFC), by this ordinary ZFC proof.

This is a correct finite specification, NOT a delivered expanded t_U string.
The actual expansion of the chosen NBG sentence, f, h, and the pairing bridge
is still required before any target length or binary state count is claimed.
It can be very large. The known theoretical translation is not a license to
replace the binary membership atom by a single unindexed modal atom directly.

The nine equations by themselves have the one-element model and are plainly
consistent. Searching for an E9 contradiction therefore does not implement
the goal. The essential datum is the designated target equation, or
equivalently its ground disequation in the finite carrier theory.

## 5. Complete reference kernel and exhaustive numeric search

Ground terms use one leaf p and four constructors: -t, ct, rt, and t+u.
Every natural number is a term code, using Cantor pairing <a,b>:

    T(0)=p,
    T(4n+1)=-T(n),
    T(4n+2)=cT(n),
    T(4n+3)=rT(n),
    T(4<a,b>+4)=T(a)+T(b).

Every recursive argument is smaller than the original code, and structural
induction gives inverse encoding. The four-way constructor tag is obtained
by modulo 4; the old five-constructor Df3 grammar does not have that same
two-bit nonleaf tag. Actual decoder-state effects remain unmeasured.

A rewrite certificate selects one of the 18 axiom orientations, a tree
address, and one optional witness term. Matching against a fixed axiom
pattern determines all needed substitution terms except y in B3 used
backwards. Repeated metavariables must have equal matched subtrees. The
chosen matched subterm is replaced by the instantiated opposite side.
Ordinary address validity is checked; no binder, fresh-variable, alpha-
conversion, quantifier substitution, or derived-theorem substitution is used.

For fixed endpoints s,t, this is sound and complete. Soundness follows by
equational congruence. For completeness, take the ground term algebra on p,
quotient by finite contextual rewrite zigzags, and use it as above. It
satisfies every universal E9 identity because every assignment of finitely
many variables is represented by ground terms. Thus if E9 entails s=t, a
finite accepted script exists. Only reverse B3 introduces a variable absent
from the matched side, and the witness supplies every possible ground value.

The script codec enumerates all natural numbers as finite lists via
0=[] and n+1=<head,tail>; the tail is smaller than n+1. Step numbers use
divmod by 18, then Cantor unpairing for the address and witness. Addresses
are enumerated by deleting the first 1 from the binary representation of
n+1. These are total ideal finite-object operations. Checking candidates
0,1,2,... is therefore fair. An optional 20-orientation variant includes the
two orientations of the ground rule r(p)=p.

Python's available memory and recursion stack are finite; the supplied code
is a transparent reference implementation of that ideal total predicate,
not a claim that an arbitrary huge input completes on a physical machine.
The public certificate checkers validate exact natural-number types, AST
arities and the literal generator, rules, address bits, and witness terms;
Booleans are not accepted as natural numbers. The low-level `rewrite`
routine has a typed-input precondition. The numeric boundary constructs
typed trees by design, and malformed public inputs cannot pass merely
because their two endpoints compare equal.

## 6. Exact phase-placement compiler (implemented by the baseline agent)

For a source tree t and i in Z/3, let D_t[i] be the minimum cost of a native
tree representing r^(-i) tau(t), in the phase-placement grammar preserving
the source nonrotation tree. Before adding outer rotations, compute bases:

    B_p[0]=1; B_p[1]=B_p[2]=infinity,
    B_{-u}[k]=1+D_u[k],
    B_{u+v}[k]=1+D_u[k]+D_v[k],
    B_{c_j u}[j]=1+D_u[j], other phases infinity.

Then

    D_t[i] = min_k (((k-i) mod 3) + B_t[k]).

The realizing expression for a chosen k is r^(k-i) applied to the base
expression. Its denotation is r^(k-i) r^(-k) tau(t)=r^(-i)tau(t).
Negation and join rules use that r is a Boolean automorphism. The modality
rule uses r^(-j)tau(c_j u)=c r^(-j)tau(u). The minimum is exact in this
grammar by induction: any chain of outer rotations reduces modulo 3,
then the first nonrotation constructor is one of the listed bases. There
are three phases per source node, so cost and reconstruction take O(|t|).

With the ground invariant-generator axiom, set all three B_p entries to 1;
the same proof works. All six global permutations of modal names can also
be compared, because the pure Df3 basis is symmetric in its three closures.
This optimizer is not complete minimization modulo every E9 identity. It
does not, for example, use Boolean absorption or c-idempotence to delete
source nodes. Its exactness claim has the stated grammar scope.

## 7. Combined-unary E8 presentation

In E9 define s=(-) r^2. Since r commutes with complement,

    s^2=r,  s^3=(-),  s^6=identity.

Replace every complement by s^3, every r by s^2, and omit R2. This leaves
eight equations over +,c,s. Conversely, in any model of those equations,
B1--B3 make s^3 a Boolean complement. Its involution gives s^6=identity,
so r=s^2 satisfies r^3=identity, and all nine E9 equations hold with
complement=s^3. The conversions are inverse: in E9, s^2=r and s^3=(-);
in E8, (-)r^2=s^3 s^4=s^7=s. This is definitional term equivalence.

Exact prefix pairs are in the code/evidence. E8 has 90 basis nodes against
75 for E9, and a three-way nonleaf grammar against E9's four-way grammar.
The proposed advantage is one fewer operation kind and one fewer equation;
the disadvantages are longer expansions and a less convenient radix.
The delivered rewrite machine kernel is E9 (plus the optional ground rule),
not an independently compiled E8 engine.

## 8. Reproducible evidence and remaining work

Run `python test_rotation9.py` in this directory. The resulting
`rotation9_evidence.json` records four main 1000-code roundtrip sets (plus
the optional 20-orientation step codec), 18 forward/reverse axiom instances,
18 nested-context checks, an accepted three-step script with natural code
3208 and several rejected mutations, the ground-only invariant rule control,
eight product-lift algebras, 2400 term-coordinate checks, 2400 E8-fold checks,
and a concrete algebra satisfying every E9 equation except M. The last
control uses the 3-cycle on the Boolean algebra of subsets of {0,1,2} and
closure under the partition {{0,1},{2}}; x=2 falsifies M.

Next steps are concrete: choose the exact finite U already calibrated in
ProveIt; generate its coded-model sentence; implement and audit f and h;
record the complete target and its hash; compare naive/phase-optimized E9,
ground-invariant E9, and E8 target+basis size; compile the winning rewrite
kernel; account for blank-tape initialization and decoder; emit the full
transition table; then prove the executable search-to-table refinement.
Until those steps are done, this is a new candidate substrate and completed
algebraic module, not a smaller ZFC-equivalent Turing machine.

## Sources and repository provenance

* Andréka and Németi, *Formalizing set theory in weak logics, searching for
  the weakest logic with Gödel's incompleteness property*, arXiv:1111.0995,
  https://arxiv.org/abs/1111.0995 and https://arxiv.org/pdf/1111.0995 .
  The relevant locations are the equational presentation (pp. 5--6), the
  scope warning in the introduction (p. 3), and the proved Theorem 5.4
  (pp. 18--20). Root should open this source itself before citing its web ID.
* Earlier draft examined independently:
  https://www.renyi.hu/~nemeti/NDis/diagonalfree.pdf . Use the arXiv version
  for the explicit scope warning and stable citation.
* ProveIt pin 8cf840b8a26d002041e7a26dc9688ce7ce5fd751,
  `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/`.
  Relevant old discussions are intake-146-source-14,
  intake-150-source-22/23, and intake-151-source-25. Their 18-equation
  discussion is prior project material; the E9/E8 compression and complete
  fixed-equation rewrite kernel here are new relative to the inspected tree.

No historical priority is claimed for cyclic product constructions or
equational rewriting. The useful new artifact is their explicit combination,
calibration, proofs, and measured implementation in this project.
