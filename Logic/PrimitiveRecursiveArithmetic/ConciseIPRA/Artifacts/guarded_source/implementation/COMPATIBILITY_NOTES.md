# Equational bootstrap and the combined checker

Pinned source: VladimirReshetnikov/ProveIt, commit
1517d9d79ce33f631e0f82960c849427cbba23bf, under
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research.

## New mathematical statement

Literal-zero-source transport is admissible already in the following purely
equational calculus E-minus. Its terms are x, 0, S(t), I(n,a;u.h). Its only
formulas are equations. It has retained hypotheses, the two computation
schemas I(0,a;u.h)=a and I(Sn,a;u.h)=h[I(n,a;u.h)/u], transport through
equation templates whose source is syntactically different from 0, and
contextual induction for equations. It needs no logical binder or logical
case introduction. Induction's eigenvariable is absent from all retained
hypotheses and fixed parameters; the term t in a retained equation 0=t
stays fixed throughout the proof.

This is a dependency strengthening of the existing source_dispatch proof,
not a new singleton-test construction. Its sole numerical-case lemma can
be obtained from equational induction: if E(0) and E(Sz) have derivations,
weaken the latter by the unused hypothesis E(z), then induce. Every
transport motive in the bootstrap preceding full formula transport is
an equation. All remaining steps of the pinned proof therefore live in
E-minus. The notable result is compatibility with a core that no longer
has case introduction at arbitrary atomic D matrices.

## Audit of the equational proof

1. Reflexivity of r follows from b=r, b=I(0,r;u.0), using b=r as both
   major and minor, with motive v=r. The source b has an I head.
2. If p is not literally 0, symmetry and numerical congruence for p=q
   are ordinary permitted transports. No statement about semantic p!=0
   is being made.
3. If p,q are nonzero syntactic terms and p=0, q=0, join through the
   nonempty term z0=I(0,0;u.0). In detail, for bp=I(0,p;u.0), transport
   bp=bp at source p using p=0 to obtain z0=bp. Safe symmetry gives
   bp=z0; transport at bp with bp=p yields p=z0. Similarly q=z0.
   Symmetry at q and transport at z0 yield p=q. No transport starts at 0.
4. Put C(v,a,b)=I(v,a;u.b), Z(v)=C(v,1,0), K(v)=C(v,0,1),
   H(v)=C(v,1,2), N(n)=I(n,0;u.Z(u)), R(n)=I(n,0;u.H(u)),
   and L(n)=N(R(n)). Equational cases and forward computation establish
   H(v)=S K(v), R(1)=1, R(SSv)=2, N(1)=1, N(2)=0, L(1)=1,
   L(SSv)=0, and L(Sv)=Z(v). The last successor branch joins two
   nonempty terms known to equal 0 by step 3. Cases on
   v=C(Z(v),v,0) prove the unconditional filter equation for each target.
   All fixed substitution instances of these helper derivations retain
   S or I heads at their transport sources.
5. Retain 0=t, with t syntactically nonzero. Put A(n)=I(n,t;u.Su).
   Induct on the literal equation n=A(n). Its base follows from
   0=t and t=A(0) using source t. Its step follows from z=A(z)
   by successor congruence at source z and the I-headed computation
   for A(Sz), reversed at the nonzero source S A(z). At n=1 this
   gives 1=St. Congruence for L, the test identities and safe symmetry
   give Z(t)=1. Rewriting the unconditional filter at source Z(t)
   then at source C(1,t,0) gives t=0. For t literally 0 use reflexivity.
6. Full symmetry now follows. Numerical congruence at a zero source
   follows by reversing the source equation, using permitted congruence
   and reversing the result. Transitivity through a zero middle uses
   step 3 when both endpoints are syntactically nonzero; otherwise a
   premise is already the conclusion. This recovers all equation-template
   transports, including zero-source ones.

The proof does not assume substitution admissibility into arbitrary
E-minus derivations. Such substitution could turn a permitted variable
source into literal 0. Weakening, cut and renaming are safe. Helper
substitution is used only when the displayed transport sources stay
nonzero syntactically, and arbitrary targets of cases/induction are
supplied by their own inference rules.

## Administrative calculus U-minus

Terms are unchanged. Administrative formulas are equations, Q_y B, and
D_xy B. Its rules are Hyp, the two computation equations, source-restricted
transport, QE, DE, and one D introduction rule:

    from Gamma, B(t, eta(z)) |- B(t,Sz), infer Gamma |- D_xy B,

where eta(z)=z for a literal equation matrix and eta(z)=0 for a compound
matrix. The usual witness/eigenvariable side conditions apply. QE uses a
Q major and its zero instance. DE opens Q_y B(a,y) at a fresh a.

Every literal equation admits contextual induction here without transport:
use an unused D witness coordinate, progress introduction, DE, then QE
with the supplied base and target. Thus E-minus embeds in U-minus. Its
full equational transport theorem is available before reconstructing
any logical case rule or formula padding.

## Soundness of the administrative rules

Interpret equality and terms literally. Q_y B means B(0)->forall y B(y).
Interpret D_xy B by the following mixed reading:

* If B is an equation, it means exists x forall y (B(x,y)->B(x,Sy)).
* If B is compound, it means exists x (B(x,0)->forall y B(x,y)).

Atomic D introduction is directly sound. Its elimination exports Q_y E
using contextual equation induction. Compound D introduction uses ordinary
numerical coverage and its elimination is the usual existential rule.
Numerical substitution preserves whether a formula root is an equation,
so equality transport is sound for the mixed reading. None of this proves
completeness for all unguarded administrative formulas.

## Canonical language and completeness

Use exactly guarded_core's canonical Eq/D grammar: an atomic matrix directly
under D must be I(y,0;u.h)=I(y,0;u.k); otherwise its matrix must be compound
and canonical. This atomic zero instance is a theorem by computation. On
this canonical grammar the mixed reading and the ordinary uniform reading
D_xy B := exists x (B(x,0)->forall y B(x,y)) are provably equivalent in iPRA.
The forward implication for atomic matrices uses equation induction; the
reverse uses their theorem B(x,0). This agreement extends recursively.

To embed guarded_core's complete calculus G into U-minus, it remains only
to derive full transport on canonical templates; all other G rules are
literally available. Induct externally on the canonical formula template.
The equation case is the equational bootstrap above. For D over a compound
matrix, open the source D at fresh a; use target case introduction, transfer
its zero premise back by the induction hypothesis, specialize the source
Q clause at Sz, then transfer the successor instance forward. For D over
a guarded atomic matrix, open the source D, supply its computed true zero
instance, specialize its Q clause at Sz, transfer that equation forward,
and apply target progress introduction while ignoring its local IH.

Consequently every canonical G proof has a U-minus proof of the same
formula. Conversely every U-minus proof with a canonical end formula is
sound in iPRA; canonical agreement and the inherited G/iPRA bridge return
a G proof. The same argument works for finite contexts of canonical formulas.

This establishes the precise compact-checker contract: for a canonical
closed guarded formula A, an accepting certificate exists iff G proves A.
The proposed canonical theory has the already established bi-interpretation
with iPRA; its proof calculus may use administrative intermediate resources.
Terms, numerical equality and numerical domain are untouched, so the
inherited numerical composites remain the identity graph x=y. Formula
composites are the inherited guarded padding composites, not asserted for
arbitrary raw administrative formulas.

Do not claim that the syntactically restricted canonical calculus, with
all unguarded administrative intermediates forbidden, has been proved
complete by this argument. Do not claim that all of U-minus is synonymous
with iPRA under the mixed reading. The canonical-theorem contract is the
same one used by the pinned guarded_core compact profiles.

## Raw representation and the exact-root cleanup

The pinned arity codec has formula arities 1=D, 2=equation, 3=Q; zero or
surplus arities denote truth. The complete raw-alias soundness proof from
guarded_core continues to apply, with the mixed D interpretation above.
The new source dispatch is exactly source_dispatch's tested major selection.
Numerical nonzero syntax is truthy in canonical encoding, but no numerical
inequality is tested. Restricted computation packets are repaired using
c0=I(2,1;u.0)=0 and a transport at nonempty source c0, as in the pinned proof.

After composing the reductions, `not len(a) % 2` can become `len(a) == 2`.
All meaningful constructors retain the same rule. Empty and surplus arrays
that previously selected progress instead select cases; their formula
meaning is truth, so both choices are sound. The arithmetic supply argument
already proves soundness for either fresh or zero image by its zero-instance
lemma. This exact-root simplification is an implementation cleanup, not
another mathematical result or a theorem about parity of arithmetic values.

## Measurements and contract limits

The selected files are exactroot_checker_tokens.py (257/285/568),
exactroot_checker_ast.py (261/279/603), and exactroot_checker_bytes.py
(264/301/522), where coordinates are significant tokens / AST nodes /
normalized UTF-8 bytes. Their maximum-compression gzip sizes are 338,
345 and 328 bytes. All full modules include JSON parsing and ACCEPT output.
These are three different programs. There is no identified single program
below all three old attained minima 259 tokens, 283 AST nodes, 526 bytes.
The new attained minima over these profiles are 257, 279, 522.

Each selected profile also improves the corresponding pinned source_dispatch
profile without worsening a primary coordinate: token 259/289/572;
AST 263/283/607; bytes 266/305/526. The comparison uses the repository's
canonical-goal convention. It is not an absolute minimality result.

The compact profiles do not reject every noncanonical end statement. The
standalone exactroot_strict_checker.py includes guarded_core's public
closed-goal validator and the combined byte kernel. Its measured size is
490 tokens / 561 AST nodes / 1202 bytes; gzip9 is 571 bytes. Therefore the
522-byte figure must not be described as including canonical-goal validation.

## Executable evidence

composition_producer.py adapts the pinned untrusted normalizer. Its numerical
cases use equation progress while ignoring IH. Its new atomic guarded D/Q
transport branches explicitly supply the zero theorem and use progress.
It refuses to claim the same conversion for an arbitrary unguarded atomic
D/Q template. The main fixtures include direct zero-source transport under
guarded D, under a guarded Q resource, and under a compound D.

reproduce_composition.py creates the certificates, audits named proof nodes
for forbidden zero sources and wrong introduction modes, tests all three
compact profiles in ordinary Python and -O, runs the strict profile on
canonical examples, executes malformed/false/capture controls, and records
measurements. Neither producer nor any fixture/database is imported by a
selected checker. Finite tests verify the implementation on these examples;
they do not constitute a proof-assistant verification of the metatheorems.
