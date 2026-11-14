# A proof strategy for the internal PA196 consistency equivalence

This is a written syntactic proof strategy, not a checked additional internal theorem or a completed arithmetization of every representation bridge. The formula-template argument is given explicitly; Section 9 identifies the remaining obligations needed to turn it into a theorem about the repository's exact sentence and proof predicate. Inspected upstream: jamesyc/BusyBeaver at commit 407cdc356f6b586635e71ac92be394255f4bfea4.

## 1. Exact upstream status

PA196/Independence.lean proves `pa_proves_nonhalting_consistency`, whose conclusion is PA proving nonhalting implies Con(PA). It does not state the converse internally. PA196/Logic/FiniteModel.lean uses an external type of hereditarily finite lists and classical filtering for pointed separation. PA196/Logic/Soundness.lean explicitly calls its soundness theorem external. PA196/Nonhalting.lean combines that theorem with the tape simulation. These facts support ordinary mathematical nonhalting but alone do not provide an internal PA equivalence.

The proposed route to the converse is a syntactic PA proof compiler. Its only substantial arithmetic axiom template is finite bit comprehension for an arbitrary inserted formula. No global arithmetic truth predicate is used.

## 2. The arithmetic formula compiler

Use precisely the numeric constructors and decoder in PA196/Logic/Basic.lean and PA196/Logic/Decode.lean:

\[
 p(a,b)=\binom{a+b+1}{2}+b,\quad I(a,b)=4p(a,b),\quad M(a,b)=4p(a,b)+1,
 \quad U(a,B)=4p(B,a)+2,\quad E(a,b)=4p(a,b)+3.
\]

The decoder sends zero to truth. At positive code, the residue modulo four determines implication, membership, universal quantification or equality. A universal constructor takes its label from the RIGHT Cantor component. Every label appearing in a decoded code c is less than c; hence x_c is absent even as a bound label in that formula.

Translate source x_i to arithmetic variable v_(2i), using odd indices for local bound variables. Write Bit(A,b) for bit b of A being one. In a fixed conservative definitional extension of PA by e(n)=2^n, one definition is

\[
 \operatorname{Bit}(A,b)\equiv
 \exists q\exists r\,[r<e(b)\wedge A=q\,e(b+1)+e(b)+r].
\]

All local binders are freshly renamed. The exponential symbol is fixed shorthand for its ordinary PA graph, whose totality and uniqueness PA proves. Elimination of this definitional extension is an effective syntactic proof translation back into ordinary PA.

Define the primitive recursive formula function J by

\[
\begin{aligned}
 J(0)&=(0=0),\\
 J(M(a,b))&=\operatorname{Bit}(v_{2a},v_{2b}),\\
 J(E(a,b))&=(v_{2a}=v_{2b}),\\
 J(U(a,B))&=\forall v_{2a}\,J(B),\\
 J(I(a,b))&=J(a)\to J(b)\quad\text{if }(a,b)\ne(0,0).
\end{aligned}
\]

The total decoder has explicit fuel c+1; alternatively compute a course-of-values table of syntax codes through c. With a fixed primitive recursive coding of syntax trees/lists this makes J primitive recursive on EVERY natural input. The bound is on recursion depth, not on output size: large expansions are permitted, and iterated primitive-recursive bounds on syntax construction suffice. Crucial exception: I(0,0)=0. Therefore J(I(0,0)) is truth rather than the literal formula truth implies truth. Insert a fixed logical equivalence proof in this case. Uniformly, a primitive recursive compiler can emit a PA proof of

\[
 J(I(a,b))\leftrightarrow(J(a)\to J(b)).
\]

Also 1=M(0,0), so J(1)=Bit(v_0,v_0), not literal falsity. PA proves Bit(A,b) implies b<A, using 2^b<=A and b<2^b. Thus PA proves forall u not Bit(u,u). Every negative code N(B)=I(B,1) consequently has its usual negative reading via a fixed PA proof. This remains valid when x_0 is bound elsewhere, since the self-membership prohibition is universal.

## 3. Finite comprehension as a uniform proof template

For each arithmetic formula psi(i,zbar), of arbitrary quantifier complexity, with n,s fresh, PA proves

\[
 \forall n\;\exists s<2^n\;\forall i<n\,
 [\operatorname{Bit}(s,i)\leftrightarrow\psi(i,\bar z)].\tag{FC}
\]

Use exactly the displayed existential bounded-bit statement as the induction invariant. At n=0 take s=0. At the successor, given a witness s<2^n, split on the classical formula psi(n,zbar). If it holds, choose s'=s+2^n; otherwise choose s'=s. The lower n bits are unchanged; bit n respectively becomes one or remains zero; and s'<2^(n+1). These bit identities are fixed arithmetic lemmas. Existential elimination and introduction give the induction step, and one instance of the ordinary PA induction schema gives (FC).

This procedure DOES NOT decide psi. It emits an excluded-middle instance with psi inserted. A primitive recursive function fcProof takes well-formed syntax of psi, allocates fresh variables, instantiates the fixed base/step proofs and the induction schema, and concatenates them. Its intended uniform proof-checker correctness lemma is verified by syntactic induction after fixing the PA presentation and its proof coding. Invalid syntax inputs may return a fixed proof of truth. The correctness assertion is that the output is a proof of the corresponding instance, not that arbitrary PA theorems are true.

For pointed separation, substitute

\[
 \psi(i)=((\operatorname{Bit}(A,i)\lor i=B)\wedge\varphi(i)),
 \qquad n=A+B+1.
\]

Every desired bit lies below n because Bit(A,i) implies i<A. The bound s<2^n supplies zero bits above n. Thus PA proves

\[
\begin{split}
 \exists s\bigl(&\forall i[
 (\operatorname{Bit}(A,i)\to(\varphi(i)\to\operatorname{Bit}(s,i)))
 \wedge(\operatorname{Bit}(s,i)\to\varphi(i))]\\
 &\wedge(\varphi(B)\to\operatorname{Bit}(s,B))\bigr).\tag{PS}
\end{split}
\]

This is a PA theorem for each inserted phi, with A,B and the remaining parameters free or universally closed. The proof compiler need not calculate the witness s.

## 4. The exact guarded bundle

The actual definitions are

\[
\begin{aligned}
 \Delta&=E(a,b)\to U(c,E(a,b)),&V&=M(a,b)\to U(c,M(a,b)),\\
 P&=c\to M(c,b),&
 S&=U\bigl(b,(M(a,b)\to P)\wedge(M(c,b)\to c)\bigr),\\
 Q&=U(c,S\to N(P)),&
 F(a,b,c)&=N(\Delta\to(V\to Q)).
\end{aligned}
\]

Assume the syntactic guard c differs from a,b. The images of Delta and V are ordinary vacuity theorems because x_c does not occur in those atoms. Apply (PS) to J(c), substituting a fresh variable for its free occurrences of x_b. Source self-freshness ensures x_c is absent in J(c), so the new witness can use x_c without capture. For a different from b, (PS) supplies a witness for S and P after alpha conversion.

There is an essential index case a=b. Under the universal binder x_b, M(a,b) becomes self-membership, hence false. In this branch apply (PS) with arithmetic set parameter A=0 and B equal to the original free x_b. The resulting singleton-or-empty witness proves the second conjunct and pointed clause; the first conjunct follows from the PA theorem forbidding self-membership. This branch tests equality of variable INDICES, which is primitive recursive. Ignoring it would give an invalid capture argument.

We have a PA proof of exists x_c(S and P). Under the assumption Delta implies (V implies Q), apply the already proved Delta,V to obtain Q. At the supplied witness Q says S implies not P, contradicting S and P. Fixed propositional and quantifier templates therefore yield J(F(a,b,c)), accounting for the code-zero collapse and the nonliteral falsity code via the bridge proofs above. If the guard fails, the actual command yields zero, with its fixed truth proof.

Therefore gateProof(a,b,c) is a primitive recursive PA proof-template compiler for the exact guarded output. Its arbitrary-formula content enters solely as an ordinary induction INSTANCE in (FC).

## 5. Other heads and proof-tree compilation

The six heads in actual push order are:

1. (exists x_D forall x_D H) implies H.
2. forall x_D forall x_A H implies forall x_A forall x_D H.
3. M(H,D) implies (E(H,A) implies M(A,D)).
4. E(H,D) implies (M(A,H) implies M(A,D)).
5. exists x_D E(H,D).
6. forall x_D A implies (forall x_D(A implies H) implies forall x_D H).

Under J these are a nonempty-domain logical theorem, commutation of universal quantifiers, two equality substitution instances, an equality witness, and universal modus ponens. Coincident labels in heads 1,2,5 are dealt with by syntactic cases and alpha conversion. Each has a fixed proof template. The propositional head

\[
 ((H\to d)\to D)\to((D\to H)\to(A\to H))
\]

is valid for arbitrary d,D,H,A. The numeric restriction d<=D need not be used for soundness, though it remains part of the actual command and completeness argument.

The saved top keeps its existing proof. The generalization U(d,h) is obtained from the existing proof of J(h); there are no undischarged assumptions. Numeric MP compiles to PA MP plus the constructor bridge. In the code-zero exceptional case emit the fixed truth proof. With these clauses, primitive recursion on a finite native proof tree gives compile(p), and PA proves

\[
 \operatorname{NativeProof}(p,c)\to
 \operatorname{PAProof}(\operatorname{compile}(p),J(c)).\tag{PC}
\]

One may first use a PA proof system allowing open formulas as theorems, then translate to universal closures by fixed specialization/generalization proofs. This convention must be fixed before specifying the final proof predicate. At c=1, append the theorem not Bit(v_0,v_0) to derive an ordinary PA contradiction, then translate to the designated falsum of the target presentation. Foundation's standard provability predicate uses its quoted falsum, so an implementation must include this final coding bridge rather than silently substitute a different consistency predicate.

## 6. A halting command execution gives a PA refutation

Instrument the exact store (t,w,d,h) of PA196/Commands/Store.lean with PA proofs of J(t), J(h) and each Cantor-paired stack formula. An empty tail yields code zero with its truth proof. The initial all-zero store has such annotations.

AX(c,x,y) produces the six heads, propositional head, generalization, saved top and guarded gate by the compilers above. MP(x) tests I(t,d+x)=h. If true, apply MP to the annotations; if false, its actual result is zero. Its pushed zero is likewise annotated. Shift moves annotations normally if t+h differs from one. If t+h=1, arithmetic gives t=1 or h=1. An available annotation therefore proves J(1), hence gives a PA refutation.

All proof duplication, syntax construction and concatenation admit primitive recursive implementations. Given the proof-checker lemmas above, induction on the finite command trace gives the intended internal statement

\[
 \operatorname{CommandHaltingTrace}(z)\to
 \operatorname{PAProof}(f(z),\ulcorner0=1\urcorner)\tag{CT}
\]

for a primitive recursive f. Under Con(PA), this gives a syntactic proved-store invariant and a successful next command. This replaces the external HF soundness used by the upstream CommandSoundness module.

## 7. From command safety to the exact literal trace sentence

An internal converse must also justify the tape-to-source connection. The inspected proof exposes all required finite mechanisms:

* PA196/Startup.lean: the explicit 58,154-step startup.
* PA196/Source/CommandTransfer.lean: every successful parsed command has a POSITIVE finite source segment returning to a command boundary.
* PA196/PrimitiveSimulation.lean: each nonhalting register instruction has a POSITIVE finite tape segment between its frames.
* PA196/Coverage.lean: all 3,812 source sites have checked contracts.
* M6/Source/CyclicInvariant.lean and M6/PositiveInvariant.lean: positive progress excludes a finite halt.
* PA196/PhysicalEndpoint.lean: the external theorem blank_halting_iff_source.

These contracts involve only finite lists/natural numbers, elementary register operations, primitive recursive configuration coding, and natural-number induction. The fixed table checks are finite PA computations. Runtime contracts are proved by induction on unary blocks and register values, source contracts by induction on macro counters. Their arithmetization uses no statement that PA itself is consistent.

Here is the positive-progress argument entirely within arithmetic. Let Inv be an arithmetic invariant of nonterminal configurations, and suppose PA proves

\[
 \operatorname{Inv}(c)\to\exists n>0,d\,
 [\operatorname{Run}(c,n,d)\wedge\operatorname{Inv}(d)].
\]

Suppose an Inv configuration halts at time m. By strong induction on m, take the next positive segment of length n. If n<=m, determinism gives a halt from its Inv endpoint in m-n<m steps, contradicting the induction hypothesis. If n>m, a finite successful tape segment cannot pass through an undefined transition; in the absorbing source convention it would instead end in the same halted configuration, contradicting Inv. This is ordinary PA strong induction, not a transfinite or semantic soundness argument.

Applying this first to the syntactically annotated command boundary invariant under Con(PA), then to the register-instruction tape frames, and prepending the fixed startup is the proposed route to

\[
 \mathrm{PA}\vdash\operatorname{Con}(\mathrm{PA})\to\neg H_{196}.\tag{REV}
\]

It is important to present the source/tape contract arithmetization explicitly: an external Lean simulation does not AUTOMATICALLY entail a PA proof. Here the finite arithmetic structure of the contracts and the displayed strong-induction argument give the formalizability reason. A fresh checked Lean declaration with conclusion PA proves Con(PA) implies nonhaltingSentence, instantiated with the literal trace coding, remains a distinct mechanical task. It is not already an upstream theorem.

Once the proof-checker, simulation-arithmetization and exact-sentence bridges have been supplied, combining (REV) with the upstream internal forward implication would yield

\[
 \mathrm{PA}\vdash\bigl(\neg H_{196}\leftrightarrow\operatorname{Con}(\mathrm{PA})\bigr).
\]

For a reduced machine N one additionally needs a PA-formalizable finite simulation proving H_N iff H_196. A proved state merge or startup replacement can supply this; agreement for finitely many blank-tape steps does not.

## 8. ConciseIPRA: transfer and barrier

The inspected ConciseIPRA README presents theories bi-interpretable with iPRA, with equation induction. Directly replacing the PA search by those smaller checkers changes the target consistency statement. Useful transferable ideas include witness-controlled dispatch, fusing equality with witness discharge, and moving computations into syntax.

A possible new PA-level direction is to strengthen the native scalar core's progress rule from literal equations to all native formulas. Its unchanged logical macros and full induction then suggest a presentation of Heyting arithmetic with primitive recursive function definitions. HA and PA are equiconsistent via the primitive recursive negative translation and inclusion into classical logic. This needs its own complete equivalence proof and state compiler. In particular Python checker length does not estimate binary single-tape state count, and full normalization is not a free primitive. This is a research direction, not an established sub-196 construction.

## 9. Independent review: exact scope and remaining bridges

The logical core survives the following alias/capture checks.

* The only implication-constructor collapse is I(0,0)=0; the fixed bridge is required at every nested occurrence, not only at the outer head.
* Code 1 is M(0,0), not a logical falsum symbol. Its PA refutation must be universally closed before a surrounding quantifier can bind variable 0. The theorem that no natural number has its own bit set handles this uniformly.
* If c=0 while a,b are nonzero, the gate witness variable is x_0, also present in the translated falsity code. This is harmless only because the falsity bridge is the universal PA theorem, valid at every assignment to x_0.
* If a=b, the first membership atom under U(b,...) changes from a free-set membership test to self-membership. The separate A=0 singleton branch above is necessary.
* Capture-avoiding substitution replaces only free occurrences of x_b in J(c). Existing inner binders with the same label must continue to shadow their occurrences. Odd helper variables are freshly renamed before every substitution; the even variable x_c is absent from the complete translation of c apart from harmless freshly renamed helper syntax.
* Empty-stack underflow and the stack alias pair(0,0)=0 are covered by a finite explicit proof-stack certificate or by canonical truncation of a zero tail. Either convention must match the exact Shift and MP clauses. MP pushes a zero only on its successful branch; its failed branch retains the old stack and puts zero in the top.

The following are still implementation/formalization obligations, not results of the small executable regressions elsewhere in this research package.

1. **Fix the final syntax and proof predicate.** Supply the primitive recursive translation from the displayed even-variable arithmetic syntax, its exponential definitional extension, and its open-formula proof convention to Foundation's Peano theory, universal closures, and standard provability coding. PA proves elimination of the exponential extension, but those proof transformations have not been emitted here.

2. **Prove the uniform proof-checker lemmas.** Give explicit definitions of J, fcProof, gateProof, the fixed head proofs and command annotation updates, with well-formedness, freshness, closure and output-proof correctness. The proof sizes can be bounded by primitive recursive iterations of finite syntax operations. No bound on numerical witness searches for arbitrary psi may be used; the comprehension proof is syntactic and uses excluded middle instead.

3. **Arithmetize source and tape contracts.** The inspected CommandTransfer and PrimitiveSimulation proofs use finite configurations, finite instruction sets and natural-number inductions. This gives a reason to expect PA formalizability, but the present draft does not list and translate every supporting lemma to the chosen arithmetic coding. The scheduler's startup to site25, register/spare-file invariants, every positive runtime segment, and the undefined-transition convention all have to appear in that internal chain. Merely citing an external Lean theorem or a Python symbolic check does not discharge this obligation.

4. **Bind the exact halting sentence internally.** `SentenceCorrectness.lean` proves a standard-natural-number truth equivalence for the published sentence. That theorem alone is insufficient for the internal converse. Supply a PA proof connecting `HaltingFormula.traceSentence`, its padded natural tape/beta-sequence coding, and the finite literal traces used by the new invariant. Also identify the output contradiction with `M6.PA.theory.standardProvability.con` as used by `M6PA/Calibration/Foundation.lean`. Matching only standard truth would leave a genuine gap in an assertion of PA-provable equivalence.

No obstacle to these syntactic steps has been identified, and the explicit finite-comprehension construction avoids the main truth/reflection trap. Nevertheless the exact PA-provable equivalence is not reported as a newly mechanically certified result by this draft. The appropriate description is **a detailed route to the internal reverse implication with outstanding arithmetization and coding obligations**.

## Pinned references

All BusyBeaver files above are relative to

https://github.com/jamesyc/BusyBeaver/blob/407cdc356f6b586635e71ac92be394255f4bfea4/

Exact additional endpoint references: PA196/Arithmetic/RefutationHalting.lean (internal forward implication using all-model correctness), PA196/Independence.lean (Con(PA) endpoint), PA196/Arithmetic/Machine/Exact/SentenceCorrectness.lean (literal trace formula binding).

ConciseIPRA README inspected via GitHub:
https://github.com/VladimirReshetnikov/ProveIt/blob/main/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md
with blob SHA 5526b516e20d61d89c1a1575744d35742f669efd.
