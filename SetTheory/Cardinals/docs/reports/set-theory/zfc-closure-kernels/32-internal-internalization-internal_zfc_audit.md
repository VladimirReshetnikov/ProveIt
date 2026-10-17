# Internal-ZFC audit and logical proposal

Prepared for the root report. Source cutoff for all upstream theorem claims below: **jeff87654/busy-beaver PR #20, 0d544f2a2e3c18f12278441a74b7879f31cbe856**. The separate incoming ProveIt packages are those extracted by the repository-audit agent at the requested snapshot, not later mutable-main reconciliations.

## Deliverables and exact closure

- **internal_zfc_proposal.tex** is a LaTeX-ready section containing the detailed mathematical argument and qualifications.
- **E2E253FullReg.v** is an additional proposed Coq composition giving the conventional Foundation-and-Choice endpoint. **It has not been kernel-checked locally.** Its header says this explicitly.
- **upstream253/** now contains **all 160 Coq source modules** in the Audit253 import dependency closure, totaling **2,770,345 bytes**. Every file was verified against its Git blob SHA1 in the exact pinned Git tree.
- **upstream253_source_manifest.json** records those Git blob hashes, SHA256 hashes and byte counts. These are source modules, not the Coq standard library or compiled proof objects.
- **audit_tail252.py** and **tail252_audit.json** independently check the proposed append-one decrement macro. They do not certify a blank-tape 252-state consistency machine.

The full 160-module closure was independently fetched through the GitHub connector. It was not independently recompiled here. The public CI compile/coqchk evidence was fetched and audited by the machine agent; distinguish those two evidence sources.

## Exact theorem interfaces and source locations

All locations are relative to the upstream repository, with line numbers in the exact pinned originals.

| Path and line | Statement or role |
|---|---|
| ZF/m253/coq/e2e/E2E253.v:36 | zf253_halts_iff_SIR: halts tm c0 iff SIR has a classical finite natural-deduction refutation |
| ZF/m253/coq/e2e/E2E253.v:42 | zf253_halts_iff_ZF: halts tm c0 iff Std_iface.ZFc has such a refutation |
| ZF/m253/coq/e2e/E2E253.v:45–47 | zf253_halts_iff_ZFC: halts tm c0 iff (ZFc + ax_ac) has such a refutation |
| ZF/stdzf/coq/Std_iface.v:26–34 | ZF0base, ZF0 schema constructors, ZFc = ZF0 + ax_om' |
| ZF/m254/coq/settheory/S_def.v:26–44 | ax_cp, ax_ir, gic, Sbase, S0, SIR |
| ZF/m254/coq/settheory/S_main.v:23 | ZF_to_S0: ZFc ⊢TC ⊥ → S0 ⊢TC ⊥ |
| ZF/m254/coq/settheory/S_main.v:32–36 | ZF_to_S and S_equicons: SIR ⊢TC ⊥ ↔ ZFc ⊢TC ⊥ |
| ZF/m254/coq/settheory/S_sound.v:267,275,301 | SIR_L, S_to_ZFR, S_to_ZF |
| ZF/stdzf_r3/zfc/Z_main.v:38 | ac_relcon: (ZF + Reg + AC) refutation → (ZF + Reg) refutation |
| ZF/stdzf_r3/zfc/Z_main.v:67–69 | ac_reg_relcon: full (ZFc + Reg + AC) refutation → ZFc refutation |
| ZF/stdzf_r3/zfc/Z_main.v:83 | ZFCReg_equicons: full (ZFc + Reg + AC) refutation ↔ ZFc refutation |
| ZF/stdzf_r3/regcon/MinZF.v:82 | Definition of the actual ax_reg' used in the full endpoint |
| ZF/stdzf_r3/regcon/Link.v:48–52 | regularity_relcon_std and bridge_std |
| ZF/m253/coq/tm/Box.v:286 | Positive-decrement macro contract |
| ZF/m253/coq/tm/Sim.v:82,118 | Arbitrary-suffix dispatch invariant and invariant-preserving machine step |

**Load-path correction:** the actual Coq root named ZF points to **ZF/stdzf/coq**, not ZF/stdzf_r3/coq. RegCon and ZFC do point into stdzf_r3. The library's ZFc omits Regularity and Choice. The public theorem named zf253_halts_iff_ZFC therefore has a literal RHS missing Regularity. This is a naming/interface distinction, not a discovered failure of the relative-consistency mathematics: ZFCReg_equicons is already available.

The extra file E2E253FullReg.v composes zf253_halts_iff_ZF with the symmetry of ZFCReg_equicons and negates. In its definition, the full theory is exactly

    (ZF.Std_iface.ZFc phi \/ phi = RegCon.MinZF.ax_reg')
        \/ phi = ZFC.Z_wo.ax_ac.

The order in the published removal proof is **remove Choice over ZF with Regularity, then remove Regularity**. A description saying that this specific proof first removes AC over bare ZF without Reg would be wrong.

## The precise internalization criterion

Choose a primitive-recursive finite-refutation predicate Ref_T(p) for a conventional effective presentation. Certificates may carry axiom schema matrices and closure lengths, so checking the axiom witness remains primitive recursive. Let H_M(t) mean that the literal blank-tape machine halts by step t.

The following is an ordinary theorem proved by elementary logic **inside ZFC**:

If ZFC proves both

\[
\forall t\,(H_M(t)\to\exists p\,\mathrm{Ref}_T(p)),
\qquad
\forall p\,(\mathrm{Ref}_T(p)\to\exists t\,H_M(t)),
\]

then it proves

\[
\neg\mathrm{Halt}(M)\leftrightarrow\mathrm{Con}(T).
\]

Compose with an internal Con(T) ↔ Con(ZFC) theorem to obtain the user's exact target. Explicit primitive-recursive witness maps would be particularly reviewable, but are a sufficient extra condition, not a necessary condition. Do not assert an unproved primitive-recursive execution-time bound.

This formulation needs neither a truth predicate for the ambient ZFC universe nor Con(ZFC). It is an equivalence theorem about finite syntax and finite runs. A serialized ZFC proof is one way to establish it; an ordinary mathematical reconstruction wholly within ZFC also suffices.

## SIR and a direct ordinary ZFC transport

SIR uses no function symbols, and two predicates: membership and equality. Its equality axioms are reflexivity, symmetry, transitivity and membership congruence. Its nonlogical content is CP, every universally closed GIC instance, and IR:

\[
\forall p\exists V\,[p\in V\land
 \forall x\in V\,(x\subseteq V\land
       \exists W\in V\,\forall z(z\subseteq x\to z\in W))].
\]

\[
\forall B\exists C\,[
 \forall a\in B\,\forall y(\phi(a,y)\to
          \exists y'(\phi(a,y')\land y'\in C))
 \land \forall y\in C\,\exists x\phi(x,y)].
\]

\[
\forall x\,\neg(x\in x).
\]

Parameters in phi are universally closed. This is an infinite recursive schema, not a finite one-axiom first-order theory. The S_main proof also gives S0 (without IR) the same consistency strength, but deleting IR from the theory does not imply the compiled 253-state program can simply be shortened.

A direct ZFC proof-template construction validates every SIR axiom:

1. For CP choose lambda = rank(p) + omega and V = V_lambda. For x in V_lambda take W = P(x). The limit-rank bound puts W in V_lambda, and transitivity gives x subset V_lambda.
2. For GIC use Collection; or derive this instance from Replacement by collecting least witness ranks over the set of nonempty fibers. A rank bound contains a witness for every nonempty fiber. Filter it by “has a phi-predecessor” to obtain the global support clause. No simultaneous arbitrary-witness choice is needed.
3. Foundation implies IR. Actual equality validates the equality axioms.

These are uniform finite proof templates in phi. Hence they give an ordinary syntactic transport from SIR refutations to conventional ZFC refutations.

For the reverse transport, use the published finite Foundation/Choice removal, then the SIR bisimulation-quotient interpretation. Its Eqv is “some membership back-and-forth bisimulation relates the two objects”; Mem(x,y) is “some Eqv-equivalent representative of x belongs to y.” The raw closure/collection lemmas supply the interpreted elementary axioms, Separation, Replacement and Infinity. S_main.ZF_to_S0 is an explicit finite-derivation transform, not merely a semantic slogan.

The conventional signature bridges should be stated: equality predicate versus logical equality, set-operation symbols versus the minimal signature, and the disjoint-family choice-set form versus arbitrary-family Choice by tagging and projection. All have elementary finite proof translations.

## Coq strength: the important positive point and the genuine remaining gate

A closed Coq theorem plus recursive coqchk is **not automatically** the corresponding theorem provable in ZFC. Universe constructions may be stronger than ZFC under their general set-theoretic semantics. “Closed under the global context” does not measure universe strength.

There is a concrete import issue in this pinned closure:

- ZF/stdzf_r3/vendor/undecidability/theories/FOL/Sets/Models/Aczel.v:12 contains the universe-indexed Acz inductive with arbitrary Type-indexed branches.
- The regularity bridge imports modules that include this semantic construction.
- Therefore do not call all 160 imported modules universe-free.

But this does **not** show the endpoint actually needs Aczel's universe construction. The inspected helpers used across that import boundary are purely syntactic:

- ZF_conservativity.v:190, prv_embed, translates finite deduction trees by induction.
- PCPb_to_minZF.v:1048–1083, rm_const_prv' and rm_const_prv, remove defined set-operation symbols from finite derivations.
- ZF_conservativity.v:112 and :151, minZF_sep and minZF_rep, compare translated schema instances by substitution and logical derivations.

These can be proved directly in ZFC and used as cut interfaces. The operational, program and logical layers likewise use natural numbers, lists, finite trees, structural recursion and induction. A reconstruction should replay these concrete arguments and the syntactic set-theory translations; it need not interpret every unrelated imported semantic model.

**Honest final scope:** we audited the interfaces, selected proof bodies and complete source closure, but have not reconstructed every opaque term or supplied a full ZFC formal replay. State the external 253-state Coq equivalence as established by its pinned public verification, and the internalization criterion/replay as a concrete proposal. Do not present Coq⇒ZFC as an automatic implication. Conversely, do not claim that absence of a serialized proof makes the ordinary ZFC theorem impossible: ordinary finite-syntax reconstruction is sufficient.

Primary background: Werner, “Sets in Types, Types in Sets” (TACS 1997), https://www.lix.polytechnique.fr/Labo/Benjamin.Werner/publis/tacs97.pdf ; Barras, “Sets in Coq, Coq in Sets” (2010), https://jfr.unibo.it/article/view/1695 (DOI 10.6092/issn.1972-5787/1695). These justify the general caution, not a claim that this endpoint requires inaccessible cardinals.

## Independent 252-state macro audit

Candidate table edits in old labels: delete old5, restore (49,1) = (0,R,64), change (97,0) from (0,L,112) to (1,L,112), start old97. Its first two blank moves match public253 after four moves exactly, at state131/head−2/ones{-1,0}. But the later blank bootstrap failed in the machine agent's 4-million-step search: this is **not** a verified 252-state consistency machine.

The useful local result is strong and independent. The positive-decrement contract changes only the appended spare block from value0 to value1. With

\[
\mathrm{sepsR}(v_0,\ldots,v_k)=
   0\,1^{v_0+1}\cdots0\,1^{v_k+1},
\]

the output is sepsR(decr(r,vs) ++ [1]) and the same return state (63 for r=0, 48 otherwise). The initial state43 marked register encoding and arbitrary finite left context are preserved.

The Coq proof skeleton changes pad2 to pad3, [false;false] to [false;false;false], and its final appended tape fragment from [false;true;false] to [false;true;true;false]. shift_dec and shift_dec_block already quantify arbitrary right suffixes. SymExec/Site's decrement denotation must append [1]. Sim.Inv already permits arbitrary ext; its positive branch changes ext ++ [0] to ext ++ [1]. All dispatcher-site certificates still require rerunning after the49 reroute.

Independent finite audit: **6,576 cases**, all nine register positions, nonzero selected values, arbitrary spare suffixes and left contexts, **1,859,630 literal TM moves**, all exact final tapes and return states correct. This tests the local macro; it neither proves all cases by kernel check nor establishes blank initialization. The files explicitly record blank_bootstrap_verified=false.

## Incoming theoretical packages

Both exact incoming source packages audited at the repository agent's pinned snapshot:

- EPSC2's two-parameter argument appears sound at ordinary mathematical level. It gets decoder/transitive covers before Union, binary common bounds with exactly a,b, hereditary Pairing before tuple packing, graft with t,a, support filter with C0,t (the seed has disappeared), and final saturation with C1. It does not pack arbitrary raw predicates before hereditary invariance. It supplies an infinite recursive schema, not finite axiomatization or a four-variable logic. Its341/343-state initializer tables explicitly do not implement EPSC2.
- The protected unary rule's proof also appears sound. The guard must be open B_rho(p), not its prematurely universal closure. Universal projection forall b beta allows the specific boundedness witness to bound the projected fiber. Existential projection would fail. A closure rule is applied only to a globally proved premise, not under a local hypothesis. It is an effective presentation transformation, with no compiled state bound.

The final report should credit both as existing incoming proposals, not claim them as new results of this session.

## Logical qualifications worth retaining

If a fixed finite theory U has a finite model, ZFC verifies that model and proves Con(U). Assuming ZFC consistent, it cannot also prove Con(U) ↔ Con(ZFC). In particular a consistent finite universal purely relational theory with finitely many constants and no nonconstant functions has a finite submodel and is unsuitable. This obstruction explains why a shorter universal relational sentence alone is not enough.

The target equivalence plus consistency of ZFC prevents ZFC from proving nonhalting by Gödel II. Excluding a proof of halting additionally follows from Sigma1-soundness, since halting is Sigma1. Mere consistency of an arbitrary theory does not in general stop it from proving its own inconsistency. Make equivalence, rather than an overstated independence consequence, the main goal.

