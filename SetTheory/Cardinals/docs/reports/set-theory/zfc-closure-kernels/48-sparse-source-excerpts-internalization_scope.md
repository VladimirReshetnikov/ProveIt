# Scope audit and a precise ZFC internalization criterion

Prepared for the ProveIt research report. This note distinguishes an ordinary mathematical proof in ZFC from a Lean/Coq theorem whose metatheory has not been translated into ZFC. It supplies proved general lemmas and concrete remaining interfaces; it does not claim to have built an object-ZFC proof of the current 252-state endpoint.

## 1. Exact source status

The upstream `jeff87654/busy-beaver` main branch inspected through the GitHub plugin is `ec9ed4f713d8c017f15743ad0692cdf31a59952a`, authored 2026-10-17 01:12:56Z. Its `ZF/m254/machine/zfc_254.tm` has SHA256 `d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb`: 254 nonterminal states, two symbols, start state 0, blank symbol 0, and a distinct uncounted terminal state 254. The state type in `TM254.v` has 255 elements because it includes the terminal. Thus the 254 convention is not 254 total states.

The exact upstream endpoint `ZF/m254/coq/e2e/E2E254.v` proves halting iff finite classical refutation of SIR, ZFc, and ZFc+AC. Here ZFc, defined in `ZF/stdzf/coq/Std_iface.v`, omits Foundation; its schemas are universally closed. `ZF/stdzf_r3/zfc/Z_main.v` separately supplies `ZFCReg_equicons`, including Foundation. These are not interchangeable names, although the finite-refutation comparisons are supplied upstream.

Upstream PR20, head `0d544f2a2e3c18f12278441a74b7879f31cbe856`, is open and proposes 253 working states. Its body explicitly limits the claim to an external halting/refutation equivalence and disclaims an extra internalization claim. It changes old rows 3/0, 5/0, 5/1, and 49/1; deletes old8; and uses old5 as the shared startup/helper state. It is not the current ProveIt 252-state candidate.

Current ProveIt sources at `fab89c5d26b81cd2ccab2ee5d213ff23725c7726` go farther numerically. `BinaryPerm252.lean` states the closed literal blank endpoint, including all-site coverage and the 82,552-step bootstrap, and proves equivalence with C254, the finite numerical checker, native refutation, and ZF refutation including Foundation and Power. `ZFCBoundPerm252.lean` proves Con(ZFC) implies nonhalting by theory inclusion; it does not prove the reverse implication. Both files explicitly leave the full Choice comparison and internalization separate.

The native theory is not a new proposal: upstream SIR already has the container axiom CP, global-image collection GIC, and irreflexivity. Its calculus already uses the single implicational Łukasiewicz basis, the alias F=Rel(0,0), self-fresh formula-code variables, and a nonextensional bisimulation quotient. These must receive attribution rather than be presented as fresh reductions.

Primary source URLs:

- https://github.com/jeff87654/busy-beaver/blob/ec9ed4f713d8c017f15743ad0692cdf31a59952a/ZF/m254/README.md
- https://github.com/jeff87654/busy-beaver/blob/ec9ed4f713d8c017f15743ad0692cdf31a59952a/ZF/m254/coq/e2e/E2E254.v
- https://github.com/jeff87654/busy-beaver/blob/ec9ed4f713d8c017f15743ad0692cdf31a59952a/ZF/m254/coq/tm/TM254.v
- https://github.com/jeff87654/busy-beaver/blob/ec9ed4f713d8c017f15743ad0692cdf31a59952a/ZF/stdzf/coq/Std_iface.v
- https://github.com/jeff87654/busy-beaver/blob/ec9ed4f713d8c017f15743ad0692cdf31a59952a/ZF/stdzf_r3/zfc/Z_main.v
- https://github.com/jeff87654/busy-beaver/pull/20
- https://github.com/VladimirReshetnikov/ProveIt/blob/fab89c5d26b81cd2ccab2ee5d213ff23725c7726/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/BinaryPerm252.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/fab89c5d26b81cd2ccab2ee5d213ff23725c7726/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ZFCBoundPerm252.lean

## 2. Fixed arithmetic and model predicates

Work in ordinary first-order ZFC. Let Form be the set of natural-number codes of finite formulas over the membership language with logical equality. Use an injective constructor coding with strictly smaller immediate subformula codes. Fixed primitive-recursive operations implement free-variable bounds, finite substitutions, closures, and renaming. Nothing below needs a coding of an arbitrary function Nat→Nat: store only its finite support relevant to the input formula, together with an explicit default rule.

For a recursively axiomatized theory T, use a primitive-recursive axiom-certificate relation AxCert_T(e,f). The certificate e records the axiom tag and, for a schema, the actual matrix code and closure parameter. This works even if recognizing the unannotated range of a schema enumerator has not been proved decidable. A proof node includes its certificate, and the proof checker verifies the literal generated formula. Let Prf_T(p,f) be the resulting primitive-recursive finite derivation checker and write Con(T) for ∀p ¬Prf_T(p,Bottom). Invalid certificates, malformed formulas, and failed eigenvariable conditions are rejected.

For the literal deterministic binary machine M, encode a configuration by a state, a signed head position, and a finite-support binary tape. The transition successor is total by making the halted state absorbing. Let Trace_M(t) check a finite list beginning with the unique blank configuration, following exactly the literal transition function, and ending halted. Every component is primitive recursive.

**Finite-trace lemma.** ZFC proves

    ∃t Trace_M(t)  iff  ∃n [run_M(n) is halted].

Proof: primitive recursion on n constructs the finite list of successive configurations. In the reverse direction, induction on the length of an accepted trace identifies every entry with the corresponding deterministic iterate. Tape normalization can be avoided by using a canonical sorted finite support, or proved once by equality of its represented tape functions. The lemma is about the actual table and initial configuration, not a simulation chosen after the fact.

A countable coded structure is A=(D,E), where ∅≠D⊆ω and E⊆D×D. Equality is identity. For each such A, ZFC constructs a satisfaction relation Sat(A,f,s) uniformly for all finite formula codes f and all sufficiently long finite assignments s. Structural recursion on syntax is set recursion, so it requires no truth predicate for the ambient universe and no inaccessible cardinal. One may equivalently use assignments in the set D^ω; finite assignments avoid needless coding of infinite functions.

Define

    Mod_T(A) :↔ A is such a nonempty structure and
       ∀e,f [AxCert_T(e,f) → Sat(A,f,empty)].

All axioms are closed. The quantifiers e,f range over the internal ω of the surrounding ZFC theory. This is one first-order set-theoretic formula, not a scheme indexed only by externally standard matrices.

**Countable completeness lemma.** For the fixed finitary calculus, ZFC proves

    Con(T) iff ∃A Mod_T(A).

Proof: finite-derivation soundness gives the reverse implication. For the forward implication, carry out the ordinary countable Henkin/Lindenbaum construction on the coded language. The chosen complete theory is a subset of ω; the equality relation on term or label codes is a subset of ω²; its quotient is a set. Relabeling or the least-representative construction below yields domain D⊆ω. At no point is an externally well-founded set-theory model required.

This use of completeness is legitimate for the ZFC target. It is not, by itself, a proof in PA. Likewise, a metatheoretic Lean completeness theorem does not establish this coded ZFC lemma by automatic reflection: one supplies the usual set-theoretic Henkin proof, with its fixed coding.

## 3. A countable interpretation lemma eliminating universe concerns

Suppose A=(D,E) has D⊆ω. Let δ(x), ε(x,y), and ρ(x,y) be fixed first-order formulas interpreted in A. Assume δ is nonempty, ε is an equivalence on the δ-domain, and ρ is invariant under ε in both arguments. These hypotheses are ordinary coded satisfaction assertions about fixed formulas.

Set

    D* = {a∈D : A⊨δ(a) and no b<a with A⊨δ(b)∧ε(a,b)},
    E*(a,b) iff A⊨ρ(a,b).

**Least-representative interpretation lemma.** ZFC constructs A*=(D*,E*) and proves, uniformly for all formula codes f and assignments s into D*,

    Sat(A*,f,s) iff Sat(A,I(f),s),

where I replaces equality atoms by ε, membership atoms by ρ, and bounds every quantifier by δ. The substitution/shift conventions are fixed in the recursive definition of I.

Proof: every ε-class in the δ-domain has a least natural-number element, so D* is nonempty and contains one representative of each class. The invariance hypothesis makes E* independent of representatives. The atomic cases are the definitions. Boolean connectives follow immediately. For an existential, a witness in the δ-domain has a least representative; formula invariance under ε, proved simultaneously by structural induction, transports the witness to D*. The universal case follows in the same way. This is an induction over one set of coded finite formulas. All constructed sets are subsets of ω or finite Cartesian powers of ω. No choice of representatives, quotient universe, or external well-foundedness is used.

For the current native interpretation, the equality formula is the explicit set-coded bisimulation formula. Membership is

    Member(x,y) iff ∃z [E(z,y) ∧ Eqv(x,z)].

This is exactly the `memberForm`/`translate` interface in `QuotientModel.lean`; raw E does not generally descend to the quotient. The final domain guard is the quotient-translation of `wfForm(0)`. Formula translation into the native structure is the composition

    J(f) = QuotientModel.translate(WFRelativization.translate(f)).

The WF predicate is internal: x belongs to a transitive represented set t such that every nonempty represented subset of t has an E-minimal member. It is not external well-foundedness of E. Restricting to the externally well-founded elements of an arbitrary countable model would change the argument and is not permitted.

This gives a useful concrete coding improvement over transporting Lean universe polymorphism: the complete interpretation can be realized on subsets of ω. It does not, however, prove the interpreted ZF axioms. Those require the next all-code obligation.

## 4. The precise all-code obligations

Let N be the exact native theory. The model route needs these ZFC theorems, each with the fixed code predicates above:

1. **Numerical calibration and literal execution:**

       ∃t Trace_M252(t) iff ∃p Prf_N(p,Bottom).

   A modular proof separates literal-machine/register simulation, the exact C254 checker, its proof-word compiler/fair enumeration, and the native-calculus comparison. The all-sites certificate is a finite constant, but the symbolic executor's soundness for arbitrary gap lengths and register values is a separate unbounded theorem. A finite bootstrap run is not its substitute.

2. **Native to ZF:**

       ∀A [Mod_N(A) → Mod_ZF(J(A))].

   The interpretation J is the countable quotient/WF construction above. The needed uniform schema assertion has the shape

       ∀A,e,f [Mod_N(A) ∧ AxCert_ZF(e,f) → Sat(A,J(f),empty)].

   Separation and Replacement are the substantive parameterized cases. Their native GIC matrices must be actual formula-code constructors in the variable f, including domain guards. An appeal to GIC for an arbitrary external predicate is invalid. The local `QuotientModel.translate`, `WFRelativization.translate`, and `WFModel.replacementForm` are concrete templates for these constructors. Internal WF closure uses the one displayed `witnessForm`, which is an actual GIC matrix.

3. **ZF to native:**

       ∀A [Mod_ZF(A) → Mod_N(A)].

   Here the same domain and relation can be used. Internally defined cumulative hierarchy stages supply CP, Foundation supplies IR, and Collection applied to the exact arbitrary native matrix supplies GIC. Every rank and ordinal in this statement is internal to A. The proof must not replace internally definable relations by arbitrary outside relations on A.

4. **ZF to ZFC:** fix the usual finite formula L(x) defining constructibility and put

       D_L = {a∈D : Sat(A,Lcode,[a])},
       L(A) = (D_L,E restricted to D_L²).

   Require the uniform coded inner-model theorem

       ∀A [Mod_ZF(A) → Mod_ZFC(L(A))].

   L(A) is a set-sized structure even if A is externally ill-founded. Its satisfaction relation exists because its domain is an ambient set. The theorem that its coded axiom instances hold is the real Choice-removal obligation. One cannot infer it merely by observing that metatheoretic Lean has `Classical.choice`.

The satisfaction identity

    Sat(L(A),f,s) iff Sat(A,rel_L(f),s)

is proved by structural induction on *all* internal formula codes. Every inserted guard is the fixed Lcode, with the necessary variable shifts; it is not recursively relativized again. The ordinary inner-model proof then discharges the actual transformed axiom instances, uniformly in their matrix code. Upstream `Rel.v` supplies the structural translation and substitution law. `Z_main.v` has a finite-refutation version of the full axiom discharge, and `Z_axL.v`/`Z_ac.v` are its specific axiom resources. These are concrete blueprints for the missing local bridge.

**Tarski caution.** There is no uniform satisfaction predicate for the proper class L available in ordinary ZFC. The construction above never asks for one: it applies the fixed formula Lcode inside an already given set structure A, then uses ordinary set-sized satisfaction. Claiming a global predicate Truth_L(f) that uniformly tells the truth of every sentence of L would invalidate the proposed shortcut. The all-code inner-model lemma still requires a proof; set-sized satisfaction alone does not discharge it.

## 5. Semantic internalization criterion, with proof

**Theorem.** Suppose the fixed arithmetic calibrations and the four model obligations in Section 4 are established in ZFC. Then ZFC proves

    [M252 never halts on its blank tape] iff Con(ZFC).

**Proof inside ZFC.** If M252 never halts, numerical calibration gives Con(N). Countable completeness yields a coded nonempty native model A. The quotient/WF model J(A) satisfies ZF. Its constructible submodel L(J(A)) satisfies ZFC. Soundness for finite coded derivations therefore gives Con(ZFC).

Conversely, assume Con(ZFC). Countable completeness gives a coded ZFC model B. By theory inclusion B is a ZF model, so the internal rank construction makes it a native model. Finite-proof soundness gives Con(N), and numerical calibration gives nonhalting of M252. Every object introduced in the proof is an ordinary set. There is no assumption that the ambient universe is a model of itself, no inaccessible-cardinal assumption, and no unformalized claim that arbitrary Lean theorems reflect into ZFC. QED.

The theorem is a sufficient criterion, not an assertion that its project-specific hypotheses have now been formally supplied. The high-level model-existence reasoning is standard. Its practical contribution is to identify a shorter route for the user's revised ZFC requirement: a separate PA representation of the entire proof compiler is not necessary. Completing such a PA theorem would remain a stronger achievement.

## 6. Effective witness transport without primitive-recursive proof extraction

The semantic route can still furnish concrete witness translations.

**Guarded-search lemma.** Let A(p),B(q) be primitive-recursive predicates. Suppose ZFC proves ∀p[A(p)→∃q B(q)]. Define a program F on input p:

    if not A(p): return 0
    q := 0
    while not B(q): q := q+1
    return q.

Then ZFC proves that F is total, and that A(p) implies B(F(p)). Moreover F is one fixed general-recursive function whose index is effectively obtained from the two predicate checkers.

Proof: the invalid-input branch terminates immediately. On a valid input, the assumed theorem provides at least one q; well-ordering of ω gives the least such q, and induction proves that the program reaches it after finitely many checker calls. The transition relation of the search is primitive recursive, and finite recursion gives an accepted computation trace. The correctness implication follows from the loop exit test. This is a ZFC proof of totality of a fixed program, not an appeal to externally observed termination. QED.

Apply this twice after the semantic criterion is proved:

    F(trace) = least accepted ZFC refutation, if trace is a valid halting trace;
    G(proof) = least accepted M252 blank halting trace, if proof is a valid ZFC refutation.

Invalid input returns 0. These are explicit effective witness transports. They supply no useful running-time bound, and they are not claimed primitive recursive. Thus one need not obtain a primitive-recursive proof-producing compiler from the original semantic Lean term to meet the ZFC target. The totality proofs remain conditional on the genuinely internal coded implications; external equivalence on standard integers alone is insufficient.

## 7. What can honestly be claimed now

- A concrete 252-state candidate and closed Lean external equivalence with ordinary ZF are already in the cited repository snapshot. This session should credit them, not reannounce them as a new construction.
- Upstream has a closed Coq finite-refutation Choice comparison in a different presentation, including a Foundation-aware theorem. Porting or directly adapting its all-code content is a concrete available route.
- The countable interpretation lemma and guarded-search lemma above are fully proved mathematical reductions. They identify sufficient conditions and avoid unnecessary universe and primitive-recursive-extraction requirements.
- The inspected sources do not contain a completed local formal proof of the user's exact internal ZFC sentence. Neither a `.lean` endpoint, a closed `Print Assumptions`, nor the existence of set-sized model constructions automatically fills that gap.
- If the report supplies all project-specific coded interpretation and simulation proofs in ordinary mathematics, it may claim a mathematical proof in ZFC while separately stating that kernel formalization is unfinished. If it only lists their statements or sketches their source ports, it must call the conclusion a proposal or conditional criterion.

Finally, the desired equivalence alone is not a two-sided independence theorem under bare Con(ZFC). Gödel's second theorem gives unprovability of nonhalting under consistency once the equivalence is internalized. Excluding a ZFC proof of the false Σ1 halting assertion generally needs a suitable soundness/consistency strengthening; this is separate from the user's requested equivalence.
