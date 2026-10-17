# Pinned audit and internalization notes

Audit cutoff: ProveIt `426592ce97e52d309bfb8f0132411556650b7ac1`, observed 2026-10-16. The exact requested commits were read through the selected GitHub connector, together with the newer research/host indexes and relevant source files. No external repository was modified.

## 1. Concrete status to preserve

* `6d8bc7f1ba02c83e54757366f019f61b966ed0b7` reconciles the first nine closure-kernel sources. It already contains ordinary equality-free PSC-only hereditary-saturation calibration, pure/mixed equivalence, runtime/prepared 252 bodies and the attribution of public 253 to mira-emmy/Mira-Cult/Jeff.
* `63c83cf79986f8a92bb75460848a1d4f863b7b15` catalogues that batch, not a new theorem or machine.
* `0301aa64e0676bed17402a63de46996631252a51` proves the exact 312,975-step public-253 blank bootstrap in Lean, preserving state 33, head -17 and every integer tape cell, including spare blocks. It does not prove arbitrary runtime or the final consistency endpoint.
* Later batches 145--151 bring the host to 25 sources. EPSC, EPSC2 (two matrix parameters), native protected-witness closure rules, quantified NAND, outgoing equality and reserved-zero falsity, artificial finite SK carriers, and exact-hull EFPC are already present. No claim to introduce any of these should be made.
* The reduced C/G base-3 252/250/248 tables and ternary-Bottom 251 are not promising consistency candidates: the current finite-sort model validates their entire retained abstract calculi; source 17 strengthens the resulting abstract nonhalting to PA. The literal machine consequence still needs the respective compiler correctness statement, but their intended frontend has already failed.
* The best retained-full-logical-word Wade control in this audit is 268 states. It remains a compiler control above the public 253 machine, not a completed consistency-search frontend.
* Source 20 combines the compact initializer with the 202-node decoder, producing 255 states. It does not implement a new theory checker.
* Source 25 already tests 148,368 symbol-wise state fusions. Source 04 already checks arbitrary well-shaped dispatcher frames, not just the exact historic bootstrap, on seven representative starts through two million steps. Repeating these exact searches is not new evidence.

The attributed public 253 table is at:

`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/04-machine-machines-zfc_253.tm`

Its SHA-256 is `84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95`.

Upstream PR 20, head `0d544f2a2e3c18f12278441a74b7879f31cbe856`, was directly checked and remained open/unmerged. Its body reports a fresh 160-module Coq rebuild, 194 closed assumption reports, and recursive `coqchk`. Its stated endpoint is an external finite-refutation/halting equivalence, explicitly excluding an extra internalization claim. This audit did not independently rebuild Coq.

## 2. A precise refutation-translation criterion

This is a useful general proposition for this project, not a historical-priority claim.

Let B be a classical recursively axiomatized metatheory capable of elementary coding and least-number reasoning (PA is more than sufficient, as is ZFC). Let S and T be effectively axiomatized theories, with primitive-recursive proof-certificate predicates `Prf_S(p,bot)` and `Prf_T(p,bot)`. If axiom recognition is only computably enumerable, include the finite enumeration witness in an axiom certificate so that proof checking is still primitive recursive. Put `Con(S) := not exists p Prf_S(p,bot)`.

**Proposition.** The following are equivalent:

1. B proves `Con(S) -> Con(T)`.
2. There is a partial-recursive program f whose totality is provable in B and such that B proves `Prf_T(p,bot) -> Prf_S(f(p),bot)` for every p.

**Proof, 1 to 2.** The code of f is fixed. First decide whether p is a T-refutation. If not, output 0. If it is, enumerate natural numbers q and return the first q satisfying `Prf_S(q,bot)`. Contraposition of the assumed implication proves in B that a T-refutation entails an S-refutation. The search therefore terminates in the only branch in which it is performed. Least-number reasoning proves existence and uniqueness of its output, and the same argument verifies that the output is an S-refutation. The construction is a partial-recursive search algorithm with a B proof of totality; no primitive-recursive bound on its search time has been claimed.

**Proof, 2 to 1.** If T had a refutation p, totality and correctness of f would yield an S-refutation f(p), contradicting Con(S). All reasoning takes place in B.

Consequently, internal consistency equivalence does not logically require a primitive-recursive translator or an interpretation preserving every sentence. Such stronger certificates are valuable engineering targets, but they are additional requirements. Conversely, externally observing that every standard input eventually translates is insufficient: the totality/correctness assertion must be proved in the chosen metatheory.

For a concrete proof-compiler certificate, a stronger sufficient condition is easy to audit: provide computable formula translation, checked axiom-instance proof templates, checked inference-rule templates (including freshness/substitution side conditions), a structural recursion producing the target derivation, and a uniform induction in B proving its correctness. Finite tests of sampled instances do not replace this last induction.

## 3. Two-model sandwich for the actual code calculus

Let C be the numerical code calculus, F its designated contradiction code, and let D and E be two explicitly defined classes of nonempty set-coded models. They need not be the same class and need not share underlying domains.

Assume the following statements have been proved inside ZFC:

(S) Every D-model rules out a C-derivation of F.

(C) If no E-model exists, then C derives F.

(L) Con(ZFC) implies that a D-model exists.

(R) Existence of an E-model implies Con(ZFC).

**Proposition.** Under these four hypotheses, ZFC proves `not Der_C(F) <-> Con(ZFC)`.

**Proof.** From Con(ZFC), (L) supplies a D-model and (S) excludes Der_C(F). Conversely, if Der_C(F) fails, contraposition of (C), using classical logic, supplies an E-model. Apply (R). No comparison between D and E is needed.

In the pinned repository, the natural choices are D = irreflexive models of all `Code254` decoded gated bundles, E = irreflexive models of literal encodable bundles. Nonemptiness must be explicit: the historical empty-domain completeness hypothesis was vacuous and has been repaired. `Code254.c254_sound`, `Code254.c254_complete` and `Enum254.enum_halts_iff` supply the abstract shape of (S), (C) and the subsequent enumerator link in Lean. Their internal ZFC counterparts must still be supplied or reconstructed by direct finite mathematics; merely invoking global soundness of the proof assistant is not an internalization proof.

At this pin, `QuotientZF0` proves that E-models give models of ZF without Foundation or Choice and that a refutation of that ZF0 theory forces the abstract enumerator to halt. Composing with an ordinary ZFC proof of the well-founded/constructible-model consistency bridge yields the intended (R). The exact formal implementation of that Foundation/Choice bridge is absent.

The new `DuplicateProfiles` result blocks a *same-raw-structure* reverse adapter from equality-free CP/GIC + IR to native-equality decoded bundles: duplicate every object with a Boolean tag and ignore tags in membership. Equality-free formulas and IR are preserved, while no native singleton exists; one actual native-equality GIC instance (matrix code 35) demands such a singleton. This does not obstruct the two-model sandwich.

## 4. Direct model resources for (L)

Here is the ordinary mathematical source-model argument, independent of raw equality-erasure shortcuts. Every model of ZF has native equality, irreflexive membership, CP and GIC for every first-order matrix, with arbitrary parameters.

For CP at a, choose a limit ordinal lambda strictly larger than rank(a), for example rank(a)+omega. The set V_lambda contains a and is transitive. For x in V_lambda, P(x) also belongs to V_lambda because lambda is a limit, and every subset of x belongs to P(x). This proves precisely the powerset-bounding transitive-container requirement.

For a GIC matrix theta(x,y;p) and a domain A, use ZF Collection, or derive its needed form directly as follows. Separate D = {x in A : exists y theta(x,y;p)}. For each x in D, choose the *least ordinal rank bound* beta_x such that some y in V_(beta_x) satisfies theta(x,y;p). This ordinal is uniquely definable; Replacement collects the beta_x values. Their supremum beta bounds witnesses for every x in D. Separate B = {y in V_beta : exists x in A theta(x,y;p)}. B contains a witness for each relevant x and every element of B has a supporting input in A, which is stronger than GIC's unrestricted-support clause. No axiom of Choice is used.

This construction is uniform in a finite formula code and its parameters. ZFC's first-order completeness theorem produces a nonempty set-coded model from Con(ZFC); satisfaction for such set models is definable. The two constructions above apply within that model, without assuming an externally well-founded model of ZFC.

To connect this resource to the *literal* numerical bundles, additionally audit all constructors and collisions. `DecodeFresh254` already proves semantic independence of the matrix's own code label for every natural code, including zero. For c>0 every occurring label is below c; zero decodes to a tautology with empty semantic support, despite its syntactic occurrence of variable zero. The actual gates are c != a and c != b. When a != b, the G bundle is the ordinary GIC instance for the decoded matrix. When a=b, its first clause has the antecedent a in a and is vacuous under IR; an empty output witnesses the second clause. Similarly, the colliding-variable C bundle reduces to finding a set containing the free point, because its universal antecedent is diagonal membership. Native Pairing/CP supplies that set. These exceptional cases must be checked rather than dismissed by a blanket fresh-label assertion. This ordinary source argument does not itself constitute the missing literal-machine simulation.

## 5. Non-repetition check for proposed selector fusion

The examined host index, research index, complete source-21 proof, source-09 theory notes and source-25 machine dossier contain no finite-conjunction-to-one-EPSC-instance theorem. Existing occurrences of 'fusion' concern machine state rows. Sources 17, 19 and 21 retain explicit finite matrix pools in their complete references. Thus selector fusion appears new relative to the examined repository material; no global historical novelty is asserted.

The proposed base matrix `Empty(y)` is sufficient on its own. Its EPSC boundedness premise is logically true. If the resulting hull C is empty, it supplies an empty object; if C has a member, support says that member is empty. Once an empty e exists, initial closure puts e in C, so C is nonempty. Hence this one base instance gives both empty and nonempty objects.

For `U := forall z Empty(z)` and `G(s) := Empty(s) -> U`, pure nonempty first-order logic proves `exists s G(s)`: if U holds choose any s; otherwise choose a witness to not Empty(s). After the base EPSC instance, U is false and G distinguishes the nonempty witness (true) from the empty witness (false). Fresh universally quantified selector parameters can therefore realize every finite Boolean pattern. A full binary decision tree on ceil(log2(m+1)) selectors, reserving the all-true leaf for the base matrix, can represent m desired matrices plus the base. Conditional matrix congruence transfers the fixed EPSC wrapper under each selector pattern. The forward implication first specializes to an all-true assignment to obtain the base, then realizes every pattern; the converse is finite case analysis. All selector predicates are parameter-only and all wrapper binders must be fresh. This does not yield one fixed finite axiomatization of the entire theory, nor a numerical state saving by itself.

### Independent quantitative refinements

Power-of-two padding is unnecessary. A balanced tree over exactly m+1 ordered leaves has height at most ceil(log2(m+1)); use the selector for the current depth. Short paths ignore the remaining selector values. The all-true path reaches the last leaf, so putting the base there retains the bootstrap. There are exactly m internal conditional nodes.

For primitive syntax Bottom/membership/implication/forall with one node per constructor, `Empty(s)` costs 4, U costs 5, and G costs 10. Use the conditional `(G -> A) and (not G -> B)`, expanding conjunction as `not(A -> not B)`. Each branch occurs once; an internal node costs 29 beyond its two child formulas. Hence the exact fused matrix size is `sum |phi_i| + 29m + 4`, with `ceil(log2(m+1))` new parameters.

Two further variants trade parameters against nodes. Reserve BOTH extreme leaves of a balanced tree for the base, with the m input matrices between them. Specializing all selectors to the same object forces either the all-true or all-false extreme, so the base can be extracted without requiring a predetermined selector truth value.

* With selectors `Empty(s_i)`, there are m+2 leaves, m+1 internal nodes, and `ceil(log2(m+2))` fresh selector parameters. The base supplies empty and nonempty objects, realizing both truth values. The internal cost is 17, giving exact matrix size `sum |phi_i| + 17m + 25`.
* With atomic selectors `h in s_i`, use one shared fresh parameter h. Pure base extraction still specializes all s_i equally. After obtaining the base, choose h=e for an empty object e; select s_i=C for true (e in C) and s_i=e for false (e notin e). This realizes every selector pattern. The internal cost is 11, giving exact matrix size `sum |phi_i| + 11m + 19`, with `ceil(log2(m+2))+1` new parameters.

These are literal formula-tree counts, not machine states or code-bit costs. For the full unrestricted EPSC schema all three variants are admissible. They do not preserve a fixed two-parameter budget. The proof uses ordinary capture-avoiding instantiation, including assigning the same object to several variable names; the retired fixed-slot calculus cannot be assumed to support it.

### Direct GIC corollary (strengthened)

The same construction applies to the public machine's source theory without changing to EPSC. The single GIC instance for matrix Bottom gives an empty e: its global-support clause forces its output B to have no members. If any edge h in C exists, the choices s=C and s=e realize true and false for the atomic selector h in s. If no membership edge exists, every GIC instance is automatically true, since its source-domain coverage and global-support clauses are vacuous. This edge/no-edge case split removes any need for CP.

Given m GIC matrices theta_i, construct the balanced decision tree with leaves `[Bottom, theta_1, ..., theta_m, Bottom]`. Specializing every s_i equally extracts GIC(Bottom), because the selector bits agree and either extreme is the base. Apply the edge/no-edge split just explained to obtain every other input instance. Conversely, finite Boolean case analysis gives the fused instance from the base and all input instances. Thus ordinary first-order logic proves

`GIC(fused) <-> GIC(Bottom) and GIC(theta_1) and ... and GIC(theta_m)`.

CP and IR may be carried as unchanged additional sentences; neither is used in the fusion argument. The matrix tree has exact size `sum |theta_i| + 11m + 13` (m+1 conditionals and two one-node Bottom leaves), with `ceil(log2(m+2))+1` fresh selector parameters. This is a direct-source proof-search proposal, not a measured Turing-machine compiler transformation. The no-CP strengthening was proposed by the theory agent and independently checked here.

### Why finite fusion is not one fixed finite axiomatization

Assume ZFC is consistent, and let S be a fixed finite family of sentences in the pure language of membership such that each member of S is provable in ZFC. Then ZFC proves Con(S): apply Levy reflection to this finite family (and its finite closure used in the reflection proof), choose a nonempty rank V_alpha satisfying the family, and apply ordinary first-order soundness to that set model. Consequently ZFC cannot also prove Con(S) equivalent to Con(ZFC), by the second incompleteness theorem.

The fusion theorem is consistent with this obstruction. Its output matrix depends effectively on the finite family occurring in a candidate proof; the search still ranges over all finite matrices. It does not select one fixed matrix that represents the entire theory. Finite class-theory presentations or artificial finite carriers have different interpretations; one cannot treat their axioms as a fixed finite family of already-true ZFC membership sentences and retain the desired consistency strength.

## 6. Primary source URLs

* https://github.com/VladimirReshetnikov/ProveIt/commit/6d8bc7f1ba02c83e54757366f019f61b966ed0b7
* https://github.com/VladimirReshetnikov/ProveIt/commit/63c83cf79986f8a92bb75460848a1d4f863b7b15
* https://github.com/VladimirReshetnikov/ProveIt/commit/0301aa64e0676bed17402a63de46996631252a51
* https://github.com/VladimirReshetnikov/ProveIt/blob/426592ce97e52d309bfb8f0132411556650b7ac1/Computability/BusyBeaver/Research/ZFC/README.md
* https://github.com/VladimirReshetnikov/ProveIt/blob/426592ce97e52d309bfb8f0132411556650b7ac1/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md
* https://github.com/VladimirReshetnikov/ProveIt/blob/426592ce97e52d309bfb8f0132411556650b7ac1/Computability/BusyBeaver/Research/ZFC/duplicate_profiles.md
* https://github.com/VladimirReshetnikov/ProveIt/blob/426592ce97e52d309bfb8f0132411556650b7ac1/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean
* https://github.com/VladimirReshetnikov/ProveIt/blob/426592ce97e52d309bfb8f0132411556650b7ac1/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DecodeFresh254.lean
* https://github.com/jeff87654/busy-beaver/pull/20
* https://github.com/mira-emmy/busy-beaver/tree/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253

All GitHub facts above came from successful GitHub-connector reads. Attempts to obtain browser-style citation references for these URLs returned DisabledError and should not be cited as source retrievals.
