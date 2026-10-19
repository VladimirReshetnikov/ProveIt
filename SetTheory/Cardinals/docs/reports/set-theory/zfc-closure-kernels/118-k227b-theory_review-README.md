# K230 theory, calibration, and source compatibility review

Reviewed checkout: `3142e4dd980f0be12f4abb636c4ae2528afc17eb` of [elliotglazer/k230-rocq](https://github.com/elliotglazer/k230-rocq/tree/3142e4dd980f0be12f4abb636c4ae2528afc17eb).

## Result

The mathematical change is substantial and complementary to our equality reduction. K230 keeps **all eight original logical row schemas and both unrestricted atomic-vacuity families**. It replaces the old CP/GIC set-theory part of the negative bundle with one compact K schema. Its repository supplies a complete external Rocq theorem connecting the exact 230-state, blank-start machine to inconsistency of the reference ordinary ZFC theory.

This review has inspected the definitions and proof chain and independently replayed the literal axiom-word comparison. It has **not** itself completed a clean Rocq rebuild or kernel recheck. Build verification belongs to the separate checkout audit. Repository provenance reports clean builds and closed final assumption reports; that is recorded upstream evidence, not a new local build result.

## 1. Exact mathematical change

For a matrix φ(y,p,q), with q a finite tuple of parameters, set

- p⊆u := ∀z(z∈p → z∈u).
- Wφ(p,C) := (∃y φ(y,p,q)) → ∃y(y∈C ∧ φ(y,p,q)).
- Hφ(C) := ∀u(u∈C → ((∃p φ(u,p,q)) ∧ ∀p(p⊆u → Wφ(p,C)))).

The ordinary theory KPrimeOrd has equality axioms and universal closures of

    ∀a ∀x ∃C ((φ(x,a,q) → x∈C) ∧ Hφ(C)).

The closure Hφ(C) is unconditional: it must hold even when the specified root does not satisfy φ. Every member of C is supported as an output of φ, and C supplies witnesses for requests whose input is a subset of one of its members.

The literal emitted formula is deliberately more compressed than this prose presentation. In `KCode230.v`, with k the private binder and m the matrix code:

    ksubset(a,b,k) = All k (Rel(k,a) → Rel(k,b))
    krequest(b,k,m) = All b (m → Ex b (m ∧ Rel(b,k)))
    kcore(a,b,k,m) = Ex k ((m → Rel(b,k)) ∧
        All b (Rel(b,k) → Ex a (m ∧
            All a (ksubset(a,b,k) → krequest(b,k,m)))))
    k230(a,b,c) = kcore(a,b,c,c)
    bundle230(a,b,c) = k230(a,b,c) ∧ (RelVac(a,b,c) ∧ EqVac(a,b,c)).

All conjunctions and existentials here denote the same negative encodings as the old numerical calculus. The support witness bound by Ex a is intentionally shadowed by the later All a. Moving that witness and reversing the relevant conjunctions are proved in the ordinary/named decoding bridge; they are not silently treated as literal syntax identities.

The gate is still c≠a and c≠b. There is no new a≠b gate. Logical equality is not removed or weakened by this release.

Primary definitions:
- `source/coq/settheory/KCode230.v`: native code, exact emitted core, vacuity, gate.
- `source/coq/settheory/KPrimeCore.v`: ordinary core, support-witness scope, core-to-seeded-to-KP0 conversion.
- `source/coq/settheory/KPrimeTheory.v`: KPrimeOrd and KPrimeOrdIR.

## 2. Why the proof reaches ordinary ZFC

The formal lower direction is a proof translation, not the assertion that the raw K objects are already extensional sets:

1. KPrimeOrd proves the factored KP0 schema (`kprime_core_to_kp0`, `KPrimeOrd_proves_kp0`).
2. K0/KP0 yields elementary raw constructions, tagged domains, bounded comprehension and collection.
3. The KQuot development interprets membership and equality through a bisimulation quotient. Extensionality belongs to the interpreted structure.
4. The power-set proof uses bounded representatives and quotient saturation; it does not postulate a raw set containing all codes of every representative.
5. `K0_ZFc_inconsistent` and `KPrimeOrd_ZFc_inconsistent` transfer a contradiction in the reference ZF theory to K.
6. `KPrimeOrd_standardZFC_inconsistent` composes the reference `ac_reg_relcon` theorem, covering Foundation and Choice as well.

`StandardZFC` is literally defined in `KQuotZFC.v` as `(ZFc φ ∨ φ=ax_reg') ∨ φ=ax_ac`. Its inconsistency means a finite classical first-order derivation of bottom, not an external set model supplied as an assumption.

For the other direction, `KUpperCore.v`, `KUpperReflect.v`, and `KUpperFinish.v` establish the required finite schema instances inside the reference constructible-hierarchy interpretation. `KUpperConsistency.v` collects only the finitely many instance proofs used in a contradiction and transfers that proof back to StandardZFC.

The final set-theoretic equivalences are:

    KPrimeOrdIR ⊢TC ⊥  ↔  StandardZFC ⊢TC ⊥
    KPrimeOrd   ⊢TC ⊥  ↔  StandardZFC ⊢TC ⊥.

KPrimeOrdIR adds irreflexivity ∀x ¬(x∈x). This is needed at the decoder interface because the numerical falsity code is 1=Rel(0,0). It is not another separately printed machine axiom row. The proof accounts for the fact that an implication to code1 is decoded as negation.

## 3. Native code and binder edge cases are actually covered

This is particularly relevant to our earlier vacuity work:

- `KDecodeFresh.v` proves every label in D(n) is below positive n; `D_private_fresh` also covers code0 by its special closed-truth interpretation. There is no assumption that arbitrary fresh labels automatically replace the native binder.
- `KDecoder230.v` treats code0 as a closed tautology and code1 as Wel(0,0). The implication(0,0) and implication-to-code1 exceptions are explicit.
- `KDecodeEncode.v` constructs genuine enabled instances using a safe encoder and double-negation padding. The private code is greater than3; active roles1 and3 avoid the exceptional atom and satisfy the literal gate.
- `KDecodeComplete.v` splits disabled gates, distinct active roles, and a=b. The coincident-role case uses independently derived empty objects and hosting containers; it is not discarded.
- `KDecodeBundle.v` proves the exact formula under the literal gate. `KDecodeTheory.v` and `KDecodeComplete.v` prove both finite-derivation translations between the decoded bundle theory and KPrimeOrd.
- `Comp_Prop230.v:thm_B6a` explicitly projects **both** old atomic-vacuity families from the bundle. Its first-order completeness proof therefore has the full old logic available before invoking substitution and alpha-conversion lemmas.

These facts avoid the specific unproved binder/alpha shortcuts encountered in the canonical-vacuity deletion experiments.

## 4. End-to-end theorem and exact scope

`source/coq/tm/Correct230.v` composes:

    blank TM halt
      ↔ rm_halts p230 ([],R0)                 [Sim230Main.tm230_rm]
      ↔ halts_from seed230                    [Main230.prog230]
      ↔ thm230 1                              [Seed230.seed230_iff_thm]
      ↔ KPrimeOrdIR ⊢TC ⊥                     [Bridge230.thm230_iff_KPrimeOrdIR]
      ↔ StandardZFC ⊢TC ⊥                     [KUpperConsistency].

`ProgramBisim230.v` checks both directions of the finite certificate between the literal released source tree and structured Dag230, and proves the resulting equivalence for arbitrary register files. `L2Root230.v` proves the structured enumerator semantics. `Seed230.v` then handles the actual seed rather than assuming zero proof counters.

The machine has 230 working states0–229 and halt state230, begins in state0 on an all-zero tape, and has table SHA256:

    e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8

The bootstrap theorem checks 408,419 literal TM steps to dispatcher84, with logical registers `[3,0,0,0,3,0,0,0,0]`, 181 initial source-counter zeros and 167 spare values1. The exact physical file is in `Boot230.v`, and the logical map is proved through `Prog230.R0` and `Main230.R0_enc_seed230`.

Both final assumptions are printed in `AuditCorrect.v`. Upstream `LibTactics.v` has unrelated axiom declarations and an admit-based skip tactic, so grepping a loaded environment is not sufficient to assess the final theorem; the actual final dependency reports are the relevant check.

This is an **external Rocq theorem**, not an assertion that ZFC is consistent and not a formalized internal PA derivation of the equivalence. The release explicitly says its separate internal-PA investigation is not included.

## 5. Independently checked source-level compatibility

Run:

    python -O research_k230/theory_review/compare_axioms.py

The checker reads the literal old Dag254 and released Dag230, expands only named macro interfaces, and symbolically checks every AX output. It imports no source generator or optimizer. `axiom_word_comparison.json` records hashes and complete words.

Verified findings:

- The old AX word has186 macro calls; K230 has154.
- The first88 calls print GEN plus rho8…rho1. The only change there is at zero-based positions32 and35: b-push becomes c-push. Thus the actual emitted rho6 instance is **rho6(a,c)** rather than old **rho6(a,b)**. Both enumerate the same full schema family.
- The old set-bundle-and-cleanup suffix has98 calls; K230 has66. The final five gate/cleanup macros are literally unchanged.
- Both full vacuity families are unchanged.
- AX still reads exactly y and u, still takes a=d+x and b=h+y, still generalizes the pre-read cache h, and still emits the same stack height: saved old top, GEN, eight logical rows, then the gated top bundle.
- Truth0, target1, the four selector commands, additive parameter enumeration, MP behavior, and gate-reset interface agree with the old abstract architecture.
- The literal released source contains5,125 leaf occurrences rather than the old235 source's6,455. Existing indexed source invariants therefore cannot simply be transported unchanged.

The program development also contains a proved QT restore-loop rotation (`ProgLib230.v`, around line700). Thus source compatibility is semantic, not a claim that replacing one subtree reproduces every released source operation or path.

## 6. What can and cannot compose with 243→235 work

There is a clean **logical/program interface** for reuse: retain the old enumerator and substitute the exact K bundle, with the rho6 parameter choice accounted for. The published code-calculus/ZFC bridge can then be reused after proving that the resulting enumerator searches exactly `thm230`. No new set-theory consistency argument would be needed for that exact theory.

Physical savings cannot be subtracted arithmetically. The later235 folds are justified by full source prefixes, table-role allocations, helper overlaps and exact startup paths. The K emitter changes the source contexts and instruction census; its frozen table uses different state numbers, dispatcher, source-counter geometry and bootstrap. Each proposed reused fold needs its guarded table/source projection checked on the new source, followed by unbounded runtime and exact blank-start proof. A statement such as230−(243−235)=222 has no justification from these interfaces alone.

Our κ equality-helper result is structurally complementary: K230 retains exactly the equality-vacuity family our ordinary interpretation weakens. But the current K230 theorem does **not** certify that modification. Its `thm_B6a`/`lprov_thm` completeness path uses full Eq-vacuity. The separate [exploratory appendix](equality_helper_transfer.md) gives an ordinary consistency argument conditional on the earlier uniform E logical interpretation: extract equality-free K instances, then quotient a homogeneous model by two-sided membership indiscernibility to recover all ordinary K matrices. A real syntax issue must be fixed first: upstream `Std_tr` translates bottom using Eq(0,0), so the appendix supplies a closed membership-only replacement before computing the actual padded native code. This is not a compiled or Rocq-certified combination, and supplies no machine-state saving.

The repository documents its pinned reference proof as the254-state development and credits Mira/Reshetnikov/Wade; I found no committed243→230 transformation certificate. The user's historical description may be correct, but a concrete243 compatibility map must be independently reconstructed rather than inferred from the state totals.

## 7. Review artifacts and boundary

- `review_receipt.json` pins the inspected proof files and distinguishes review from a local kernel rebuild.
- `compare_axioms.py` and `axiom_word_comparison.json` replay the exact old/new AX word and symbolic stack comparison, including rho6(a,b) versus rho6(a,c).
- `equality_helper_transfer.md` is a separately labeled exploratory appendix. Its conditional logical-interpretation premise and new quotient/syntax obligations are explicit.
- `check_quotient_bridge.py` and `quotient_bridge_checks.json` provide finite semantic regressions for that appendix, not a general calibration certificate.

The main 230-state theorem and backend compositions that preserve its existing axioms require no equality-helper extension. This review makes no state-count claim for those separately audited compositions.
