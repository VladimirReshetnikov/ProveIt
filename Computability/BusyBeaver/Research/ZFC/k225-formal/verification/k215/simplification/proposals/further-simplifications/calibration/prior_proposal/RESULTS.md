# Further logical-calibration simplifications

Inspected actual Lean sources at c9dc79323429112c698100f3226a6e4d56c8b782 and local inherited Rocq sources, not only mathematical reports. Downloaded files are inert source data. No Lean/Rocq executable is available on PATH, so proposed Lean changes are not claimed kernel-checked.

## 1. Concrete dependency deletion: use semantic rather than syntactic round trip

KSeedModel222.lean currently proves enc_dec_enc and eqFree_dec_enc by two independent structural inductions (lines174–200), solely to establish derivability of dec(bundle222 a b (enc ψ)) in the local chain. But hT ranges over ALL named formulas with derivable interpreted codes. Choose the original named bundle instead:

    derivable_named_bundle:
      EqFree ψ → enc ψ≠a → enc ψ≠b →
      DerivableNF (bundleNF a b (enc ψ) ψ).

Its proof is just th_eqFree, enc_bundleNF, and C222.bundle. Apply hT to this formula, and use the already imported theorem

    sat_encode_decode mem hirr f e:
      Sat mem e (dec(enc f)) ↔ Sat mem e f

to supply seed_of_bundle. This preserves precisely the semantic equivalence needed by the lower bound, instead of proving unnecessary syntactic reconstruction and decoded-formula-class preservation.

KSeedModel222.proposed.lean and SEMANTIC_ROUNDTRIP.patch give the exact change. It removes 28 lines of two inductive lemmas, replaces derivable_bundle by a same-length direct named-bundle theorem, and adds three lines at the call site: net25 source lines (270→245 before a comment-only edit). Other statements, notably seed_eqFree, are unchanged. No runtime/source/table change. External uses of the deleted public lemmas must be searched before deleting their definitions globally; they can temporarily remain as compatibility results while the endpoint no longer depends on them.

This does NOT assume dec(enc f)=f: falsehood is encoded as membership00, so only semantic roundtrip in an irreflexive structure is valid. It does not remove the raw-code decoder or weaken soundness to well-formed inputs.

## 2. Concrete generic proof-predicate interface

KThmK.lean itself says that TarskiDerived/TarskiLeibniz rules are re-proved. Audited overlap:22 theorem names with TarskiDerived and9 with TarskiLeibniz; overlap is not31 identical proofs because several statements deliberately differ. See OVERLAP.json.

### Layer A: propositional proofs

Parameter: P : NF→Prop and hC : Kalmar.Classical NF.imp NF.bot P.

No quantifier, substitution or axiom assumptions. Move h0/h1/h2, thm_of_der0, ded1/ded2/ded3, syl, contra_thm/contra, dne/dni, imp_cases to this interface. These are KThmK lines93–139 (47 lines) and corresponding TarskiDerived lines30–98 (the latter additionally contains helpers). Existing TarskiDerived already passes hC but hardcodes P=Thm Ax. Generalize the predicate, then retain theorem aliases for both calculi. This saves one real proof copy rather than introducing a new calculus.

### Layer B: quantifier algebra

In addition to hC, exactly these rules suffice for all_mono, ex_mono, ex_elim_of_vac, vac_neg and all_imp_ex:

    gen: P a → P(all i a)
    dist: P(all i (a→b) → (all i a→all i b))
    collapse: P(ex i (all i a)→a)

The collapse rule is rho6. No substitution law is assumed. Add swap=P(all i(all j a)→all j(all i a)) only for recursively propagating vacuity. These correspond to KThmK143–157 (15 lines) and259–268 (10 lines), with matching blocks in TarskiDerived and TarskiLeibniz. Both Thm and ThmK supply gen,rho2,rho6,rho4 as constructors.

### Layer C: admissible vacuity, without strengthening ThmK

Choose ε : Prop. Define Allowed ε by structural recursion:

    rel: True; eq: ε; bot: True;
    imp a b: Allowed ε a ∧ Allowed ε b;
    all i a: Allowed ε a.

The required inversion/closure laws follow definitionally. Renaming preserves Allowed by structural induction. Add membership vacuity for fresh binders, and equality vacuity only conditionally on ε:

    vacRel: c≠a → c≠b → P(rel a b→all c(rel a b))
    vacEq: ε → c≠a → c≠b → P(eq a b→all c(eq a b)).

Then a SINGLE structural theorem proves

    Allowed ε f → ¬Occurs i f → P(f→all i f).

Proof uses ex-falso for bot, implication cases + vac_neg + all_mono for implication, and swap for all. Instantiate ε=True for unrestricted Thm; ε=False for ThmK, where Allowed False is EqFree. The impossible equality branch is eliminated, not silently assumed. This consolidates KThmK160–175 with TarskiDerived139–155 (16 and17 lines respectively).

### Layer D: atomic transport and admissible Leibniz

For the generic atomic substitution lemmas, the needed inputs are hC, symmetry P(eq x y→eq y x), and the displayed left/right congruence rules for the chosen atom constructor A. The same code covers membership and, when available, equality. KThmK204–234 and TarskiLeibniz190–221 are essentially this duplicate31/32-line block.

For structural Leibniz define a second predicate SubSafe ε ν x y f:

    rel,bot: True; eq: ε;
    imp: conjunction of child predicates;
    all i a: i≠x ∧ i≠y ∧ ν x y i ∧ SubSafe ε ν x y a.

Require conditional equality-atom congruences when ε and guard-vacuity

    guardVac: ν x y i → i≠x → i≠y → P(eq x y→all i(eq x y)).

Then one induction gives BOTH directions

    P(eq x y→(f→rn x y f))
    P(eq x y→(rn x y f→f)).

The implication case uses the two induction directions contravariantly/covariantly exactly as current proofs; the all case uses guardVac, gen and dist. For full Thm set ε=True,ν=True and derive SubSafe from the current no-Bound hypotheses. For the existing ThmK API set ε=False,ν=False: SubSafe is exactly equality-free quantifier-free syntax. Consequently no quantifier case is manufactured for ThmK. More permissive helper-binder instances are unnecessary and should not be introduced in this refactor.

Specialization and alpha-renaming remain constrained by their original hypotheses. The shared QF specialization needs: Allowed ε f, QF f, y≠x, membership/equality existence rho1, the above Leibniz instance, renaming closure, and not_occurs_rn. Alpha additionally needs ¬Occurs y f. The unrestricted Thm theorem on quantified bodies retains its existing bound-aware part unless separately instantiated with the full SubSafe proof. Do not replace it by the QF version or claim that ThmK supports unrestricted specialization.

Recommended implementation order: generalize LayerA first (small interface, no logical risk), LayerB next, then parameterize admissibility. Count proof copies, not just names. The ranges above are duplicate candidates, not a guaranteed net line saving after interface declarations.

## 3. Shared bundle semantic normalization, retaining the exceptional case

Current KSeed222.bundle_of_seed (approximately110 proof lines) and KSeedModel222.seed_of_bundle (approximately100) independently expand the same nested req/clos/bundle expression in opposite directions. For ordinary roles, replace these separate derivations by one normalization theorem:

    sat_bundle_iff_seed (mem) (hirr) (e) (a b c)
      (hab:a≠b) (hca:c≠a) (hcb:c≠b):
      Sat mem e (dec(bundle222 a b c)) ↔
      SeedProp mem (matrixRel mem e a b c) (e a).

Build it from sat_req (already present), a new sat_clos iff and sat_dec_agree, then classical propositional normalization. The closure theorem at update e c C is

    Sat mem (update e c C) (dec(clos a b c c)) ↔
      ∀ y, mem y C → ∃ x, matrixRel mem e a b c x y ∧
        ∀ x', (∀ w, mem w x'→mem w y) →
          ∀ y', matrixRel mem e a b c x' y' →
            ∃ z, matrixRel mem e a b c x' z ∧ mem z C.

This theorem requires hab/hca/hcb; the request theorem similarly identifies the seed-root condition. Normalize bundle to an existential C whose closure and root request hold, using membership-vacuity validity. Both directions follow from a single iff chain, so the syntax expansion is written once.

The existing forward theorem intentionally also supports a=b. Its degenerate branch must remain separate, with only the forward SeedProp→Sat statement. Do NOT generalize the ordinary-role iff to a=b: the inner update to a then modifies the same variable used as output b. The generic refactor has to preserve this exception and the all-natural c≠a,b gate. sat_dec_agree still needs its proof that c is semantically fresh in dec c, including c=0 truth alias.

This is a concrete proof architecture based on existing two proofs, not yet an implemented normalization proof; no measured line-saving claim is warranted.

## 4. Generic seed transport with an actual proposed proof

SeedTransport.lean proves two precise reusable statements:

- congr: pointwise equivalent relations give equivalent SeedProp, with unchanged membership and input;
- map: a surjective map f:V→W reflecting and preserving both membership and the selected binary relation transports SeedProp m R A to SeedProp n S (f A).

No injectivity, equality preservation or raw-code wellformedness is assumed. Surjectivity is required to lift arbitrary target witnesses and subset quantifiers; one-way membership preservation is not sufficient.

This directly replaces the nine-line witness reconstruction at the end of seed_eqFree by congr, and the final quotient witness reconstruction in KIndisc222.fullSeed_quotient by map, after its existing hR and representative environment are established. It does NOT replace sat_mk, surjectivity, or the interpretation of equality; those are the needed hypotheses, not removable bureaucracy. The proposed code is47 lines, uncompiled; one use alone need not reduce file size. Its value is sharing the same transport across model constructions and removing repeated witness mistakes.

## 5. What equiconsistency abstraction cannot legitimately remove

KEndpoint.c222_iff_zf_refutation already hides the full calibration behind precisely the needed refutation equivalence. Replacing it with an identically scoped axiom/record saves no proof. Its upper direction uses arbitrary raw codes, code0's implication alias, code1 as membership00, irreflexivity and constructible-model seed validity. Its lower direction needs equality interpretation, seed-matrix coding and freshness, a nonempty valuation, indiscernibility quotient, tagged-domain quotient and ZF interpretation. These are mathematical content.

A raw algebra homomorphism may factor repeated derivation inductions, but syntactic decoding does not preserve implication literally at (0,0). Use semantic preservation sat_wim or equivalence modulo valid formulas, not an injective syntax homomorphism. Dropping decoding is only justified locally as in item1, where an already proved semantic roundtrip supplies exactly the needed fact. All-natural soundness cannot be replaced by checking well-formed codes, cofinally many whole bundles, or a list of classical truth tables.

Rocq audit: Complete222.v has an explicit seed_code_fresh proof from tau_fr and th_fr; Sound222.v separately proves decoded-bundle soundness. They are different directions, not duplicate obligations that can simply be removed. Its lower route uses a syntactic named/de-Bruijn transport rather than exactly Lean's semantic quotient chain; do not port Lean dependency deletions to Rocq by name alone. The generic propositional/rule interface and semantic-normal-form methodology can be reused, but each existing trust boundary must remain kernel-checked.

## Verification and sources

Exact pinned Lean sources are in upstream/. Links use https://github.com/VladimirReshetnikov/ProveIt/blob/c9dc79323429112c698100f3226a6e4d56c8b782/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ followed by filename. Main files: KThmK.lean, TarskiDerived.lean, TarskiLeibniz.lean, KSeed222.lean, KSeedModel222.lean, Code254Models.lean, KEind222.lean, KIndisc222.lean, KUpper222.lean. Existing endpoint inspected at research215_proof_simplification/upstream/KEndpoint.lean. Rocq sources inspected at latest219_baseline/k225-formal/rocq224/src/{Complete222,Sound222,Codes222,Thm222}.v.

No new proof-assistant build, timing claim, smaller TM, changed consistency strength or internal-PA endpoint is claimed.
