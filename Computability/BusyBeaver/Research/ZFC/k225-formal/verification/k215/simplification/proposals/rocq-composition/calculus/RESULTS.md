# Round10: remove a quotient congruence induction and stop duplicating pure syntax

Pin: aa66d0a33f1f8237a348899eb8095b045a502832. This is additional to prior roundtrip/enc_pos/SeedTheory proposals. Recent de9fdb0 adopted shared semantic lemmas in ConstructibleAbs/InternalSat; these proposals target different unchanged files. All delivered Lean changes are UNCOMPILED proposals. No received generator or other downloaded script was executed.

## 1. Derive relational satisfaction congruence from the quotient theorem

QuotientModel.relSat_congr currently repeats a34-line theorem block, including an eight-constructor structural induction on Form. The file already proves sat_quotient: relational satisfaction is ordinary satisfaction in the quotient. Pointwise Eqv-related environments have pointwise equal quotient images, by mk_eq_iff. Function extensionality gives equality of the entire quotient environments. Hence the two satisfaction statements are identical.

Move relSat_congr AFTER sat_quotient and replace its proof with:

    have henv : (fun i => mk mem witness h (env i)) =
        (fun i => mk mem witness h (env' i)) :=
      funext fun i => (mk_eq_iff mem witness h (env i) (env' i)).mpr (he i)
    rw [← sat_quotient mem witness h phi env,
      ← sat_quotient mem witness h phi env', henv]

The exact statement, names and hypotheses remain unchanged. The dependency graph is acyclic: sat_quotient uses mk_eq_iff/mk_scons/member_congr, none of which uses relSat_congr. Later quotient_extensional does not need it either. The old formula induction is genuinely removed, not restated inside a new generic theorem.

The generated KQ1Model copy has the identical opportunity, with QHyp replacing ModelsCPGIC. Changing the parent source and regenerating applies it to both.

Counts: QuotientModel216→192lines,24removed; new block10lines including documentation versus old34. Same24-line deletion in KQ1Model. These are textual proof sizes, not measured compile speedups.

## 2. Stop forking the model-independent syntax into KQ1Model

KQ1Model is explicitly generated from QuotientModel by generate_kq1.py. The54-line block memberForm/sat_memberForm/translate/RelSat/sat_translate/equalityFree_translate is exactly model-independent: no witness, ModelsCPGIC or QHyp assumption occurs in any definition or theorem. Forking it duplicates recursive definitions and TWO structural inductions without changing the semantics.

Replace that block in the generated file with17lines of aliases and theorem wrappers to QuotientModel, and add its import. The theorem wrappers preserve public statement names. All dependent definitions reduce through the aliases; no theorem about model existence or ZF consistency is imported as an unproved assumption. QuotientModel imports CompositionModel, not KQHyp or KQ1Model, so this adds no import cycle at the inspected pin.

KQ1Model combined count219→159lines:24from the congruence proof,37from the syntax block, minus1new import =60removed. Together with the parent file the measured Lean-source reduction is84lines. The generator grows; this is not a claim of84net repository lines or smaller compiled objects. The explicit old theorem proofs are reused rather than replicated.

A cleaner eventual module boundary is a hypothesis-free QuotientSyntax file imported by both models. The delivered low-disruption proposal aliases the already existing parent module instead; it may make KQ1Model wait for that module to compile, so a speedup is NOT promised.

## 3. Generator-aware integration

Apply QuotientModel.patch first. Then apply GENERATOR.patch and regenerate KQ1Model through the maintained generator. KQ1Model.proposed.lean is the expected source-level result, not an instruction to manually modify a generated file permanently.

The alias replacement MUST run after transform(t). Otherwise the generator's namespace rewrites change QuotientModel references back to KQ1Model and produce self-referential aliases. The proposed generator patch deliberately inserts aliases after transform and asserts that the old relSat_congr block is no longer in the replaced interval, preventing accidental theorem deletion if the parent patch was omitted.

The accompanying build_proposals.py is locally authored and was run only to rewrite inert source text. Neither the received generator nor its modified proposal was executed. Exact regeneration and Lean compilation are still required in the repository environment.

## 4. Minimal quotient hypotheses are smaller than QHyp

Inspection of KQ1Model establishes a further safe module-boundary refinement:

- member_left_congr/member_right_congr/member_congr use only h.symm and h.trans plus the DEFINITION of coded bisimulation Eqv;
- modelSetoid needs h.refl/h.symm/h.trans;
- sat_quotient needs that equivalence structure and member congruence, but not GIC, pairs, union, power, singleton containers or extensionality;
- quotient_extensional additionally uses h.ext;
- the supplied witness:V is unused in proofs after changing the CP/GIC-specific calls into QHyp fields. It is carried through the API, not needed to form or reason about the quotient itself.

An exact reusable core could therefore have fields

    refl : ∀x, Eqv mem x x
    symm : Eqv mem x y → Eqv mem y x
    trans : Eqv mem x y → Eqv mem y z → Eqv mem x z

with ext supplied only for quotient_extensional. Current QHyp provides these fields directly. Current ModelsCPGIC provides them through its existing theorems and witness. Such a core would let both front ends share the remaining quotient construction/satisfaction proof instead of generating a second whole model module.

This is a valid smaller interface, but NOT yet a delivered full refactor. Preserve compatibility wrappers so callers do not acquire a new domain presentation accidentally. In particular the larger QHyp fields are still needed later by separation, collection, union, power and infinity. The final ZF-consistency theorem still needs an actual nonempty model: do not remove its witness just because the quotient-construction helper does not need one.

The known mathematical domain is identical: its equivalence relation remains Eqv mem, membership remains Member mem, and the quotient is by that same relation. Proof-field differences are proof-irrelevant; any API migration still needs definitional-equality or explicit equivalence checks in Lean, not an unsupported assertion that arbitrary quotient presentations coincide.

## 5. Limits and validation plan

1. Fresh kernel compile of parent QuotientModel, regenerated KQ1Model and dependent lower endpoint.
2. Check unchanged theorem statements for relSat_congr/sat_translate/equalityFree_translate and final consistency endpoint.
3. Compare axioms of endpoint, ensuring no sorryAx/new logical axioms.
4. Verify generated bytes match expected source and rerunning generator is idempotent.
5. Measure timings separately; line reduction alone does not establish runtime improvement.

The proposal leaves raw-code soundness, freshness, equality interpretation, quotient existence, seed property and ZF model construction intact. No smaller machine, new calibration, stronger consistency statement or internal-PA theorem is claimed.

## Artifacts and provenance

- QuotientModel.proposed.lean, QuotientModel.patch (QUOTIENT_CONGR.patch is the initial identical parent diff).
- KQ1Model.proposed.lean, KQ1Model.patch.
- generate_kq1.proposed.py, GENERATOR.patch.
- upstream/: exact pinned inert originals.
- build_proposals.py: owned source-rewrite utility.

Upstream URLs at the pin use:
https://github.com/VladimirReshetnikov/ProveIt/blob/aa66d0a33f1f8237a348899eb8095b045a502832/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/QuotientModel.lean
and KQ1Model.lean; generator is Computability/BusyBeaver/Research/ZFC/k225-formal/generate_kq1.py.
