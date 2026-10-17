# Batch152 / manuscript01 / local source26

## Provenance, read coverage and placement

Arrival `da6dabcd8976acf94c4f3652ed3eeae5713b3d2a`; archive `zfc_consistency_machine_report_20261016.zip`, 162 files. Immutable original: `/tmp/zfc-intake-152-7x8qx8co/original/zfc_consistency_machine_report_20261016/zfc_consistency_machine_report_20261016`. All execution and PDF builds used the separate copy `/tmp/zfc-review152-bic-0i02n42d/01`.

Title: **One-parameter closure and the search for smaller ZFC consistency machines**. Main ProveIt pin `6ec2e80dbbe45a99b7812fb5757977307959a51e`; accepted upstream254 `297ab8df7e5de329605c3875b4934643b371a5e3`; public253 `0d544f2a2e3c18f12278441a74b7879f31cbe856`. Requested earlier commits are contextual references, not the audit cutoff.

Read the complete report (main + all nine included section files), README, NOTICE, `least_hull.md`, `observational_pairing.md`, baseline findings/reproduction notes, new checker/template/codec code and search drivers. Verdict: **addition to the existing zfc-closure-kernels report**, continuing sources14/21/24 and the explicit parameter-arity/open machine questions. No earlier theorem requires retraction. Keep the base article unchanged and retain this article in the arrival archive under the host's placement procedure.

## Mathematical review

The main new ordinary theorem is raw **deductive** equivalence `EPSC1+AU ↔ EPSC1+OPair ↔ EPSC2 ↔ EPSC_full`, not merely a model-consistency comparison. AU is the fixed adjunction sentence with outgoing inclusion U. The proof is sound under precisely the declared full classical equality-free logic, genuine Bottom, nonempty domain and unrestricted internal binding.

Checked dependencies: EPSC false matrix supplies empty objects; constant-in-input globally subset-bounded predicates give exact extensions. Full incoming-and-outgoing profile O is a pure logical membership congruence. O-singletons use one ordinary parameter; testing U(a,b) against an O-singleton of a makes U equivalent to O. The transitive-container switch has disjoint local-bound cases and uses one parameter. Its two-step singleton decoder does not presuppose Pairing/Union. The fixed two-parameter pair matrix explicitly handles an empty first parameter by its E(a) arm; it never combines unrelated bounds. Kuratowski coordinates are recovered via the intersection and union profiles, even when outer codes have only incoming agreement. This handles nonunique inner pair representatives. Finite tuple formulas then pack arbitrary raw parameters modulo O; formula invariance suffices to replace the original matrix. The reverse AU derivation obtains a legitimate common subset bound using already derived transitive cover, O-pair and raw Union. No hidden extra matrix parameter was found.

The second ordinary result is `EPSC_k ↔ XFP_k` for k≥1. The least hull mu quantifies over **all represented closed objects**, rather than all external subclasses or only supported ones. A preliminary supported hull and one-parameter transitive bound prove global subset-boundedness without entering the defining matrix. The constructed least hull inherits global support from that preliminary hull. The active-image formula nu has the original parameter budget; its exact extension is closed, so represented minimality gives mu=nu. Same-parameter induction and incoming-only hull-witness elimination are valid. The note correctly forbids replacing an outgoing occurrence m∈z by mu. The one-object self-loop counterexample distinguishes mere existence of a least represented prefixed point from EPSC's support requirement. No general external finite-reachability claim is made.

The inherited saturation calibration is reconstructed correctly: full raw Separation/Union/Power follow from legitimate bounds; hereditary H is D-invariant and hereditary; its purity cut uses an actual raw separated transitive cover, avoiding a family of selected witnesses. Guard the interpreted relation by H, apply raw EPSC, and saturate under incoming profiles. Initial closure, recurrent closure and unrestricted global support all transfer. Point-seed graft, Russell root, partial functional image and successor closure recover ZF0 without assuming Collection or Foundation. Exact fibers in P(b) plus Replacement and omega recursion prove the reverse schema without choosing arbitrary local bounds. The ordinary internal-ZFC consistency claim uses uniform finite syntax/interpretations or set-coded model completeness. It is not a serialized Lean/PA/ZFC theorem.

Unsettled and retained: EPSC1 **alone** calibration; zero-parameter XFP; complete literal compiler; whole runtime and internal endpoint of a new table. Formula53 versus85 is a declared expanded-tree metric, not a state estimate.

## Executable and source-interface review

The fifteen-rule ND checker retains exact shifted-context AllI/ExE conditions, strictly backward DAG references, exact final axiom context and genuine Bottom. The equality-free wrapper rejects Eq throughout proof contexts/conclusions and fourth free slots even under binders. The theory preset is external to the word, so descriptor0 denotes AU or PairO only under the selected preset. Strict decoding requires exhaustion. Both positive certificates prove an empty object, not Bottom.

The table arithmetic semantics and library proof predicates are separate encodings from the numerical base-four logic; the note does not conflate code0 truth with ordinary syntax. Foundation-inclusive `ZFCReg_equicons` and finite proof-presentation changes are identified. Three nontrivial arithmetic transports F/G/K remain unsupplied; no arbitrary Coq soundness principle is assumed. Python recursion/resource failures propagate and are expressly excluded from the ideal total semidecider claim.

## Verification and PDF

Commands are recorded in `run01.py`, `01-searches.log`, `01-quick.log`, `01-full.log` and `01/reproduced/*/logs/commands.json`. Release-manifest/hash auditing was omitted in memory; functional table reconstruction, source/executor identity checks and certificate-byte identities were retained. No original was modified, and no line-ending work was done.

`uv run --no-project python -B run01.py --searches`: **PASS**. This includes n≤4 packing (66,066 binary structures), both full reference checker variants, saved4087/5404-bit positive certificates, metrics, least-hull controls, literal312975 boot, both public253 macro searches (r4/64 andr6/128), and every49,952 mixed construction. Complete normalized mixed candidate records and summaries match; 886 protected-row exclusions,49,066 tested, no survivor. Fuel/abstraction failures are inconclusive, not semantic lower bounds.

Separate `--quick` and `--full` branch replays also **PASS**, with nine functional commands each. They exercise the selected n≤3 quick census as well as full n≤4. All three modes and command records are retained in `data/intake-152-source-26-verification.json`.

PDF: three scratch pdflatex passes, all exit0,40pages, no warnings/overfull/underfull boxes. `pdf-review.json`, `01-pdfinfo.txt`, and `01-pdflatex-{1,2,3}.log` retain evidence. Rendered pages5/11/13/25; pages11 (raw equivalence/AU theorem) and13 (represented fixed-point argument) visually inspected and clean.

## Current-tree comparison

The raw parameter theorem is new relative to the cited EPSC2 source21 consistency argument; the basic full-profile/U singleton argument is already reflected locally in `OutgoingProfile.lean:37` (`outgoing_iff_full`) and `:88` (actual rawPSC model corollary). Its header `:14` explicitly says there is no EPSC-to-PSC adapter; `:178–180` excludes a whole EPSC schema interpretation/proof transport. Thus this existing local theorem does not formalize the new EPSC1/2 parameter-collapse result.

The current `RawPSCModel.lean:292` supplies `pure_hull_of_model` for an actual EF-definable invariant relation, with its local bound and invariance explicit. `QuotientZF0.lean:38` now assembles quotientZF0 and `:78–93` proves the one-way abstract-enumerator consistency implication. These postdate the manuscript's snapshot and strengthen the old formalization ledger, while leaving its new raw parameter theorem and complete numerical/binary endpoint open. The checked finite public253 boot and subsequent register/box proof progress do not certify any new smaller table.

Recommended write status: accept ordinary theory proofs and finite evidence, attribute hereditary/PSC calibration and public253, record zero newly certified sub253 machines, preserve the ideal-vs-literal-Python distinction.

## Durable intake evidence

Independent verification and PDF/build metadata: `data/intake-152-source-26-verification.json`. Placement is `b123527ff4`. Supplied sources remain unchanged; the project base article is unchanged. All advertised functional modes and bounded optional searches completed successfully; exact normalized comparisons are retained in that JSON. Ordinary mathematics, finite executable checks and kernel claims are distinguished above.
