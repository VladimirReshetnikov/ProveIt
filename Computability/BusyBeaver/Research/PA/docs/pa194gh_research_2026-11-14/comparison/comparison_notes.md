# Comparison at the pinned repository revision

Snapshot: `VladimirReshetnikov/ProveIt@32d0d8b7d93a63ad4106c18cdb29b37927acdad2`.

The delivery ledger covers **82 packets**: all 77 filed research packets and all five ZIPs actually present in `docs/incoming`. The statement “none remain in incoming” in the filed README is stale at this revision. Every packet has an attributed summary and exact location in `packet_ledger.csv`. The named-design comparison contains **58 principal or supplementary named 194-state designs**; this is a roster of reported designs, not 58 independently established consistency theorems. The `named_designs.tex` fragment gives each distinguishing mechanism, and the CSV/JSON versions retain exact table locations, historical identities, and current canonical classes.

## Architectural comparison

The progression from U209/U208 through PA196 and PA195 to PA194 changes both the numerical proof calculus and its tape implementation. The current 194-state designs vary several largely independent choices:

1. **Formula arithmetic and logical heads.** Coefficients four, five, and six require genuine hereditary recoding of formulas and variable labels. Q exchanges the curried premises of universal distribution. D changes the separate diagonal head from Gamma(A) to Gamma(D). These are not changes to the number printed on a control. Their correctness requires explicit translations of proofs, including exceptional zero codes and the dominated-head side condition.
2. **Successful MP.** The original operation pushes a dummy zero. N leaves the consequent visible and does not push. C caches the consequent and clears the visible top. The no-push compiler must reserve a zero explicitly before proving MP premises, so its later Pop preserves an arbitrary underlying stack.
3. **Contradiction detection.** Original Shift tests `t+h=1`; H tests `h=1`. Symmetric destructive comparisons remove a restoration loop while preserving the selected guard. Changing the guard changes the required final refutation word: a lone Shift does not detect visible top one under H, whereas the appropriate Pop does.
4. **The AX interface.** The ten-entry operation and AX11's eleven-entry/four-operand operation have different stack protocols. AX11 is already present in several combinations with Q, H, coefficient five/six, and symmetric comparison. G changes the saved generalized theorem from `U(d,h)` to `U(c,h)`, making the first explicit AX operand the binder and shortening the generalization word. The body remains the raw incoming cached theorem, not its numerical offset.
5. **Source control.** J, A, F, ZR, CZ, CSZ, HA, and HAZ replace selected returns or jumps by decrements of registers proved zero. Each needs its own invariant, including startup; clean-frame correctness alone does not validate a blank start.
6. **Physical layout.** AD, TDY, P5, and HX change physical register positions and routing. They preserve the logical source but change recurring tape access. These are distinct physical implementations, not distinct consistency theories.
7. **Decoder shape and contextual sharing.** The primary budget is `134+67−7=194`; the alternative 68-reader/eight-fold decoder has the same count. Other designs use 135 fixed controls and extra folds. B uses a dedicated history selector; 4L reassociates the four-increment decoder and adds one helper plus one fold. A shorter source word or fewer instruction sites does not automatically imply fewer physical controls.

The new GH command interface combines G's explicit binder with H's cache-only guard and N's no-push MP. GHS has the same command semantics and a different symmetric physical comparison. Their novel graph identities were checked against the current frontier, not merely against the older 82-class snapshots reused by many packets.

## Duplicates and naming hazards

PA194C has five principal deliveries. QN and NQ are the same table class. The two QNS deliveries agree, as do the standalone/paired QN6 deliveries. CSZ and X name the same design. HS equals the cache-only machine named NS in one lowercase packet; the sum-guard NS in `PA194NS_research` is different. The current incoming AX11QH5 is byte-identical to the already filed AX11QH5 table. Counting packet names as new machine designs would therefore overcount.

Table starts require separate treatment. Some files are dense renumberings of native tables in which zero is not the intended blank start. A table's state-zero convention does not establish its theorem. The frontier records whether the start was declared in a comment, conventionally inferred, or absent. Structural comparison deliberately forgets the chosen root and tries every graph-spanning root. This makes novelty stronger while leaving the actual start as an independent proof obligation.

## Count reconciliation and recognition scope

The historical index counts **11,631 delivered `.tm` occurrences** in the 77 packets and **662** historical classes. Duplicate table files were removed on placement. These original-delivery counts must not be identified with the count of files currently stored or with the number of consistency constructions.

The complete current scan checks **10,090 tracked files** against their Git blob identities: 9,404 JSON files, 675 `.tm` files, and 11 ZIPs. Recursive inspection covers 12,461 file/member payloads and 19 distinct archive payloads encountered through 31 references. It recognizes **3,594 complete single-terminal table occurrences, 778 labeled normalized tables, and 658 spanning single-terminal action-graph classes**, of which **94 have 194 working controls** and **53 have 193**. There are no missing tracked inputs or archive-opening failures. The 27 unrecognized `.tm` occurrences are explicitly listed fixed/toy tables without exactly one external terminal label.

For comparison, omitting direct JSON files while retaining archive JSON gives 2,154 recognized occurrences and 737 labeled identities, with the same 658 graph classes and the same 94-class 194-state frontier. Direct JSON inspection adds occurrences and label forms, not additional graph classes at this pin.

The exact relation to the historical 662 representatives is: 649 satisfy the present spanning/single-terminal convention; eight are fixed/toy tables with zero or several external labels; five have no spanning root. Nine additional graphs occur in the current incoming packets: five 194-state candidates and four unfolded parents. Thus the literal/ZIP count is `662−8−5+9=658`. Every historical kept table is accounted for; no unexplained identification is needed.

The historical classifier uses a maximum reachable subgraph when a table is not spanning. Its “states” column can consequently say three for a diagnostic table with 194 working labels. Two current disconnected 194-state diagnostic tables have at most three controls reachable from any root. They cannot match either new machine, whose 194 controls are graph-reachable from its declared start. They are retained separately, without promoting them to consistency candidates.

The recognizers cover complete numeric five-column tables and documented explicit JSON table encodings, recursively inside ZIPs. They do not execute arbitrary generators or extract machines solely from prose, diagrams, Lean definitions, JSONL streams, or opaque binary formats. The packet/named-design ledger is the complementary source-level comparison. Small accidental JSON table fragments and rejected experiments are not mathematical constructions merely because they satisfy the parser.

## Reduction evidence and proof boundary

Every current spanning 194-state class, and both GH/GHS, has 194 classes under the greatest immediate-action control congruence with the terminal distinguished. This exhausts an ordinary direct quotient test. It is not a lower bound for contextual quotients, source rewrites, different runtimes, or arbitrary 193-state machines.

The 53 historical 193-state classes are attributed rejected or uncalibrated objects, principally the coefficient-three logical collision and Runtime193 startup failures. Their finite source contracts and failed startups have different logical status. This audit does not re-label a runtime-only core as a blank-start consistency machine, and it does not infer universal impossibility from bounded repair searches.

The repository distinguishes written PA-calibration manuscripts, standard finite-run Lean results, modeled-scheduler results, and the uncompleted literal-machine iPRA endpoint. All five current incoming packets explicitly retain that boundary. The new command-level proof and exact finite certificates do not by themselves discharge the inherited physical/model-level and PA-proof-translation obligations. An eventual calibration of the shared calculus can be transferred only after the relevant physical bridges are supplied in the stated arithmetic.

## Sources and attribution

The old named/frontier mechanism descriptions are adapted from the pinned `PA194B_PA194G_research_2026-11-14/comparison/` ledgers and checked against the filed READMEs, with all newer filed and incoming designs added. Historical table identities are from `docs/MACHINES.tsv` and `docs/MACHINE_FILES.tsv`, independently reconciled with the new byte-level scan. Source rows and archived table representatives retain their exact locators and hashes. Project and upstream notices accompany the comparison inputs.
