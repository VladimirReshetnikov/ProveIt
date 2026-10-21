# Zero-spare MP-first transfer: a new 215-state composition

This candidate combines MP=0 / transfer=1 enumeration with zero-valued spare allocation. It has 215 working states and 430 binary transitions, a separate halt, and entirely blank startup. No 214-state result or new proof-assistant endpoint is claimed.

Only native row 198/read0 changes from the included MP-first table: 1L40 becomes 0L40. The initial state is 74. The source is unchanged, but every increment appends 01 instead of 011. Its exact new blank execution reaches an interior AX frame after 73,172 steps, matched by a separate 177-step source trace. The resulting eight theorem heads protect a dirty tail under the MP-first all-natural debt-one theorem, leaving a permanent conservative margin of seven.

PROOF.md gives the ordinary candidate-specific mathematical calibration, identifies all inherited dependencies, and explains why Q_1(1) in the buried tail must not be assumed sound. The full original MP-first packet is preserved under parent/.

Run python3 -B verify.py for literal reconstruction, source identity and dual CFGs, exact native/dense startup, complete tape/frame equality, source-prefix replay, stored symbolic-census audits, an independent startup checker, and graph distinctness against 77 frozen 215-state tables (44 rooted graphs), including all 28 current public candidate-k215 table paths at the pinned upstream commit. State renaming and global tape reflection are included; universal novelty and semantic inequivalence are not claimed.

Run python3 -B verify.py --runtime --out /a/new/directory to additionally rederive every arbitrary-natural runtime case from the changed table. The directory must not exist. Fresh verification does not modify archived evidence.

The duration/motion/rule-count summaries happen to coincide with the unit-spare parent. This is not used to infer correctness: --runtime derives the changed whole-tape output with append=0. The optional check python3 -B independent_review/check_spare_policy.py confirms both correct table/policy pairs pass and both crossed pairs are rejected on source CI occurrence 3.
