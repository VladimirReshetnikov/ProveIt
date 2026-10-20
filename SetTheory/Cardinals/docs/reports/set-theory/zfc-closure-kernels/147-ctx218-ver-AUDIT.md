# Independent audit of the exact 218-state construction

The mathematical/evidence gates pass for normalized table
`4dd4ca3893a80b99a1df52e4a57f0357eeb697255f86f43b859a1a97ef511651`
and source
`1dcd14a47c4f100316c71f8a346b84000f3d12efc29123d1cce212d4bbfa2efe`.
This statement is separate from the final portable-release and archive gates.

## Independently established facts

- Exactly 218 working states and 436 binary rows, all working states graph-reachable. The only external destination is halt 254, with no outgoing rows. State 79 is present; 96 and 190 are absent.
- The upstream-label native export (301/302) is bijectively identical to the normalized export (102/120). Its SHA-256 is `3c64cf321c9ca11153901cdb19e7326b8bfbd0d3c8d94357ead127a9c9b491c1`. Independent breadth-first canonicalization gives working labels 0 through 217 and halt 218, SHA-256 `7ca993f2c7f2cbdbca5b69756712d0fac17ff81e81e260190a599115c0643acb`.
- All seven source stages have exactly the original 4,744 ordered operations and arguments. Independent subtree-interval and exact dyadic-cut resolvers agree with the original on all 6,166 guarded nonhalting successor edges and the halt case. Thus ordinal/register-store identity is a strong bisimulation for every ordinal and every natural nine-register store, not merely the initialized run. No break or continue argument is retagged.
- The final source has 205 distinct subtree types, 182 interior types, maximum depth 38, and 2,933 addresses different from the original. These are source statistics, not physical-state counts.
- Both right rotations are independently reconstructed as nested-tree transformations, at five and four exact occurrence roots. Each new right child is exactly an already represented pair. The table patches, including deletion of 190 and the final contextual fold, are independently applied and compared row for row.
- All 4,743 interior-prefix contracts pass by literal execution: the head reaches the declared state at the end of the prefix, no unknown exterior cell is read, and every prefix cell is restored. The proofs total 132,281 literal transitions; the longest is 45 transitions.
- Two distinct whole-blank-tape interpreters agree after 312,701 transitions, including every row-use count: state 84, head -5, precisely the recorded 277 one cells, all other cells zero. The logical registers are `(3,0,0,0,3,0,0,0,0)`, the physical permutation is `(6,2,0,4,3,7,8,5,1)`, and the frame has 130 spare values equal to one and extra gap 80.

## The state-saving mechanism

The final fold is not a quotient of identical transition rows. Before it, states 85 and 96 share zero successor 98, but their one successors are 12 and 150.

The nine actual old-85 prefixes end in zero. The four old-96 prefixes end in one. The final read-one row at 85 moves left into 221 to consult this known predecessor bit. For the former role the route is `85,221,188,12` (three transitions); for the latter it is `85,221,189,156,176,150` (five transitions). Both inspect only the current and preceding cell, restore them exactly, and end one cell to the right. On zero, state 85 directly reaches 98 in one transition. Redirecting 177/1 from 96 to 85 therefore allows removal of both rows of 96 without a new helper.

This local lemma is not an assertion about arbitrary malformed entries to state 85. The fresh full primitive proof is what validates all shared arithmetic uses and complete returns to the dispatcher.

## Fresh unbounded evidence

The separately executed full proof covered exactly 6,167 ordered cases, including both guards of all 1,423 decrements. No case was excluded. It used 1,514,325 symbolic operations and all 436 literal rows. Every duration is an affine expression with nonnegative natural coefficients and positive constant; the smallest constant is 13.

This audit independently checks the complete case inventory, all durations and motions, rule counts, exact hashes, and the complete runtime renaming (including 79 to 1079 and 102/120 to 1301/1302). It independently rederives all four one-block identities from literal rows, valid for every natural unary length including zero and arbitrary untouched exterior. Startup support, row counts and canonicalization agree exactly with the independently run small-fact check.

The receipt audit does not itself repeat all generic symbolic derivations. The separate fresh run is preserved, and the portable release default repeats them from bundled dependencies.

## Exact provenance and reproducibility

Independent isolated copies of the full upstream-to-218 constructor and the source-only constructor reproduce the exact table/source bytes and stored receipts with an empty `PYTHONPATH`, disabled user-site imports and only the declared files. The independent audit also expands the declarative grammars and applies every allocation edit itself. The original source/table are checked as actual members of the pinned original219 archive, SHA-256 `04813567f393b6c4015a96aba092159e9021703b4b662c7be69bd2a86497e31b`. Historical startup37 and direct188 seed certificates are hash-checked, but the final machine has its own complete proof.

Historical discovery receipts that say finite-only or unbounded-pending remain historical evidence. They are not silently promoted. Current source, construction, machine, startup and runtime pins agree.

## Trust and theorem boundary

These are ordinary executable mathematical checks and inductive arguments, not a newly checked exact-byte proof-assistant endpoint. The source bisimulation and finite positive primitive refinement transport the same pinned upstream logical calibration to the final blank machine. They do not establish the foundational calibration independently, prove consistency, assert unconditional nonhalting, or establish minimality. The finite 30,810-case discovery test is not used as a universal theorem.

## Audit artifacts

`independent_facts.py` produces `independent_facts.json`, `whole_blank_startup.json`, `prefix_contracts.json`, and `k218.canonical.tm` without importing candidate or proof code.

`audit_runtime_evidence.py` produces `runtime_evidence_audit.json` and independently derives the four block traces.

`audit_provenance.py` produces `provenance_audit.json` and the isolated construction logs.

All three reject optimized Python execution. These scripts' research-checkout paths make them historical reproducibility evidence; the portable packet has a separate self-contained driver.

## Portable release gates

The isolated default replay passed in 447.8595363180066 seconds from a private copied tree with cleared `PYTHONPATH`, no user-site imports, and only bundled dependencies. It freshly rederived all 6,167 final-machine cases. Its case, startup and canonical files are byte-identical to the preserved original fresh evidence; the four block schemas, all row coverage, labels and duration totals also agree. The inherited construction/calibration was freshly replayed while ancestral runtime receipts were audited, rather than all ancestral symbolic derivations being regenerated. All 13 semantic/checker negative controls passed. Five manifest-boundary corruption controls were independently rerun and rejected.

All executable, machine, recipe, input and vendor bytes from the initial 46-file snapshot remain unchanged. Two nonexecuted independent-audit receipts were reissued solely to update audit-checker hashes after explicit optimized-Python rejection was added. The preseal receipt records their exact old and new hashes and permitted metadata changes. The other 44 initial files are byte-identical.

The final 12-page PDF, SHA-256 `b0cddae1200426cb04f6e05c3555a6e931a3687ae389128148acbfe94c54685f`, passes independent full-text/numerical/hash review and visual review of all pages. Its exact construction identities and fresh-versus-stored proof boundaries agree with the checked artifacts.

`preseal/preseal_audit.json` is the portable preseal receipt. The final archive audit is deliberately external, avoiding self-referential archive hashes.
