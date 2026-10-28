# Independent source-negation C222 review and replay

Reviewer: `/root/complemented47_review`, 2026-10-26. **PASS; no finding or source correction.** I did not author this packet or its actual C222 logical prerequisites. I have previously reviewed several C222 prerequisites; my native-carrier authorship is unrelated to this leaf. This receipt distinguishes complete reading of the new proof and critical imported contracts from authentication and reuse of the larger prerequisite cache.

The complete 168-line main and 71-line Checks were read, together with the author receipt, prepare/build drivers and replay metadata. Frozen source hashes are:

- `ValidatorSourceNegation222.lean`: `766f589378be9c2bfe583f248b8e2a448945d74114400f46c7d8ed210bbd16b4`.
- `ValidatorSourceNegation222Checks.lean`: `7fd75fe179da81627761d1ad4845bd0bf8c81768e3fd6db1691ae450e1f2afcc`.

Both files are under `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA`. Author receipt `9dcf2b99736157f99d9015580dd275a5b2229d79ad672859c91b1ec9286ca025`, replay `cfb206112f8eb04f4a104a7313b8ef51cb566bb82509518f731d78accd81351e`, and the complete 27-file author manifest `70c7319c28aab8df8b6ebb065a7d3ad017a599266bd4d5dc658e64b3fba57920` were checked against the actual bytes. Historical failed-check diagnostics are retained and are not evidence of accepted declarations.

## Mathematical scope

`encode_neg` is uniform over every internal typed code `IsSemiformula ℒₛₑₜ n p` and arbitrary internal `F,B,s`. Its conclusion comprises two actual `CProv222` implications, between the actual encoder of source NNF negation and implication from the original encoding to false code `1`. `encode_neg_witnesses` exposes actual `ArithmeticHistory222.value` witnesses for those implications. The typed premise is essential and remains explicit.

The finite Kalmar deductions were checked with the actual `ValidatorProvability222.cProv_classical`: MP/GEN and propositional resources have new-checker witnesses; they do not come from an assumed C254 semantic correctness theorem. Implication congruence reverses the antecedent direction correctly. The AND/OR cases have the required double negations, and truth/falsity use true code `0` and false code `1` consistently. The equality atom remains actual `Eind`; the proof does not equate it with primitive `weq`.

The induction motive is explicitly Π₂, including all four universally quantified state/arity parameters. Its ingredients use actual Σ₁/Δ₁ graph definability. I read the relevant Foundation `Schemata.order_induction_sigma` contract and the represented source `IsSemiformula.case_iff`, constructor bounds, and negation clauses. Thus the IΣ2 assumption supports internal code induction, rather than only external induction over standard finite syntax. All eight typed source cases are present. Each quantifier case invokes the child at exactly `(n+1,F,s∷B,s+2)` and compares the same binder label, so no freshness, stack-length or distinct-label assumption is silently needed. This agrees with the fully read actual `ValidatorFormulaEncoder222` clauses.

I also read the actual CProv definition and finite rule closures, the relevant complete relational-core and Kalmar sources, and the focused cases for colliding/fallback labels, negated equality, double source negation, nested alternating quantifiers and malformed zero. No old R2/CProv254 semantic theorem is imported by this leaf. Reused `254`-named syntax components remain syntax/recursion infrastructure.

This is not a complete source-proof translation, source-axiom interpretation, closed consistency reduction or HA endpoint. Classical rules inside the represented C222 calculus are not new inference rules of the separate HA proof system.

## Independent replay and provenance

The entire pinned inventory `validator-source-negation222-cache.json`, SHA256 `fb33ff9c1bf83ca829d82958beadb725e3db1a347878caac2ab1a98e55fc4fae`, was authenticated before and after execution: 152 custom cached modules, of which 117 are Foundation, 503 artifact companions, and 40 explicit external boundary objects. All current selected source hashes, object hashes, inherited receipt pins, compiler/toolchain/manifest pins and author evidence files matched. An independent nested-comment-aware import scan checked every selected header and its closed custom/external boundary, including implicit `Init` and `public meta import Aesop`. This is dependency-cache reuse, not a new Foundation or full dependency build; external package internals remain the stated authenticated package boundary.

I fully read my new replay driver before executing it. It created `/tmp/validator-source-negation222-peer-ux05dhdf/lib`, linked only authenticated prerequisites, excluded both target objects, and built the main and Checks sequentially as new regular files. Commands were exactly the recorded Lean4.32 compiler with `-M6000 -j1 -DElab.async=false`, one Lean thread, no `LEAN_SRC_PATH`, and a 512 MiB disk-reserve guard. No shared source or object was changed.

Both commands passed on the first peer attempt in 6.018 and 3.138 seconds. Main output was empty; there were no warnings or errors. Maximum main RSS was 1,904,332 KiB. All 16 focused axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`. Both new objects are byte-identical to the author's:

- Main: `6155f06b7f9809a19ca7aec04c4f813fd69f58a41dc88e1a9a547f35eac6f119`.
- Checks: `aa98d0b79ce994484b5e4250522a269e17fa753016cc65040148d8ca89257c29`.

Durable peer evidence is `validator-source-negation222-peer-replay.json`, SHA256 `f9013d100f8e3365c7fe19e39857ad9bba3fa5f3ef084c2a576d8745159294ef`, and the ten-file `validator-source-negation222-peer-replay/FILES.json` manifest, SHA256 `44144ed5d421b8aba56c87b3ca1b5dacbcbeaa86910ca01cede9c9e1ea38b209`. It retains the complete driver, input inventory, source snapshots, two commands/exit codes, timing/logs, object pins and 2,205 pin observations. Driver SHA256: `09b87d36f4d1f7763b1eeeb13d03871471bcd8c42ad839a87618d4d32a5b3f23`.
