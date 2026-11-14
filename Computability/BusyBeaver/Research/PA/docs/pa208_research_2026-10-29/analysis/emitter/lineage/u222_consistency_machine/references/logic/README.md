# Retained logical and proof-search templates

These twenty-three source files are verbatim reference material from the
ProveIt checkout at commit
`651d6258e9d57f974839ff2ef98060466973a512`. They supply readable versions
of the finite logical derivations and counter-program contracts used in
the accompanying mathematical proof. Together they occupy about 198 KiB.
The exact upstream path, byte count, and SHA-256 of each file are recorded
in `provenance.json`. Original headers and attribution are preserved.

**This folder is not a new compiled Rocq project or a kernel certificate
for the delivered U machine.** The files retain their original theorem
names and, where applicable, their original Theory K bundle. Import
dependencies outside this selected reference set are not bundled here.
No theorem about the original K machine is asserted to certify the
modified transition table automatically. The new bundle, its two small
code cases, its consistency calibration, and the changed source are
proved separately in `../../paper/report.tex` and checked by the new
source audit.

## Definitions and purely logical derivations

| Files | Relevant content and exact scope |
| --- | --- |
| `KCode230.v`, `Codes230.v` | Dual Cantor pairing, native numerical constructors, quotation, and the ordinary eight logical row definitions. These are the unchanged codec and row definitions. |
| `Codes222.v`, `Thm222.v` | The original merged equality row `growG`, membership vacuity `vrel`, and numerical proof rules. The original `nks222` and `bundle222` are Theory K formulas; the new report replaces that nonlogical bundle, rather than reusing its axiom as a U axiom. |
| `CD222.v`, `Prop222.v` | Finite implication, deduction, falsity, double-negation, and conjunction-projection derivations. Their logical derivations depend on the retained rows, MP and GEN, not on the Theory K schema. In particular `thm_F` explains the native falsity eliminator. |
| `DominatedCore.v`, `DomRho8.v` | The generic finite derivation of every `rho8` instance from its dominated family, together with the numerical domination interface. The arithmetic preorder and MP premises are explicit. No Theory K axiom is used. |
| `G222.v` | `refl222`, `helper222`, `spec_eq`, and `rho7_222` recover reflexivity, the fresh-binder equality helper, and the usual Euclidean equality row from the merged row and retained logical rules. These derivations do not require a nonlogical set-theoretic axiom. |
| `L224Def.v`, `L224Prop.v`, `L224Meta.v` | The reduced first-order presentation and its propositional, quantifier, and membership-vacuity metatheorems. The original interface includes full membership vacuity, including diagonal membership atoms. The delivered bundle preserves that interface. |
| `L224E.v` | Equality is interpreted by two-sided membership indiscernibility. Its final theorem `lprov_th` translates ordinary first-order logical proofs into the reduced presentation. It does not assume that primitive equality has arbitrary vacuity. Equality-free formulas are fixed by the interpretation. |
| `Interp222.v` | `bundle222_proj`, `vrel_thm222`, `lprov224_thm222`, and `lprov_thm222` show how bundle projection and quotation supply the logical interface. The original Theory K projection is not used as a new nonlogical axiom. Its propositional projection proof transfers to the new bundle `N(I(V,H))`, yielding the same membership-vacuity premise. |
| `Complete222.v` | The initial lemmas `Q_of_lprov`, `Q_lprov`, `Q_genall`, `Q_tr_cl`, `Q_discharge`, and `TB_to_thm` give the finite natural-deduction/quotation transfer to numerical falsity. `tau_fr` supplies the relevant code-versus-free-name bound. Later named-seed and ZFC-completeness theorems are Theory K-specific and are included only to preserve the original file; they are not applied to U. |

The finite proof templates have an ordinary syntactic interpretation:
replace the old numerical proof predicate by the predicate with the new
bundle, and use the new bundle's proved projection to membership vacuity.
The report explains each changed premise. This is a mathematical transfer
argument, not a claim that the unchanged Rocq files have already been
recompiled with the new predicate.

## Exact enumerator and counter-program reference

| Files | Relevant content and exact scope |
| --- | --- |
| `EnumPerm.v` | The four exact commands and field order: NIP `[0]`, DROP `[1]`, MP `[2,x]`, and AX `[c+3,y,x]`. AX pushes ten entries. Only its current bundle is changed in the new construction. |
| `L1_SoundPerm.v` | The theorem-stack/current/cache invariant and soundness by induction on a command run. The same proof works when every emitted new bundle is an axiom of the new numerical calculus. |
| `L1_CompPerm.v` | Exact stack compiler blocks and proof-enumeration completeness. Their transfer requires the unchanged ten-entry AX interface and the new bundle leaf contract. Both are proved in the report. |
| `SeedPerm.v` | The cofinal completeness argument from next-proof seed 4, with all other logical registers zero. Its `START 4` candidate has a code at least 4 and halts independently of the retained tuple left by previous candidates. |
| `ProgLibPerm.v` | All-natural counter-program contracts for pair/unpair, formula constructors, stack operations, copies, and related helper blocks. The new source is a closed composition of unchanged primitive macro intervals. Its independent audit binds every replacement instruction and branch target to those intervals. |
| `DagPerm.v` | The precise source DAG whose named nodes are used in `ProgLibPerm.v`. The new audit expands the seven reused nodes and checks their resolved control graphs against the accepted primitive intervals, allowing only verified adjacent increment commutations and reencoded branch counts with identical destinations. |
| `RM.v`, `RMEquiv.v` | Definitions of the source-language path and structured semantics, and their generic equivalence for well-formed programs. Their finite branch rules are the ones resolved by the ordinal source audit. These are language semantics, not the new binary table's simulation certificate. |

The new source audit and the literal binary-machine verification are
separate artifacts. These old files supply the proof-search and arithmetic
templates; they do not bind the modified source or the final physical
table on their own.

## Uniform proofs for the exact emitter macros

The newly written `macro_contracts.txt` gives a compact ordinary proof of
the transfer, pair, and unpair loops and their compositions into the
seven reused macros. The exact matching lemmas in `ProgLibPerm.v` are:

| Macro / node | Lemma | Accepted primitive interval |
| --- | --- | --- |
| Implication, 119 | `cons119` | `[78,105)` |
| Parameter C, 168 | `par168` | `[107,133)` |
| Push zero, 171 | `pushwff171` | `[26,45)` |
| Push one, 177 | `v177` | `[995,1015)` |
| Universal quantifier, 180 | `wal180` | `[78,107)` |
| Membership, 181 | `wel181` | `[695,723)` |
| Negation, 218 | `wn218` | `[995,1042)` |

The substantive loop lemmas are `sem_while`, `pair_step`, `pair162`,
`ubody154`, `unpair115`, and `unpair116`. Each quantifies over arbitrary
natural register contents. The expression macros require scratch
registers 6 and 7 to be zero and restore them to zero; all parameter
registers and other untouched registers are preserved exactly.

Running the release source audit with
`--macro-dag references/logic/DagPerm.v` adds an exact finite binding
to these proof nodes. The receipt records every permitted normalization
step. The normalization uses only resolved branch equality and adjacent
increment commutation, with no external jump into a swapped pair's
interior. This establishes the link between the named unbounded proofs
and the exact reused primitive intervals. The 1,792 small-value macro
executions remain supplemental diagnostics.

## Provenance

Repository: <https://github.com/VladimirReshetnikov/ProveIt>

Most selected files come from
`Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/`.
The two shared codec/row-definition files come from the pinned
`verification/k215/simplification/proposals/shared-proof-core/rocq_core/src/`
snapshot. Exact paths and hashes are in `provenance.json`.
The source-language semantics come from two small pinned dependency
snapshots in that same checkout, also identified in the manifest.

Some original comments mention earlier package names such as K217F,
K222, or K224. They are retained verbatim; the manifest records the
actual checked-in source location. This release asserts no new
repository-wide license for upstream material whose licensing is
unspecified. See the release's `NOTICE.txt` for attribution.
