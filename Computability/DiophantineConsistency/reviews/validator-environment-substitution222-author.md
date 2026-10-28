# Actual C222 source substitution and opening: author receipt

`controller_certificate`, 26 October 2026. This is the first, explicitly authorized substitution checkpoint. The complete new sources, reused syntax helpers, and private drivers were read before execution; final sources were read again before freezing. This receipt reports authorship and local execution, not independent review.

| File | Lines | SHA-256 |
|---|---:|---|
| `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorEnvironmentSubstitution222.lean` | 123 | `db2374e4030d1e6792e7426f59f0699796f9b85f78d66c53a478c488ef34ff61` |
| `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorEnvironmentSubstitution222Checks.lean` | 59 | `9ee53adb965b11ec40a63bf5d5b2fd56ad5b300f5401a6956d6f33650cfb9983` |
| `reviews/validator-environment-substitution222-replay.json` | — | `42ac6d1d3b89d5741bce555bf653329b9d09f8dd7254842d2a603eaba1815e1c` |
| `research/c222-substitution-opening-proposal-20261026.md` | — | `d7dcf6a02d884224c1d7c2c49885bfb5aeda87b54eba273d8f1d7a62dcb52856` |
| `research/c222-substitution-opening-cache-plan-20261026.json` | — | `16d3cbc7ac69f4386b9dd02cba242c98de51e79a6d0fc6cff4d029e7b9bb0c19` |

The last three paths are relative to `Computability/DiophantineConsistency`. The earlier proposal's stream-selection and interpreted-transport sections remain prospective; neither was implemented in this packet.

## Exact content

The two imports are actual `ValidatorFormulaEncoder222` and syntax-only `ValidatorEnvironmentSubstitution254`. The latter supplies only unchanged `Matches`, qVec/term/vector interpretation helpers, and the finite pair match. Its old formula-encoder substitution theorem is not used. No CProv254 semantic theorem or primitive equality-vacuity premise is used.

`encode_subst` applies actual `IsSemiformula.pi1_structural_induction` under IΣ1. The invariant universally quantifies internal target depth, free/bound environments, replacement vector and fresh-stream seed. Its Π1 definability is explicitly discharged using the fixed represented substitution and encoder graphs. The source is typed at depth n; the vector contains n terms typed at target depth m. `Matches` requires equality of the interpreted replacement with every used source slot. It is not an assumed provability or semantic substitution statement.

Each constructor uses actual Encoder222 equations, including the Eind equality atom and actual membership atom. Vector-label equality makes the two atom argument pairs numerically identical, so arbitrary Eind auxiliary collisions require no vacuity premise. Under ALL and EXS, n and m both increase by1, qVec lifts the replacement vector, the same literal head s is pushed onto both stacks, and the stream advances to s+2. The existing typed `matches_qVec` supplies this exact next invariant.

Total lookup is retained. Neither stack length, freshness, positivity nor distinctness is assumed for the numeric equality; a short bound stack is legal when its total lookup satisfies Matches. The set-language no-function condition is enforced in the reused typed term helpers. No theorem identifies malformed source0 with a typed source formula.

The public clients are `encode_subst_pair`, `encode_substs1`, `encode_substs1_fvar`, `encode_free`, `encode_all_opened`, and `encode_exs_opened`. Opening uses the literal source definition `free p = substs1 (^&0) (shift p)`: singleton substitution inserts the label x into the bound stack, and accepted actual `encode_shift` removes only the free-environment head. It leaves the inserted bound slot and stream intact. No repeated-qVec iterator or ModelCodedSpecialization dependency is introduced. The opened quantifier statements are numeric syntax identities, not semantic quantifier inference rules.

Focused checks cover x=0 with stream0, repeated zero labels, free fallback1, an empty label stack despite replacement typing at depth3, two nested qVec pushes, and the separate malformed0 encoder branch. Thirteen final axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

Before implementation, `complemented47_review` gave a read-only challenge of the proposed opening chain and found no missing bound/free shift. That was a proposal challenge, not review or compilation of this final packet. The packet itself still awaits independent review. It does not implement Streams222, semantic quantifier transport, arbitrary proof translation, CP/GIC calibration, or an HA derivation.

## Execution and authenticated reuse

Private overlay: `/tmp/environment-substitution222-controller-aw9ui_fn`. Input-inventory SHA: `918d3460337cdaf0bc1a128905bfc10e5b20d0eaddceb7353f8bb8d556f18e27`. The exact Git source snapshot is recorded in its inputs and the replay JSON.

All **153 cached current sources / 117 Foundation modules / 504 prerequisite artifacts / 40 explicit external primary boundaries** were reauthenticated before execution and again afterward. There were no fresh prerequisite builds. In particular, the syntax-only Substitution254 primary remains the approved historical current-source pair: source `13bc509376d444d9ad71de08468151637a8ec8aa943968aa61f57152c0ae9d9c`, primary `95d444289b2efdf8cde2c13483d8ddba7967060711939e6ca0b3402303f4c87f`, at `/tmp/zfc-validator-substitution-bridge/run1/cache/ZFCinPA/ValidatorEnvironmentSubstitution254.olean`. Its provenance is a captured successful 4.32 build and later authenticated reuse, not a fresh build for this packet. Its absent companion artifacts are not supplied or invented.

The inherited extra Foundation subset retains the distinction between twenty central trace-authenticated modules and two historical successful private primary builds with separately observed later companions. The import parser includes repeated public/private/meta modifiers, Aesop and implicit Init. Private LEAN_PATH contains only the new overlay and recorded package paths, excluding the shared project cache.

Pinned Lean4.32.0 ran with `-M6000 -j1 -DElab.async=false` and private output paths. Main passed first try in 14.926605s with an empty log. Initial checks failed only because simplification did not prove the internal numeral comparison2<3 in `short_stack`. That failed check emitted a `sorryAx` diagnostic and is excluded from accepted evidence; its source, command and log are preserved. Adding the explicit `lt_add_one` proof and numeral equality resolved that check. The main and all theorem statements remained unchanged. Final checks passed in 2.244394s with exactly thirteen standard-only reports and no other diagnostics.

Final primary objects:

- Main: `99f58288809049cc943f25f7d31b6755e8faec3aadca5732890896cf39a090fc`, 244864 bytes.
- Checks: `9b7770f8f4566a2bde05bea1130d6f5afc96f94e9bc216cd0a0a61b74871c82f`, 69344 bytes.

The recorder verified all 712 compiler/source/artifact/parent/final observations. Peak successful-run RSS was 1,911,852KiB; free disk at recording was 548,130,816 bytes, above the 512MiB reserve. Complete driver texts, pre-build source snapshots, every attempt, final logs, timing data and object hashes are in the replay JSON. No accepted source, shared object, shared documentation or Git state was changed. Work freezes at this checkpoint before any later stream-selection or proof-translation implementation.
