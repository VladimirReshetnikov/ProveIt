# Batch80 review: three-mass reversible computation and exact targets

**PASS within the stated model and interfaces.** I found no new mathematical or intended certificate-verifier defect requiring a repair. Both complete author replays passed, and the independent checks described below passed. The original archives and all 104 extracted published members remain unchanged. This is a mathematical/source audit supported by finite executable evidence, not a formal proof, a novelty assessment, or a claim that small examples instantiate a universal machine.

The review covers the complete mathematical manuscripts, the exact-target theorem companion and audit note, the native collision generator, certificate producer and independent checker, both radius-one wrappers, cleanup producer/checker and affine lift, literal exports, and relevant test/replay entrypoints. The modular and standalone source presentations were cross-read. Author tests and their independent audit harnesses were inspected before execution. The PDF build/QA receipts are authenticated provenance; I did not rebuild or independently visually QA the PDFs.

## Pinned inputs and replay artifacts

| Archive at upstream `4e270aa46` | SHA-256 | Published members |
|---|---|---:|
| `Three_Mass_Reversible_Computation.zip` | `fd86a8a6b71735ef08ebd7913498603213244484da8b23d81876b10c40ffd1de` | 66 |
| `Exact_Targets_Three_Mass_Units.zip` | `d69d8df9ee3a2074bcff1ef400853724eafb679ada8b287ef397eb8891965dcc` | 38 |

The [portable checker](review_batch80_three_mass.py) embeds every member hash, authenticates before executing any report source, rejects unsafe/duplicate archive members, and extracts only into temporary directories. Its [receipt](review_batch80_three_mass.json) includes the archive pins, independent check counts, exact fixtures, and normalized comparisons with the author evidence. The five exact-target `vendor/` sources are byte-identical to the companion's corresponding `code/` sources.

Key executed source pins are:

| Source | SHA-256 |
|---|---|
| Native `code/three_mass_collision_generator.py` | `14b8bde4362803181dbee33d81e083ba4758ee51df7b23fcfd920a6f1de12d52` |
| Native `code/certificate.py` | `fed96578694af665258fca9eeab14fa94d8a56e810de8f684a2c9fdcd9d751e8` |
| Native `code/checker.py` | `9fc3879eb24f4b4d9d2e1c8ebc0c123510c04141bd754547d191ceef28815c66` |
| Exact-target `clean_targets.py` | `a79405023df5a1038a69bc947314979093df39be8da7abcdf5588f77da848315` |
| Exact-target `check_clean_targets.py` | `51ce0665dcc74bc3cf2461a25344a8688b23258b9281205c68fabb0526881d72` |

Complete replay from archive paths, using standard-library Python 3.10 or later, is:

```sh
python review_batch80_three_mass.py \
  --native-archive /path/to/Three_Mass_Reversible_Computation.zip \
  --clean-archive /path/to/Exact_Targets_Three_Mass_Units.zip \
  --authors --expect review_batch80_three_mass.json
```

`--native-root` and `--clean-root` can instead point to the two authenticated extracted package roots. Omitting `--authors` runs the bounded independent checks only. `--output PATH` writes a fresh receipt. If the two author suites have already been run, `--native-replay DIR --clean-replay FILE` consumes those explicitly supplied outputs and applies the same exact comparisons; it does not claim to execute the suites again. The saved receipt was assembled from the actual successful runs recorded below. The helper's `verify(native_root, clean_root)` function is portable and has no permanent `/tmp` dependency. Temporary imported report-module names and `sys.path` are restored after the audit.

The original entrypoints run were `sh replay.sh OUT` in the three-mass package and `python replay.py --receipt FILE` in the exact-target package. Both manifest verifiers also passed. The native replay regenerated all 16 example JSON files byte-identically. Its 16 compared published receipts match after removing only `elapsed_seconds`/`python` metadata and normalizing the two source-path metadata fields to basenames. The exact-target replay ran all 11 commands, including normal and optimized producer tests, four independent audits, and the byte-exact CLI round trip; all six resulting detailed receipts match the originals under the same narrow normalization. Every other compared JSON value remains exact. Native normal/optimized clock and wrapper checks are distinguished in their receipts. No PDF build is part of this execution claim.

## Native three-mass theorem

The construction is sound as a **weighted Boolean-channel CA** on the infinite line. A cell holds a subset of finitely many channel types; its weight is the subset cardinality. Many distinct symbols have weight one. Three conserved units therefore do not mean three scalar Diophantine coordinates or the ordinary integer-state NCCA convention.

The full-shift reversibility argument is complete. Singleton rules are permutations. The union of prescribed pair rules is an injection, including transitions between routines; closing each finite directed path and fixing untouched pairs extends it to a permutation. Identity on every unspecified pair before closure would be unsound, but that is not what the generator does. Independent channel streaming then gives a globally invertible, cardinality-preserving CA. Both directions have radius at most four. The type velocity conventions are consistently collision-then-stream.

The residue query correctly includes the phase updates on collision ticks. At gap `12N`, its first return phase is `24(N mod 6)` modulo 144; the second return restores phase zero. The measured scratch translation and its inverse leave no residual phase, and each query takes `48N+1` ticks. The rational-gap primitive uses shuttle speed `p+d` and controller speed `d-p`; the factor 12 makes every relevant meeting integral. Valid divisions have the required prime divisibility. No intermediate marker crossing or hidden triple collision invalidates the intended trajectory.

Instruction tags are retained until the backward selector `H(q',N' mod 6)` can recover and erase them reversibly. The report does not erase an arbitrary tag by a many-to-one merge. Missing or disabled instructions enter the explicit permanent leftward escape, which never uses a completion row and cannot later create a false committed halt. The observer requires the complete clean stage-zero pair. What happens after its first occurrence is intentionally unrestricted; freezing a reached state is not claimed.

The exact channel and pair counts agree with the actual generator. With `q` source states, `m=J+1` instruction modulus, and `d` arithmetic instructions:

\[
s=96qm+6qd+2d+6q+2314,
\]
\[
P=3528qm+6qd+d-6m+1152,
\]
\[
C=7008qm+12qd+2d+6q-6m+2304.
\]

Here `C` is the stored completed pair support, not every possible pair or every cell symbol; the actual alphabet has `2^s` symbols. The example cycle's 4,872 types and 177,752 completed pair rows are not universal-machine counts.

Both radius-one constructions are valid, with different interfaces. Four-site blocking is a full conjugacy using Euclidean floor division at negative coordinates, preserves physical time, and maps the canonical gap to `3N` blocks. The internal four-phase construction works on the complete mixed-phase alphabet, applies the old collision only to the phase-zero projection, preserves the old coordinate convention, and multiplies time by four. Neither adds mass or a background clock.

The mass-at-most-two decision proof has the necessary matching scope: fixed finite radius/alphabet, positive integer nonvacuum weights, a unique zero-weight vacuum, sparse binary coordinates, and full anchored or unanchored finite observations. Independent walkers cannot cross before entering the near region. First encounters are minimized over every type-cycle phase; later returning excursions begin at a rule-bounded gap. All intermediate far phases and all later translations of a recurrent near loop are checked. This yields fixed-rule polynomial bit complexity, not a uniform bound for an arbitrary rule supplied as input. It supports the stated typed-weight mass-three threshold and does not extend to active zero-mass backgrounds, signed masses, or arbitrary finite-ring replacements.

## Source dependency and exact targets

The source normal form agrees with Definitions 3.1–3.3 in [Morita–Imai (2001)](https://www.numdam.org/item/ITA_2001__35_3_239_0.pdf). Proposition 3.4 supplies reversible two-counter simulation of any Turing machine, and Lemma 3.5 explicitly supplies a simulator whose initial state has no incoming instruction while preserving reversibility. I inspected these statements in the primary PDF, pages 245–246; downloaded PDF SHA-256 is `43234d22536a84486ae1f772f81049acad374e14b3229b756422d8bdb3d64790`. That literature dependency establishes an existence theorem after choosing a fixed universal source. Neither archive expands that universal source table or supplies its numerical alphabet size. Broader priority claims or uninspected full texts of other cited papers are outside this review.

The cleanup wrapper correctly requires structural freshness, not merely absence of an enabled incoming edge at the chosen input. Its disjoint `F:` and `B:` state copies and terminal `H` remain collision-free even when original state names contain those strings. Reversing the separated instructions preserves both incoming and outgoing guards. The two no-op bridges use genuinely empty sides of the transition graph.

If the original source first halts after `h` steps, the cleaned source first reaches `H` after exactly `2h+2`, with the whole original raw integer restored—including any cofactor coprime to six. The stationary right marker and restored left gap give equality of the **entire absolute finite configuration**, with vacuum elsewhere. The target is `C(H,N0)`, computable from the input; it is not a single input-independent target. Infinite or stuck forward runs cannot enter the reverse copy. Arbitrary local completion cannot add a later target to those intended nonhalting continuations.

The clock formula is exact:

\[
T_{\rm clean}=2\Theta+192(N_h+N_0)+16.
\]

An inverse increment/decrement exchanges endpoints and therefore has the same macro duration; tests and no-ops have the same unchanged value. This is forward-time logical uncomputation, not a claim that the microscopic paths retrace the original paths. Spatial blocking keeps this time; phase dilation multiplies it by four. The `h=0` case still uses both bridges and costs `384N0+16` ticks.

The independent fixture in this review uses `INC2; DEC2`, raw input 5, and no producer `step` or `ready` routine. It checks all 7,968 native ticks through the first exact target, inverse motion, mass three, every source section, and exclusive use of prescribed pairs. Its actual cleaned rule has 7,236 types, 174,154 prescribed pairs, and 346,040 completed supported pairs. Another 48 checks cover full spatial conjugacy and mixed-phase inverses, including coordinates of magnitude `2^80`.

## Certificates, domains, and witness correspondence

The fixed-horizon certificate is one polynomial of degree at most two over **natural numbers**. With `B` residue-expanded branches and external source horizon `h`, its core contains `2Bh` variables, `3h+1` affine-square slots, and `Bh` nonnegative affine-product slots. These are syntactic slots, not a fully charged straight-line arithmetic count. On the full natural orthant, each inactive product `(E-e_j)(e_j+u_j)` is nonnegative. At a zero, `E=1` makes the natural selectors one-hot and forces every inactive quotient offset to zero. This establishes complete witness uniqueness for each fixed input and first-halt horizon.

The `h=0`, empty-branch, cofactor, free-positive-raw input `N0=x+1`, fixed endpoint, and both clock conventions are handled. A free bounded-counter loader pays `(A+1)(C+1)` selectors and three squares, plus its actual free counter coordinates. It is a finite table with potentially large coefficients, not a free unbounded exponentiation gadget. Raw `N` is not silently required to be 2-and-3 smooth.

The exact-target compact certificate reuses this forward witness; it does not independently quantify the reverse computation. Directly certifying the full cleaned source would use

\[
8(B+1)(h+1)\text{ core variables},\quad6h+7\text{ squares},\quad4(B+1)(h+1)\text{ products}.
\]

The compact version retains `2Bh`, `3h+1`, and `Bh`, plus separately stated input/loader/time-output charges. This reduction is justified by the explicit natural-zero-fiber section: copy each original `(e,u)` into forward slot `(t,j)` and inverse slot `(2h-t,B+j)`, set the bridge selectors to one and their offsets to `Nh-1` and `N0-1`, and zero every other full-core coordinate. The converse follows from the unique cleaned trace and `2k+2=2h+2`. The implementation's hygienic renaming correctly handles public coordinates that collide with newly introduced full-core names.

The zero-fiber restriction is essential, and accurately retained in both manuscripts. My exact off-zero fixture for a one-step increment at `N0=1`, `e=u=0`, gives compact polynomial value 3, lifted full polynomial value 18, and a bridge coordinate −1. Thus neither a whole-orthant natural map nor an off-zero polynomial identity is present. Natural integrality is also essential: a one-step prime-two zero test at raw `N0=2` has a nonnegative rational zero at `e=1,u=1/2` despite its false integer guard. The intended verifier rejects this witness. These are documented limitations, not new defects.

The independent checker reconstructs 360 literal core/expansion cases, including 82 successful source executions and 278 rejected horizons/guards, and enumerates 2,400 natural assignments. It verifies 45 compact-to-full natural-zero bijections across all three physical models, fixed/free/bounded inputs, `h=0`, and adversarial public names. It also checks exact target/clock/source metadata mutations and numeric coefficient aliases, including float/Boolean corruptions at `2^100`; no malformed intended verifier boundary was accepted. The 689 rejection count includes the 278 semantically impossible horizon/guard cases. All verifier and algebra checks are supported by the separate author suites; the all-input conclusions rest on the proofs above rather than exhaustive testing.

## Relation to prior sparse-lattice work and the arithmetic objective

The earlier [sparse-lattice review](review_sparse_lattice_aebfa386e.md) established the mass-at-most-two decision barrier and audited a generic paid sparse-history compiler. It explicitly did not show three units suffice. The new collision frontend supplies that missing upper construction in the typed weighted model, and the separate cleanup wrapper strengthens observed halt to exact input-dependent configuration-pair reachability.

Its compact source-horizon certificate gains efficiency by using proved macrostep semantics and reconstructing the unique microscopic trajectory, rather than quantifying a generic arbitrary sparse history. Comparing `2Bh` directly with the previous per-tick sparse-record ledger would mix different certificate interfaces and time parameters. Likewise three physical mass units and radius one do not imply a small fixed-arity universal polynomial: the channel alphabet, finite source table, input encoding, branch forms, all affine evaluation work, and unbounded-history coding still require explicit payment.

The useful transferable result is the proved elimination of an entire uniquely determined reverse witness through an affine section on natural zero fibers. The paper supplies actual literal compact/full certificates and a working hygienic lift. It has not supplied a paid full-operation schedule for a fixed universal instance or eliminated the external horizon. The degree-two and uniqueness statements therefore do not improve the existing fixed-arity universal arithmetic frontier, and do not establish a finite-fold or single-fold unbounded-time representation. No repair patch is proposed because the reviewed statements and intended verifier behavior already preserve these qualifications.

## Integration replay

The root reviewer read the frozen review and checker, then independently ran the
complete portable audit with both original archives, `--authors`, and `--expect`.
Both complete author suites and the independent checks passed. The freshly written
receipt is byte-identical to the committed receipt. No original report or archive
was modified.
