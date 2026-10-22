# Semantic coverage for K215 proof sharing

This packet implements and checks the interface refactor left open by the
phase-nine shared-CB1 design. It is based on ProveIt commit
`2ca3a5c16f0876d2cab842056353c03a1ed2f5f0`.

## Result and scope

The register-machine simulation now consumes semantic edge contracts. The
existing finite-fuel symbolic checker supplies those contracts through a
separate soundness theorem. A second producer can supply them from direct
decoder-prefix, primitive, and return lemmas. A checked mixed-coverage theorem
allows both producers in one source-tree coverage proof.

The original four public theorems retain their exact hypotheses and types:
`KSim.sim_step`, `KSim.sim_stop`, `KSim.sim_halt`, and `KSim.halts_iff`.
The executable definitions `start`, `tgtConf`, `runTo`, `runHalt`, `checkEdge`,
and every other original definition are byte-identical. The first 9,648 bytes
of the original module, through `rel_view`, are preserved verbatim.

**This packet does not replace any concrete K215 leaf check.** It does not
claim a new endpoint verification, smaller machine, source-size saving, or
compilation speedup. It removes a genuine API barrier to those future proof
savings. Its immediate cost is 129 lines / 5,842 bytes: KSim changes from
356 lines / 16,146 bytes to 485 lines / 21,988 bytes. The proof inductions are
shared; they are not copied into a second alternate simulator. The old
eight-line stopping case analysis is retained separately because its public
type does not require the register-box lemmas.

## Why the refactor is needed

The original `Covered M p` requires `checkEdge M Q e = true` for every reached
source leaf. Proving that an edge has the intended physical execution does
not imply that a specific fuel-limited checker accepts it. A shared suffix
theorem therefore cannot honestly discharge the old Boolean obligation.

The new `SemanticCovered M p` has the same deterministic source walk and the
same exact consumed path, but requires `EdgeContract M Q e` at its leaf.
`Covered.semantic` converts existing coverage to this semantic form without
assuming checker completeness. Existing clients continue to use the old API.

## Exact contracts

`RunContract M br Q target` states, for every natural gap parameter `n` and
every register list `vs`,

```
Valid br vs -> Reach1 M (conc n vs (start Q)) (conc n vs target).
```

`Reach1` is essential: every simulated register step must make strictly
positive physical progress. The backward halting simulation uses that
progress in its well-founded induction on the remaining physical run.

`EdgeContract` keeps all original length and index requirements. An increment
has its index bound and one positive run; a decrement has both guarded runs;
a break and a continue have their exact target paths and overflow flags.
A halt has the existing state-230 terminal premise and an actual halting
conclusion. Internal source nodes are excluded by `False`.

No contract forgets the full consumed word, quantifies away a decoder port,
assumes a right frame absent, or replaces arithmetic gap bounds by truncated
subtraction identities. These properties must be proved by each future direct
contract producer.

## Checked interfaces

- `checkEdge_contract B`: an accepted existing Boolean check yields its full
  semantic contract, using the existing checker-soundness theorems.
- `semanticCovered_of_allSites`: any Boolean producer with a proved semantic
  interpretation can reuse the existing finite source-tree coverage theorem.
- `semanticCovered_of_mixedSites`: combines a `shared Q e` guard with the
  existing checker by `shared Q e || checkEdge M Q e`. Its essential premise
  is `shared Q e = true -> EdgeContract M Q e`; setting the guard to true does
  not bypass any physical proof obligation.
- `Semantic.sim_step`, `Semantic.sim_halt`, and `Semantic.halts_iff`: the
  single simulation core. It requires semantic coverage and does not require
  `BoxLemmas M`; those lemmas remain on the existing-checker producer only.
- The original public theorems: compatibility wrappers with the original
  argument order and types, plus the unchanged stopping case analysis.

## Validation

The modified KSim module and all 12 project dependencies were compiled from
source with Lean 4.32.0. A typed audit then checked the four original public
interfaces, the new semantic endpoint, and the mixed-coverage interface.
Twelve named axiom reports use only `propext`, `Classical.choice`, and
`Quot.sound`; the semantic simulation core itself uses no `Classical.choice`.
The modified module and audit have no warnings. No `sorry` or new axiom is
introduced.

The successful proof follows one recorded unsuccessful elaboration attempt:
the first mixed-coverage proof used `Bool.or_eq_true.mp`, which was not a valid
constant. The replacement simplifies the Boolean equality to a disjunction
and then performs case analysis. Both original logs and exact attempt sources
are retained. The corrected candidate is the only one used by the successful
typed audit.

The reproducibility driver binds the compiler binary, shared runtime library,
Init object, every source, direct dependency object, and transitive source
closure. It uses the repository's shared proof-build lock. It can replay from
the bundled sources without network access or a repository checkout.

```
python3 check_semantic.py \
  --lean /path/to/lean-4.32.0-linux/bin/lean \
  --out /tmp/k215-semantic-coverage-check
```

For a checkout-based run, also pass `--repo /path/to/ProveIt`. The checkout
route uses the pinned repository's import-inventory helper; the bundled route
uses the explicit hash-checked source manifest. Use a fresh output directory
for an independent replay. Incremental retries retain all failed attempts and
reuse only sources, dependencies, objects, logs, and toolchain identities that
match their records.

## Integration sequence

1. Apply `KSim-semantic.patch` to the pinned module, and rerun the focused audit.
2. Complete a specific shared primitive contract, starting with the exact
   86-leaf CB1 family already proposed in phase nine. Its guards, source-role
   binding, full prefix, and target equality remain proof obligations.
3. Define the finite `shared` guard and prove its `EdgeContract` interpretation.
4. Prove mixed `allSites` coverage and use `Semantic.halts_iff` at the concrete
   endpoint. Keep the existing Boolean coverage theorem as an independent
   regression boundary until the new endpoint is verified.
5. Freshly compile changed descendants, including generated site proofs and
   typed endpoint audits. Measure against the same toolchain and source tree.
   Report the library overhead as well as any reduction in checker work.

The initial source overhead is repaid only if enough direct contracts are
adopted. The 86-leaf CB1 family is an appropriate bounded integration test,
not evidence by itself of a net speed or proof-size improvement.

## Files and provenance

`candidate/` contains the proposed replacement module. `baseline/` contains
the pinned original. `KSim-semantic.patch` is the repository-relative patch.
`checked-sources/` contains the full focused source closure and audit.
`evidence/` contains hashes, metrics, raw compiler attempts, named axiom
reports, and toolchain identity. Compiled objects are omitted.

The original KSim attribution to K230 and Jeff Ketchersid's m254 is retained
verbatim in the replacement. This work changes proof organization and adds
semantic interfaces; it makes no claim of originating the machine, register
semantics, source coverage theorem, or existing simulation argument.
