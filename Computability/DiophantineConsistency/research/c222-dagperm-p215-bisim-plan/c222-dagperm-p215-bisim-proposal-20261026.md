# Actual DagPerm–p215 internal control bisimulation: next checkpoint proposal

Prepared across the 26–27 October boundary. This is a read-only source/cache
proposal. No new Lean source, compiler invocation, prerequisite refresh, or Git
operation was performed for it. The just-frozen DagControl author packet remains
unchanged and awaits root independent acceptance.

## Concrete endpoint and why it is narrower than the machine theorem

For every internal model of IΣ1 and every encoded nine-register file `x`, prove

```lean
(∃ t : V, ArithmeticDagControlPerm222.run t (liveValue 1 x) = 0) ↔
  (∃ t : V, run215 t (liveValue 1 x) = 0)
```

Here `run215` is the genuine represented `controlRun` of a new fixed packed
table proved equal to the **actual** `KSource215.p215` catalogue. Neither a
table identity, certificate validity, standard-time bound, nor an external
simulation theorem is a caller premise. The time witnesses and file components
range over the internal model. Both directions come from the already checked
`ArithmeticControlBisim.halts_iff_of_check`; its positive segment clocks support
the genuine internal Σ1 induction.

This endpoint compares two numbered control interpreters. It does not identify
one of them with the binary Turing machine's represented tape/site/boot run.
Actual EnumStep dispatch to DagPerm, the subsequent register/site simulation to
the literal 215 machine, the source-ZFC bridge, Pell arithmetization, and final
HA proof existence remain separate. The external 1,426-tree certificate and
standard-Nat conjugacy are not semantic premises.

## Fixed data and two small sequential leaves

First propose `ArithmeticControl215Table` + Checks, importing only the frozen
`ArithmeticDagControlPerm222` and the existing syntax/data-only
`KSource215Program`. The latter defines exactly `p215 := ⟨p215Nodes,178,179⟩`
and `t215 := ptree p215`; all 179 literal node rows were read. It does not import
the large source, site, or halting certificates.

Define `packed215 : Nat`, `table215 := PackedTables.table packed215 4751`,
`rows215 := PackedTables.rowsOf packed215 4751`, and
`run215 := ArithmeticControlTable.controlRun table215`. Prove:

```lean
table215_length : table215.length = 4751
packed215_bound : packed215 < 2^(36*4751)
table215_eq_catalogue :
  table215 = (ControlCatalogue.leafEntries KSource215.t215).map
    (ArithmeticControlTable.rowOf KSource215.t215)
spec215 : rows215 c = some row →
  stepValue table215 (liveValue (c : V) x) =
    sem regValue write liveValue row x
```

Use the indexed-tree proof pattern that just succeeded for DagPerm: a local
generic `entryAt`/`entryAt_eq`, direct packed-slot lookup, 75 complete 64-index
blocks, exact length, and quotient/remainder composition. The original generic
helper is private; this requires a small local helper, not an edit to the frozen
module or use of private-name internals. All 4,751 rows and the final 15 indices
remain covered. The measured p215 depth is only 47, but no monolithic-list
performance assumption is needed. Expected logical main size is about 210–250
lines plus its one literal, and 35–50 check lines. Freeze this table before
building the certificate leaf so any certificate elaboration correction does
not repeat its expensive finite proof.

Then propose `ArithmeticControlBisimPerm215` + Checks, importing that table
leaf. Define a single fixed `packedCert`, `certSize := 2850`, `fuel := 6`, and
`cert := PackedTables.certOf packedCert certSize`. Each entry is diagonal in
the control numbers and contains **two literal nine-zero vectors**; `[]` is not
interchangeable in `entryIs`, which compares actual lists. The entry at index 0
has controls `(1,1)`. Its two successor indices are checked from the fixed
literal, not guessed or supplied.

The existing complete read-only reconstruction found exactly 512 differing
control rows, consisting of 256 adjacent, distinct-register INC swaps. All
successor fields agree; no branch enters the second instruction of a swapped
pair. Ordinary labelled PC renumbering fails. Root plus all test successors
gives 2,850 entries; fuel 6 reaches a matching test or halt with equal accumulated
offsets, and both branches return to certificate entries. The prior reconstruction
is only a candidate-generation audit; all its required facts will be replaced
by concrete kernel checks in the proposed leaf.

Prove the actual checker interface directly:

```lean
check_all (i : Nat) (hi : i < 2850) :
  entryOK ArithmeticDagControlPerm222.rowsLit rows215 cert 6 2850 i = true
cert_zero : cert 0 = some rootEntry
root_controls : rootEntry.a = 1 ∧ rootEntry.b = 1
root_offsets : (∀ p : Fin 9, vget rootEntry.α p = 0) ∧
               (∀ p : Fin 9, vget rootEntry.β p = 0)
```

Use 45 blocks of 64 potential indices, with the last 34 valid entries covered,
then a generic quotient/remainder proof. This checks `entryOK` itself, including
positive A-control, both bounded successor indices, exact test register,
matching accumulated offsets, and both successor entries. It supplies the
universal premise of `halts_iff_of_check` directly; a monolithic recursive
`checkFrom` theorem is unnecessary. Preserve every failed check and split the
same complete check further if needed, without raising caps or dropping rows.
Also prove `packedCert < 2^(96*2850)` and kernel-check each slot's unused top ten
bits are zero (`slot packedCert i 96 < 2^86`). Thus the fixed-width representation
does not hide unused high certificate data. Expected main size is about
140–190 logical lines plus its literal, with 35–50 focused checks.

Instantiate the existing theorem with `fileValue`, `reg_file`, `live_ne_zero`,
`liveDef`, `projectionDef 8 p`, `reg_write_same`, `reg_write_other`, both actual
table specs, and each actual run's zero/add/one/absorbing-zero laws. The generic
theorem supplies the represented relation and internal induction; no new
INC-commutation theorem, all-Lean-predicate induction, or standard enumeration
argument is needed. The old `ControlBisimRotation240` source was inspected only
as an instantiation guide; it is not an import or a source of old 254 semantics.

## Exact cache and finite evidence

The new plan reauthenticates **140 custom / 95 Foundation modules**, **425
recorded artifacts**, and **39 external boundaries**, with **zero prerequisite
refreshes**. Its two direct imports are the frozen DagControl main and
`KSource215Program`. Every actual source import was checked against this closed
graph, including repeated `public`/`meta` modifiers, and the graph was traversed
from both roots. The second leaf adds only its just-frozen table prerequisite,
so its planned closure is 141 / 95 / 426 / 39. No Foundation build is proposed.

The current DagControl/PackedTables author objects are explicitly pending root
acceptance; an accepted byte-identical root provider can be selected by a later
supplement, without rewriting this historical plan. DagLoops is already root
accepted at `b5459f3024`. The p215 program provider is the source-identical
accepted native object recorded in the current native/source-construction
packets, not an arbitrary discovered olean:

- `KSource215Program` source:
  `7ab40d3faf9ddb976cdac2f77727e9e43b99b13a81fb45a340ad99abdfcd8310`.
- Its object:
  `4e0d002fb42450a8b3ac470b725c7b22760cdc1b6d807156d897fda0859f1070`.
- `ArithmeticControlBisim` current source:
  `d7dbd8d4407eba785f1ef8461fad6c4f3366337fcce9ecbb2f61054a49a18cd9`;
  accepted fresh object:
  `7db58088fc2a846e8f97758c7dfa2ee04770d391e2427d40af56b0d5f9073cbc`.

The selected cache plan is
`c222-dagperm-p215-bisim-cache-plan-20261026.json`, SHA256
`2ad54bece693f305077d6f8c35fb5a6b8aec9769eb346cecba52bcd682f7883f`.
It records 607 selected source/object/boundary observations plus rechecks of
1,219 inherited pin observations; these counts deliberately include repeated
observations and are not fresh-build counts.

Complete existing finite-audit pins remain:

- Actual DagPerm rows:
  `42bcd1c057e73b82f6e13d151dbe280f1d30e06784575e788dbe2a8430704dcd`.
- Actual p215 rows:
  `7bbbab9793f6e6ec2b82593b9ad51b8845753b1a1658ca40517adf30a12c938f`.
- Candidate 2,850-entry certificate:
  `22677a305a6889a1d731f1d78467314bca4ae1f9a889705fffed70d61065b6db`.

The selected-cache planning script and its initial metadata-schema failure are
preserved separately. That failure concerned the toolchain Omega boundary's
nested object/companions schema; no plan was written and no compiler/cache
operation ran. The corrected inventory rehashed all nested boundary records.
If implementation is approved, retain the same Lean 4.32.0 executable,
`-M6000 -j1 -DElab.async=false`, private regular output files, and per-invocation
512 MiB free-space guard. This proposal does not authorize execution by itself.
