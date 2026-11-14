# Comparison at ProveIt 17f92105e2bc4317feae6c219cb2143437b482ff

This is a current, read-only inventory, not a new proof of every inherited machine.
The 36 packets relocated under `Computability/BusyBeaver/Research/PA/docs` and
five additional incoming packets form 41 report packages. The 26 ZIPs still in
`docs/incoming` overlap those relocated packets; counting them as 26 additional
independent designs would be incorrect. `packet_ledger.csv` and `.json` give one
entry for each report package. All 26 current ZIP byte streams were read recursively. The 15 literal
194-state reference forms are retained under `reference194/` for offline
comparison; the full-corpus census can be regenerated from the pinned checkout.

## Literal-table census

`census.py` reads current incoming ZIPs recursively and the entire PA research
subtree, including relocated reports and nested ZIPs. The strict recognizer accepts
complete, deterministic binary five-column numeric tables (whitespace separated)
with L/R moves and exactly one undefined halt target. Files named `.tm`, `.txt`,
`.tsv`, or `.csv` are considered. JSON/source-only encodings are not silently
counted as literal tables. Every raw table identity, its occurrences, and its
root-free action-graph classification are recorded in `census/census.json`.

The current census finds **4,417 table occurrences, 620 byte identities, and 446
root-free action-graph classes**, plus two disconnected synthetic controls not
classified by the spanning-root algorithm. There are no recognized tables with
10 through 193 working states. The 6- and 9-state files are synthetic controls,
not supplied consistency-machine proposals. These are corpus counts, never a
lower bound on possible Turing machines. Experimental, rejected, and unsupported
machines are included in the counts.

At 194 states there are **15 byte forms and eight graph classes**. The classes
remain distinct under global tape reflection. `frontier194.csv` and `.json` supply
exact representative paths, complete SHA-256s, graph hashes, and evidence status.

## Complete 194-state frontier

| Design | Allocation | Source sites | What distinguishes it | Evidence boundary |
|---|---:|---:|---|---|
| PA194-67/7 | 134+67-7 | 3673 | Separate diagonal head, original controller; primary table hash `4bfea62b...` | Ordinary mathematical PA calibration; two universal symbolic physical implementations supplied. |
| PA194-AD | 134+67-7 | 3673 | Exchanges physical A and D; hash `27613aa9...` | Same logical source; independent literal-tape checks supplied. |
| PA194-68/8 | 134+68-8 | 3673 | Different decoder association and eight compatible folds; hash `9087d70f...` | All raw/folded contracts and local folds supplied; this audit freshly reran its main build successfully. |
| PA194C | 134+67-7 | 3649 | Shift tests H=1; successful MP returns its consequent in H and clears T/D without pushing zero; hash `d759313c...` | Same table repeated in all five newly incoming packets; full source binding, two universal physical implementations, ordinary inherited PA calibration. |
| PA194CS | 195-1 | 3646 | Shift uses symmetric destructive equality on (1,h), removing three source sites; new reader offset by fold 41 into 330; hash `1c71002e...` | Separate source-preservation argument and both universal physical implementations supplied. |
| PA194CZ | 134+67-7 | 3649 | Replaces source 26 jump with decrement R6, justified by a positivity invariant; hash `b713e734...` | Supplemental search seed with construction checker and invariant; packet explicitly does not supply a separate independent physical replay. |
| PA194altC | 134+68-8 | 3649 | Cached controller on the alternate eight-fold decoder; native hash `a509952c...` | Included as a reproducible search input with full inherited-engine source/contract/startup audit, not a new independent list-lemma derivation. |
| Rejected scanner quotient | 134+68-8 | 3700 | Diagonal191 emitter has a seven-zero address run; native hash `c48d6711...` | Explicitly rejected: scanner mistakes an address for its header at source 1003. Valid local folds and source CFG do not repair the failed physical refinement. |

The last row is **not** PA194-68/8. The accepted alternate allocation has the
separate190 source, 3673 sites and 4780 outcomes; the rejected seven-zero scanner
has the diagonal191 source, 3700 sites. The relevant text in
`pa194c_conpa_2026-11-13 (1).zip` explicitly calls the rejected object a fourth
supplied graph after listing three positive PA194 tables. It does not reject the
`9087d70f...` machine. Fresh main-build output is in `evidence/alternate68_build.log` and
reports 202 raw controls, 194 final controls, and PASS for all 4780 outcomes.

A failed physical refinement rejects the claimed implementation; it does not by
itself decide every unrelated possible statement about that table's blank run.
For some older 196-state experiments, stronger direct blank-halting counterexamples
are supplied and are identified separately in the earlier ledgers.

## Larger design families

* Published PA196 has a 201-token axiom emitter, 3812 primitive sites, and 4959
  outcomes. Its source framework and register engine underlie the later family.
* The diagonal-vacuity transformation reduces the emitter to 191 tokens and the
  source to 3700 sites. Original PA195 realizes it with 134+68-7=195. The scanner8
  variant M195S8 pays an extra scanner control and realizes 135+68-8=195; its repair
  is precisely what the rejected 194 scanner version omits.
* Separating the diagonal head reduces 191 tokens to 190 and 3700 sites to 3673. The
  accepted 195S and the two original 194 decoder allocations realize this source.
* The cached/Combined controller removes 24 source sites: PA195C and PA194C use
  3649, while the bundled-diagonal PA195DC uses 3676. Both the controller and its
  composition with the 194 decoder already exist in the current corpus.
* PA194CS saves three further source sites while retaining 194 physical controls.
* Other 196-state designs change axiom order/association, register layout, source
  rotations, closing instructions, H-only Shift, MP storage, or invariant-based
  zero jumps. The original PA195 ledger classifies 25 supported 196 classes and 65
  rejected/incomplete classes at its historical snapshot. Current counts of 99
  root-free 196 classes must not be called 99 correct consistency machines.
* Source-shortening is not monotone in physical-state count. The NEG18 source has
  an 18-instruction negation macro and can reduce the complete source to 3441 sites,
  yet its checked table has 197 states because useful physical sharing changes.
* U208/U209 and historical PA209 are distinct ancestry families. Their contextual
  reader reductions motivated the method but cannot be subtracted again after the
  corresponding native roles have already disappeared in PA196.

The paper and executable statuses remain distinct. Current PA README says the
machine-specific consistency reductions are unfinished at its iPRA/Lean endpoint;
ordinary mathematical PA calibration arguments in the delivered research packets
are not thereby either proved by Lean or refuted. New candidates should state
exactly which logical argument is inherited and which source/physical obligations
are newly discharged.

## New tables and independent verification

The new package supplies PA194R, PA194F, PA194A, and PA194X. Each has 194 working
states, 388 rows, 3646 source sites, and 4746 primitive source outcomes.
The primary design, PA194R, reassociates the decoder of PA194F, changing
1111 source-address paths while preserving its exact resolved instruction
graph. It has a different physical control graph and compatible fold set.
PA194F changes the final emitter jump at source position 3553 to a decrement
of X. PA194A and PA194X change the jump at position 26 to a decrement of A
or X respectively. These are changes to the represented source operations
and their physical decoders. They use registers proved to be zero at those
positions; the relevant unreachable positive branches are nevertheless
included in the universal physical checks.

| Machine | New source instruction | Independent symbolic steps | Exact blank startup |
|---|---|---:|---:|
| PA194R | Same instruction graph as PA194F; new decoder changes 1111 source-address paths | 1,104,215 | 57,768 |
| PA194F | At 3553, decrement X; zero successor 3637, positive successor 3554 | 1,100,612 | 57,768 |
| PA194A | At 26, decrement A; zero successor 34, positive successor 27 | 1,100,478 | 57,978 |
| PA194X | At 26, decrement X; zero successor 34, positive successor 27 | 1,100,566 | 58,014 |

All four independent literal checks passed every source outcome, rederived
four generic register-list lemmas from the actual transition rows, and
verified the entire finite-support blank seed including its zero exterior.
No arithmetic-box oracle is used by those independent checks. The largest
individual symbolic count is 409 for PA194R and 403 for the other three;
the smallest positive duration constant is 3 in every case. These symbolic execution counts are not physical
running-time bounds or evidence of nonhalting by extrapolation.

The recorded checks are under `../verification/recorded/`. The inexpensive
`../verification/compare_recorded.py` compares the rebuilt native and dense
tables byte for byte with those checked outputs, compares the complete
source/sites/label objects, checks conjugacy, and binds the full seed and
all 4746 recorded contracts to their independent PASS receipts. The older
internal names CSZ_A and CSZ_X in some receipts refer to PA194A and PA194X.
The source proofs and logical-calibration boundary are stated in the report.

## Portable novelty and census commands

From the package root, for example:

```sh
python3 -B comparison/compare_candidate.py machines/PA194R/machine.tm \
  --output comparison/novelty_PA194R.json
python3 -B comparison/compare_new_families.py
python3 -B verification/compare_recorded.py
python3 -B comparison/census.py --repo /path/to/ProveIt \
  --output /tmp/pa-census
```

The novelty checker rehashes and re-canonicalizes every supplied same-size
literal reference, checks that this list equals the census's complete list
of same-size byte forms, and then compares all four cosmetic transformations:
arbitrary state renaming and root choice, optionally combined with global
L/R reversal and global read/write bit exchange. Global bit exchange is only
a stronger cosmetic check; it need not preserve an initially all-zero tape.

`novelty_PA194R.json`, `novelty_PA194F.json`, `novelty_PA194A.json`, and `novelty_PA194X.json` record
absence from all 15 recognized prior 194-state byte forms in eight graph
classes. `new_family_graphs.json` additionally records that all six pairs
among R, F, A and X are distinct under the same four cosmetic transformations.
This is a finite graph statement within the pinned corpus. It is
separate from correctness of the machines and does not assert that no
unexamined source-only or JSON-only encoding could describe an isomorphic
machine. The prior report families were also compared as described above.

The full census script accepts `--incoming PATH` when the archive directory
is separate from the checkout. Without that option it uses
`REPO/docs/incoming`. Its default output directory is the `census/` directory
beside the script. A fresh run recomputes every graph signature; optional
`--reuse-cache` is explicitly marked and is unnecessary for independent
reproduction. It reads the pinned repository and writes only its selected
output directory. The full source checkout is required for this full-corpus
reproduction; the compact reference tables suffice for offline 194-state
novelty checks.
