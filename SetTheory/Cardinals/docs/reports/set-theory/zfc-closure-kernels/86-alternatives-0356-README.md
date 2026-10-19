# Packed direct-architecture components

**Actual generated libraries:**

- `final_with_compare/library.tm`:216 working states,432 rows; source inventory
  query133 + native68 + writer11 + comparator29; five unlinked return ports.
- `final_without_compare/library.tm`:187 states,374 rows; same inventory
  without comparator; three unlinked return ports.
- `native62/library.tm`:62 states,124 rows; unconditional six-state native
  control quotient, preserving the separate native return and reject.

No complete blank-tape machine is claimed. All failure states remain separate
and counted. Both libraries preserve the original three-field arena encoding.
See `PROOF.md` for universal read-guard assumptions, exact-step theorem,
certificate interpretation, ledger and missing caller obligations.

## Reproduce without repeating search

From the workspace root, with Python3.12 and the pinned shared source present:

    python research_sub246/machine_encoding/component_packing/rebuild_certificate.py research_sub246/machine_encoding/component_packing/final_with_compare
    python research_sub246/machine_encoding/component_packing/rebuild_certificate.py research_sub246/machine_encoding/component_packing/final_without_compare
    python research_sub246/machine_encoding/component_packing/test_library.py research_sub246/machine_encoding/component_packing/final_with_compare
    python research_sub246/machine_encoding/component_packing/test_library.py research_sub246/machine_encoding/component_packing/final_without_compare
    python research_sub246/machine_encoding/component_packing/emit_native_quotient.py

Each manifest is a finite independently checkable quotient witness. The rebuild
verifies every admitted source row, every projected entry and distinct port,
and every protected failure state before requiring the emitted SHA-256 to match.

## Re-run the finite search

    python research_sub246/machine_encoding/component_packing/guarded_congruence.py --seeds 12 --selector-guards --output /tmp/packed_with_compare
    python research_sub246/machine_encoding/component_packing/guarded_congruence.py --seeds 12 --selector-guards --without-comparator --output /tmp/packed_without_compare

Search merges classes only when every shared admitted symbol has equal write
and movement, recursively requiring projected targets to agree. Ports and
failure states are never merged. This is a heuristic finite search, not an
optimality proof. Its final certificate is checked separately.

## Earlier controls

`core/` packs the original oracle/native/writer disjoint entries into168states.
`full/` is an older loose215-role inventory with202states and11 external ports;
it is superseded for architecture planning by the retained query inventory.
`retained_conservative/`, `retained_guarded/`, `retained_reviewed/`,
`guarded_before_selector/`, and `guarded_congruence/` retain successive controls.
The two headline directories above are the latest reviewed-guard inventories.

The --comparator27 flag is an optional unpromoted stronger-gap lane; no headline
result relies on it. The exported216-state result uses the comparator29's
original gap>=2 contract.

The final one-state delta is reproduced by `remove_unreachable.py`, applied to
`guarded_reviewed/` and `guarded_without_compare/`. It checks the entire admitted
reachability graph before absorbing query prefix000. Its own proof certificate
is in each final directory. The preceding217/188-state witnesses remain saved
unchanged. A newly added internal query entry would invalidate this dead-role
proof and must not be hidden by the linker.

## Independent audit

`../../verification/audit_packed_libraries.py` independently parses the original
literal component tables and reviewer guard maps, checks every projected row,
entry, return/failure distinction and universal class, and recomputes the exact
unreachable-role graph. `packed_libraries_independent_audit.json` reports PASS
for216,187,217,188 and native62. No packing defect was found. This confirms the
component-library equivalence only; the listed full-machine obligations remain.
