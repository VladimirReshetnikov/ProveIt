# Transfer accounting: the historical 243-to-235 sequence and K230-to-K226

Historical numbers in the second column use the inherited ProveIt machine
labels. K230 numbers in the fourth column refer to the pinned Elliot Glazer
table, before dense renumbering. The two number systems are not interchangeable.

| Historical saving | Inherited state reduction | Status on K230 | Actual result in this construction |
|---|---|---|---|
| 243 to 242 | `27 -> 15` | Already present | K230 already incorporates this reduction. It supplies no additional state saving here. |
| 242 to 241 | `39 -> 17` | Already present | K230 already incorporates this reduction. It supplies no additional state saving here. |
| 241 to 240 | Closed H transfer-plus-one source identity, then `90 -> 72` | Transferred | Four source replacements prepare K230 `79 -> 63`; one working state is removed. |
| 240 to 239, boundary branch | Split the two roles of old `218` between `179` and `223` | Transferred in combination | K230 state `175` has the corresponding two roles. Its `pi` role goes to `150`; its `zi` role goes to `152`, together with the later predecessor-fold idea. The two historical steps together give one K230 deletion, not two. |
| 240 to 239, delayed-erasure branch; composed result 238 | `169 -> 80`, with a coordinated helper return | Transferred | K230 `140 -> 71`, with the corresponding helper and caller changes; one working state is removed. |
| 238 to 237 | `235 -> 98`, with the `240/1` helper route | Changed decoder premise; not separately transferred | The new K axiom packet changes this source word and its sharing. The old source role has no corresponding standalone decoder to delete. No state saving from this historical fold is claimed. |
| 237 to 236 | `223 -> 182`, after predecessor preparation | Transferred in adapted combination | The new four-role assignment uses `150` for `pp/pi` and `152` for `W/zi`, deleting K230 `175`. Its eight open-tape blocks prove the combined change. This is the same single deletion reported in the boundary row. |
| 236 to 235 | `193 -> 74`, after seven source rotations | Changed sharing premise; direct transfer remains open | The needed historical decoder roles are not standalone shared nodes in the K230 source. The literal historical fold was not transplanted. |
| Additional K227 to K226 improvement | New closed rotation exposes literal `65 = 98` in K230 labels | New successful reduction | One rotation at ten occurrences creates the exact duplicate. The complete one-step quotient deletes `65`; five further closed rotations repair its addresses. This is independent of the two historical folds that did not transfer. |

The verified new savings relative to K230 are therefore **four states**:
the H fold, delayed erasure, the combined boundary/predecessor role assignment,
and the newly exposed exact duplicate. Two historical savings were already
included in the K230 reference. Two other historical reductions rely on a
different axiom-packet layout. The boundary and predecessor ideas combine
into a single deletion in this layout.

This accounting describes exact constructions and identified premises. It
does not assert that the unsuccessful transfers are impossible, that the
searched reassociation space was exhaustive, or that K226 is minimal.

## Evidence pointers

- The historical composition and labels are documented in the inherited
  237-state report and its `reference/boundary239_local_proof.tex` and
  `sections/fold237.tex`, preserved by the 236 and 235 upstream packets.
- The final old `193 -> 74` reduction is documented in the 235-state
  `build_zfc235.py`, README, and `sections/fold235_section.tex`.
- `generated/construction.json` and `source_roles227.tex` record the three
  actual K230-to-K227 deletions and source preparation.
- `role_proof.json` and `verify_roles.py` certify the combined decoder-role
  change with complete positive blocks and incoming-tag checks.
- `generated226/construction.json`, `generated226/duplicate_quotient.json`, and
  `source_duplicate226.tex` record the additional K227-to-K226 reduction.
