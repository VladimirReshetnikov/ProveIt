# Direct exact246 selector and coverage route

The shortest proof route is to reinstantiate the already checked prefix250
marking, register and symbolic contracts on the exact246 table. It avoids
adding a global old-machine avoidance invariant to the runtime theorem.
The old→new restricted quotient remains useful corroboration, with its
six excluded state/read pairs explicit. It is unnecessary as a premise of
the direct exact246 macro proofs or closed instruction checks.

This is source-only design and static source comparison. None of the new246
sources discussed here has been compiled by this agent. Root owns proof
execution. The exact246 Table/Fast lane belongs to opening; Pulse/Boxes and
frame/runtime transport belong to reflection; Mark/Symbolic/coverage belong
to this lane.

## Exact changes and minimal selector proof

Old250→new246 deletes old labels 0,1,3,97 and changes the surviving rows
60/0 from 0R0 to 0R20, and 255/0 from 1L97 to 1L255. The old-label start
changes from97 to95. All other surviving rows are identical. The canonical
new table is SHA256 `89cda615b3ea9fcac07ad6b08e0351faa34841a56935b6f5846d3920f13bc0fc`;
its old-label table is `303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee`.

For a direct marking proof, change only the erase-entry abbreviation from
old0 to old20. The selected ordinary block is `0 1^(v+1)` for arbitrary
natural v; therefore the successor of60/0 reads one. Old20/1 performs the
required `(0,L,2)`. The proof never uses old20/0. All nine skip loops and
old2/4/6 return rows survive. Thus the entire existing `mark_word` proof
still preserves arbitrary left word l and suffix X, returns one cell left
of the original boundary and takes exactly `2*width(pre)+3` moves. Its
unpadded whole-tape clients are unchanged.

Drafts are `/tmp/zfc-prefix246-lean/mark/RegisterMarkPrefix246.lean` and
`Audit.lean`; the source-port diff separates the one behavioral abbreviation
from state/type/module renaming. The audit includes explicit old20 entry
checks in addition to the existing arbitrary-prefix and complete-tape clients.
No global transport invariant is needed for this theorem.

The alternative quotient maps old0↦old20 and old97↦old255, with identity on
surviving labels. Its commuting domain excludes exactly
`{(0,0),(1,0),(1,1),(3,0),(3,1),(97,0)}`. Incoming0 is only60/0; incoming1 is
0/0,1/1,3/1; incoming3 is only1/0. The mandatory first one proves the
selector's avoidance on the actual register shape. This does not establish
avoidance for arbitrary tapes, nor transport the old blank start.

## Local pulse and symbolic interfaces

The direct246 pulse uses75/0→255/0→255/1→131; the last read is the one
written at the original position. Its three-step whole-tape endpoint is
the same local endpoint used by Boxes250. The neighboring-one branch reaches
131 after two moves, then112 after the third; the three-step old112 contract
is the interface needed by zero rollback. The old250 global left-neighbor
invariant must not be copied: after the new255/0 self-return, the current
cell is forced one, but the cell to its left is arbitrary.

Reflection's direct Boxes246 port retains every operation contract. Its
only proof-row change beyond names/types is private blank-pulse97/1→255/1.
INC still appends one value-one spare; positive CD shifts the physical origin
right one cell; zero CD requires an actual following block and returns via112.
The `Valid` premise remains ten physical blocks, supplied by nine primaries
and an explicitly nonempty finite suffix.

`SymbolicPrefix246.lean` retains the checked proof-producing executor and
full-tape denotation. Its concrete behavioral changes are the exact new
machine/Fast lookup, new Mark/Boxes parents and the compact selector recognizer.
The nine physical selector labels and regenerated canonical IDs are:

| Physical index | Old label | New canonical ID |
| --- | ---: | ---: |
| 0 | 60 | 54 |
| 1 | 44 | 39 |
| 2 | 31 | 27 |
| 3 | 56 | 51 |
| 4 | 38 | 34 |
| 5 | 40 | 36 |
| 6 | 28 | 24 |
| 7 | 64 | 58 |
| 8 | 69 | 63 |

The old250 numeric match cannot be copied. The draft regenerates it from the
exact delivered renumbering and supplies both `skipTarget_sound` and
`skipTarget_complete` as finite kernel decisions. Deleted labels must never
be passed to the total old-label helper's fallback and treated as valid states.

## Source63 full-affine audit to Lean

The delivered full-PC checker freshly parses all6459 `Prog254.v` rows,
compares its6460 paths to the cache, retains overflow and trailing zero cells,
and supplies the actual246 table to the inherited affine engine. Its observed
8391 successes comprise1931 zero CDs,1931 positive CDs,2601 INCs,128 breaks,
1799 continues and one halt. It reports342 oracle-guard checks, three overflow
cases, minimum13 literal moves and at most497 symbolic rules. These are
recorded Python results, not kernel premises or guaranteed Lean resource costs.

Our own source-only traversal of maintained `ActualTree254.tree` matches all
6460 delivered source63 site triples, in DFS order, including the physical
register mapping `[6,2,0,4,3,7,8,5,1]`. See
`source63-static-decoder.json`, SHA256
`e0681caef1d8c16e0fca9ed183e3af0a49e0f15a934e362e43a3bfc04236c632`.
The maximum depth is34. `ActualTree254.tree_eq` provides the separate checked
Lean connection to `Prog254.program`; no copied Python list becomes a theorem
premise.

| Source63 rule or invariant | Direct Lean counterpart |
| --- | --- |
| Literal exact table row, including final halt write/move | `literal_left`, `literal_right`, `box_back`; `FastTablePrefix246.fast_transition_eq` |
| Natural affine run a*n+c; peel only positive constant, remove only zero run | `peel_right`, `peel_left`, `empty_run_right`, `empty_run_left` |
| Literal same-state unary self-loop induction, including writes | `scan_right`, `scan_left` using generic `WritingRuns` |
| Mark unchanged file only at nine selectors | `box_mark`, regenerated `skipTarget`, `boxChecked` |
| Same selected physical CD register and correct zero/positive guard | Typed `Branch`, `Valid` and `boxChecked` equality test |
| Exactly one pending effect | `Effect`/`Box`; modified plain boxes cannot be marked again |
| Positive CD adds a left one and shifts the boundary witness | `box_positive_decrement`, witness h+1, target extra=1 |
| Word normalization and blank left padding | `matches_sound` and `exec_to_matches` with whole-tape `ZipRep` |
| Progress is a literal transition, never mere scan/box rewrite | `CheckedStep.moved`, `exec_sound`, `verifies_sound` |
| Full-width increment/strip and independent overflow | `RegisterPath` operations; Site target distance40+overflow+extra |

The source-only Site/Frame/Instruction/Runtime ports can retain their exact
public contracts under246 names. The physical permutation, clean-PC lemma,
minimum total distance40, overflow convention, nonempty-spare output and
strictly positive segment obligation are unchanged. The all-sites theorem
must be for `SitePrefix246.checkSite` itself. Python's at-most497 rules do not
prove the Lean fuel4000 sufficient: the closed Lean decisions establish that.

## Coverage packaging without233 mandatory files

Reuse the actual-tree frontier and structural completeness method, after
renaming the checker and namespace to246. A leaf/cut theorem must decide
`allSites SitePrefix246.checkSite reverse(path) (descend ActualTree254.tree path)`.
Each join must take both actual children; the final theorem must have no
coverage premise. Existing generic `SiteCoverage` and literal-tree providers
can be reused with exact successful evidence.

The64-guard frontier has233 cuts,232 joins and6460 leaves. These cuts do not
require233 independent source modules. Keeping the same closed cut theorems,
plus the existing15 join modules and final module, adaptive grouping gives:

| Batch limit | Total modules, keeping first pilot separate |
| --- | ---: |
| 4 cuts and128 guard cases | 101 |
| 8 cuts and256 guard cases | 53 |
| 16 cuts and512 guard cases | 35 |

These are static packaging counts, not performance measurements. First check
the actual246 small pilot and representative cut42 (61 guards, prefix depth23,
subtree depth11) and cut210 (34 guards, prefix depth24, subtree depth10).
Choose batches from measured margin under the same wall/memory/default proof
limits. Split a failing batch; if one closed theorem fails, split its actual
subtree and add a binary join. No250 pilot result proves acceptance on246.

The bounded pipeline must bind all successful predecessor source/object pairs,
freeze source objects before audits, verify first-provider resolution, retain
failed attempts, and bind every final import. Final audits must include all
three public roots: `all_sites`, `actual_walk_checked` and `actual_walk_exists`,
with typed arbitrary-PC callers. This supplies the coverage premise for
`RuntimeInstancePrefix246`, not the initial frame or consistency calibration.

## New blank-start boundary

The246 startup must be checked independently. It begins in canonical0=old95
on the zero tape at head0; the old250 and247 startup certificates do not apply.
The exact target after410735 moves is canonical88=old96, head−5, marker−6,
header176, path[], gap181, logical registers `(3,0,0,0,3,0,0,0,0)`, and167
value-one spares. Physical primaries are `[0,0,0,3,0,0,3,0,0]`; file positions
177 through701 have exactly24+501 cells. Total support has351 ones and the
entire remaining infinite tape is zero. For Site's start representation the
natural gap parameter is181−40=141.

The required endpoint is whole-tape `DispatchFrame` for that logical root,
plus explicit nonempty spares and `RegisterPathClean.clean_nil`. The downstream
logical chain must pass through the all-register `Bisim254` comparison from
the actual6459-node program to the219-node DAG, then specialize
`DirtyProgram254.six_nonformula_path_iff 3 0 3 0 0 0`, followed by the maintained
native/ZF/ZFC refutation comparisons. Applying the dirty-root lemma directly
to `Prog254.program` would omit its distinct program-comparison bridge.

A complete external Lean exact246 endpoint will still leave the user's
proof-inside-PA requirement separate. The current source work claims neither
that endpoint nor unconditional nonhalting or Con(ZFC).
