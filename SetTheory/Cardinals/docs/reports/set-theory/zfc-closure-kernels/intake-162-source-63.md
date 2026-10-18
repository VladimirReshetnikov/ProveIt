# Source 63: contextual folds to 246 states — independent source review

The two local identifications are mathematically sound on the stated runtime
invariant. I found no new mathematical blocker in the exact 246-state
construction. This conclusion concerns the conventional argument and the
reviewed checking rules, not a new Lean endpoint or a PA proof. Root owns
fresh suite execution; this reviewer executed no supplied script, compiler,
version query or dependency build.

The review reads the complete main `report.tex`, complete
`reviews/independent-fold-proof.tex` and `reviews/independent-calibration.tex`,
the inherited prefix-carry contracts, and the relevant exact constructors,
fold checker, macro induction checker, affine rule implementation, full-PC
checker and bootstrap interpreter. It also checks the signatures of the
maintained dirty-root, program bisimulation and consistency declarations.
Own-code static parsing compared the displayed tables; this involved no
machine execution and imported no delivered Python module. Full input hashes
and precise scope are in the companion JSON.

## Provenance and exact comparison

Arrival is `8cdc55ff92`; the contribution pins ProveIt
`e0b512a63e2c1ca6a1698fa437b8568f1643ff6b` and upstream
`c132d7eae8158cd3a9850ea3eb7251158c3dd821`. Historical prefix250 references
retain their earlier pins. These are inherited dependencies, not another
new 250-state discovery. No checksum manifest was verified by this reviewer.

The canonical 246 table is
`89cda615b3ea9fcac07ad6b08e0351faa34841a56935b6f5846d3920f13bc0fc`;
the old-label table is
`303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee`.
There are 246 working states and 492 rows; start old 95/canonical 0,
dispatch old 96/canonical 88, separate halt old 254/canonical 246.
The sole halting action retains its final write and movement.

Static comparison to the exact prefix250 old-label table confirms only
these surviving-row edits: `60/0: 0 R 0 → 0 R 20` and
`255/0: 1 L 97 → 1 L 255`; old states 0, 1, 3 and 97 are removed, and the
start changes from 97 to 95. Comparison with source 61's exact 247 table
shows the first three deletions and marking change were already present
there: relative to 247, this contribution removes only 97, retargets only
255/0, and changes the blank start to 95. This is a further one-state
reduction relative to that concurrent contribution, not a second discovery
of the same three-state selector saving. No worldwide-priority claim is
needed to use the result.

## The folds and their domains

The marking proof is exact for arbitrary unary values, including zero:
`B(v)=0 1^(v+1)` always supplies a one immediately after its separator.
Thus the new `60→20→2` segment and old `60→0→2` segment perform identical
writes and moves. The selector and unchanged 2/4/6 return scans preserve
arbitrary exterior context and the exact duration `2*width(A)+3`.
Deleting 1 and 3 is justified by the complete incoming-edge facts once the
only external entry through 0/0 is excluded. Main report lines 208–255 and
independent fold note lines 120–150 explain this argument.

For the pulse, old 255 is entered only from 75/0 and old 97 only from
255/0. Starting at coordinate x, the first step writes one at x. If the
right neighbor is zero, the next step returns to that deposited one;
97/1 and 255/1 are identical. Both old and folded three-step pulses end in
131 at x−1 with x and x+1 set to one. If the neighbor is one, the unchanged
two-step route ends in 131 at x. Both conclusions preserve the whole tape.
The folded 255/0 self-target is therefore safe on this route; no assumption
that all entries into 255 scan one is made. Main report lines 257–325 and
independent calibration lines 72–108 give the correct distinction.

The restricted quotient map `f(0)=20`, `f(97)=255` and identity elsewhere
commutes on 494 old state/read pairs, excluding precisely
`{(0,0),(1,0),(1,1),(3,0),(3,1),(97,0)}`. The remaining two redundant pairs
map onto the retained read-one rows. A transition-count induction transports
any old trace avoiding those pairs with identical head, complete tape and
duration. It does not identify arbitrary old and new configurations, and
specifically excludes the old blank start 97/0. The new finite initializer
is logically indispensable.

The direct induction route also matters: the new table is substituted into
the block/macro checker and full instruction checker. Its local proof rules
were inspected: self-loop induction checks the actual row; unknown affine
lengths may be peeled only with a positive constant; arbitrary contexts are
opaque; finite-list induction uses an already checked same-state block
contract; and `C(A)1 = 1B(A)` is derived by list induction. These are
ordinary mathematical checking rules, not an independently verified kernel.
A successful new-table trace is sufficient without treating absence of
removed states from that table as an independent proof about old traces.

## Register contracts and recurrent frame

The four arbitrary-length block contracts are seeker 73, carry 95, return
48 and rollback 112, each of duration v+2. They give the three operations:

- Positive decrement: from marked `B(A) 00 1^x B(S)`, x>0, duration
  `2*width(A)+4`; old 48 exits at the old origin, which is the new boundary.
  The file moves right by one, leaves a one at its old origin, changes the
  selected value to x−1, and preserves the spare list.
- Zero decrement: requires a following block, whose compulsory one selects
  rollback. Duration `2*width(A)+7`, exit old 112 at coordinate −1, complete
  unmarked file restored. Replacing this exit by an older one is invalid.
- Increment: duration `2*width(full file)+7`, exit old 48 at −1; restores the
  mark, increments the selected register and appends a value-one spare.

The nonempty spare premise is explicit and sufficient for every primary
index 0–8. It remains true after arbitrarily many instructions because
increment appends and the other operations preserve the suffix. There is
no fixed finite reserve that the proof can exhaust.

The complete recurrent frame carries a clean PC P, total head-to-header
distance d≥40, |P|≤d, nine primary blocks, a nonempty finite spare list, and
blank exteriors. The clean-path rebasing equation handles both zero padding
past the stored path and an existing zero suffix past the consumed leaf.
The maximum leaf depth is 34; the distance bound is on the entire
PC-plus-gap region. The full-PC target retains overflow and trailing zeros.

For positive decrement δ=1 and otherwise δ=0; for left PC overflow ε=1 and
otherwise ε=0. The certified output has `h'=h−ε`, `d'=d+δ+ε`, so the absolute
header moves by δ. No false invariant that the gap is constant is used.
The full program has 6,459 nodes, 6,460 leaves and 8,391 guarded cases.
The full-source parser and distinct full-PC construction are useful checks;
the latter reuses the affine transition engine and is not an independent
second binary semantics. Oracle guards name the same selected physical
register, and a box can carry only one pending effect.

Positive literal progress makes reverse halting reflection valid: for a
binary halt time t, a nonterminal logical step has a positive segment k
ending active. Halt absorption forces k<t, so strong induction applies at
t−k. This avoids an unjustified infinite choice or inference from long
finite runs. An intermediate visit to dispatch state 96 is not accepted
until the whole target frame is restored.

## New initializer and logical calibration

The claimed finite prefix is exactly 410,735 transitions, not a bounded
search acceptance criterion. The sparse and dense interpreters are read as
source only here. They compare full finite support, not a window, with:
old 96/canonical 88, head −5, marker −6, header 176, total distance 181,
empty PC, physical primaries `[0,0,0,3,0,0,3,0,0]`, and 167 value-one spares.
The 351 one-cells include marker and header. Primary width 24 and spare
width 501 put the file at coordinates 177 through 701, with blank exterior.
These counts are internally consistent; root's fresh replay is separate
execution evidence.

The unchanged physical map yields the same logical root as source 61:
`(N,T,W,A,D,H,X,Y,L)=(3,0,0,0,3,0,0,0,0)`. The exact maintained interface is
`DirtyProgram254.six_nonformula_path_iff 3 0 3 0 0 0` at
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DirtyProgram254.lean:94`.
It concludes native refutation, with formula fields T=H=W=0 and all six
numerical fields unrestricted. The proof uses two `C254.truth` witnesses
and `Enum254.good_zero`. `Bisim254.prog254_halts_iff` at line 3155 is
universally quantified over the register file; it is not restricted to the
old all-zero binary bootstrap. `EnumSafeStart254.complete_from` at line 109
provides padded refutations above an arbitrary initial candidate counter.

The inherited endpoint chain is numerical falsity derivability ↔ native
CP/all-formula-GIC/raw-IR refutation ↔ ZF refutation ↔ ZFC refutation. Relevant
maintained declarations are `NativeTheory254.lean:76`, `WFTheory.lean:43`
and `ChoiceCalibration254.lean:65`. These are external Lean source
interfaces, not newly replayed proof dependencies in this review.

The conventional ZFC argument is carefully scoped: completeness yields a
set-coded model, not a transitive model; the well-founded predicate is
internal, quantifying over represented subsets; construction of the
Foundation subdomain depends on the identified relativization/closure
lemmas; and the internal constructible class of a set model forms a set
subdomain externally. Syntax and satisfaction are set-coded. There is no
universe truth predicate or generic Lean-to-ZFC translation. This makes
the claimed ZFC derivation credible as an ordinary proof relying on those
inherited model constructions, but it does not establish the user's
stronger requirement of a derivation inside PA.

## Concrete issue and integration boundary

One minor reproduction reference is stale:
`reviews/independent-fold-proof.tex:213` says the bootstrap is reproduced by
`build246.py`, which is absent. The packaged actual driver is
`code/check_bootstrap.py`; `reviews/audit246.py` contains another replay.
The main report and portable instructions name existing commands, so this
is not a mathematical or execution blocker. Preserve the delivered source
and record the correction in reconciliation notes.

No new exact 246 Lean theorem is supplied. The current checked exact 252
endpoint still refers to its own table. Completing a 246 endpoint needs
exact table binding, either the restricted quotient with domain avoidance
or direct local contract port, all instruction/frame composition, and the
new whole-tape finite bootstrap. Existing checked 250 pulse/mark/boxes and
ongoing generic frame work remain directly useful; the initializer cannot
be reused unchanged. The separate PA proof-code translation and calibration
obligations remain open. Neither the tables, finite regressions nor this
review prove Con(ZFC), unconditional nonhalting, state minimality or full
two-sided independence under mere consistency.
