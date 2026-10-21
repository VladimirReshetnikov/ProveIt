# Antecedent exchange: a calibrated formalism family and its measured cost

The new formalism family below has exactly the same native theorem codes as
accepted K215. The source experiments did **not** reduce the state count and
do not constitute additional binary machines. The initial measurements use the exact
K215 source at ProveIt commit `b6fb232916d008383e7cf2990d68ddb30fded7db`.

## Exact preservation theorem

Let I(x,y)=4P(x,y), R(x,y)=4P(x,y)+1, Q_x(y)=4P(x,y)+2,
E(x,y)=4P(x,y)+3, where P is the accepted Cantor pairing. Let C be the
accepted numerical calculus with truth0, MP, theorem-only GEN, its literal
bundle and gates, rho1–rho6, merged G, and rho8 restricted by U<=A.
The inherited dominated-rho8 theorem supplies every unrestricted rho8
instance and therefore K and S, on arbitrary natural formula codes.

The propositional exchange theorem is

    (X -> (Y -> Z)) -> (Y -> (X -> Z)).

For an explicit derivation, assume f:X->(Y->Z), y:Y, and x:X. Two MP steps,
f with x and the result with y, yield Z. The ordinary K/S deduction lemma
successively discharges x, y, and f. That lemma itself is the finite
induction replacing an assumption A by A->A, another assumption/theorem B
by B->(A->B), and an MP step by the corresponding S instance. No GEN occurs
inside this deduction, so no generalization side condition is implicit.
Repeating with X and Y exchanged proves the reverse transformation.

Consequently any chosen subset of the following four native rows can have
its two curried antecedents exchanged:

| Row | X | Y | Z |
|---|---|---|---|
| rho2 | Q_A(B->C) | Q_A B | Q_A C |
| rho3 | E(A,B) | R(C,A) | R(C,B) |
| rho5 | E(C,A) | R(C,B) | R(A,B) |
| G | E(C,A) | E(C,B) | Q_(R(A,B)) E(A,B) |

Replace X->(Y->Z) by Y->(X->Z), retaining every other row and gate literally.
Both calculi still contain the same dominated rho8 basis. Each therefore
proves exchange, and derives each omitted old/new axiom from its retained
partner by one MP with exchange. Induction on finite derivations, replacing
only the changed axiom leaves, proves equality of all theorem codes.
The translations are primitive recursive. They preserve falsity code1,
truth's numerical alias I(0,0)=0, all gates, and the private matrix/binder
couplings in the bundle. They never assume formula-code injectivity,
ordinary formula substitution, or decodability.

An independent permutation of A,B,C within any retained logical row also
preserves that row's full schema family. The source compiler can recover
any desired row instance by resetting the incoming counter and cache and
using the inverse permutation for the three AX fields. Rho8 and the gated
bundle are unchanged. This is the same parameter-selection interface used
by the already accepted rho6-permutation construction. The additional
exchange step above is a new theorem-family transformation, rather than
merely a parameter renaming.

## Literal source construction

The G row occupies zero-based primitive ordinals [479,888). Its original
closed macro word is

    caE cbE abR abE Q I I.

The first two atom constructors occupy [479,643). Swapping registers4 and5
only in CI/CD operands in that prefix changes the word to

    cbE caE abR abE Q I I.

The rest of G, every opcode and source path, every guarded successor ordinal,
and every other source instruction remain unchanged. The exact reconstructed
source has SHA-256
`14b7480d6fa9369287c4183f824d321f7b805d2c253ea96c8c0aee9bbdfc6b6e`.
It has205 distinct source subtrees, compared with202 for the parent.

`gexchange_census.py` then tests all6^7=279,936 independent parameter
permutations of G,rho6,rho5,rho4,rho3,rho2,rho1, retaining this literal source
association. The minimum is204 distinct subtrees, achieved by four recipes.
The exact count is an exhaustive result **only for this finite family**.
Every variant retains4,751 primitive occurrences; a source DAG count is not
an actual binary-machine state price.

A subsequent closed-reassociation beam, of width64 and at most40 rounds,
visited76,675 sources and stopped after11 rounds with an unchanged frontier.
The best saved count remained204. It uses only rotations of closed source
blocks, checks the complete primitive word and both independent guarded-CFG
resolvers for every saved finalist, and enforces zero-run<=6 and depth<=64.
It is a bounded heuristic search, not a lower bound on other associations.

## Other measured rows and the dual-rho6 boundary

A four-wide interval beam over existing closed source blocks and new binary
joins re-emitted individual changed rows. Every saved source was checked for
its literal macro word, matching independent CFG resolvers, and unchanged
opcodes/guarded successors outside the rewritten row.

| Single rewrite | Smallest saved DAG | Maximum zero run of first saved source |
|---|---:|---:|
| rho2 antecedent exchange |205|6|
| rho3 antecedent exchange |205|6|
| rho5 antecedent exchange |207|6|
| G antecedent exchange, full-row re-emission |206|7|
| G antecedent exchange, original association |205|6|
| Dual rho6, experimental only |203|8|

The last row replaces `(Ex_A Q_A C)->C` by `C->Q_A Ex_A C`. The usual
classical duality proof relies on ex falso, while accepted rho6 itself
supplies ex falso. Thus that proof cannot simply be reused after the
replacement. The repository already contains a countermodel to equality of
the two theorem sets (`alternatives/zero-spare-transfer/report.tex`). No
consistency calibration or machine bound is claimed for the dual row here.
The near-neutral source price and possible relative/Friedman translation
are future research directions only.

## Reproduction

From this appendix directory, with Python3.10+ and assertions enabled:

    python3 -B code/gexchange_census.py --seed baseline --output fresh-census
    python3 -B code/rotate.py --source fresh-census/combo000.json --baseline baseline/sites215.json --output fresh-rotation --seconds 60
    python3 -B code/price_rows.py --output fresh-row-pricing

Output directories must be fresh. The finite census should reproduce the
four minimal source byte strings exactly; elapsed times can differ. The beam
is time capped, and a slower run may return a partial frontier explicitly.
The row-pricing beam is a heuristic and does not certify optimality.
The archived receipts retain their original working paths for provenance;
the reproduction commands use only included local inputs and vendor modules.
The final source-pricing outputs have no allocator, physical transition
table, startup proof, or new proof-assistant endpoint.

## Attribution and execution scope

The accepted numerical constructors, dominated-rho8 completeness, K/S
basis, source parser and closed-splice utilities are inherited from ProveIt
and its attributed upstream work. The census is adapted from the repository's
rho6 packet `code/row_combo_search.py`; the rotation beam is adapted from
`k215-residual-parameter/rotate.py`. Original notices and licenses are retained.
This contribution adds the antecedent-exchange theorem family, exact G edit,
new finite census and source-price experiments. The original naive interval
search was stopped after its first completed row; the archived complete
row-pricing receipt comes from the optimized boundary-based run. The later
outside-CFG check passed on every saved source and is now included in the
portable script. These execution details do not change the measured source
bytes or the stated proof boundary.


## Final census on the new direct-transfer source

The same finite family was also checked on the new DR215 source, SHA-256
`74d21758da7e932de766bee079adf11a7917c03a1957b1111abc6463d70eb332`,
with4,732 primitive occurrences and201 distinct subtrees. Its seven row spans
are the original spans minus one; its rho6 samples B instead of C. All
279,936 independent parameter permutations have minimum201, achieved by
four recipes. The exhaustive statement fixes the literal source association,
the existing seven row formulas and bijective parameter renamings. It does
not cover arbitrary arithmetic parameter maps, removal of rows or every
logically equivalent presentation.

Performing the calibrated G exchange at [478,642) first gives204 nodes. All
279,936 subsequent independent row permutations have minimum203, again
with four recipes. Thus neither of these two exact families reaches200.

An unrestricted closed-reassociation beam on the201-node direct source,
with width64, zero-run bound6 and depth bound64, converged after11 rounds
with75,077 visited sources,75,076 expansions and best saved count201. It
checked the complete primitive word and both guarded-CFG resolvers of every
saved finalist. This bounded beam is not exhaustive over associations.

Additional reproduction commands, from this appendix directory:

    python3 -B code/direct_census.py --seed baseline/dr215.sites.json --output fresh-direct-census
    python3 -B code/direct_census.py --seed baseline/dr215.sites.json --exchange-g --output fresh-direct-G-census
    python3 -B code/rotate.py --source baseline/dr215.sites.json --baseline baseline/sites215.json --output fresh-direct-rotation --seconds 60

The rotation script now writes compact finalist receipts and source files.
The archived compact receipts record the hashes and byte sizes of the
original expanded receipts; the approximately197MB expanded syntax-tree
traces are omitted. This changes only reporting, not the search or checks.


An independent local check also binds the new DR215 row to the exact old
and new macro words `aacQFIQFIcI` and `aabQFIQFIbI`. It checks all literal
primitive words, macro exit locality with both CFG resolvers, the four
changed register operands and the resulting numerical constructor AST.
The copied register3 loads at [939,965) and [1117,1143) become the inherited
register5 loads exactly. It reuses the stated inherited all-natural load
and constructor contracts; it is not another physical runtime proof.

    python3 -B code/check_macro_binding.py --work fresh-macro-check
