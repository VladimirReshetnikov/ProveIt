G_X: an arbitrary-consequent gate, with an exploratory 198-state realization
============================================================================

Status
------
This is supporting research, not one of the delivered 194-state machines.
The logical/source construction is validated; its initial physical realization
has 198 working states.  No complete blank-start verification, independent
literal physical simulation proof, or physical Con(PA) theorem is claimed for
this 198-state table.

The change replaces the original guarded gate

    (V(a,b,c) -> Q(a,b,c)) -> 1

by its arbitrary-consequent family

    (V(a,b,c) -> Q(a,b,c)) -> z.

This is a conservative change of the numerical calculus.  The old gate is
the z=1 instance, and the inherited h1 and implicational basis derive 1 -> z,
which composes with the old gate to prove every new instance.  The fourth AX
field is now this consequent.  The resulting AX command has ten entries and
does not fall through into MP.  See gate_x_notes.tex for the written proof,
including all-store selectors and the refutation compiler.

Source proof and checker
------------------------
check_gate_x.py independently assembles every primitive arithmetic template,
resolves the complete named source tree, and checks the full AX expression in
a free arithmetic term algebra.  It keeps both guard tests symbolic and checks
every intermediate scratch precondition.  Its receipt records:

    3,666 primitive sites; 4,772 source outcomes; 191 expanded macro tokens.
    AX break 3566 -> return 3654 -> fetch 25; MP begins at 3567 and is skipped.
    Exact visible gate, nine generated stack heads plus saved top,
    zero offset/cache/scratch, and the correctly consumed fourth field.

The inherited arithmetic-template module is bundled at
../ax11h_audit/verification/check_source_commands.py.  The source theorem relies
on the written uniform arithmetic-template lemmas, not on treating its one
hundred small duration examples as a uniform proof.

Physical exploratory artifacts
------------------------------
initial198/ contains the initial raw and folded native tables, source arrays,
folds, local simultaneous-fold certificates, grammar, and the original
oracle-based runtime receipt.  Its decomposition is:

    134 fixed controls + 70 AX readers - 6 checked folds = 198 working controls.
    Raw table: 204 controls.
    Runtime outcomes: all 4,772 pass; maximum 497 symbolic events per outcome;
    total 1,508,421 symbolic events in the original validation run.

The runtime validator uses inherited arithmetic-box oracles.  It is distinct
from the independent literal checker used for PA194OM and PA194OMF.  These
physical artifacts therefore document a promising implementation route rather
than an additional calibrated blank-start machine.  The portable builder
regenerates the table, checks the same source graph and local folds, and repeats
the oracle-based runtime validation.  It does not run a blank initializer.

Corrected bounded grammar search
--------------------------------
The retained valid run used random seed 2026111431 and stopped after exactly
2,000,000 iterations (629,416 accepted moves; observed runtime 183.352 seconds).
It searched reassociations of the fixed G_X macro word, enforcing entry-context
and address constraints through its score.  Parameter renaming was disabled.
Its best effective reader cost was 64, hence the best predicted total remained
134 + 64 = 198.  It found no qualifying candidate of 194 states or fewer.  This is a
bounded search result, not a proof of optimality.

search/ contains the exact corrected C++ sources, initial seed description,
leaf attributes, log, empty-hit CSV, summary, and its best final pool grammar.
The latter has the same fitness as the initial construction and was not
presented as a physical improvement or subjected to another full rebuild.

An earlier exploratory fitness calculation improperly reused native control 333
for the subtree (98, 90), even though the G_X fixed engine has no control 333.
The retained screen.cpp fixes this by requiring fixedstate[333].  Results from
that earlier run are excluded from the search totals and state claims here.
An attempted physical rebuild of its apparent improvement still had 198 states.

Reproduction (Python standard library and a C++17 compiler)
---------------------------------------------------------
From this directory:

    python check_gate_x.py
    python build.py --out rebuilt_initial198
    c++ -O3 -std=c++17 search/search.cpp -o gx_search
    ./gx_search search/seed.txt search/leaf_attrs.txt search/replay 3600 2026111431 2000000

The search command has both a one-hour wall-clock ceiling and an exact
two-million-iteration ceiling; on the recorded run the iteration ceiling was
reached first.  The original recorded valid log is GX_valid.log.  The source
and seed determine the bounded search; elapsed times need not match.

Inputs and provenance
---------------------
The fixed raw table and H-controller edits come from the supplied PA194ORH
research packet's construction/inputs.  The compiler, symbolic runtime,
support functions and fold screen are retained modules from that packet, with
their original notices.  build.py adds a portable binding to the new source
nodes, gate grammar and macro entries.  The top-level package includes the
applicable upstream licenses.  copy_provenance.json records copied-file hashes;
search/summary.json binds the corrected search files and its exact result.

The new logical gate and source proof are separate from the PA194OM/PA194OMF
calibration.  They are included to preserve a materially different avenue for
future compression, without overstating its current binary state count or
verification status.
