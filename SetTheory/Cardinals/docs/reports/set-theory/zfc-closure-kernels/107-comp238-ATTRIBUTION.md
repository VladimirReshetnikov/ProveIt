# Attribution and inherited material

The original compact set-theoretic calculus, source program, and 254-state machine are credited to Mira-Cult. The upstream Rocq/Coq verification is credited to Jeff Ketchersid and contributors. Compiler framework work is credited to Andrew James Wade. The existing ProveIt formalizations, source transformations, machine reductions, and logical calibrations remain credited to their original authors.

This package uses two distinct incoming results at ProveIt read commit `ce192939372ac7944fe2a0208c68a96d49fb5e3b`:

- `ZFC_239_State_Construction_2026-10-19.zip`: source reparenthesizing, charged decoder repair, and entry-context split producing Boundary239. The complete archive is retained verbatim in `vendor/`, including its notices and source pins.
- `BusyBeaver239_Research_2026-10-19.zip`, also represented by `ZFC239_Companion_2026-10-19.zip`: state-169 reuse through states 80 and 91, shared-return repair, local simulation, the inherited symbolic guard engine, and the inspected 946-bit equational packet.

The **new machine contribution** is their explicit 238-state composition and its proof of compatibility on the changed source. New checks include the four-block transfer and its exact local invariants, complete parent/new blank-prefix comparison, the rederived universal right-neighbor guard on Boundary239, and the direct unbounded check of the final table. Re-executing a prior proof engine does not transfer authorship of that engine or its underlying induction principles.

`verification/symbolic_runtime.py`, `verification/independent_runtime.py`, and `verification/check_literal_runtime.py` are unchanged inherited files from Boundary239. The two helper files under `verification/guard169/` are unchanged inherited Coordinated239 files. Its driver adapts input pins and the expected runtime row census, with exact provenance in that directory. `references/previous_guarded_fold239.py` preserves the inherited local construction for comparison.

The **separate equational contribution** combines a complemented-witness binder with explicit Boolean factoring and elimination of the auxiliary flag. The raw EPSC/ZFC comparison, native stack, same-carrier model, shared cons/NAND class constructor, truth fusion, and member-selector specialization are inherited and cited. Boolean factoring and flag elimination are standard logical operations; no general historical priority or global shortest-packet claim is made. `foundations/ATTRIBUTION.txt` and `foundations/sources.json` give additional dependencies.

The Boolean single axiom Sh1 is due to William McCune, Robert Veroff, Branden Fitelson, Kenneth Harris, Andrew Feist, and Larry Wos, *Short Single Axioms for Boolean Algebra* (2002), Theorem 2. The report cites the authors' primary paper.

Original license files and notices are retained under `licenses/` and inside the unchanged vendored archive. Their inclusion does not relicense inherited material. This report and the new construction files are prepared for incorporation into the user's ProveIt repository. No remote commit, publication, or claim of a newly closed proof-assistant endpoint was made.
