# K215-R6: two fully checked 215-state machines

This packet constructs **K215-R6-120** and **K215-R6-210**, two concrete binary, one-tape Turing machines with 215 working states and 430 transition rows. It supplies an ordinary mathematical proof, formalizable in ZFC, that each machine's blank nonhalting is equivalent to Con(ZFC), using the explicitly inherited numerical-calculus calibration.

**No 214-state construction is claimed.** These are materially changed source/decoder presentations. Exact graph checks exclude a mere state renaming of the four included accepted K215 references and of one another. No new Lean/Rocq kernel endpoint, internal PA endpoint, unconditional nonhalting result, or state lower bound is claimed.

Start with [report.pdf](report.pdf); its complete editable source is [report.tex](report.tex).

## Recommended candidate

Use **machines/rho6_120/** for the main integration candidate. It combines the sixth-axiom parameter change with the accepted DROP0/NIP1/MP2 command order. The companion **machines/rho6_210/** uses NIP0/DROP1/MP2.

| Evidence | K215-R6-210 | K215-R6-120 |
|---|---:|---:|
| Working states | 215 | 215 |
| Transition rows | 430 | 430 |
| Source primitive occurrences | 4,751 | 4,751 |
| Complete guarded runtime cases | 6,176 | 6,176 |
| Symbolic proof-rule applications | 1,699,838 | 1,699,893 |
| Minimum positive clock constant | 6 | 9 |
| Exact blank prefix transitions | 95,714 | 96,284 |

Both reach native dispatcher 84 at head −8, header 57, gap 1, logical registers [4,0,0,0,0,0,0,0,0], forty unit spare blocks, exactly 95 one cells and complete zero exterior.

## Exact changes and logical idea

Relative to the respective pinned parent, only two native transition rows change:

    199/1: 1 R 166 -> 1 R 12
    206/0: 0 R 186 -> 0 R 76

Only four source operands change, at zero-based primitive ordinals 959, 964, 1137 and 1142, from register 3 to register 5. All paths, opcodes and guarded successor ordinals remain identical.

The changed sixth generator emits rho6(A,B) = Ex_A(Q_A B) -> B instead of rho6(A,C). Each parameter ranges over every natural number, so the full numerical axiom family is identical. This includes undecodable codes and the numerical alias I(0,0)=0. It does not assert that a fixed AX argument tuple emits the same codes; the report supplies a repaired axiom-selection compiler, its reset and stack-selector proofs, and the cofinal enumeration argument.

The two-row changes do not occur during either startup prefix. Separate full runtime checks connect the changed source to each changed binary table.

## Provenance and novelty

All parent material is pinned to ProveIt commit:

    75716498437bfc7291d5900cab2983a11fd54bac

The parents are candidate-k215 and candidate-k215/alternatives/commands120 under Computability/BusyBeaver/Research/ZFC.

The rho6 parameter permutation itself predates this packet: it appears in Source163 / K216_Rho6_Permutation_2026-10-21, including the same order-210 source hash in a source/pricing investigation. This packet does not claim to invent that symmetry or source.

The contribution is the exact two-row composition on both accepted K215 parents, including command order 120; complete fresh arbitrary-natural binary runtime verification; an explicit source/calculus proof; separate blank/source/evidence audits; and a portable reproduction path. Further source variants and scoped negative searches are included as research supplements.

## Machine conventions

Each table row is:

    state read_symbol write_symbol L_or_R target_state

Blank is 0, the tape is two-way infinite, and start/head are 0. The halt label is separate from the 215 working states. Entering it halts.

- **candidate.native.tm**: start 0, dispatcher 84, halt 254.
- **candidate.tm**: exact dense relabeling, working labels 0–214, start 0, dispatcher 83, halt 215.
- **canonicalization.json**: exact state bijection and input/output hashes.
- **sites.json**: the matching primitive source list.

Do not mix the source of one command order with the other table.

## Reproduce the positive result

Python 3.10+ with assertions enabled is sufficient. No third-party Python package, solver, network or external repository checkout is required.

From this directory:

    python3 -B code/reproduce.py --output fresh-audit

This reconstructs both tables and sources from the included pinned parents, checks the expected hashes, runs the source certificate, and independently audits the archived complete runtime records and every blank-prefix transition.

To rerun the full symbolic induction checker on both reconstructed machines:

    python3 -B code/reproduce.py --full-runtime --output fresh-runtime

Output directories must be fresh. Allow several minutes. The default per-runtime subprocess timeout is 600 seconds; increase it with **--timeout** on a slower machine. Do not use **-O** or **PYTHONOPTIMIZE**.

Both commands were successfully executed from this assembled packet. The full reproduction independently recreated the per-case and startup JSON bytes; its new process receipts and report records are included in **evidence/portable-full/**.

To reproduce the finite 279,936-recipe source census:

    python3 -B code/row_combo_search.py --seed baseline/candidate-k215 --output fresh-row-census

To compile the report, run **pdflatex report.tex** twice. Standard TeX Live packages suffice.

## What the verification proves

The runtime checker uses literal steps, natural-number induction over unary scans, and finite-list induction after checking the four one-block schemas from the exact table. It covers all natural primary values at each guard, any natural gap, any nonempty finite spare list, and the complete zero exterior. Every affine duration has nonnegative coefficients and a strictly positive constant. This supplies unbounded primitive correctness and divergence preservation.

The standalone auditor imports no supplied checker. It verifies input identities, source/control differences, case completeness and ordering, positive recorded clocks, literal row/block coverage, dense renaming, graph comparisons, and an independent complete blank replay. It does **not** independently reconstruct the entire symbolic induction proof. The separate source proof and inherited numerical-calculus calibration are necessary mathematical premises.

Original runtime records bind executed inputs by report hashes and record observed successful process completion; they do not claim a prelaunch before/after manifest. The fresh full reproduction additionally records before/after hashes of reconstructed artifact files and direct subprocess return statuses.

## Supplementary research

The **research/** directory contains:

- A complete 6^7 = 279,936 row-permutation census. The minimum is 202 source subtrees, achieved by identity, rho6, joint24 and joint246. This is not a Turing-machine state lower bound.
- Exact calibrated sources for joint swaps of B/C in rho2 and rho4, optionally also rho6. These have no accepted new binary allocation here.
- Local-fold, elimination, rewrite and physical-rotation result records, scoped in HANDOFF.md and the report. Some exploratory local-search receipts retain original paths and are not self-contained rerunnable search suites. None is a premise of the positive construction.
- A portable controlled global allocator, its successful source-identity control, two restricted-family infeasibility records, and a broader timeout. NumPy/SciPy are needed only for these allocator experiments.
- An independently reproducible **rejected** 215-state NIP0/MP1/DROP2 machine that halts from blank after exactly 646,553 transitions because its initialization places falsity on the stack.
- A symbolic obstruction to a tempting shared-PUSH shortcut. No equiconsistency claim is made for that shortcut.

## Files and integrity

**manifest.json** pins the parents, exact candidate identities, original runtime outputs and verification implementation. **SHA256SUMS.json** covers every final packet file except itself.

**baseline/**, **references/** and **licenses/** retain the inherited source readers, proof expositions, attribution and terms. Original historical output records retain their absolute working paths, but positive reproduction uses paths relative to the packet.

The report's bibliography links to exact predecessor files at the pinned commit. Copies of inherited proof expositions retain their original relative links; use the pinned bibliography links for upstream context.

## Attribution and terms

The underlying machine architecture, numerical theory, dominated-row theorem, command compiler, source readers, runtime engine and older proof/search methods are inherited. Their original notices credit ProveIt and its submitted constructions, Elliot Glazer's K/K230 work, Jeff's busy-beaver/Rocq reference, Andrew James Wade's compiler ancestry, BusyCoq, and the Coq Library of Undecidability within their respective scopes.

This packet's reconstruction, exact new compositions, audits, source-family proof and manuscript were prepared by the research collaboration for Vladimir Reshetnikov's ProveIt project. Separate agent reviews are internal to that collaboration, not an external human endorsement. New material follows the repository's MIT No Attribution terms; inherited components retain their original terms. See **licenses/**.
