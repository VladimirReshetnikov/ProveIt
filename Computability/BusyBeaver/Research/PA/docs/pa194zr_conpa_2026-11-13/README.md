# PA194ZR: a 194-state PA consistency machine

This archive supplies an explicit new 194-working-state, binary, single-tape Turing machine and an ordinary mathematical proof that PA proves its blank-tape nonhalting equivalent to Con(PA). No verified machine below 194 states was obtained. The result addresses the requested same-size alternative.

Read **report/pa194zr.pdf** for the construction, proof, corpus comparison, negative search record, complete transition table, and archive-by-archive ledger. All LaTeX source fragments needed to rebuild that report are present.

## Definitive machine

**machine/pa194zr.tm** is a complete five-column table. A row is:

    current_state read_bit write_bit L_or_R next_state

Working states are 0 through 193. State 0 is initial; 194 is the separate halt label and is not counted. The head starts at position 0 on a two-way infinite all-zero tape. There are exactly 388 transitions, all moving one square left or right. Every working state is graph-reachable.

SHA-256 of this exact file:

    11e4b81320382c3293cb075119f6f87b4b454f96e13798c432744a391ee2398f

The native-label presentation starts at 74 and halts at 254. Its digest is:

    745dd4343d88f6d3458cbde6146cfe360283bc7e8a9113d020eed999b81ad85d

The exact relabeling is in machine/labels.json.

## What changed and why it is correct

PA194ZR inherits the supplied PA194CS calculus, scheduler, register arithmetic, and symmetric Shift protocol. It changes the return convention at nine source instructions: eight shared-comparator returns and the axiom-emitter exit now decrement logical register 3 and take their zero branch. This is implemented by changing two native table rows:

| Read instruction | PA194CS action | PA194ZR action |
|---|---|---|
| State 103, read 1 | Write 0, left, state 302 | Write 1, right, state 17 |
| State 2066, read 1 | Write 0, left, state 302 | Write 1, right, state 17 |

A 129-site source region contains every changed instruction. It has exactly three incoming edges, all zero branches of decrements of register 3, and contains no increment of that register. Induction therefore proves register 3 is zero throughout the region. The old and new source configurations agree after every step, for every initial register store at the designated source entry 25.

The full physical implementation is checked separately. Exact blank initialization reaches the required complete source-frame tape after 59,816 transitions. The initial logical register vector is (2,0,0,0,0,0,0,0,0), with 26 spare blocks of value 1. Initialization is 2,048 transitions slower than PA194CS.

The supplied independent literal-tape symbolic checker rederives four list-sweep lemmas from the actual rows and verifies all 4,754 primitive source outcomes for arbitrary natural register values, arbitrary natural gap parameter, and an arbitrary finite nonempty spare list. It imports no compiler, allocator, or arithmetic-box oracle. Its receipt records 1,103,242 symbolic operations. The separate construction engine checks the same outcomes using the inherited box lemmas.

The consistency theorem composes exact source equivalence, complete positive physical simulation, and the inherited ordinary syntactic PA calibration. The finite calculations and inductive arguments are PA-formalizable. This archive does **not** claim a new end-to-end Lean, Rocq, or iPRA kernel-checked theorem.

The new table is different from every supplied 194-state action graph, even allowing arbitrary state renaming, a different choice of starting control, tape reflection, and global symbol interchange. This is a change of executable control convention, not a new logical calculus. The underlying known-zero-decrement idea is inherited.

## Reproduce the accepted construction

Use Python 3.10 or later, with the standard library. Run from this directory, without Python's -O option: assertions are certificate checks.

Fast reconstruction, complete source invariant, and exact blank initialization:

    python3 -B build_verify.py --quick

Full construction check, including every inherited-engine physical contract:

    python3 -B build_verify.py

Independent source invariant:

    python3 -B verification/check_source_equivalence.py \
      --original reference/parentCS/machine/pa194CS.instructions.json \
      --modified source/instructions.json \
      --output proof/independent_source_invariant.json

Independent literal-tape check, including its own source resolvers and complete blank tape:

    python3 -B verification/check_literal.py

The full symbolic checks can take several minutes. Their completed receipts and logs are included; discovery searches are not needed to regenerate the accepted result.

Second exact blank-start simulator:

    python3 -B verification/check_startup.py \
      --table machine/pa194zr.native.tm --sites source/sites.json \
      --output proof/second_startup_receipt.json

Novelty comparison against the frozen corpus:

    python3 -B comparison/check_novelty.py \
      --candidate machine/pa194zr.tm --start 0 \
      --census comparison/census_current/census.json \
      --table-dir comparison/census_current/tables \
      --output comparison/novelty_replayed.json

Alternatively, run the primary checks in sequence:

    python3 -B verify_all.py --quick
    python3 -B verify_all.py

The first mode omits both full symbolic passes; the second runs them. Neither reruns heuristic discovery searches.

Compile the paper with a normal LaTeX installation:

    cd report
    pdflatex -interaction=nonstopmode -halt-on-error pa194zr.tex
    pdflatex -interaction=nonstopmode -halt-on-error pa194zr.tex

## Artifact map

| Location | Contents |
|---|---|
| report/ | Main PDF, main TeX, and all included TeX fragments |
| machine/ | Definitive dense/native transition tables and exact relabeling |
| source/ | Complete addressed source occurrences and resolved instructions |
| proof/ | Construction, source invariant, and exact startup certificates |
| verification/ | Independent literal-tape and source checkers, engines, receipts |
| comparison/ | Corpus census, 41-packet ledger, frontier table, novelty checker |
| reference/parentCS/ | Frozen supplied PA194CS package; these are parent artifacts |
| reference/logical/ | Relevant inherited calibration sections and command audit |
| reference_cs/ | Required frozen construction dependencies and license notices |
| search/ | Bounded exploratory search sources, receipts, and limitations |
| mathematics/ | Auxiliary antecedent-exchange derivation, not used by PA194ZR |
| PROVENANCE.json | Pinned repository revision, origins, and imported-file hashes |
| RESULTS.json | Concise machine and verification summary |
| SHA256SUMS | Content checksums, excluding the checksum file itself |

## Comparison scope and limitations

The comparison is pinned to ProveIt revision 17f92105e2bc4317feae6c219cb2143437b482ff. It covers 41 principal research packets: 36 filed historical packets and five further incoming submissions. Only 26 ZIPs are currently incoming. Recursive archive traversal recognizes 4,417 complete numeric table occurrences, 620 byte-distinct tables, and eight supplied 194-state action-graph classes. Seven of those classes have implementation evidence; one is a documented failed design. The five new principal cached-machine submissions all contain the same headline PA194C table.

The numeric parser has an explicit text-format scope. It does not automatically recognize machines hidden only in arbitrary source code or JSON; the manuscript review complements the table census. Many experimental tables in the census are invalid, ancestors, or repeated references. The counts are not counts of correct consistency machines.

No verified sub-194 result was found. Search counts are bounded mutation or action trials, not distinct verified machines and not a minimality proof. A seemingly promising register-6 return variant is explicitly rejected: its universal source contracts pass, but it halts during blank initialization at step 1,361. An optimizer defect also invalidated an apparent smaller result; affected runs are excluded from trusted accounting.

## Attribution

This construction depends substantially on the supplied ProveIt research packets, their authors, and James Chang's PA196 development. Relevant notices are retained in LICENSE.ProveIt, reference_cs/LICENSE.JamesChang, and the frozen reference directories. New work here is the nine-return transformation, its local invariant and full physical validation, the current corpus audit, the bounded reduction experiments, and the report assembling the evidence.
