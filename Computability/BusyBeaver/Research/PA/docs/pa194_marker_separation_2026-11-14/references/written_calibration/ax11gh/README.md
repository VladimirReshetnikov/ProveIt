# Two new 194-state PA consistency designs

**No valid machine below 194 working states was obtained.** This archive
delivers two new source designs, PA194AX11GH and PA194AX11GHS, with an exact
accelerated implementation of each. All four complete binary transition
graphs differ from every one of the 110 complete 194-state classes in the
pinned corpus. The main report contains the complete comparison, written
proof, all four transition tables, and the named-design and delivery ledgers.

## Read first

- `report/pa194_ax11gh_research.pdf` and `.tex`: combined report, with all
  TeX source fragments included.
- `proof/new_protocol.pdf` and `.tex`: standalone command protocol,
  primitive-recursive proof compiler, weak-induction argument,
  source/physical composition, and inherited-calibration dependency.
- `acceleration/acceleration_proof.pdf` and `.tex`: exact physical
  acceleration theorem, proved using primitive recursion and
  quantifier-free induction.
- `STATUS.json`: result and proof-status summary.
- `MANIFEST.sha256.json`: SHA-256 of every delivered file except the
  manifest itself. Replays can regenerate receipts and logs; check
  this manifest before modifying or rerunning the archive.

## The four literal machines

| Machine | Dense transition table | States / rows | Source sites | Blank startup |
|---|---|---:|---:|---:|
| PA194AX11GH | `machines/PA194AX11GH/machine.tm` | 194 / 388 | 3,671 | 57,922 |
| PA194AX11GHS | `machines/PA194AX11GHS/machine.tm` | 194 / 388 | 3,668 | 57,768 |
| PA194AX11GHF | `acceleration/machines/PA194AX11GHF/machine.tm` | 194 / 388 | 3,671 | 57,870 |
| PA194AX11GHSF | `acceleration/machines/PA194AX11GHSF/machine.tm` | 194 / 388 | 3,668 | 57,712 |

Each line has `state read write direction next`. The tape is two-way infinite,
binary, initially all zero; the initial head position is zero. Dense working
states are 0 through 193, the initial state is 0, and the separate halt label
is 194. Native tables start at 74 and halt at 254. Native label 194 is a
working control, distinct from dense halt label 194. The label maps give
the exact translation. Startup is the prefix to the canonical proof-search
frame, not a claimed halting time.

The new architecture combines an explicit generalization binder `c`, a
four-operand AX command saving eleven entries, no-push modus ponens, and a
cache-only Shift test `h == 1`. Older AX11G has a sum test; GH/GHS has the
ten-entry AX interface; AX11QH gets its binder from the offset. The second
new implementation reverses comparator operands and removes three source
sites. The component ideas are attributed prior work; the combined exact
interface, corrected compiler, and literal realizations are the contribution.

The F versions change exactly two native rows:

```text
26/1:  1 R 42  ->  1 R 91
101/0: 0 L 26  ->  0 R 17
```

A direct incoming-row invariant supplies the required local zero bits.
Each changed transition executes exactly three parent steps. The expanded
primitive-recursive clock satisfies `t <= sigma(t) <= 3*t`, with identical
complete tape configurations. Thus the acceleration preserves halting and
nonhalting in iPRA, independently of PA calibration.

## Written theorem and formalization boundary

The new proof establishes in iPRA that each base machine halts exactly when
the specified numerical calculus has a refutation. It gives both
primitive-recursive witness transformations, the early-halting Pop rule,
reserved-zero MP compiler, bounded-store quantifier-free induction,
four-field word encoding, and source/physical clocks. The physical clock
tracks the augmented frame, including its varying spare list and gap.

Composing the relative theorem with the **current incoming AX11H packet's
written PA calibration** gives the written iPRA equivalence
`Con(PA) <-> not Halt_blank(M)` for all four tables. The exact inherited ZIP
and all ten proof TeX sources are retained in `references/`. This is the
later incoming completion, not the earlier filed relative-only packet.
The absolute claim depends on its PA adapter, numerical proof compiler,
distribution exchange, and weak-arithmetic transfer arguments. Neither
the inherited manuscript nor this work is presented as a newly completed
end-to-end Lean proof. A separate focused mathematical review of the new
argument is included; it does not replace a kernel audit of the inherited
calibration.

## Verification and reproduction

From the archive root, with Python assertions enabled:

```bash
python3 -B reproduce.py
```

This reruns command algebra, every source instruction and outgoing edge,
stored physical-certificate closure, literal list-lemma certificates,
whole blank startup for all four tables, both physical shortcuts, and
exact novelty against all 110 prior graphs. The staged archive passed
this command.

For reconstruction and independent literal symbolic replay:

```bash
python3 -B reproduce.py --full
```

The underlying full construction and independent literal gates were all
executed successfully. Full replay can take several minutes. It covers
nine arbitrary natural primary registers, an arbitrary nonnegative header
gap, an arbitrary nonempty finite spare list, and complete blank tape
exteriors. The independent literal checker imports neither the construction
compiler nor an arithmetic-box oracle.

| Independent literal check | GH | GHS | GHF | GHSF |
|---|---:|---:|---:|---:|
| Source outcomes | 4,778 | 4,774 | 4,778 | 4,774 |
| Symbolic steps | 1,106,693 | 1,110,639 | 1,106,033 | 1,109,979 |
| Maximum steps per symbolic case | 385 | 385 | 385 | 385 |
| List lemmas from literal rows | 4 | 4 | 4 | 4 |
| Minimum positive duration constant | 3 | 3 | 3 | 3 |

Receipts and contracts are in `verification/results/` and
`acceleration/independent_results/`. Finite executable checks and written
uniform proofs have separate roles; checks alone are not an end-to-end
consistency theorem. Do not run Python with `-O`.

To regenerate and compile the combined report:

```bash
python3 report/build_report.py
cd report
pdflatex -interaction=nonstopmode -halt-on-error pa194_ax11gh_research.tex
pdflatex -interaction=nonstopmode -halt-on-error pa194_ax11gh_research.tex
```

## Complete comparison

The pinned corpus has 86 deliveries: 82 filed packets and four incoming ZIPs.
The ledger identifies 63 named principal or supplementary designs in 22
mechanism families. The recognizer finds 3,012 text/explicit-JSON occurrences,
804 normalized labeled tables, 680 complete spanning classes across all
sizes, and 110 complete spanning 194-state classes. All 94 official 194-state
classes are present. The 110 include auxiliaries and rejected candidates;
they are not 110 proved consistency machines.

`comparison/packet_ledger.{csv,json}`, `named_designs.{csv,json}`,
`family_matrix.csv`, and `frontier194.{csv,json}` give the complete comparison.
`comparison/census/` contains provenance and exclusion reconciliation.
`verification/search_frontier194/` contains all 110 actual representatives.
`verification/novelty_four_receipt.json` records exact comparisons admitting
arbitrary state renaming, spanning roots, tape reflection, global bit
exchange, and terminal-action erasure. Exact graph tuples are compared
when the structural invariant does not separate a pair; unequal hashes
are not the novelty proof.

The full census can be repeated with a Git checkout containing the pinned
objects and nested archives:

```bash
python3 comparison/tools/census_git.py /path/to/ProveIt 1e1a41f799d4658b829cdd0eabae3775a0c8c4a0
```

That optional census writes below `comparison/tools/census/`. It needs
repository objects; all new-machine checks and the 110-table novelty
check are offline and self-contained.

## Reduction searches and limits

`search/state_reduction/` contains the two-sided stuttering synthesizers,
69-table frontier, source envelopes, 222 quotient screens covering
4,156,062 control-pair checks, and 74 newly exposed neutral runtime-core
edits. `search/bootstrap/` contains the 86,361 compatible two-row bootstrap
repairs, focused marker repair, and joint three-row local screen. All
source code, frozen inputs, recorded results, and replay drivers are included.

```bash
python3 search/state_reduction/replay.py --suite all --out /tmp/pa-state-search
python3 search/bootstrap/replay.py --suite all --out /tmp/pa-bootstrap-search
```

The pair bootstrap search tested 16,667,673 blank starts and found no complete
source frame: 174,344 halted, 16,482,658 entered certified outward rays,
and **10,671 reached a resource bound**. Those capped runs are not certified
nonhalting. Bounds and templates are stated in the report. No general
state-count lower bound follows. Optional searches need a C++17 compiler;
the main machine checks use only Python's standard library.

## Source and attribution

Repository: <https://github.com/VladimirReshetnikov/ProveIt>

Pinned revision: `1e1a41f799d4658b829cdd0eabae3775a0c8c4a0`.

Inherited current AX11H ZIP SHA-256:
`93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075`.

The architecture builds on James Chang's PA development, the current
ProveIt GH/GHS and AX11G packets, and their inherited compiler/engine work.
The source and physical proof framework comes from the current AX11H
packet. Original ProveIt, James Chang, and Wade notices/licenses are retained.
See `NOTICE.md`, `licenses/`, and per-input provenance records.
