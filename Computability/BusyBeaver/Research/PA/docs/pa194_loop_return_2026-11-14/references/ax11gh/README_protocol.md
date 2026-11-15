# PA194AX11GH and PA194AX11GHS

This packet constructs two complete 194-state, two-symbol, single-tape,
blank-start Turing machines. Their recurring command architecture combines
the explicit generalization binder of AX11G with the cache-only Shift
test of GH/GHS and the four-field, eleven-entry AX operation of AX11.

The written proof establishes the new relative machine/calculus theorem
in iPRA. Composing it with the **current incoming AX11H packet's written
PA calibration** gives the claimed iPRA equivalence between nonhalting
and Con(PA). The exact inherited packet and all ten of its proof sources
are included. This is not a newly completed Lean or Rocq proof.

## Main artifacts

- proof/new_protocol.tex and proof/new_protocol.pdf: complete 12-page
  protocol, compiler, weak-induction, enumeration, physical/source
  composition, and calibration-dependency proof.
- machines/PA194AX11GH/machine.tm and
  machines/PA194AX11GHS/machine.tm: the complete dense transition tables.
- Each machine directory also contains the native table, raw table,
  source tree, primitive instruction graph, dense/native labels,
  contextual folds and their cases, and construction receipt.
- verification/results/: independent literal contracts, rederived
  unary-list lemmas, whole-tape startup records, and receipts.
- verification/physical_ipra_receipt.json: complete finite closure,
  destination-address, and duration audit.
- verification/source_commands/: independently generated arithmetic
  template ports, every-source-edge matching, and symbolic AX endpoints.
- verification/novelty_pair_receipt.json: graph comparison against
  110 current 194-state classes, with no matches, including neither
  new table matching the other.
- references/pa194_ax11h_research_2026-11-14.zip: the exact current
  inherited written calibration, retained as a self-contained archive.
- references/ax11h_written_ipra/: extracted proof sources, claims,
  README, notice, and precise provenance.
- verify.py, build.py, construction/, inputs/, and verification/:
  reproducible construction and checks using only the Python standard
  library.

## Exact machine convention

Each transition line is "state read write direction next".
The tape is two-way infinite and initially all zero, with head at
coordinate zero. The dense initial state is 0. Working states are
0 through 193, and the separate halt label is 194. Each table contains
388 transitions. Native start/source-boundary/halt labels are 74/84/254.

| Quantity | AX11GH | AX11GHS |
|---|---:|---:|
| Working states | 194 | 194 |
| Raw fixed controls | 134 | 135 |
| Raw AX readers | 67 | 67 |
| Contextual folds | 7 | 8 |
| Local two-cell fold cases | 28 | 32 |
| Primitive source sites | 3,671 | 3,668 |
| Source outcomes | 4,778 | 4,774 |
| Independent literal symbolic steps | 1,106,693 | 1,110,639 |
| Maximum independent symbolic case | 385 | 385 |
| Blank startup transitions | 57,922 | 57,768 |
| Nonhalting destination checks | 4,777 | 4,773 |
| Halting outcomes | 1 | 1 |

Dense SHA-256:

- AX11GH: 513e9c8b28e0dd41e6003bb8d82c80ff3dac5fb3c5274cd2f709a3bba8c3e9e1
- AX11GHS: 7a4738a9eedd3f53674d67568b3197d38237d11d0fc08fa3d41251a8faf8052c

## What changes

Relative to the current incoming GH/GHS raw source, the final AX return
is replaced by the ordinary Push macro. The sole raw row edit is

    (2066, 1): (0, L, 302) -> (1, R, 19).

It preserves all existing contextual folds and reaches the full MP
operand reader. This creates a genuine fourth AX operand; it cannot be
treated as a three-field no-op. The new command saves eleven entries,
including the old top, returns top/cache zero, and leaves the fourth
operand as its offset.

The new generalization head is U(c,h), using the explicit first AX
operand and the incoming cached theorem. It does not use the incoming
offset as binder, and it does not generalize the arbitrary offset value
h+y. The source algebra checker verifies these distinctions.

Shift tests only h == 1. Pop therefore halts on an incoming top one;
it is not an unconditional returning identity. The proof compiler
handles this early halt, and the all-store refutation word uses Pop,
not a lone Shift. The generalization suffix remains safe even when
its input theorem has code one.

The GH and GHS source programs implement this same command protocol.
GHS reverses the two comparison operands after copying the cache;
this shortens the primitive Shift code by three sites without changing
the working-state count.

## Reproduction

From this directory, with assertions enabled:

    python3 -B verify.py

This rechecks command algebra, every primitive source instruction and
edge, stored certificate closure, the four generic list certificates,
and novelty against the bundled 110 prior graphs. It also verifies
the exact dense-table hashes. It does not claim to regenerate the
long literal symbolic traces.

For complete regeneration and independent literal replay:

    python3 -B verify.py --full

The full mode additionally rebuilds both tables and replays all
construction and independent physical contracts and both blank
startups. It can take several minutes. Logs are written to
verification/logs/; each checker stops on the first failure.

Do not use Python's -O option: assertions are verification gates.

The TeX proof compiles with a normal pdflatex installation. In the
shared task environment, the available prebuilt TeX format was selected
using TEXMF, TEXFORMATS, and TEXFONTMAPS; no such local paths are
needed on a standard TeX installation.

## Scope and provenance

Pinned repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: 1e1a41f799d4658b829cdd0eabae3775a0c8c4a0.

The bases are the latest incoming GH/GHS and AX11G packets, while the
absolute calibration comes from the latest incoming AX11H packet.
The latter's archive hash is
93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075.

The literal contracts quantify over arbitrary natural registers, an
arbitrary nonempty finite spare list, and an arbitrary nonnegative
header-gap parameter. Complete finite-support tapes, not a bounded
view window, are compared at startup and at symbolic boundaries.

The checks establish finite bindings and replay symbolic certificates.
The written generic rule proofs and the inherited PA calibration are
separate mathematical inputs. proof/new_protocol.tex names those
dependencies and explains the quantifier-free induction invariants.
The absolute statement is a written mathematical result, not a claim
of an end-to-end kernel check. A flaw in the inherited calibration
would affect that absolute conclusion while leaving the new relative
machine/proof-calculus construction separately reviewable.

No machine below 194 states is claimed by this packet, and no
minimality statement follows. The parent research deliverable records
the parallel state-reduction attempts and any additional variants.

