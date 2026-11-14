Local state-elimination experiments
==================================

These are unsuccessful, restricted searches for a one-state deletion.
They do not prove a lower bound on Turing-machine state counts. The two
row programs are synthesized independently: a return to the merged state
on the other read bit rejects that first-row candidate. New destinations
are surviving working controls, not the removed control or halt label.

All runs use native state labels and start 74. The exact input tables are:

  ../../construction/AX11QH4L/machine.native.tm
  ../../construction/AX11QH4R/machine.native.tm
  pa194b.native.tm
  b4l.native.tm
  ax11qh4lb.native.tm
  ax11qh4rb.native.tm

The last three are local B/4L compositions used as search inputs. This
directory does not promote them to additional proved consistency machines.
The original B input and the inherited B/4L method are attributed in the
main report and inventory; exact bytes are bound by the package manifest.

Build any program using a C++17 compiler, for example:

  g++ -O3 -std=c++17 multistep_pairs.cpp -o multistep_pairs

Example invocation, from this directory:

  ./multistep_pairs ../../construction/AX11QH4L/machine.native.tm fresh.json 31 3

The optional numeric arguments are the new-transition bound and radius.
The retained multistep runs use 31 transitions and a seven-cell window
(radius 3). They accept equality with any of the first nine old transitions,
provided the local executions remain within the window and match the
entire window, head position and aliased control. The .contexts.json files
contain the inductive abstract reachable-window supersets, initialized with
every possible window at control 74 and treating incoming exterior bits as
arbitrary. This is not a finite simulation of the all-zero tape.

invariant_pairs.cpp uses the same abstract invariant and requires equality
with one old transition. local_pairs.cpp uses only immediate incoming-history
constraints; the retained runs use a five-cell window and bound 19.

Every complete retained run had zero hits. Empty JSON arrays are deliberate
negative results. The logs report pair, action, and case-test counters; the
action count does not enumerate every possible pair of replacement rows.
See the main report for the restrictions and interpretation of these counts.
