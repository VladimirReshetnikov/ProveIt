Research search programs and frozen inputs
=========================================

These programs are research tools, not a substitute for the literal machine
verifiers. They derive from the attributed symmetric-witness grammar search
and screening code; provenance for the ancestor is in ../../references/.
The new joint search enables dormant per-head parameter permutations and
corrects the lengths of the two/four-increment macros. The fused search
changes the relevant head boundaries and searches the new fused source word.

Build with a C++17 compiler, for example:

  g++ -std=c++17 -O3 screen.cpp -o screen
  g++ -std=c++17 -O3 search_permutations.cpp -o joint_search
  g++ -std=c++17 -O3 search_fused.cpp -o fused_search

Run each complete prepared permutation grid (deterministic case count):

  ./screen H5XS.tagged.templates.txt Hgrid_new 31 46656 compatible
  ./screen JH5XS.tagged.templates.txt Jgrid_new 31 46656 compatible
  ./screen FH.tagged.templates.txt FHgrid_new 31 46656 compatible

The presence of the final compatible argument enables simultaneous-fold
replay. Each grid covers six independent choices from the six permutations
of three parameters on each of 31 retained shapes, hence 31*46656 cases.
Prepared template inputs include all fixed controller rows, tagged leaves,
shape DAGs and roots needed by the executable.

Recorded stochastic runs used the following seeds and time budgets:

  ./joint_search PA194H5XS.templates.txt leaf_attrs.txt Hperm_new 420 15112201
  ./joint_search PA194JH5XS.templates.txt leaf_attrs.txt Jperm_new 420 15112202
  ./fused_search FH5XS.templates.txt leaf_attrs.txt FH_new 420 15112211

Their exact iteration count depends on wall-clock timing and hardware;
the supplied logs record the actual runs. Reassociation mutates tree shape,
not the token order. Per-head moves permute only the unrestricted ordinary
schema parameters; guarded/dominated blocks are outside the mutation spans.
For the fused grid, the h4 and equality-witness constituent spans are
independently permuted; each projection separately remains surjective onto
its old schema. The primary selected machine uses identity permutations.

The source template convention has 134 fixed states after its already proved
controller fold. Thus effective reader cost 60 corresponds to 194 working
states, and a cost 59 hit would require fresh source/formula and literal
runtime verification before acceptance. No such hit was found in these runs.

selected.grammar.json is the frozen chosen fused grammar. Machine rebuilding
uses that frozen grammar and explicit fold list under ../../construction/;
it does not depend on the search being repeated or on its time budget.
