# Blank-calibrated source invariant

The delivered source has nine natural-number registers. CI r increments register r;
CD r takes its zero branch unchanged when r=0, otherwise decrements r and takes
its positive branch. CB/CC affect only control; CH halts. Exact machine startup
is an inherited, separately checked obligation: source ordinal136 with registers
(1,0,13,0,0,1,0,0,1). The invariant here starts at that source entry.

Each mask represents a union of four disjoint categories: {0}, {1}, {2}, {n:n>=3}.
A row of nine masks represents their Cartesian product; None is the empty set.
The generator joins masks monotonically, so its finite product lattice iteration
terminates. Correctness does not rely on trusting that generator or on leastness:
the independent checker tests seed inclusion and every feasible abstract successor
against the supplied invariant. It resolves source control through binary-prefix
increment/strip arithmetic, rather than the generator's subtree intervals.

Increment images are 0->1,1->2,2->>=3,>=3->>=3. Zero decrements preserve0;
positive decrements map1->0,2->1,>=3->{2,>=3}. Representatives3 and4 suffice for
the last category's two abstract decrement images; all n>=4 have the same image
category as4. Other register components are unchanged. Thus each checked abstract
transfer soundly contains all concrete one-step successors. Induction on source
steps gives membership in the invariant throughout the calibrated run. The finite
certificate has3906 admitted sites and5078 checked successor inclusions.

Sites3848(CI6),3849(CC2),3892(CC2) have empty invariant. At3847(CD1) and3891(CD6),
the tested register is always0. These facts justify eliminating positive branches
only along the calibrated source run, not universally from arbitrary source stores.
The checker also checks the Joint/classA source has the same ordered instructions
and complete ordinal graph as the Compatibility source; the same invariant applies.

This is ordinary finite arithmetic plus induction, formalizable in PA. It is not a
new proof-assistant certificate, and not a claim that every abstract valuation is
actually reachable. Any physical decoder optimization still needs an exact source
simulation (including ordinal mapping), canonical runtime and blank initialization
proof; these source guards alone are not a smaller Turing machine.
