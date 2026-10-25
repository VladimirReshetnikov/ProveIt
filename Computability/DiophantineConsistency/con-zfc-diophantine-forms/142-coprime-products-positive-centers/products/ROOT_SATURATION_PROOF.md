# Why the degree-189 equation is sound

The full definitions and proof are in PROOF.md, Sections 1, 2, 4 and 5.
This note isolates the subtle order of reasoning.

The raw polynomial uses W=Delta*A*(i*c^2)^2 and Q=Delta*W. Before a zero
is analyzed, neither A nor Q is known to be a square. Therefore it would
be invalid to exclude the negative unit of f^2-W by calling W a Pell
radicand times a square at the outset.

Instead the factor 3*Eprod+1 is forced to +1 by its residue modulo 3,
and the main norm is forced to +1 modulo 4. Then Q>1 and A|Q prove that
A is coprime to both Q-1 and Q*V^2-1. The product equation forces A to
be a square by prime valuations. Now, and only now, f^2-W becomes a Pell
norm f^2-Delta*(tau*i*c^2)^2 and cannot be -1 modulo 4. This establishes
the remaining unit sign without circularity.

The completed circuit has 70 operations and degree 189. It supersedes the
intermediate 70-operation degree-233 circuit, which put A^2 into W and
paid for that unnecessary extra degree. The source completion permits the
weaker condition tau|i_old by the same finite Pell-period argument.
