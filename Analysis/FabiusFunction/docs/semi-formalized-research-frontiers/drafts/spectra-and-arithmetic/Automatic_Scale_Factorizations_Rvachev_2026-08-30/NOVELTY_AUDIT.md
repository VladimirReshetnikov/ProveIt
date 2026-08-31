# Novelty audit

The source comparison used the current GitHub tree for
`VladimirReshetnikov/ProveIt`, recursively under
`Analysis/FabiusFunction/docs`, together with the repository's generated
`MANIFEST.md`, corpus inventories, audit files, and theorem/open-problem summaries.
The active consolidated volumes and the closest-overlap full sources were searched
for the following concepts and formula patterns:

- scale partition, scale thinning, selected dyadic scales;
- Thue--Morse selector and positive-definite sinc subproducts;
- complementary convolution factors of the Rvachev law;
- support radii involving `prod_j (1-q^(2^j))`;
- q-Mahler recursions coupling two characteristic factors;
- exact plateaux of complementary factors;
- selector-density Fourier and endpoint exponents;
- equal convolution roots and zero-multiplicity obstructions.

Closest occupied topics included:

1. periodic polyphase convolution factorizations obtained by residue classes of the scale index;
2. cyclotomic q-Fabius/Rvachev natural boundaries and root-of-unity blow-ups;
3. reciprocal-integer convolution divisors `Phi(z)/Phi(z/M)`;
4. Fourier decay of the original up-function;
5. endpoint and inverse-Fabius Lambert-W asymptotics;
6. Thue--Morse products, block factorizations, and natural-boundary formalization;
7. Bell--Bernoulli cumulants, Legendre/Lagrange representations, sampling, and
   dyadic-comb asymptotics.

The report therefore does **not** claim those subjects as new.  Its principal new
object relative to the audited corpus is the pair of probability laws obtained by
partitioning the individual dyadic uniform summands according to the two signs of
the Thue--Morse sequence.  The natural-boundary discussion is explicitly presented
as a consequence/synthesis of an already occupied theorem applied to the new Mellin
transform, not as a new natural-boundary theorem.

“New” in the report means “not found in the audited repository corpus.”  It is not a
claim of worldwide priority, and the arguments have not been peer-reviewed or
formally checked in Lean.
