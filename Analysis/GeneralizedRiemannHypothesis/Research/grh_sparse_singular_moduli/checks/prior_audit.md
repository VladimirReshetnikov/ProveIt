# Earlier work and replay of its CM certificates

The GitHub Contents API for ProveIt at commit c59bde1a0f52eee7a7a8dc6b326072f9b71f76a6 lists eight ZIPs in docs/incoming. We inspected manuscripts from all eight, as well as the exponent-six supplement and the later companion material described below.

| Archive | Topics relevant to avoiding overlap |
|---|---|
| grh_cm_prime_applications.zip | Riffaut's trinomial problem via Bilu–Luca–Pizarro-Madariaga, sparse equations for singular moduli including all degrees at least six and 79 outstanding quartic/quintic discriminants, sparse-twist Landau tests, Mills constants and additive prime powers |
| grh-arithmetic-transfers.zip | Norms and primes in geometric progressions, isogenies over sextic fields, splitting tests for alternating-group subset fields, congruence rigidity |
| grh-lean-transfers.zip | Classification of CM modular coefficient fields, genus fields, quintic classification, prime races, cubic targets, norm-Euclidean fields and primitive roots |
| grh-transfer.zip | Abelian classification question of Zhao, Euclidean fields, three-squares representations, completely split prime tests |
| grh_transfers.zip | Partial exponent-six class-group census, modulo-four weighted prime race, Artin RH for the cubic of discriminant −23 reduced to a sign |
| grh_lean_transfer_analysis.zip | Degree-two Artin transfer, analytic and geometric transfer lemmas, basic conditional consequences and next research questions |
| grh_transfer_analysis_2026-11-25.zip | Landau transfer and sparse auxiliary-prime families, barriers for K-theory and Vandiver, concrete cubic goal |
| grh-exponent-six-and-transfers.zip (staged supplement) | Complete exponent-six census, prime-gap graphs, reflected quintic fields and a joint prime-splitting test for six zeta functions |
| grh_transfer_analysis.zip | Determinant comparison, one-sided criterion, abelian Dedekind RH, least nonresidues, and the cubic target of discriminant −23. All 25 members passed the ZIP integrity test. The manuscript contains no classification of sparse equations for singular moduli. |

The eighth indexed archive has 11,517,846 bytes, Git blob 68caedfbe84e88899ec097e2e1a7b92ae7657bd5, and SHA-256 a0a9c7ab278c5273e041db15cd6ba003832c096ae88f19fd1619a3503d901d85. The incoming CM archive has Git blob 746436c106c9250299668d88e5ef508b8d11afd9.

## Replay of the four-term exclusion outside the 79 cases

We extracted grh_cm_prime_applications.zip and ran its SHA-256 manifest, its GCC/C++17 finite sieves, and the two Python certificates using unmodified source. All comparisons below passed. Timings are wall-clock times from this environment.

| Check | Result | Time |
|---|---|---|
| checks/run_cm_small.sh | All 5,000,000 admissible positive D through 10^7 checked. First pass excluded 4,999,603, 67 had class number <4, and 330 proceeded to interval arithmetic. 228 separation and 22 determinant certificates left exactly 80. The list matched checks/cm_small_unresolved.txt byte for byte. | 1.41 s including compilation |
| checks/cm_range.cpp (g++ -O3 -std=c++17) | The replay's stdout matched checks/cm_range.out byte for byte, covering 49,995,000,000 discriminants in [10^7,10^11), with zero residuals. Its CRT residue-class counts include 12,498,750,000 split-at-two certifications, 37,449,133,804 odd split-prime power certifications, and 47,116,196 individually checked split-prime triples. | 14.64 s excluding compilation |
| checks/verify_4075.py | Two large-gap bounds and 121 small-gap complex minor bounds passed. This removes the single h=6 case among the 80. Transcript matched checks/4075.out. | 0.052 s |
| verify_four_term.py | All three large-D endpoint margins passed (68, 191, 751), as did both factor-16 archimedean separation bounds. Transcript matched checks/four_term.out. | 0.038 s |

The finite middle range is a count of arithmetic progressions and candidate-by-candidate checks of the survivors. The quadratic form construction uses a root of −D modulo an odd split prime q, Hensel lifting, and a parity choice to obtain leading coefficients 1,q,q²,q³ whenever 4q⁶≤D. The congruence D≡7 mod 8 supplies the dyadic analogue. Certified classes are counted once within each disjoint dyadic bin. When direct primes are used, the integer separation inequalities are tested on each successive coefficient. The checker balances its counts against the exact number of admissible residues in each bin.

For the analytic tail the prior argument applies Grenié and Molteni's Corollary 1.2 in a quadratic field. Its Dedekind zeta is a product of the Riemann zeta function and a quadratic Dirichlet L-function. For each requested interval, split rational primes larger than the square root of its far endpoint contribute two degree-one prime ideals each. Removing small-prime powers costs at most 2 sqrt(y) log y. Removing the other ramified primes and primes of the order conductor costs at most log D, because D is the fundamental-discriminant magnitude times the conductor squared. The quoted error terms divided by sqrt(D) decrease on the stated range by logarithmic differentiation. Thus the rational margin checks at D=10^11 propagate to all larger D. The analytic estimate and CM facts are cited mathematical inputs. The new calculation begins at the explicit list of 79 cases. No Lean checking of the incoming manuscripts was performed.

## Additional companion report

The separately available `grh_cm_four_terms_and_prime_bias.zip` (SHA-256 `47817f2addaa089194065bc676a6499331e057656d1f9d79264fa70a5ffb7308`) also establishes the four-term result. Its quintic computation excludes five-term multiples for discriminant -131 through degree 1000, and leaves general exponents open. Its growth theorem gives a square-root class-number bound under Dirichlet GRH and a discriminant exponent 1/4 minus epsilon independently. The present report answers the global five-term question, including -131 in every polynomial degree, and gives a larger growth exponent. The density result and infinite exact family are additional results. The older scope description above refers to the pinned GitHub snapshot, not to this companion. The later GitHub snapshot c477d08ef7be4241e94bd1cffb43ff56240321e3 contains the exponent-six archive, and the same input CM archive under the same Git blob.

A further supplied report, `grh_beyond_dirichlet_grh_2026-11-25.zip`, treats simultaneous nonvanishing, Galois cohomology, and bounded analytic families. Its research questions are distinct from the five-term classification. The four-term companion also gives a one-prime unconditional proof of Riffaut’s trinomial conjecture, which is prior work for the present report.

## Parallel report on the same support problem

The parallel package `grh_cm_sparse_equations.zip` (SHA-256 `8f51ed8a76140c0c2ead4824b7e754267c090d7080bdcaa5063fb668e31779bd`) reduces the unrestricted five-term problem to −87, −131, −348, −432 and −675, and excludes all five through exponent width 65,536. We inspected its manuscript, finite cutoffs and extremal-family section. It independently obtains the near-degree uniform bound, the unconditional Pollack exponent, and the density-9/13 near-maximality condition. Its explicit exact family has discriminants four times ours in absolute value for the same parameter. Its five outstanding cases are eliminated for unbounded exponents by our confluent rank certificates. The density calculation among Gaussian prime conductors is an additional result here.
