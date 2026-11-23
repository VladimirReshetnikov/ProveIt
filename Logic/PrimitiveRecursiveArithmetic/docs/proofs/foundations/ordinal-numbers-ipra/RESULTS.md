# Result index

The finite results use coded finite sets and relations. Unless a row names the epsilon extension, infinite ordinal variables denote hereditary Cantor normal forms below epsilon-zero. The paper proves the stated arithmetic versions. The last column identifies additional Lean kernel checks or executable checks where supplied.

| Topic | Results proved in the paper | Companion coverage |
|---|---|---|
| Order comparison | Decidable validity and trichotomy, equality reflection, transitivity, canonical multiplicities, witnessed extrema for finite lists | `OrdinalCore.lean` proves the comparison laws |
| Finite well-orders | Least points, predecessor ranks, unique order type, canonical initial segments, rigidity, optimal descent length, finite induction and recursion | `Finite.lean` proves the rank/unrank isomorphism on arbitrary finite Boolean linear orders |
| Hereditarily finite sets | Exact members of each von Neumann ordinal, inclusion versus order, intrinsic recognition, finite union and intersection, unique Mostowski collapse of an acyclic extensional finite relation | `Finite.lean` proves the membership, inclusion and recognition theorems |
| Successor and limit | Least successor, unique finite remainder, first infinite term, predecessor and supremum characterizations of a positive limit | `Limits.lean` proves the immediate-successor theorem and checks the last-exponent classifier |
| Cofinal sequences | Increasing canonical fundamental sequences, node-count bound, exact least-index recursion, sharp maximum-coefficient bound, cofinality 0/1/omega and idempotence | `Limits.lean` proves increasing cofinality and the node-count bound. `Threshold.lean` proves exactness of the first-index search. `check.py` tests the sharper recursion |
| Order topology | Isolated points, discreteness criterion for initial segments, neighborhoods and witnessed finite subcovers at omega, derivative stages and ranks read from the last exponent | Human proofs |
| Fixed-dimensional descent | For each fixed positive d and fixed PR control, a PR upper bound on descending lengths below omega to the d, with a computed index of failure | Human proof |
| Addition and multiplication | Associativity, one-sided distributivity, cancellation, monotonicity, left subtraction, absorption, principal exponents, and counterexamples to the other-sided laws | `Power.lean` checks addition associativity. `arithmetic.py` exercises both operations |
| Exponentiation | General PR power, both power laws, monotonicity, witnessed right continuity, and the least fixed point of the article's spiral map | `Power.lean` defines power, proves the finite-exponent equations and checks transfinite examples |
| Primes | Classification into finite, infinite successor and limit primes. Existence, computation and uniqueness of an ordered prime factorization | `arithmetic.py` computes prime factors |
| Division | General left Euclidean division, unique remainder, explicit block isomorphisms for ordered sums and products | `Power.lean` proves both inverse laws for division by omega. `check.py` checks general division |
| Powers as order types | For any represented base and exponent, finite-support functions ordered by the greatest differing position give the initial segment of the ordinal power. Both maps are PR | `digits.py` implements and tests both directions |
| Ordinals and cardinals | All represented infinite initial segments are uniformly PR-bijective with the naturals. Omega and its successor have different order types | Human proofs with explicit maps |
| Hessenberg arithmetic | Commutative semiring laws, strict monotonicity, comparison with ordinary arithmetic, closure of principal segments, discontinuity and finite-polynomial representation | `check.py` checks operations and inequalities |
| Nimber arithmetic | Unique finite mex addition, exclusive-or formula and addition laws | `check.py` verifies the finite mex equations on a rectangle |
| Epsilon numbers | Exact tower-height levels below epsilon-zero. In an extended notation for the order below epsilon-omega, the fixed points are exactly the markers, each with a depth-bounded cofinal sequence | `Limits.lean` proves the height levels of the original system. `epsilon.py` checks the extended system |
| Cuts and normal functions | Initial-cut inclusion, successor, union and intersection. Least fixed point given a cofinal orbit with a named limit. Two disjoint closed cofinal tower ranges | Human proofs |
| Hereditary bases | Order isomorphism of base-admissible terms with the naturals, invariance under base change, and strict descent for each positive Goodstein step | `check.py` checks base-change steps |
| Limits of uniform computation | A least-member schema on omega plus one entails the PR-predicate instance of LPO. A computable supremum of all increasing two-valued programs or a normalizer of arbitrary promised presentations would decide halting | Human proofs. The final two consequences are computability arguments in the metatheory |

The theorem on universal Goodstein termination is cited as an external independence result. The paper gives a route to object-language derivations in ProveIt for the internal assertions. The Lean files here prove theorems in Lean about the definitions they contain.
