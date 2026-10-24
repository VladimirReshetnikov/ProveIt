# Independent audit: commutative certificates and shared local polynomials

## Verdict and scope

The new architecture is mathematically sound. It is a substantial change of proof source: an unordered multiplicative obligation accumulator replaces the chronological stack. This is **not yet a new completed small ordinary Con(ZFC) equation**. The global Lean constructor is an uncompiled proposal, and its final polynomial and witness count are unmaterialized. The completed small objects in this component are local relations only.

This review reads source/data without executing upstream programs or importing the submitted generators. `check.py` is a separately authored sparse-polynomial checker. Its finite fixtures supplement, and do not replace, the arguments below. No Lean/Rocq kernel compilation is claimed.

## 1. Nonnegative one-conclusion flow

A finite multiset of rules has balances equal to the target unit vector precisely when it can certify derivability, provided every rule has exactly one conclusion and nonnegative multiplicity. The stronger soundness hypothesis of coordinatewise domination works as well.

To prove soundness, saturate the finite set of rules actually used, including the freely derivable truth label when it is present. If the target is not in this closure, assign weight one to each nonderived label and zero to each derived label. A rule whose conclusion has weight one has at least one weight-one premise; therefore its conclusion-minus-premise balance has weight at most zero. The same is immediate for a weight-zero conclusion. Every nonnegative combination has weight at most zero, contradicting a positive target balance. All sums have finite support, so this does not require a finite universe of all formula codes or any semantic model assumption.

Completeness follows by unrolling a finite proof to a tree and counting occurrences. Internal premise/conclusion contributions cancel. Cycles in an arbitrary certificate cause no difficulty. Multiple conclusions or negative rule counts do invalidate the proof and must not be admitted.

For C222, code zero is freely derivable. Padding axioms to premises (0,0), and generalization to one real premise and zero, preserves the theorem only after quotienting out the zero coordinate. The proposed product encoding does exactly this, since its weight at zero is one. It does not silently require an impossible full balance including padded zero leaves.

## 2. Affine coprime factors and integer accumulator

Let m>=1 and let M>=1 be divisible by each integer 1,...,m. For 0<i<j<=m, a divisor of both 1+iM and 1+jM is coprime to M and divides (j-i)M. Hence it divides j-i, which divides M, so it is one. The positive-label factors are greater than one and pairwise coprime. Each has a prime divisor unique to that label; its valuation proves that equality of finite products is exactly equality of positive-label multiplicities. Primality of the factors themselves is neither asserted nor needed.

The update

    S_next (1+cM) = S (1+pM)(1+qM)

with S_initial=1+M and S_final=1 is sound over nonnegative integers. All factors are strictly positive, so the initial positive S inductively forces every S_next positive. Multiplying the updates and cancelling internal S values gives precisely the required product balance. Completeness is not inferred by arbitrarily reordering a flow certificate, which could produce fractions. Instead take a proof tree, expand one open obligation at a time, and let S be the product of the factors of all open obligations. Every update then has integer witnesses. Zero-labelled obligations contribute one and may be left unexpanded.

## 3. Shared scratch and elimination

For finitely many branch polynomials B_j that are sums of squares, their product vanishes iff one B_j vanishes. Thus existential scratch coordinates may be reused across all branches: choose the scratch values for the successful branch and fill its unused coordinates arbitrarily. Unselected branches impose no constraints. This reasoning uses a fixed product of twelve explicitly supplied polynomials, not a variable-length product.

Each eliminated constructor wire denotes a polynomial that is nonnegative on natural inputs. Substituting its definition and deleting its defining residual therefore preserves existential solvability over naturals in both directions. Independence of the eliminated set guarantees that no substituted definition refers to another eliminated wire, keeping residual degree at most four; soundness itself can also be proved by ordered substitution without that degree advantage. Surviving definitions remain triangular nonnegative constructor compositions. This is important: arbitrary elimination of natural witnesses with possibly negative reconstructed values would not be valid.

The bundle guard

    ((c-a)(c-b))^2 = (d+1)^2

has a natural d iff c differs from both a and b. The reverse direction chooses d=abs((c-a)(c-b))-1, which is natural because the product is nonzero. The guard is degree four; after squaring it contributes degree eight to the bundle factor.

The inspected constructor expressions `Req`, `Clos`, `Bundle`, the eight unconditional schemas, and MP/generalization match the pinned `Code254.lean` and `KCode222.lean` numeric definitions. The source uses growG, not the replaced rho7. The bundle's inequalities are retained. The finite local checker also verifies every expanded SOS exactly and every surviving defining residual against its listed positive triangular wire value.

### Counts that must remain local

- Stack: 17 existential natural witnesses plus two exposed states; degree 52.
- Padded Horn: 17 existential natural witnesses plus three exposed labels; degree 50.
- Affine accumulator: 23 existential natural witnesses plus four exposed parameters; degree 50.

The last count is 17 scratch/base witnesses, three formula labels, and three bound slacks. Its extra update square has degree ten, below the Horn factor product's degree fifty. The product has degree fifty because each factor is a nonzero polynomial and degrees add in the integral polynomial ring; there is no higher-degree extra term to cancel it.

## 4. Proposed global constructor

The five outer naturals are t,x,y,m,M0, with M=M0+1. The first bounded universal block ranges i<t and checks the local relation between beta(i) and beta(i+1), holding m and M0 fixed. The second ranges j<m and asserts M0+1=(j+1)k for a natural local k. This is exactly divisibility by 1,...,m, with no missing endpoint or unintended requirement to divide by zero.

The endpoint constraints require beta(0)=M0+2 and beta(t)=1. If t=0 these are inconsistent. If m=0, all three bounded labels are zero, so every local update forces S_next=S; the endpoints again contradict. Thus an explicit m>=1 conjunct is unnecessary. In soundness, deduce m>=1 before applying the coprimality lemma.

For completeness choose a finite proof tree, m large enough to contain all its labels and target 1, M=m!, and the finite integer accumulator sequence above. The finite beta/CRT encoding supplies x,y. The separate divisibility block supplies M/(j+1). The arithmetic common multiple M, the beta scale y, and the representation compiler's internal majorization/CRT scales are distinct witnesses. Their sequential choice introduces no circular bound.

The generated local Lean expression is independently read back to its sparse polynomial data by the checker. Static inspection confirms `Rep.existsBlock`, `Rep.compose`, `Rep.boundedForall`, `Rep.conjunction`, and `Rep.reindex` usage against the pinned APIs, two bounded blocks with the intended bounds, and closure of five outer variables. This is not elaboration or a correctness theorem connecting the generated expression to C222. Completing that bridge, kernel-checking the constructor, and materializing/counting the resulting polynomial remain obligations.

## 5. Findings and reproducibility

The initial audit found a stale description in the direct component's copied Horn JSON: it said one-stack transition although its exact polynomial was Horn. Refreshing the copy resolves this metadata-only discrepancy; the checker requires byte identity with the final alternative source. No mathematical counterexample was found.

Run `python check.py` from this directory or by its full path. The program uses explicit exceptions, so `python -O check.py` performs the same checks. `CHECKS.json` records exact input hashes, finite fixture counts, SOS expansion checks, and local Lean-literal round trips. The review does not advertise global minimality, a measured compiler improvement, or an already completed K215/Jones-independent small consistency equation.

The twelve inert inherited files and their original manifest are bundled under `inherited/`. Their hashes are verified. This is not the full transitive Lean import closure: the C222/ZF and ZF/ZFC equivalences are inherited from the pinned repository and not re-proved by this packet.
