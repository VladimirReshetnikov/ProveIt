# Binary finite-prism Diophantine certificates for the literal U15 loader

Research design and executable coefficient compiler, 3 October 2026. This is a composition and specialization of existing support-burning certificates, not a new sandpile universality theorem or an unbounded fixed-arity representation theorem.

## 1. Precise theorem and scope

Let P be a nonempty finite integer rectangular prism in Z³. Every lattice site has the ordinary six-neighbor threshold 6. Let η be a natural-valued configuration that is stable outside P, specified by a stable periodic background and finite nonnegative additions all contained in P. The executable general interface accepts precisely such additions; the mathematical argument also permits any finite modifications whose resulting heights are natural and whose entire support lies in P.

There is an explicitly generated integer polynomial F_(η,P), in natural witness coordinates, with the following properties:

1. F is nonnegative throughout the nonnegative real orthant and has degree exactly 3
2. F has a natural zero if and only if a finite legal GLOBAL stabilization exists, its odometer is supported in P, and every odometer entry is 0 or 1
3. When it exists, that entire natural zero is unique
4. If V=|P|, E is its number of internal undirected edges and H is its exterior nearest-neighbor halo size, the polynomial has exactly 8V+6E+H witness coordinates and 8V+7E+H displayed nonnegative summands

Inputs, prism endpoints and side lengths are EXTERNAL compiler parameters. A different prism gives a different polynomial of generally different arity. Uniqueness here is at each fixed prism: enlarging a successful prism gives a new uniquely padded witness. No unique index across all prisms is claimed, no ranks are uncounted, and no fixed-arity Diophantine or finite-fold MRDP claim follows.

The degree is exactly 3 even for a singleton: for example the success term contains k_v z_v² with positive coefficient that is not cancelled. The semantic theorem concerns NATURAL zeros, not real zeros. For a singleton with η=1 and zero exterior, the real tuple z=0, ell=5, f=5/6, k=1/6, c=beta=g=h=0 and all six halo gaps29/6 is a spurious nonnegative-real zero, although the actual odometer is zero. Orthant nonnegativity does not establish integral soundness.

## 2. Existing results being reused

Pinned public repository: VladimirReshetnikov/ProveIt, commit
83befe707f2840c2b53e0606701d8a2b28598e47.
Directory: SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/.

- README.md: manuscript16 is the support-burning/compact cubic result; manuscript19 reproves the support theorem and gives quadratic residuals, a quartic and the47-field finite-deviation normal form on Z³
- code/16-sandpile-sandpile_compact.py, Git blob37bfc3a35cf08a219ba071adff656cfe9932183f: ten vertex coordinates, six per undirected edge,10V+7E summands, five-way rank comparisons
- code/16-sandpile-sandpile_spatial.py, blob91bfaba37eea1bb3571baeb8254feecc05b8069e: no-firing exterior collar and optional canonical cube radius
- code/19-no-borrowed-firings-sandpile_certificates.py, blob962d790489b1b96ec23f37e45095786e4e69381b:11V+12E witness/12V+16E quadratic-residual compiler and47 local fields; those fields are not47 natural scalar variables encoding arbitrary unbounded activity

These were targeted public text reads only. No clone, upstream build, upstream script execution or public modification occurred. The report is a research manuscript, not a Lean-verified result. Its constructor defects disclosed in the README concern mutable data and unchecked external defects; the new general input class snapshots tuples and explicitly checks that ALL additions lie in P.

What is new here: the literal binary specialization, rectangular rather than cube-only indexing, exact coefficient stream and collection algorithm, complete ledger, and composition with the separately audited literal finite-tape U15 loader. The underlying least-action, support-burning, canonical-rank and halo theorems are existing mathematics, not claimed as new.

## 3. Geometry, indexing and the halo

Write P=[l1,l1+a−1]×[l2,l2+b−1]×[l3,l3+c−1], a,b,c>=1. Then

V=abc; S=ab+ac+bc; E=3V−S; H=2S.

H consists of the six EXTERIOR faces, with the other two coordinates inside their respective intervals. It has no diagonal edge/corner points. Each halo point has exactly ONE neighbor in P, including when some side length is1. The graph sends each missing lattice edge to a sink but retains threshold6. It is finite, undirected, loopless and every component reaches the sink, so the existing finite-graph theorem applies.

Vertices use lexicographic x,y,z indexing. Edges are grouped by positive axis, then lexicographic lower endpoint. Halo sites are grouped by axis, negative/positive face, then lexicographic two remaining coordinates. The code implements direct index/inverse-index formulas; explicit nested range loops stream coordinates without eager Cartesian-product pools. No graph adjacency table is materialized by the coefficient generator.

Witness counts simplify to W=26V−4S=26V−2H. Summands simplify to J=29V−5S. A1×1×1 prism has W=J=14. Empty activity is allowed, but an empty prism is not an input to this interface.

## 4. Literal polynomial

At each v use eight natural coordinates

(z_v,ell_v,f_v,k_v,c_v,beta_v,g_v,h_v).

Define u_v=k_v+c_v and r_v=k_v+2c_v+beta_v. There is no separately quantified u or rank coordinate.

For every internal edge oriented v<w, use six natural variables

(lambda_minus,lambda_neg,lambda_zero,lambda_pos,lambda_plus,sigma).

For δ=r_w−r_v its contribution is

Ψ=(lambda_minus+lambda_neg+lambda_zero+lambda_pos+lambda_plus−1)²
 +lambda_minus(δ+2+sigma)²
 +lambda_neg(δ+1)²
 +lambda_zero δ²
 +lambda_pos(δ−1)²
 +lambda_plus(δ−2−sigma)²
 +(lambda_neg+lambda_zero+lambda_pos)sigma.

Exactly one selector is1 at a natural zero. Its five cases are δ<=−2, δ=−1, δ=0, δ=1, δ>=2. The gap is max(|δ|−2,0); in each middle case the final product forces it to0. These are unique integer comparison data.

The comparisons for the lower endpoint v are

1[r_w>=r_v]=lambda_zero+lambda_pos+lambda_plus,
1[r_w+1>=r_v]=lambda_neg+lambda_zero+lambda_pos+lambda_plus.

For the upper endpoint w they are respectively

lambda_minus+lambda_neg+lambda_zero,
lambda_minus+lambda_neg+lambda_zero+lambda_pos.

Sum these over incident edges to obtain A_v and B_v. They are affine-linear selector expressions. The eight vertex summands are

(z_v+6u_v−sum_(w∼v in P)u_w−η(v))²,
(z_v+ell_v−5)²,
(f_v+k_v+c_v−1)²,
(f_v+k_v)beta_v,
(k_v+c_v)(z_v−A_v−g_v)²,
f_v g_v,
c_v(B_v−z_v−1−h_v)²,
(f_v+k_v)h_v.

For each halo site x use one natural gap q_x and add

(η(x)+u_neighbor(x)+q_x−5)².

F is the sum of these expressions, with every affine substitution performed by the generator. Every summand is a square, a nonnegative-linear weight times a square, or a product of nonnegative-linear expressions. Hence F is orthant-nonnegative and has degree at most3. All coefficients are integers and all variables are accounted for.

The specialization from manuscript16 is exactly u=k+c, alpha=0. It removes two vertex variables and the two identically zero summands (u−k−c−alpha)² and f*alpha. At any original compact natural zero with binary u, these substitutions are forced. This proves an explicit bijection between its binary-odometer zero subset and the new zero set.

## 5. Proof of soundness, completeness and uniqueness

The finite sink process terminates. For example the reduced Laplacian is positive definite and has a positive inverse applied to the all-ones vector; the corresponding weighted chip potential decreases by1 at each legal toppling and is bounded below. Standard least action says that any stable nonnegative candidate u bounds every legal firing prefix. In particular its actual sink odometer u* obeys u*<=u.

At a natural zero, f,k,c form a one-hot triple. Thus u is binary; r=0 iff u=0, r=1 in category k, and r>=2 in category c. Inactive beta,g,h are forced to0. Balance gives the candidate endpoint z=η−Lu; stability gives0<=z<=5.

The comparison gadget is exact. For u_v=1 the success term enforces z_v>=A_v, and for r_v>=2 the preceding-round term enforces z_v<B_v. These are the canonical parallel support-burning conditions. For any nonempty X⊂supp(u), choose a member of minimum rank. It satisfies z_v>=A_v>=deg_X(v), so X is not a forbidden set. Thus the support burns.

For this BINARY specialization there is also a direct legality proof, without needing the stronger general support-burning characterization. Fire all u=1 sites in increasing rank, using any order within a tied layer. Immediately before v fires, balance says its current height is z_v+6 minus the number of its support neighbors not yet fired. Such neighbors have rank at least r_v, and their count is at most A_v (some same-rank neighbors may already have fired). Success gives z_v>=A_v, so the current height is at least6. Every proposed firing is legal. After these finitely many firings the interior endpoint is z and stable. Least action gives uniqueness of this legal sink odometer, and the halo argument below proves global stability. Tied-layer ordering is an argument for existence, not a witness coordinate. Previous-round failure, separately, forces the unique parallel rank vector.

For comparison, the inherited general support-burning proof also identifies the exact odometer: suppose w=u−u* is nonzero. Let m=max w>=1 and X={v:w_v=m}. Symmetry, sink dissipation and integrality give (Lw)_v>=6−deg_X(v). As z*=z+Lw is stable, z_v<=deg_X(v)−1 for every v∈X, contradicting burnability. Thus u=u*.

The local ranks are uniquely the EARLIEST parallel burning rounds. Induct on round j: rank-j vertices are eligible by success. Any vertex of rank r>j is ineligible because z_v<B_v=deg_{r_neighbor>=r−1}(v)<=deg_{r_neighbor>=j}(v). Exactly the assigned layer burns. This forces every rank, permits simultaneous equal ranks, excludes arbitrary delays or arbitrary sequential orderings, and proves r_v<=|supp(u)|<=V.

The halo terms prove GLOBAL closure. Execute the finite legal sink stabilization in the infinite lattice while not firing exterior sites. Inside P it is exactly the same evolution. Exterior heights only increase, their final halo values are<=5, and outside the halo nothing changes from the initially stable configuration. The result is globally stable after finitely many total topplings. No exterior initial defect is allowed: all additions were checked inside P.

Conversely a finite legal global stabilization whose support is in P is a legal sink stabilization there. If its odometer is binary, take its unique endpoint and parallel support-burning ranks, set the categories accordingly, beta=max(r−2,0), g=z−A on active sites and0 otherwise, h=B−z−1 for r>=2 and0 otherwise, the unique edge comparison data and q_x=5−η(x)−u_neighbor. All coordinates are natural and all summands vanish.

Finally u,z,r are unique, the category bits and beta follow from r, ell follows from z, active gaps follow from their residuals, inactive gaps are forced to0, and all edge/halo coordinates are forced. The complete witness is unique, including when u=0 everywhere. The necessity direction for support burning is the usual earliest-last-toppling argument: in any nonempty X in the true support, the vertex whose final toppling is earliest receives at least deg_X(v) chips after that last toppling, so X cannot be forbidden.

Counterchecks: on two neighboring sites at initial heights(5,5), proposed u=(1,1) gives z=(0,0) and even a stable zero-background halo, but fails burning. A singleton initially6 in background5 has a sink stabilization but fails the exterior halo. A singleton initially12 in background0 globally stabilizes but needs u=2, so is intentionally outside the binary specialization.

## 6. Exact residual, monomial and arithmetic ledger

There are exactly:

- W=8V+6E+H natural witness coordinates
- J=8V+7E+H nonnegative summands
-3V+E+H unweighted affine-square residual occurrences
-2V+5E weighted affine-square residual occurrences
-3V+E product summands

A weighted square is not being relabelled as a plain quadratic residual. This is a single CUBIC polynomial, not manuscript19's quadratic residual system.

Let d_v be internal degree, I_v=1[η(v)!=0], and I_x=1[η(x)<5] on the initially stable halo. Put T(q)=q(q+1)/2. Define raw monomials to be the distinct nonzero monomials of EACH displayed summand after its internal expansion, counted again if the same monomial appears in another summand. The exact raw record count is

R=Σ_v {T(3+2d_v+I_v)+21+2T(2+3d_v)+T(4d_v+3)}
 +173E+Σ_x T(3+I_x).

Each edge contributes exactly173; each halo point contributes6 or10. There is no intra-summand collision hidden in this count. Inter-summand collisions and cancellations are real: for a singleton η=6, background0, R=103 but the collected polynomial has55 monomials. For two sites η=(6,5), zero exterior, the counts are473 raw and345 collected.

The degree histogram is given without enumerating P by the product of three polynomials: for a side of length1 use1; for lengtha>=2 use2X+(a−2)X². If N_d is the coefficient and A_d counts nonzero-height vertices of degree d, the same exact R is

Σ_d N_d{T(3+2d)+21+2T(2+3d)+T(4d+3)}
 +Σ_d A_d(4+2d)+173E+6H+4L,

where L=Σ_x I_x. Only the explicitly defined data-dependent tallies A_d,L require coefficient-height evaluation. We do NOT replace them with invented numeric counts for the giant universal prism.

Arithmetic ledger: count a multiplication for coefficient-times-variable in an affine form, add its nonzero terms by initializing with its first term, square once, evaluate a nontrivial weight in the same way, and multiply weight and square once. Evaluate product summands analogously and sum the J summands with J−1 additions. This is a specified straight-line implementation, NOT a count of CPython's internal operations, allocation, iteration or multiplication by literal1 in its convenience evaluator.

Let A=Σ_v I_v. Exact evaluation costs are

multiplications =33V+76E+4H,
additions =21V+63E+3H+A+L−1.

For coefficient expansion, compute c_i*c_j for i<=j, double off-diagonals, and reuse those coefficients for every unit-weight term. Product-summand coefficient products are counted. Exact coefficient arithmetic multiplications are

X=Σ_v {(3+2d_v+I_v)²+30+(2+3d_v)²+(4d_v+3)²}
 +301E+Σ_x(3+I_x)².

The implementation's closed_ledger returns these formulas and its summand ledger independently computes the same counts. These totals exclude coordinate/index manipulation and the input-height evaluator; those are charged separately below.

## 7. Fully collected coefficients without giant global memory

records() emits coefficient/monomial pairs in a deterministic stream. polynomial() is a small-instance convenience collector and is NOT used as the universal materialization claim. collected_records() is the actual bounded-workspace fully collected generator:

1. Assign a vertex variable to its site, an edge variable to its lower endpoint, and a halo variable to its inward neighbor
2. Assign each nonconstant monomial to its least variable-owner vertex
3. For each owner v, regenerate only summands anchored at v or a nearest neighbor, retain records with owner v, collect coefficients in a local dictionary, remove zeros and emit sorted keys
4. Emit the constant coefficient separately as26V+E+Σ_vη(v)²+Σ_x(η(x)−5)²

A vertex summand's variables are owned at its anchor or neighbors. The same is true for an edge summand anchored at its lower endpoint and a halo summand anchored at its inward neighbor. Therefore ALL contributions to a monomial owned at v are present in step3, and no emitted monomial occurs in another bucket. This proves exact global collection without materializing the global polynomial, evaluating a universal computation or sorting all records.

The exact collected monomial count is1+Σ_v |{m: owner(m)=v and the sum of its local record coefficients is nonzero}|. The generator evaluates this finite formula exactly. It is deliberately kept distinct from R; a geometry-only formula falsely pretending away data-dependent cancellations is not claimed.

For η<=6, each vertex has at most955 raw records, each edge173 and each halo10. Each anchor has at most3 positive-axis edges and6 halo points. A bucket therefore considers at most7(955+3*173+6*10)=10738 raw records, an explicit constant independent of V. At most7X coefficient-expansion arithmetic multiplications are needed to regenerate local summands, plus the separately charged constant computation. Filtering/indexing also sees at most7R raw records. Height evaluations number at most7(V+H) for buckets, plus V+H for the constant. The generator uses a constant number of local polynomial records plus input-description memory; variable IDs and coordinates are unbounded integers, so its BIT space is not constant.

For a general maximum interior height M, raw coefficient magnitude is at most max(72,12M,M²). In the literal loader M<=6, so it is at most72. The coarser collected coefficient bound72R is valid. The constant coefficient is<=215V, and every nonconstant coefficient is<=72*10738=773136, hence collected height<=max(215V,773136).

## 8. Bit costs and certificate heights

At a natural zero, z,ell,g,h and halo gaps are<=5; categories/selectors are0 or1; beta and edge gaps are<=max(V−2,0). Thus every witness coordinate is<=max(5,V) and needs at most ceil(log2(max(5,V)+1)) bits. W such coordinates give an explicit W times that bit bound; no rank/order certificate is free. Generating that witness still requires the actual finite stabilization/burning computation. Coefficient generation does not require a halting time or an actual witness.

For the literal loader, R<=1534V, X<=2414V, evaluation multiplications<=285V and additions<=235V−1. These are safe bounds using E<=3V,H<=6V; exact formulas above are sharper.

Let b be the maximum of: bit lengths of prism coordinates and dimensions, input length counters, a variable index (<=W), and constant coefficients. When evaluating an arbitrary proposed witness, also include its maximum coordinate bit length in b; the sharper O(log V) witness bound applies to actual natural zeros. Standard schoolbook arithmetic gives O(b²) bit time for a bounded number of additions/multiplications/divisions/modulos and O(b) bit space per integer. With K_height counting the bounded loader evaluator's arithmetic operations, coefficient generation costs O((V+H)K_height*b²+R*b²), plus explicit output writing; collected generation has the charged factor<=8 on height evaluation and<=7 on local expansion/filtering. A raw or collected monomial has degree<=3 and can be encoded by at most3 variable IDs plus an integer coefficient, so total output length is O(R*(log(W+1)+log(V+1))) bits with displayed explicit bounds on both factors. No dense V×V graph is built.

The general PeriodicInput.height convenience method scans all s addition entries, so its cost includes O(s) coordinate comparisons per query. LiteralInput uses a frozen seed set (expected constant-time membership, or a deterministic ordered lookup could be substituted and charged O(log(s+1))). A pessimistic deterministic linear seed scan remains a valid bound if hash-table adversarial complexity is considered.

The literal background evaluator is NOT an uncharged oracle: per queried point it performs at most two scans of M=5819945 explicitly generated edge records, seven modular segment-membership tests and a41-site primitive lookup. Initial Circuit construction scans388146 rules and their1940004 input occurrences once; validation reads/hashes the fixed24-file manifest. These enormous fixed costs, and the binary arithmetic costs of the supplied prism/input, remain part of the algorithm even though they are constants with respect to unbounded tape/time parameters. No materialization of the enormous fundamental table is claimed.

## 9. Composition with the audited literal loader

The separate loader bundle has frozen manifest SHA256
de3e161de813afb098110223f9850c49cb8bcd481af69f8b9789daa3ca2950e3.
Its proof SHA256 is1791518f521a147b014ca7636910b7775df64fcfe799b6fcb5a0261de4f99d34 and compiler SHA256 isf879d4a285c749e493e7004f3e985779c425222ec5cbd165c93ac1601da7735a. LiteralInput verifies the manifest and all24 listed hashes before importing that newly authored local code. It temporarily removes cached lazy_u15/periodic_router module names, checks both imported dependency paths and restores the caller's prior module entries and search path, so an unrelated cached module cannot masquerade as the verified dependency. No upstream program is executed.

Loader hypotheses proved there, reused here:

- Ordinary Z³ six-neighbor threshold6, stable periodic b∈{0,4,5}
- Periods(1303671936,744955392,1955501604)
- B=186238848, Zmax=1955501572
- Finite nearest-head-first binary halves ell,right, blank0 under the state-A head; seed δ adds one chip to each selected height5 WIRE root, at most n+7 roots where n=|ell|+|right|
- All lattice sites topple at most once under every legal schedule; support-exterior sites never topple and receive at most2 chips
- U15 halts iff there are finitely many total topplings, including shutdown and partial gate activity

For a halt after T transitions at head position p, set

L=min(−3,−|ell|−1), R=max(3,|right|+1),
H_CA=2T+max(p−L,R−p),
Xmin=2L−2T−p+1, Xmax=2R+2T−p−1.

All activity is in

P=[B(Xmin−2),B(Xmax+3)]×[0,B(H_CA+1)]×[0,Zmax].

Our certificate adds its TRUE external six-face halo without enlarging the vertex graph. It does not rely on the distinct support-exterior leakage lemma to omit a prism boundary condition: halo sites may themselves be background support outside P and still must be stable. The explicit halo polynomial handles exactly that issue.

The volume is bounded by

V<=C(n+T+1)²,
C=80B²(Zmax+1)=5426111451172075939316367360.

Consequently W<=26C(n+T+1)², J<=29C(n+T+1)², R<=1534C(n+T+1)² and X<=2414C(n+T+1)², with witness bit height O(log(n+T+1)) plus the displayed fixed constants. These are parameterized resource bounds, not a computable halting cutoff depending on n alone.

Matching-order work corollary. Put s=n+T+1 and D_L=p−L+T, D_R=R+T−p. The loader's exact active-CA count is

A_CA=(T+1)(R−L+1+T)+D_L(D_L−1)/2+D_R(D_R−1)/2.

Here D_L,D_R>=3 and D_L+D_R=R−L+2T>=n+2+2T>=s. For D>=3, D(D−1)/2>=D²/3; hence A_CA>=(D_L²+D_R²)/3>=(D_L+D_R)²/6>=s²/6. Each active CA cell activates a distinct physical root, so total physical topplings are between s²/6 and C*s² on halting inputs. Thus the total-work order is Θ((n+T+1)²), with explicit constants. This does not provide a computable bound on T in terms of n alone. It uses only the loader's root semantics and exact shutdown count, without changing its frozen sources.

For any fixed prism containing the seed, this literal F has a natural zero exactly when the global sandpile stabilizes inside that prism, since one-shotness is already proved for the entire loader. Taking the union of this EXTERNAL family over all finite prisms gives U15 finite-tape halting. The supplied (T,p) bound constructor need not verify that T,p describe a real halt; if they do, the theorem guarantees containment. Otherwise the polynomial still certifies its own exact global closure or has no natural zero. example_hypothetical_bound.json uses empty halves,T=0,p=0 only as a size example, NOT as a claim that that U15 tape halts.

This supplies a literal finite-tape U15→sandpile→finite-prism coefficient chain. The arbitrary-TM/program→U15 tape compiler remains the published dependency in the loader bundle; no executable universal encoder or new fixed-arity/unbounded finite-fold theorem is supplied here.

## 10. Verification boundary and files

- prism_certificate.py: immutable finite-period input; direct prism/edge/halo indexing; exact cubic summands; raw and fully collected coefficient streams; exact ledgers; finite test witness constructor
- literal_composition.py: frozen loader input adapter; halt-bound prism; parameter-only size ledger; raw/collected CLI streams
- test_prism_certificate.py: scoped coefficients, uniqueness mutations, domain/halo/input contracts, actual literal seed heights, a45-record literal coefficient prefix, truly lazy huge-coordinate iterator prefixes and huge dimension-only bounds
- verification.json and verification_optimized.json: normal/-O receipts; output equality required
- review/: independently authored mathematical model, sparse polynomial cross-checks and review

All negative guards in new primary code are explicit exceptions, not Python assert statements. Finite tests supplement the mathematical proofs, never replace them. The giant background table, a full literal universal prism polynomial and a full routed U15 sandpile execution have NOT been materialized, expanded, solved or simulated.
