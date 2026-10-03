# A literal fixed periodic sandpile loader for U15

Research construction, 2026-10-03. This is a quantitative materialization of the ordinary Z^3 global-halting reduction, not a new undecidability theorem. It closes the imported periodic-loader construction at the fixed U15 finite-tape interface. It does not implement the Neary–Woods arbitrary-program-to-U15 encoder. No claim of practical efficiency or minimal constants is made.

Finite coefficients are also available through compiler.literal_loader.background_height(point,circuit). It computes the gate-plane coefficient directly, identifies any shaft by an explicit edge-incidence scan, and identifies a horizontal route from its height index followed by exact modular-segment tests. At most two scans of the M-edge generator, seven segment membership tests and a <=41-site primitive lookup suffice for one background coefficient. This is a charged bounded algorithm, not an assumed background oracle.

## 1. Exact theorem

Let U be the fixed binary 15-state machine in ca/lazy_u15.py, checked against the pure-data table SHA256 0c6d8ae506f503e2783f6ed2ee68db4cde2f501b9864f376ab3773f86b59428a. States are A through O, blank is0, initial state isA, and the sole undefined transition is J1. Given two finite binary words ell,r, put ell[i] at tape coordinate −i−1, r[i] at i+1, and a blank under the head at0. Both halves are nearest-head-first. This is the same precise finite-tape convention as Report32.

There is ONE explicitly specified stable periodic background b:Z^3→{0,4,5}, with periods

    (1303671936, 744955392, 1955501604),

and a literal finite loader delta(ell,r):Z^3→{0,1}, such that

    U halts on (ell,r) iff b+delta(ell,r) has a finite least activation closure, equivalently every fair maximal legal execution has finitely many total topplings.

The halting statement uses a fair legal complete history; equivalently its total odometer mass is finite. It does not confuse finite total activity with each individual site toppling finitely often: indeed EVERY site in this construction topples at most once even in a nonhalting computation.

A binary serialization is w=1^|ell| 0 ell r. The parser scans the initial unary length, consumes exactly that many following bits as ell, and takes the remaining bits as r. All arbitrary pairs have such an encoding. The formula applies to every well-formed input; syntactically invalid inputs can be recognized and assigned the empty loader if a total binary-word map is desired. The ordinary program/input→(ell,r) universal compilation remains the published Neary–Woods mathematical dependency, not reimplemented software. Thus the sandpile reduction from each finite U15 tape is literal, and universality/r.e.-completeness imports only that named fixed-machine universality theorem.

## 2. Literal lazy CA, including shutdown

ca/lazy_u15.py enumerates 388146 partial positive-state rules of radius2 on 34 active states plus the absent/lazy state. There are2 tape states,30 headed states and2 moving fronts; final headed state h(J,1) has ID21. Every pattern condition is a required positive state at a listed offset, never a negative test. Wildcards simply omit conditions. The rule generator uses only finite integer loops and the displayed 30-entry transition table. ca/manifest.json gives the rule hash, all state counts and all input/output incidence counts.

The finite initializer sets fronts at

    L=min(−3,−|ell|−1),  R=max(3,|r|+1),

all cells strictly between L,R to the specified tape state, except coordinate0 which is h(A,0); all other cells are lazy. For every pre-halting row t, fronts are at L−t,R+t, the head is the correct U15 head, and the intervening tape agrees with U. The head starts at distance at least3 from the fronts and cannot catch them because both move at speed1. The source construction's positive rule families therefore have exactly one matching rule at each intended active successor, and none elsewhere. See ca/SEMANTICS_AND_BOUNDS.md for the detailed case proof.

If U never halts, a distinct headed root at every row eventually activates, giving infinitely many topplings. If U halts at timeT at coordinatep, write

    D_L=p−L+T,  D_R=R+T−p.

The lazy shutdown front moves at speed2. The first all-lazy row is exactly

    H=T+max(D_L,D_R).

The last active row is H−1. The full CA active x range is exactly

    Xmin=2L−2T−p+1,  Xmax=2R+2T−p−1.

These extrema include the still-moving fronts before shutdown catches them. In particular, for n=|ell|+|r| and |p|<=T,

    H<=n+3+3T,
    Xmax−Xmin<=2n+4T+10.

This is a finite-work CA statement. The proof below separately charges partial gate activations in cells that never acquire a CA state.

## 3. Fully enumerated finite circuit cell

Use one WIRE state root for each of the34 active states. A condition for state s at offset k in rule j receives its signal from state root s in cell(x+k,t−1). In the source-indexed edge convention this is displacement(−k,1).

For a rule with k positive input conditions in ascending offset order, use k−1 binary AND gates in a chain: the first combines conditions0,1; each later gate combines the preceding output and the next condition. Every rule has k>=2. For each output state s with m_s producing rules, merge their outputs in deterministic rule order with an OR chain of m_s−1 gates, then connect its output to the state's WIRE root. All m_s are positive here. For each state with f_s input occurrences throughout all rules, use a FORK chain of f_s−1 boxes to distribute its root to these occurrences in generator order. The final state21 has f_21=0 and no outgoing wire; every other f_s>=2. FORK is a single undirected logical signal, not an isolating Boolean gate. The receiving AND/OR input diodes provide directional isolation.

compiler/literal_loader.py gives explicit numbering and a streaming enumeration of EVERY primitive and edge. It does not invoke a truth-table synthesis or routing oracle. The exact counts are

- State WIRE roots:34
- Rule AND gates:1551858
- Producer OR gates:388112
- Signal FORK gates:1939971
- Total primitives N=3879975
- Temporal edges:1940004
- Internal edges:3879941
- Total edges M=5819945

The exhaustive port-incidence audit visits all M edges. Every nonroot primitive uses all three ports exactly once. State roots use both ports except final state21, whose output is unused. This is a finite machine-verifiable graph ledger, not merely a bounded sample.

## 4. Literal geometry, all seams and cumulative leakage

geometry/periodic_router.py and geometry/periodic_router_proof.md specify every site. An AND/OR has41 support sites: horizontal tail −12..12, downward output tail of length12, and the four diode bypass sites. The two input diode barriers are height4, with a height4 center for AND or5 for OR. FORK has37 height5 sites and WIRE25. All unspecified sites have height0.

Set B=48(N+1)=186238848. Primitive j in cell(x,t) has center(Bx+24+48j,Bt+24,0). Each of its ports has a distinct x coordinate moduloB; minimum gap12. Each edge e in source cell(x,t) has its own planar routing level

    z=64+12[e+M((x mod7)+7(t mod4))].

Its seven axis-parallel segments are given in closed form in the router proof and the corners function. Port shafts rise vertically, their lateral lanes are shifted by4, and the main horizontal route uses the cell midpoint corridor. Periods are7B,4B,336M+84. Enumerate28 source-cell residues and all edges, including targets outside the period, then reduce all sites modulo the periods. This accounts explicitly for every seam. The max routing height is

    Zmax=336M+52=1955501572.

The global separation proof controls different edge labels, residue copies at the same height, shafts crossing other edge planes, bend-to-bend separation, attachments, all primitive copies and the z seam. Every support vertex has degree<=3 within support; every zero-background vertex has at most TWO support neighbours. The bound is for the entire infinite union, not the sum of separate local assertions. Adjacent active slabs are separated by31 all-zero planes.

The first-bad-event proof is uniform over all legal schedules: before any first repeated support firing or first exterior firing, each support neighbour has fired at most once. An exterior vertex has at most2 chips. A support vertex has lifetime available chips at most5+1+3=9<12, so cannot fire twice. Thus support vertices fire at most once, no exterior vertex fires, and exterior leakage never exceeds2 chips, regardless of how long or how widely the computation runs. An unseeded z slab stays stable forever.

The dense fundamental table has exactly

    1899139038016727160551374848

entries. It is specified by the finite compressed circuit/segment generator; this huge dense table has NOT been materialized. Every coordinate and coefficient of that table is nevertheless determined by bounded loops, with all loop counts and lengths charged. There is no unresolved geometric choice.

## 5. Composition and arbitrary asynchronous port behavior

The AND, OR and diode templates are checked for every external activation subset, including output-only and input+output activation. For externally active input bits a,b and output bit o, final external ports are

    AND: (a,b,o OR (a AND b)),
    OR:  (a,b,o OR a OR b).

Backward output activation may fire an AND center when combined with one input, but it cannot cross the other input diode. A diode maps(I,O) to(I,I OR O). These are proved by a least-threshold-closure argument, not only forward truth tables. All off-template sites remain inert by the global confinement lemma.

For completeness of the circuit composition, take its Boolean least closure above the seed state roots. Assign each physical connecting wire the corresponding logical signal, and fill each finite template by its least local threshold closure with exactly those true ports activated. The full activation-subset contract ensures that this does not activate any false input or any logically false output. FORK/WIRE regions are assigned one common signal. Hence the union is a closed upper bound on the true sandpile activation set. Conversely, every finite Boolean gate derivation propagates along finite wires and through its gate under any fair legal schedule. This proves equality. It handles output activation at a seeded root's incoming OR circuit as well as all delayed arrivals; no sandpile timing assumption appears.

For rows t<0 no root is seeded and all rules have positive arity, so the least closure there is empty. For each row t>=0, the logical circuit computes exactly the positive rule matches from the preceding row, except for the row0 finite initializer. The valid CA invariant excludes multiple matching rules. Thus exactly its CA state root activates, or none if lazy. There are no nontrivial unseeded solutions imported from infinity: only the least closure is the legal process.

Finite CA activity implies finite sandpile activity, with one necessary qualification: a rule AND chain may partially activate even though its output cell remains lazy. Every temporal wire is a branch of some state root and cannot be activated backward through a receiving diode. Therefore all temporal activity starts from active CA roots, and reaches at most one further row and two further x cells. All remaining activations are within the finite internal circuit of one such cell, or in row0 producer circuits reached backward by a seed. No further temporal propagation occurs without an actual new state root. Finitely many such cells, each with finitely many finite wires, imply finitely many topplings. A nonhalting CA activates infinitely many distinct roots, giving infinitely many topplings. This proves the equivalence in §1.

## 6. Fully charged initializer and quadratic active prism

The loader adds exactly one chip to the midpoint of the selected state-root WIRE in each initialized cell x∈[L,R]. Its coordinate is

    (Bx+24+48s_x,24,0).

These midpoints are distinct height5 support sites, so additions are nonnegative, finite and in{0,1}. Their number is R−L+1<=n+7. Each coordinate has absolute value<=B(n+4). The loader directly parses the two finite binary words and emits these sites; it performs no infinite blank initialization. On serialized input of length m, n<=m−1, so both count and coordinate bounds are linear in m. All initial unseeded background sites are stable.

For a halt(T,p), all activated sandpile support lies in the following integer prism:

    B(Xmin−2) <= physical x <= B(Xmax+3),
    0 <= physical y <= B(H+1),
    0 <= physical z <= Zmax.

The two extra x cells and one extra row pay for incoming partial-rule computations. Every edge between source and target stays between their x endpoints with an extra lateral shift4 still inside these cell margins; its y midpoint corridor stays inside the stated row margin. The finite internal circuits may use every primitive in an included cell and all are charged. The selected z slab has fixed thickness Zmax+1.

Consequently the number of lattice sites in this prism is at most

    [B(2n+4T+15)+1] [B(n+3T+4)+1] (Zmax+1)
    <= C (n+T+1)^2,

where the explicit fixed constant is

    C=80 B^2 (Zmax+1)
     =5426111451172075939316367360.

This is a deliberately loose, proved quadratic bound in two unbounded spatial directions. It includes initialization and the entire shutdown, and also includes all partially activated rule gadgets. Since each site fires at most once it bounds the total number of topplings as well. It does not provide a computable stopping bound in n alone.

If the existing odometer compiler requires a one-site halo, enlarge all prism sides by1. A sufficient explicit bound is126 B^2(Zmax+3)(n+T+1)^2. This observation supplies geometry for a later certificate composition; no new odometer theorem or fixed-arity Diophantine universality theorem is claimed here.

## 7. Verification boundary and sources

The original universality and qualitative lazy-CA reduction are Hannah Cairns, “Some Halting Problems for Abelian Sandpiles Are Undecidable in Dimension Three,” arXiv:1508.00161v2, §§2,5,6. The new work makes finite primitives, port semantics, all-period routing, finite U15 initialization, explicit gate counts and shutdown/resource accounting literal.

Executable evidence includes all28 gate port subsets and complete halo stabilization, all388146 rule patterns with no duplicate pattern, independent bounded TM/CA trace comparisons and exact shutdown checks, two complete periodic router tori including all five offsets, and the exhaustive incidence check for all5819945 edges. The analytic proofs, rather than sampled geometries or bounded traces, establish the unbounded theorem. The huge universal dense table and a full 3.8-million-primitive sandpile computation were not materialized or simulated. Scripts are newly authored; no upstream implementation was executed. Independent adversarial review is recorded separately and must be read with this proof.


## 8. Concrete finite input example

Take ell=00010111100110000110 and r=10100111001100001011. Both have length20, the initial scanned bit is0, and the U15 run in stateA halts after75 transitions at position−13 in stateJ reading1. The literal loader uses43 one-chip additions; every coordinate is listed in compiler/worked_example.json. The CA becomes all-lazy at row184, with18257 active spacetime cells and extrema−178,204. The proved physical active prism is

    x in [−33522992640,38551441536],
    y in [0,34454186880],
    z in [0,1955501572].

compiler/make_example.py independently recomputes the finite U15 trace, verifies every seed lies on a height5 root, and emits the exact additions. Its trace digest is1c7a88bbb39ef169e6f508492a063ced31a36a0663adfc93491e431976e14777. Sandpile halting for this explicit input follows from the construction theorem; a full sandpile stabilization of this enormous example is not claimed.
