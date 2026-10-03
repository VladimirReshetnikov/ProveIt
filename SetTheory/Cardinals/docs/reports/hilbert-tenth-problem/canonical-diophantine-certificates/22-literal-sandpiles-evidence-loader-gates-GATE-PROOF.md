# Literal asynchronous sandpile primitives

## Model and exact coordinates

The graph is the ordinary nearest-neighbour lattice Z^3, threshold 6. All unspecified sites begin at height zero. For tail length l>=8, an AND or OR template has support

- (x,0,0), -l <= x <= l
- (0,y,0), -l <= y <= -1
- (-5,1,0), (-4,1,0), (4,1,0), (5,1,0)

Every support site has height 5 except (-4,0,0) and (4,0,0), which have height 4. The center (0,0,0) has height 4 for AND and 5 for OR. Ports A,B,O are (-l,0,0),(l,0,0),(0,-l,0). These are direct literalizations of the diode/wait-gate construction in Cairns, arXiv:1508.00161v2, §2.3, with longer separated tails.

The diode has support (x,0,0), -l<=x<=l, together with (-1,1,0),(0,1,0); its center (0,0,0) has height4 and all other sites height5. Input/output ports are (-l,0,0),(l,0,0). A FORK is the three-tail support above without diode auxiliaries, all height5. A WIRE is the straight horizontal support, all height5. FORK means a single undirected logical signal: all its ports have the same value, not an isolating two-output logic gate.

There are 3l+5 sites per AND/OR, 2l+3 per diode, 3l+1 per fork and 2l+1 per wire. AND height sum is 15l+22, OR height sum 15l+23, diode height sum 10l+14, fork height sum 15l+5, wire height sum 10l+5. For the actual l=12 layout, these are 41,27,37,25 sites and height sums 202,203,134,185,125 respectively.

## Uniform one-shot and confinement lemma

Let S be ANY finite or countable union of templates and routed wires. Suppose (i) b is zero outside S and 0<=b<=5 on S; (ii) each v in S has at most5 neighbours in S; (iii) each v outside S has at most5 neighbours in S; (iv) the finite loader delta has values0 or1, is supported on S, and b(v)+delta(v)+deg_S(v)<=11 on S.

Every legal sequential toppling history topples no site outside S and each site of S at most once. Indeed, consider the first forbidden event in any finite prefix. Before an outside toppling, each of its support neighbours has toppled at most once, all outside neighbours have never toppled, so its height is at most5. Before a second toppling at v in S, v has received at most deg_S(v) chips from neighbours and has height at most b(v)+delta(v)+deg_S(v)-6<=5. Both contradict legality. This is a proof for every legal schedule, including infinite histories, not a simulation claim. It also works when finitely many additions are delayed, since the total addition per site remains<=1.

Consequently all cumulative leakage at an exterior site is at most deg_S(v); it cannot accumulate further with elapsed time or with infinitely many remote activations. The geometric acceptance obligation is global, including seams: control deg_S, not merely the leakage of each template separately.

Each isolated template above has support degree<=3 and exterior co-degree<=2, directly by its coordinate table (the checker enumerates all affected sites). Its arbitrary port subsets therefore satisfy the lemma with a margin of at least3 chips against a second toppling.

## Least-closure semantics and asynchrony

Under the lemma, write a site as active iff it topples once. A nonseed height5 site activates when at least one support neighbour is active; a height4 site activates when at least two are active. A port seeded with one chip activates without a neighbour. The active set for every fair legal history is exactly the least set closed under these threshold implications. Every legal activation has a finite justification in that closure. Conversely every finite-depth implication eventually fires by fairness. This establishes schedule independence without assuming synchronous arrivals, fixed propagation speeds, or simultaneous port activation.

For a diode, its connected upstream height5 region includes both bypass sites and has two neighbours of the height4 barrier. The downstream region has one neighbour of that barrier. An active upstream region therefore fires the barrier and downstream region. Downstream activation alone contributes only one chip to the barrier and cannot initiate upstream activity. The least closure cannot create the missing upstream signal through a circular implication. Thus for externally activated port bits (I,O), the final bits are (I,I OR O).

For AND/OR, each of its two input diodes has precisely this property. Let external activation bits be a,b,o. Input ports finish at exactly a,b. Let c be central-site activity. Each interior input tail becomes active if its input is active or c is active, while the output tail is active if o or c. Before the central site first fires, its three neighbouring tails are active exactly as specified by a,b,o. Thus c is the two-out-of-three threshold for AND and the one-out-of-three threshold for OR. After c fires, it cannot cross a reverse input diode. Final external port bits are therefore

- AND: (a,b,o OR (a AND b))
- OR: (a,b,o OR a OR b)

This covers all eight subsets, including only O, A+O, B+O, and A+B+O. Internally, backward output activation can help fire the AND center; that is allowed and does not manufacture an inactive input. A connected all-height5 WIRE or FORK activates everywhere iff any port or designated seed activates. FORK outputs are ports of the same signal; isolation against independent outputs is supplied by the receiving gate's input diode.

## Finite verification and its boundary

check_gates.py enumerates literal templates, verifies degree/co-degree bounds, computes a threshold fixed point, and independently performs actual six-neighbour chip firing in lexicographically ascending and descending legal schedules. It checks all 28 external-port subsets for AND, OR, DIODE, FORK, including every reverse-output case. It does not exhaust exponentially many schedules: the first-bad-event and least-closure arguments above prove every schedule. The simulation includes every site that receives chips, so it does not silently turn the exterior into sinks. The geometric proof must still establish the global degree/co-degree hypotheses after wires, all template copies and periodic seams are composed.
