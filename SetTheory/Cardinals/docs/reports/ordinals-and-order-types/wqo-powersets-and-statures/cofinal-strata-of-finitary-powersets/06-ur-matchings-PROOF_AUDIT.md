# Proof and scope audit

## Conclusions and dependencies

1. **Schedule length = maximum uniquely restricted matching size.**
   A fresh witness from each productive group makes a triangular matching.
   A triangularly ordered matching is realized by scheduling its upper endpoints
   first. Alternating-cycle/unique-perfect-matching equivalence is reproved and
   credited as classical.

2. **Uniform actual ordinal height.**
   This does NOT assume the repository's height formula. A finitely generated
   downset is described by its upper support S, completed lower fibres N(S), and
   bounded active cuts. The ranking is
   alpha*d(S) + natural_sum(active cuts),
   where d(S) counts the maximum productive steps of a prefix on S. New completed
   lower fibres increase d; otherwise old active coordinates persist and some
   cut increases. The natural sum is strictly below pure alpha. An explicit
   chain has alpha*(nu_ur+1) elements in ordinal order.

3. **NP-completeness.**
   Imports the published bipartite uniquely restricted matching NP-completeness
   result of Golumbic–Hirst–Lewenstein (2001). The polynomial reduction from that
   problem to height-two ordinal height is given in full. The article does not
   claim a new proof of the original matching hardness reduction.

4. **Weighted ordered-matching formula.**
   Entirely finite. Pick a maximum-priority witness per group for one inequality;
   realize an admissible matching prefix and use weak monotonicity of ordinary
   addition for the other. No assumption that a natural sum can replace the
   ordered sum is made.

5. **Priority layers.**
   Entirely finite. The highest coefficient is the UR matching number in the
   highest-priority row subgraph. Upper endpoints of a maximum such matching
   cover all high rows. The residual keeps low rows adjacent to NONE of those
   endpoints. Optimal tails are maximized over ALL such endpoint sets. The upper
   proof uses ordered-matching witnesses after the last high event; it does not
   assume that arbitrary low-prefix columns can be moved later harmlessly.

6. **Nonuniform actual ordinal height.**
   Imports exactly ProveIt's Theorem 35.1 (`nh:wpo:thm:heighttwo`) for a finite
   nonempty height-two skeleton and positive pure ordinal fibres. The finite
   matching and layer formulas then compute its scheduling objective. This
   imported transfinite theorem was not re-proved or formally checked here.

7. **Bellman certificates.**
   Induction over subsets proves the full table exact from every predecessor
   inequality and one attaining predecessor. The checker does not invoke the
   optimizer but shares ordinal arithmetic. Certificates are exponential, not
   claimed to be polynomial upper certificates for all inputs.

8. **Structural algorithms.**
   Lower twins keep maximum priority; upper twins keep the first productive
   representative. Terminal priority is unchanged. Equal neighbourhoods may be
   merged, but proper containment is not a valid deletion rule. A dual covered-row DP is sound because every previously used column
   has its neighbourhood already covered, so every productive future column is
   automatically unused. After lower-twin compression it has 2^a states for a
   lower-neighbourhood types. The vertex-cover
   bound counts upper neighbourhood types; no unsupported kernelization claim is
   made.

## Boundary cases checked in the mathematics

- Empty skeleton: K(empty) has height 1, outside the nonempty formula.
- Nonempty antichain: no productive lower events, one terminal alpha block.
- All exponents are positive; finite/successor fibres are outside this solver.
- Zero-degree residual columns contribute zero and may be removed.
- No zero-degree lower rows are permitted in a scheduling instance.
- Terminal omega^tau persists even when a residual has no rows or columns.
- p < tau: terminal absorbs everything; p = tau: add one to the high coefficient.
- p > tau: residual tail is strictly below omega^p.
- All ordinal additions in schedule values are ordinary, not natural.
- Natural sum occurs only in the uniform rank proof and explicitly indicated
  special calculations.
- Arbitrary set-sized ordinal exponents are mathematical inputs; executable
  exponents are positive binary integers or, abstractly, correctly ordered labels.
- Finite graph results extend to arbitrary allowed priorities; tests do not
  establish that extension.

## Validation independence

All-permutation evaluation uses a position map to locate first neighbours.
The independent normalizer scans right to left. Ordered matchings are checked
by their earlier cross-edges, and the priority recurrence enumerates high UR
matchings. Some representation and matching-enumeration routines are shared.
The implementation is standard-library Python, not a verified kernel.

## Not claimed

No Lean/Rocq compilation; no peer review; no universal novelty or priority;
no exhaustive comparison of incoming repository ZIP archives; no solution of
arbitrary higher-skeleton scheduling, nonpure WPO substitution, or binary CNF
coefficient compression; no polynomial-time general solver; no approximation
ratio for an ordinal objective; no proof that matrix-rank bounds are always tight.

The article resolves identified repository questions with precise dependencies,
not an unspecified famous open problem in matching theory.
