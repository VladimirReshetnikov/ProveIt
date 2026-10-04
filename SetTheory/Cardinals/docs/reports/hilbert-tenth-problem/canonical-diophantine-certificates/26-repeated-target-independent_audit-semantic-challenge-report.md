# Independent semantic challenge of the repeated-firing tableau

## Verdict and scope

**No theorem-level gap or counterexample identified in the repeated-tableau semantics.** Conditional on the advertised arithmetic POWER/Sub/AND interfaces, the source equations implement exactly a finite legal ordinary sandpile sequence that contains the supplied signed target. The arbitrary-carry recurrence, own-firing depletion, boundaries, and target event survive independent mathematical checking.

This is an independent adversarial review, not acceptance of any earlier PASS. I read `ARCHITECTURE.md` and `build_repeated_certificate.py` as text; I did not run or import the submitted builder, upstream programs, or Lean. Only the fresh `independent_checks.py` beside this report was executed. No file in the submitted packet was changed.

Reviewed source hashes:

- ARCHITECTURE.md: `ccb59eac23edab6db8500814123c0e0e9486253d577f52be1e177c959efe5e9f`
- build_repeated_certificate.py: `c37f455dc5a9a673fb2b980fb5dc41103f9a85e82a97c24cae296ed580fe9928`

The line references below refer to that builder.

## 1. Arbitrary candidate carries are ruled out, without assuming the conclusion

Lines 204–209 force a natural pre-stream below W=Q^K and a binary event in each allowed b-digit. Since b≥64(K+1), K<b. For any allowed event stream E, independently construct A* from cumulative previous event digits and V* from all event digits. Each digit of A* is at most K−1; every digit of V* is at most K. Thus these are valid radix-b streams with A*<W, and direct telescoping gives

Q(A*+E)=A*+W V*.

For an arbitrary satisfying candidate A,V, subtracting gives

(Q−1)(A−A*)=W(V−V*).

The coprimality gcd(Q−1,Q^K)=1 forces W|(A−A*). Both A and A* are in [0,W), so A=A* and then V=V*. This controls all candidate spatial carries, all temporal carries, the first frame, and the terminal frame at once. No inference about candidate digits was used before uniqueness. In particular K=1 and empty intermediate layers pose no exception.

A necessary premise here is the bounded pre-stream. The actual Sub mask supplies it. Without that premise A+W,V+(Q−1) would be another algebraic solution; this attack does not apply to the submitted clauses.

## 2. Geometry and SPREAD do not recode the physical input

At lines 152–169, the original radix-32 tile/patch streams are validated before conversion. The tile bitplanes have no digit carries, and the extra Sub condition excludes simultaneous 2- and 4-bits, leaving exactly digits 0–5. The patch condition permits exactly digits 0–15. The conversion length is positive and its range is strict, including zero streams and declared leading zeros.

The SPREAD formula itself has a direct coefficient proof. With n input digits and s≥n+1, multiplication by the copy sum places disjoint n-digit intervals starting at k(s−1). The output mask selects positions is. Such a position is in the k-th interval only when i=k, where it selects input digit i. Therefore no multiplication carry or incorrect diagonal is available. Every radix used by these calls is a power of two.

For a tile slot x+p y+p q z, the first reshape sends it to x+A y+A q z; the second sends it to x+A y+AB z. Repetitions by p, Aq, and ABr independently cover exactly the tile copies in the box, without overlaps. A patch slot x+d y+d e z analogously becomes x+A y+AB z, followed by translation by hx+Ahy+ABhz. These are the expressions at lines 171–191, not an alternate construction.

Each negative box corner coordinate is a multiple of the corresponding tile period. Thus physical coordinates and local tile residues agree. The patch is strictly interior because hx≥2d, hy≥2e, hz≥2f. Initial coefficients remain between 0 and 20. The intermediate row reshapes fit strictly inside the range required by their next plane reshape, including extreme final slots.

## 3. Both ends of every spatial axis protect temporal frames

Lines 193–208 give the exact strict-interior mask: each factor is a geometric sum of length A−2, B−2, or C−2 and the leading bXY shifts each coordinate to start at one. Its digits are one exactly for

1≤x≤A−2, 1≤y≤B−2, 1≤z≤C−2.

For every allowed source, each of the six physical neighbors remains in the same full spatial box. Consequently shifting by ±1, ±A, or ±AB does not wrap a row, plane, or Q-frame. This is stronger than merely proving that the global integer divisions exist. It covers the first and last time frame, and permits legitimate destinations on the shell while excluding shell sources.

The divisions at lines 210–213 are exact because every source exponent is at least 1+A+AB in its own frame. There are no contributions from nonexistent negative time, frame K, or unrepresented outside firings.

With the recurrence already resolved, the coefficient of the availability stream at (t,v) is exactly eta(v)+sum of the six neighboring prior counts. It is at most 20+6t≤6K+14<b, so the availability expression at line 214 has no remaining carry ambiguity.

## 4. The lower-half slack closes the repeated-own-firing loophole

Lines 215–220 select exactly the whole digits at event positions and charge six times the actual prior own count. Since b is a power of two and half=b/2, the slack mask allows independently the range 0,…,b/2−1 at selected slots only.

Before using digit equality, the entire right-hand coefficient is bounded by

6(K−1)+6+(b/2−1)=6K+b/2−1<b.

Thus a slack cannot force a carry into another event slot, including an adjacent selected slot. Equality is genuinely coefficientwise. The selected condition becomes exactly

eta(v)+sum of prior neighbor counts−6 prior own count≥6.

Conversely a legal event has slack at most 20+6(K−1)−6=6K+8, which fits within b/2−1 under the same growth bound. There is neither loss of a legal prefix nor acceptance of a repeated firing supported only by the site's original chips. Same-layer events do not enter the availability stream.

## 5. The supplied target cannot be replaced by another time, position, or parity

At lines 222–234, natural sign satisfying s(s−1)=0 has exactly values 0 and 1. With zeta=2h+s, the local coordinate is the unique half-extent plus signed coordinate h−2sh−s. The positive upper gap forces the strict upper coordinate bound; the natural local adapter supplies the lower bound.

The resulting point is one bit at b^j with 0≤j<N. The product point·timepoint is the one bit b^(j+N tau), where tau is natural. Its Sub containment in E<Q^K forces j+N tau<NK, hence tau<K, and requires that exact event. The interior mask also rejects shell targets. A positive even final count is accepted through an actual event bit; no low bit of the final count is tested.

## 6. Soundness and finite-prefix completeness require no global stabilization

Every distinct event in a layer is unstable at that layer's start. Firing any other member can only add chips to an unprocessed member, so serializing the finite layer in any order preserves legality. Repeating this across K layers gives an ordinary finite legal sequence with precisely the recovered cumulative counts and the marked target firing.

Conversely, any finite ordinary legal prefix containing the target can be truncated at its first target firing and represented using singleton layers. The required choices of padding are consistent and unbounded:

- Choose L≥max(pqr+1,def+1) with 32^L≥64(K+1)
- Choose tx≥2 large enough for both 2d tx≥qr+1 and 2p tx≥ef+1, and for all x coordinates of the finite support
- Choose ty≥2 large enough for both 2e ty≥r+1 and 2q ty≥f+1, and for all y coordinates
- Choose tz≥2 large enough for all z coordinates

These conditions are independent lower bounds; none introduces an upper bound or a cyclic choice. Increasing spatial extents after choosing L is harmless: spatial SPREAD gaps depend on tx and ty, not on a new restriction on L. The physical patch remains interior. Outside sites need not fire or be stable; a finite legal prefix has no requirement to topple every unstable site. Thus the construction does not silently impose finite global stabilization.

## Fresh finite checks

The runnable independent script and machine-readable results are in this directory. All checks passed:

- 10,894 binary event streams, solving the complete recurrence by modular inversion over arbitrary candidate pre-values
- 3,344 additional brute-force candidate pre-values in small domains
- 36,480 literal arithmetic SPREAD cases
- 80 independently generated geometry boxes, checking 166,480 physical slots
- 27 actual integer interior masks and 13,122 spatial/temporal shift positions
- 384 exact target-bit membership tests, including late times and even total counts
- 981,834 local legality/bound cases
- 5,456 complete enlarged-radix b=1024 two-site tableaux, of which 1,065 are legal, with initial pairs (12,4), (6,0), (5,5), and (20,20), all four event subsets in each layer, and lengths 1–5

The last group computes the actual integer recurrence, event/pre/final masks, six shifts, selected availability, own depletion, masked slack, and exact target-event membership. It independently rejects false support from two initially height-five sites and unsupported repeated own firing, while accepting the repeated-firing separator.

## Limitations

- The universal conclusion above is a mathematical argument, not a Lean-checked theorem
- Finite tests alone would not establish universal correctness
- This review does not independently establish the inherited constructive Pell theorem or all positive arithmetic witnesses implementing POWER
- This review does not certify the emitted DAG's identity with the source, polynomial degree, witness count, or arithmetic gate count; those are separate source/accounting checks
- No result here establishes a universal-machine loader, machine-to-physical compiler, global stabilization, or witness uniqueness

The bounds and clauses needed for the repeated-tableau theorem are present in the inspected source. No missing tableau-domain restriction was found.

## Explicit separator and negative-control fixtures

The script also evaluates the following complete integer macro-level fixtures at b=1024 in an 8×4×4 box, with target positions strictly interior:

These b=1024 fixtures are complete dynamical/tableau macro-level tests, not full raw-interface/Pell witnesses: a two-slot patch requires conversion width L≥3 and hence b≥32768. Conversion is checked separately, and the dynamical proof is uniform in b.

1. Zero background and patch [12,4]: the layers origin, origin, neighboring target are accepted; final counts are [2,1]
2. The same prefix with origin as target: its marked event is accepted, despite the origin's final count being even and the corresponding low bit of V being absent
3. Zero background and [5,5]: each of the three nonempty first event layers (first site, second site, both) is rejected, so these sites cannot manufacture the first firing
4. Zero background and [6,0]: firing the first site twice without external support is rejected by the own-depletion term
5. Periodic height-five background with one added chip at origin: the singleton origin event is accepted. This configuration has no finite global stabilization: any nonempty finite toppling support has an adjacent outside site receiving at least one chip on top of its original five, leaving that untoppled site unstable. The accepted finite event therefore demonstrates that endpoint stability is not imposed
6. Parent-suggested adversarial negative control: replace the lower-half slack mask with an incorrectly widened full-digit mask, take zero background with adjacent heights [0,7], K=1, and events at both sites. If the first site's point is P, then E=P+bP, Csel=7bP, and slack=(b−6)P satisfy Csel=6E+slack. The full-digit slack mask would accept this counterfeit. The actual lower-half mask rejects it because b−6≥b/2. Physically the first site can never fire: the second site can fire just once, after which every height is below six. This confirms that the lower-half restriction prevents a substantive false positive

No relaxed-variant counterexample above is a counterexample to the submitted source; they test that the source's repaired guards are operative.
