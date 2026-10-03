# Practical scope before full Grill arithmetic emission

This is a resource assessment, not a new universal operation bound. `resource_estimate.py` constructs only a sparse support census from the literal Genera rows; it does not emit the dense Grill table or the history DAG. Source templates were read through the GitHub connector, saved as `resource_source_*.txt`, and never executed.

## Exact geometric and template sizes

For N_G=1,013, a=28(N_G+1)=28,392 and m=14a=397,488. There are24N_G-12=24,300 positive runs and373,188 zero runs. The maximum exponent is275,944;2,030 distinct run exponents occur. Their multiplicity-weighted sum is1,058,311,800.

The native wrapper's affine table has s=2m=794,976 rows:

    (2,0,1,0), (2,1,2*4^n,2*(4^n-1)/3)

for each run exponent n. The U baseline2 has no slope exceptions. With V baseline1, each distinct n is one exception class, including n=0; hence g=2,030. The pinned template gives:

    raw witnesses = s+g+29 = 797,035
    native-unit witnesses = s+g+23 = 797,029
    native-unit comparisons = 20-9 = 11
    native scale exponent = s+g+5 = 797,011.

These are native-history template counts before adding either recoder or any new input binding. They are not the finished universal polynomial's witness/count ledger. Exact operation totals depend on the emitted live DAG and remain unclaimed. The template's selector packing, group sums and phase residual suggest roughly four million arithmetic rows, so planning for several million rows is appropriate.

## Why the old in-memory driver is unsuitable unchanged

The run table alone is modest:1,589,952 bytes as uint32, with every entry fitting32 bits. The affine coefficients are much larger. The largest slope has551,890 bits. Eagerly constructing both large coefficients separately at every positive run needs about529 MB of raw integer bit payload, before Python object overhead or metadata. Decimal JSON would contain about1.274 billion coefficient digits for one such listing. The exact byte census is in `resource_geometry.json`. Interning by distinct exponent reduces integer payload considerably; symbolic fixed-numeral recipes reduce it further.

The historical code repeatedly builds/copies whole packets, retains old/new sources and maps, serializes duplicate constants, and uses recursive DAG walks. Several million rows already require substantial memory in ordinary Python objects, independently of the coefficients. Increasing a recursion limit proportional to m is not a robust remedy.

More seriously, `grill_tag_native_phase_residual206.py::_poly` caches an expanded polynomial at every node in the long phase-prefix sum. The prefix polynomials grow linearly, so their cumulative stored monomials grow quadratically in m. At roughly397,000 phases this is prohibitive even if the final residual has only linear support. The phase-sharing predecessor has a similar risk if its proof materializes each intermediate linear form. Do not invoke this old proof path on the new table unchanged.

## Recommended implementation stages

1. Emit and pin the sparse/dense integer Grill run table, checking every defined position and all zero defaults. Keep the original Genera source, IDs, width metadata and halt ID separately. This should be a small bounded artifact
2. Introduce a typed, canonical fixed-numeral representation for powers of two, (4^n-1)/3 and signed linear combinations used as coefficients. These denote fixed integers and are not runtime exponentiation gates. Intern by recipe; test exact values only at small exponents and by independent modular identities at large ones
3. Emit the arithmetic DAG once with compact numeric register IDs and references into the constant pool. Use iterative streaming passes for topological closure, gate counts, formal degree upper bounds and backwards liveness. Evaluate highest-degree coefficients iteratively where their local cancellation identities are justified; modular leading-coefficient checks can support nonvanishing claims but must not be mistaken for a complete exact-degree proof when a bound cancels. Avoid whole-packet copies and recursively traversed linear chains
4. Prove phase sharing/residual identity by direct coefficient formulas or a single linear dictionary accumulation, with the common B treated as a proved unchanged atom. Avoid retaining every prefix's expanded polynomial. Validate this emitter against complete pinned small receipts as data, without executing the old author source
5. Compose `canonical_input_bits`, `unrestricted_tape_exponent`, tape-value binding, exact unary E value and exact native width with disjoint witness namespaces. Keep the five valid-slice program coordinates free and fixed for the represented set. Their astronomically large specialized values should not be expanded during ordinary source emission
6. Emit one safe integer-unit finalizer containing every nonunit comparison square. Check its whole-polynomial correction identity against the native history, rather than appending a loader SOS outside the unit product
7. Have an independent checker reconstruct the source motifs, coefficient recipes, full comparisons and finalizer. Only then report a numerical operation/witness/degree ledger for this source. Bounded accepting fixtures and modular evaluations do not replace the parametric positive-converse proof

A practical first full-size gate is a metadata-only planner plus streaming source prototype, with measured memory/time and explicit failure limits. The proven source compiler and input semantics need not be changed to solve these engineering scaling issues. No CPU/RAM guarantee is inferred from the small reject-all example, and no existing 16,291/16,289/205 ledger is reused.

## Witness count is a template obligation, not a lower bound

Keep all797,029 positive native witnesses in the first correctness construction. The797,029 formula counts794,976 phase-and-head selector hats,2,030 already shared V-slope-class history hats, and23 other retained positive coordinates after the established native-unit projection. The U slope is already common and needs no exception-class hats. Further source/table sharing has not been proved to eliminate any of these coordinates.

Equal appendants at different phases cannot simply have their selectors merged: the chronological phase equation distinguishes those phases, including long zero-run intervals. The existing slope-class grouping already combines equal affine multipliers while retaining the phase-specific selectors. Replacing those selectors by a periodic-mask circuit or changing the controller representation is a separate theorem and paid source transformation.

Interning a fixed coefficient recipe only saves representation space. It neither supplies a runtime product for free nor eliminates an existential witness. Likewise, ordinary DAG common-subexpression sharing can reduce duplicate gates without automatically identifying independently quantified coordinates. Later optimization is possible in principle, but the count here is not claimed minimal and no such elimination is included in this packet.
