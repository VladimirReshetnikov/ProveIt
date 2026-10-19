# Independent packed-library review

The literal 217-state guarded library, 188-state comparator-free guarded library,
and 62-state unconditional native-edge quotient pass independent structural
certification. The verifier `audit_packed_libraries.py` parses the published
component tables directly, does not import the packing search or its builder,
and checks the complete saved admitted-row certificate. Its JSON/log record
all hashes, counts, port IDs, and nontrivial universal classes.

## Exact theorem

Let D(q) contain every read symbol occurring at original state q on each run
covered by a component's documented entry contract. Let pi map all original
working states and external ports into quotient labels, preserving distinct
external ports. Suppose, for each b in D(q), the quotient row at (pi(q),b)
is exactly (w,d,pi(t)) whenever the source row is (w,d,t). Then induction on
steps gives exactly the same tape and head and projected state pi(q) until
an external port. All incoming targets and public entry labels must be
projected. No restriction on incoming edges beyond the original-run guard
invariant is needed. Same-symbol identifications are valid when their writes,
moves and projected targets agree; complementary-symbol pairing is only a
special case. Quotient behavior outside these original contracts is not
certified by this theorem.

The independent audit checks every allowed source row, completeness and lack
of duplicate certificate rows, all entries/targets, dense two-row working
state numbering, source hashes, and distinct external ports. It also checks
the earlier universal classes on BOTH read symbols, with no guard assumption.
Each distinguished failure state remains a singleton working class.

## Results

- 217 working states, 434 rows, 5 distinct unlinked ports, 4 distinct working
  failures. SHA256 d76e2f0e53414f3833ba2681a82d24012f676bfa21666263ea105222d54824b5.
- 188 working states, 376 rows, 3 distinct unlinked ports, 3 distinct working
  failures. SHA256 28282596979b8c34abb60fd55684e758b77be3e50aaa8487dd9df7ec0e23319f.
- Native68 to native62 admits all 136 source rows, so its six identifications
  are universal all-tape, exact-step bisimulations: {23,25}, {34,36}, {38,50},
  {39,51}, {40,52}, {45,47}. Return68 and reject54 remain distinct. Published
  quotient SHA256 7cfb46d1075f2009735e3a8b70972538f75c1ef1d3c4bc97375d78c3af472e52.

Reviewed guard maps are source/hash-bound. The query requires rule3..11,
complete path, output capacity, and three untouched left zero cells. Native
edge and comparator require their whole prepared-frame invariants. The writer
requires one of exactly four valid headers. Distinct unlinked returns are NOT
free extra working states or a single global halt; they must be linked into
an actual controller with preserved contracts. The 217/188 totals are valid
component-library counts, not complete blank-tape consistency machines.

## Comparator quotient wrappers

Independently checked every source row admitted by reviewer guard maps against
literal emitted wrappers: comparator29 to28 has 51 admitted rows; comparator27
to24 has 46. Entry projection and distinct EQ/NEQ ports pass. Their contracts
remain exactly the parent contracts, minimum loaded-counter gaps2 and3
respectively. No additional guard premise is used. These savings cannot be
counted again when a global quotient already makes the same identifications.

## Unreachable query role

Query127 is conservatively admitted on both symbols in this certified output.
Under the sole documented query entry, it can instead be given empty domain
once graph reachability using the admitted rows proves it unreachable. That
claim must be reconsidered if later linkage adds an external entry there.
Failure-state sharing has not been assumed or licensed.

## Final unreachable-role delta, independently checked

Final216 and final187 also pass every check above. The independent verifier
recomputes the admitted-row reachable set from ALL documented component
entries before narrowing any domain. Query127 is absent; its only incoming
literal edge is query124/read0, and query124 is proved forced1. It then checks
the saved reachability certificate and all projected rows again with the
empty query127 domain. This licenses its merge into query121 under the same
entry contract. The final hashes are:

- 216: a9277e69fd408225008c68bbf690c37881e918ac5ef52b431b0cf1c467237e7b
- 187: 041cc31a7c727a52b5cfea2de89aecd4efacc132cc1d1e94bfcaa668d9b504dc

These remain open-port libraries, with five/three distinct returns and
four/three distinct counted failures respectively.
