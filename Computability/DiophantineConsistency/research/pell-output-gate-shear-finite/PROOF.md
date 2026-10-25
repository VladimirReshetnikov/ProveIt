# Complete finite verification contract for the fixed output-gate shear

This is CODE ONLY/HOLD. All statements about future checks describe the
source contract; no application has run and no output/receipt exists.
The exact ordinary theorem is the whole accepted
`research/pell-output-gate-shear` note, seal916d271f8e0433ba02753ce8082aa8f606d1d24509a226bdd9b9a478d905cbab,
jointly accepted in a3dc95494b after both complete ordinary reviews.
This file explains how every part is to be checked against actual whole
artifacts, not how selected successful examples might be extrapolated.

The INITIAL packet deliberately retains the author self-read finding
listed in README: guard.py's SOURCE literal names the absent successor
verification folder instead of the accepted neighbor parent. The pinned
inputs are the correct existing neighbor data; no unavailable successor
bytes are assumed or invented. This is an unresolved preparation defect,
not a failed application attempt. No code may run. Both full initial
reviews and this exact initial packet must be preserved before ROOT
separately releases a bounded correction and fresh final-seal reviews.
The complete remaining source/contract self-read found no second issue.

## 1. Algebra and arithmetic independence

Let a=z10,b=z11,c=z12,u=z21,p=z25,r=z27,v=z35,k=z36 and

    L=-2a-4b+2c+2u+2p, H=4a+5c+2p+r, W=8a+6c+2r, K=k-W-3.

Only x35=v-H changes. Since its four bases remain fixed, the complete
inverse adds H and both compositions are the identity on all Z^n.
The literal target is mul.137; fixed bases are crt.encoded.a,
crt.encoded.c,mul.64,mul.75 at10,12,25,27. No free parameter is exposed.

Producer substitution starts a coefficient c as the constant polynomial
and multiplies once for every monomial factor. A factor35 contributes
the whole five-term linear form; every other factor contributes itself.
Distribution and coefficient collection therefore implement the unique
Z-algebra homomorphism T. The producer then multiplies all ordered term
pairs in every row square, so its entire output is sum_j r_j(Tz)^2.

The checker uses no producer arithmetic. For q copies of35 it enumerates
nonnegative ia,ic,ip,ir,iv summing to q, with iv the remainder. The
coefficient multiplier is

    binom(q,ia) binom(q-ia,ic) binom(q-ia-ic,ip)
      binom(q-ia-ic-ip,ir) (4d)^ia (5d)^ic (2d)^ip d^ir,

and the new factors are a^ia c^ic p^ip r^ir v^iv. This is exactly the
five-way multinomial theorem; d=-1 gives T and d=1 its inverse. Indices
are sorted after replacement and coefficients collected, including
zeros and repeated input factors. q=0 is the identity term. Its SOS
uses each diagonal term pair once and each unordered off-diagonal pair
twice, independent of the producer's ordered-pair implementation.

The checker reconstructs ALL accepted parent rows and coefficients,
checks the entire old SOS and census, transforms every row, reconstructs
the whole new SOS, compares direct T substitution on the whole parent
quartic and reverses the whole result. For each actual saved equation
it separately compares every row and row metadata; for its actual saved
quartic it checks the complete SOS and the inverse on every coefficient.
Thus arithmetic and both integer zero-set directions cover the complete
objects rather than a table, digest or selected leading part alone.

## 2. All old occurrences, row formulas and local coefficients

Both complete old row lists must give35:{19,20} and
36:{20,59,90plain/91weighted}. The checker independently transcribes
the COMPLETE old rows19/20 as

    A=v-L^2+8L-12,
    B=k-(8a+10c+4p+2r+2v)^2-24a-26c-8p-6r-4v-3
     =K-4(v+H)^2-4(v+H).

The complete new formulas are A'=A-H and B'=K-4v^2-4v. It also checks
all terms of old k consumers59 and90/91. Exactly rows19/20 change;
every other216plain/215weighted row and its metadata is literal.
Old counts22/22 and new23/7 prove14 fewer residual term occurrences.

For s=v+H the exact whole difference has homogeneous parts

    Delta4=-16(s^4-v^4),
    Delta3=2HL^2-32(s^3-v^3)+8(k-W)(s^2-v^2),
    Delta2=-82Hv-39H^2-8WH-16HL+8kH,
    Delta1=Delta0=0.

The accepted proof contains every hand calculation, including the
constant cancellations. The checker transcribes every literal table
entry independently of producer arithmetic:70 quartics,95 cubics and26
quadratics,191 unique monomial keys;189 old nonzero and136 new nonzero.
The95 cubic cells include the20 a/c/p/r,30 changed b/u, six unchanged
b/u,15 v, nine unchanged b/u-v and15 k cells. Weighted ab^2 alone adds2
to both columns. The whole before/after actual subsets must equal these
entire dictionaries. ALL coefficients outside their complete key union
must agree exactly. Linear and constant parts additionally agree in full.

The actual old support minus new must have55 terms, by degrees1quadratic,
19cubic,35quartic; the only additions must be ur=[21,27] and
upr=[21,25,27]. Net53 and support5728plain/5734weighted are checked on
actual whole data. No coefficientwise nonincrease is asserted: e.g.
a^2b and abp explicitly grow in magnitude. Degree4 and every coordinate
live are computed from the complete output, not inferred from counts.

## 3. Entire height, row height and census

The full old list must have exactly three quartic coefficients above
54709 in absolute value:57172a^3c,93109a^2c^2,71162ac^3. The ordinary
tables give36692,54709,39162, and every coefficient is bounded at its
whole degree:0<=2674,1<=2116,2<=10576,3<=48942,4<=54709 in absolute
value. Those bounds are checked on EVERY actual coefficient. The
54709 witness is required, as are the pure fourth liveness witnesses
12716,16365,640,848 at a,c,p,r.

The old full row lists must have exactly the single above128 entry
-160ac in row20. The replacement rows have exact heights32/8 and
unchanged row12 retains-128ac. Every output row, polynomial coefficient,
degree cell, support, height, row degree/height and live-coordinate list
is independently recounted. The full prospective term censuses are
(1,112,809,1388,3418) plain and(1,112,808,1390,3423) weighted. Their
totals5728/5734, exact degree4, row degree<=2, height54709, row height128
and used-coordinate sets0..315/0..314 are explicit additional gates.
These source gates do not constitute observed metrics before execution.

## 4. Canonical13-artifact and witness-map contract

Both equation objects preserve their entire old metadata except the
explicit chart variant suffix and term lists. Every variable and row
label is retained. Expanded headers are retained in full. Actual term
coefficients and indices require type(...) is int, excluding bool and
float; out-of-range indices fail. Normalization allows valid equivalent
private presentations, whereas real saved terms must exactly match the
unique sorted nonzero serialization. Every saved JSON file must equal
its complete canonical encoding. Duplicate keys and nonfinite numbers
are rejected at read time. Every whole artifact and expected field set
is checked; canonical JSON equality distinguishes integer and float.

The certificate binds the five forward/inverse terms, literal names,
source/output, complete occurrences/changed rows and ordinary seal. The
maps embed the entire accepted neighbor maps, endpoint and certificate.
Exact whole comparisons retain T then N then S then58 shifts then83
free initializations then204plain/203weighted monic restorations then
mandatory Horn private overwrite then the whole source calibration.
Only shears/translation are whole-space bijections; older private maps
retain existential meaning. Source signs/calibration apply to the
recovered old tuple, not directly to the new chart.

Each endpoint binds the other five complete profile objects, ordinary
and accepted neighbor seals, parent INDEX and entire source calibration.
INDEX binds all12 profile objects and exact source pins/build/check/guard.
Its own hash is bound only by the outside report, avoiding a hash cycle.
The source131/Round15/C222/ZF-to-ZFC/native, fresh interval and Hstar/H0
boundaries, absence of old324/old327 identities and absence of fresh
compiler/native/Lean replay remain exact. The old optimized143 remains
unresolved. The observed34-file old source gets no new MANIFEST.

## 5. All128 actual-artifact negative controls

Each of the following64 cases runs for each profile. Each starts from a
deep copy of the ACTUAL loaded thirteen-object bundle, mutates an actual
field, requires a nontrivial object change, and rebinds only outer chart,
profile-file and INDEX byte records. It never repairs a mathematical,
policy, census or source field. The same complete verification path must
raise ValueError with exactly the listed reason. Schema, source and
coverage cases are contract checks and need not change a zero set.

| Case name | Required reason |
| --- | --- |
| wrong_direction_first_row | forward row identity |
| wrong_direction_second_row | forward row identity |
| mixed_sign_actual_row | forward row identity |
| wrong_gate_actual_row | forward row identity |
| missing_whole_row | complete row count |
| missing_actual_term | forward row identity |
| unchanged_row_corruption | forward row identity |
| preceding_row_corruption | forward row identity |
| row_label | row metadata |
| integer_domain | equation metadata |
| literal_name | equation metadata |
| boolean_coefficient | integer coefficient |
| float_coefficient | integer coefficient |
| boolean_index | integer index |
| out_of_range_index | integer index |
| quartic_coefficient | full SOS coefficient identity |
| dropped_quartic_term | full SOS coefficient identity |
| boolean_quartic_coefficient | integer coefficient |
| quartic_header | expanded metadata |
| certificate_schema | shear schema |
| direction_convention | shear convention |
| inverse_convention | shear inverse convention |
| first_forward_sign | shear direction |
| second_forward_sign | shear direction |
| inverse_map_sign | shear inverse |
| wrong_gate_schema | shear policy |
| boolean_gate_schema | shear policy |
| stale_input_binding | shear input binding |
| changed_row_coverage | shear changed coverage |
| occurrence_coverage | shear occurrence coverage |
| ordinary_proof_binding | shear ordinary binding |
| inverse_map_order | complete composed maps |
| free_coordinate_omission | complete composed maps |
| monic_restoration | complete composed maps |
| parent_balanced_map_sign | complete composed maps |
| source_calibration | complete composed maps |
| native_rerun_claim | complete composed maps |
| whole_height_census | complete census |
| support_census | complete census |
| row_height_census | complete census |
| float_degree_census | complete census |
| endpoint_calibration | complete endpoint binding |
| endpoint_parent_binding | complete endpoint binding |
| index_schema | data index schema |
| index_search | data index policy |
| index_combined_family | data index policy |
| third_forward_sign | shear direction |
| fourth_forward_sign | shear direction |
| missing_forward_term | shear direction |
| wrong_forward_base_index | shear direction |
| wrong_inverse_target_index | shear inverse |
| alternative_shear_family | shear policy |
| restore_deleted_quartic | full SOS coefficient identity |
| omit_introduced_cubic | full SOS coefficient identity |
| omit_introduced_quadratic | full SOS coefficient identity |
| outside_support_corruption | full SOS coefficient identity |
| output_occurrence_coverage | shear occurrence coverage |
| parent_neighbor_map_sign | complete composed maps |
| parent_neighbor_certificate | complete composed maps |
| endpoint_optimality_claim | complete endpoint binding |
| private_tuple_identity_claim | complete composed maps |
| ordinary_proof_length_binding | shear ordinary binding |
| pure_target_quartic_corruption | full SOS coefficient identity |
| omit_new_inverse_step | complete composed maps |

The first46 retain every prior neighbor control role, adapted to this
fixed map and its extra parent layer. The final18 exercise the new four
base coefficients/target/policy, deleted acpr, introduced upr/ur, outside
table support, output-consumer coverage and the newly prefixed inverse
step/whole-parent maps. Exact mutation paths and values are literal in
check.py; loops deep-copy their captured values and do not mutate inputs.

All12 valid controls use the same semantic path: per profile,
row_reorder, row_split_coefficient, row_cancel_pair, quartic_reorder,
quartic_split_coefficient and quartic_cancel_pair. Row operations use
actual changed19/20; cancel pairs are exact opposites on the same
monomial. Quartic operations similarly preserve the full polynomial.
Canonical saved ordering is tested separately on the original actual
artifacts, permitting these equivalent private forms without suppressing
row/SOS/forward/inverse/table/census/map/source checks. Complete control
counts are explicit runtime requirements retained under -O.

## 6. Authentication, external I/O and held chronology

Both entry points disable bytecode writes, read the entire held inventory
and hash every payload BEFORE the sole local guard import. The guard has
no polynomial arithmetic and reauthenticates the exact eight-file held
set, own core, every external input and every whole source member set.
All existing source bytes remain fixed around arithmetic and I/O. The
outside statically reviewed HOLD digest is the trust anchor; a self-hash
inventory alone is not an independent signature or execution release.

Only the reviewed absent /tmp data directory may be created, with exactly
13 exclusively written files. All paths are absolute, outside the whole
repository and nonsymlink through every component. Check/rebuild modes
read exact existing data only. Both pure rebuilds reproduce every object
independently in memory and compare whole canonical bytes, writing only
their exclusive receipts. Normal materialization has no fresh build
path. Every read-only role has separate first/fresh fixed allowlisted
receipts from the initial seal. No receipt records the pathname or first/
fresh status, allowing exact same-mode byte comparison.

TOOLCHAIN gives exactly nine planned commands and all27 capture paths.
All28 outputs including the data folder must be absent before the first
run. Two complete final-seal static approvals and a separate ROOT release
are required for the first five. Fresh four require another release.
Every command must return actual exit0 with complete PASS JSON equal to
entire stdout before continuing; preserve stderr/warnings even if empty.
Stop first failure/interruption without repair/retry/deletion/reseal.
Final inert evidence closure and endpoint acceptance need later decisions.
No new data, execution result, page gain or endpoint is asserted here.
