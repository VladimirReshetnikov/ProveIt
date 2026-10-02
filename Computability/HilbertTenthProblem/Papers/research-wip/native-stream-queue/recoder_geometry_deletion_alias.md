# Deleting the recoder geometry admits false dilation outputs

The recoder geometry cannot be replaced by its retained dyadic-scale and repunit conditions alone. The existing recoder AND component's dyadic scale and both exact repunit equations do not synchronize the repunit duration with the exponent of the input bound. For every width k>=2 and integer a>=k, the family below retains every outer recoder equation, strict positive outer bounds, the exact prescribed-AND semantics and positive native truth fields, but sends ordinary input x=1 to the incorrect output

    z=1+2^(k(k−1))=spread_k(1+2^(k−1)) != spread_k(1)=1.

The deleted geometry population condition excludes it. The [guarded checker](recoder_geometry_deletion_alias.py) and [receipt](recoder_geometry_deletion_alias.json) evaluate actual retained outer sources, including both the757 and754 width64 interfaces. Existing compilers remain unchanged. No universal-polynomial operation bound is improved.

## 1. Actual source obligations

The width-k recoder retains

    q=x+input_slack, Q=q^k, B=2^(k−1)Q,
    P=(B−1)J+1, S=qP,
    S=(2B−1)K+1,
    Ahat+Q=(Q−1)quotient_hat+z+2,
    z+output_slack=Q.

Its prescribed AND component has semantic arguments H=xJ,M=K,Z=Ahat−1 and scale S. The exact projection of that component is

    S is a positive power of two,
    0<=H,M<S, Z=H AND M.

All supplied outer coordinates are positive. The component's padded truth classes also have to be positive; those are checked explicitly below.

The source and theorem locations used are:

* [The arbitrary-width source](gpcp_fixed_program_input_bridge.py), `recoder(width)`, and [its proof, Section1](gpcp_fixed_program_input_bridge.md#1-arbitrary-fixed-block-width-with-every-power-paid), give the exact definitions, synchronization role and complete positive converse.
* [The literal width2 source](native_binary_input_dilation129.py), `build()`, and [its proof](native_binary_input_dilation129.md) supply the smallest example.
* [The prescribed-scale AND64 theorem](native_binary_masked_selection63.md#2-complete-and-projections-and-positive-domains) gives the retained component's exact projection and full positive Pell extension.
* [The frozen757 source](gpcp_index_linear_units757.py) and [the754 source](gpcp_coupled_index_units754.py) supply the actual width64 wrappers after their computed-coordinate and first-padding changes.

The script imports these sources and evaluates only the exact ancestor rows of the stated outer comparisons and AND scalar ports. It does not fill missing native Pell inputs with arbitrary placeholders or claim the unexecuted native comparisons vanish.

## 2. All integral duration aliases

Set q=2^a with a>=k>=2. Write

    b=ka+k−1, B=2^b, Q=2^(ka).

If the retained AND gives S=qP dyadic, then P is dyadic. The first repunit equation forces P=B^t for some integer t>=1, since 2^b−1 divides2^e−1 exactly when b divides e. Thus

    J=sum_(i=0..t−1) 2^(bi), popcount(J)=t.

The second repunit equation requires 2^(b+1)−1 to divide2^(a+bt)−1, equivalently

    a+bt=0 modulo b+1,
    t=a modulo b+1.

Since0<a<b+1, all its positive solutions are exactly

    t=a+h(b+1), h>=0,
    m=(a+bt)/(b+1)=a+hb,
    K=sum_(j=0..m−1) 2^((b+1)j).

The sound recoder chooses h=0. The retained equations alone allow every h>=0. The omitted condition q=2^popcount(J) would force2^a=2^t and therefore h=0.

## 3. The first extra period produces the false output

Choose h=1 and x=1. Then t=a+b+1 and m=a+b. A1 in J is at a position bi with0<=i<t; a1 in K is at position(b+1)j with0<=j<m. Since gcd(b,b+1)=1, their common positions are multiples of b(b+1). The inequalities0<a<b imply that exactly two such positions fit both finite words, namely0 and b(b+1). Consequently

    A=J AND K=1+2^(b(b+1)).

Modulo Q−1, exponents reduce modulo ka. Since b=ka+k−1,

    b(b+1)=k(k−1) modulo ka.

The assumption a>=k makes0<k(k−1)<ka. Thus the unique permitted positive output is

    z=1+2^(k(k−1)), 0<z<Q−1.

It is different from1 and is itself a correctly formed width-k dilation of the different input1+2^(k−1)<q. This is therefore not merely an out-of-range or malformed output.

Set

    Ahat=A+1,
    quotient_hat=(A−z)/(Q−1)+1,
    input_slack=q−1,
    output_slack=Q−z.

These are strictly positive integers and satisfy every displayed outer equality. Also J>B, J>=9, J>q and J is odd: the alias even respects these scalar geometry bounds if they are retained separately. Its geometry failure is the population equation, since popcount(J)=t>a.

## 4. The actual native AND inputs and positive truth classes

S=2^(a+bt) is dyadic. Both J and K are strictly positive and below S. Define the native fields exactly as in the prescribed-AND converse:

    F0=16*(S−1−(J OR K))+1,
    F1=16*(J−A)+4,
    F2=16*(K−A)+2,
    F3=16*A+8.

Since J,K<S and S is dyadic, J OR K<=S−1. Also A<=J,K. Thus every field is positive, even if an unpadded Boolean class is absent. Direct calculation gives

    F0+F1+F2+F3+1=16S,
    F1+F3=16J+12,
    F2+F3=16K+10.

These are the actual checksum and padded port comparisons; the source computes F3 from Ahat as16*Ahat−8. Hence the full prescribed-AND positive converse applies with precisely these scalar arguments. It existentially supplies all its positive private native coordinates, including the strong auxiliaries. The finite script does not materialize those enormous coordinates.

Accordingly this is a genuine obstruction to deleting the whole geometry component from the standalone complete recoder while retaining only its wrapper and prescribed AND: the retained component has a full positive extension by its already proved theorem. It is not merely a false tuple that could be rejected by the unchanged AND domain. This packet does not emit or cost a new mechanically deleted polynomial.

For both frozen757/754 first-padding versions the actual first padding is16J+13, so its difference from F1+F3 is1; the corresponding first-padding factor is+1. Its computed checksum factor is likewise+1. The exact current width64 source checks below establish this directly. This observation checks compatibility with the present scalar ports; it is not an assertion that all remaining compiled-history factors have been extended.

## 5. Exact small literal fixture

For k=2,a=2,h=1:

    q=4, Q=16, B=32,
    t=8, m=7,
    P=2^40=1099511627776,
    S=2^42,
    J=35468117025,
    K=69810262081,
    A=1+2^30=1073741825,
    Ahat=1073741826,
    z=5,
    quotient_hat=71582789,
    input_slack=3, output_slack=11.

The checker evaluates all five actual width2 outer comparisons, both actual padded AND ports, the actual computed F3 and prescribed checksum. They agree exactly. It independently checks A=J&K, positivity and the field equations. Geometry requires popcount(J)=2 but the literal J has8 one bits.

The correct output at x=1 is1;5 is spread2(3). The receipt includes the full small integer fixture and all four full truth-field integers.

## 6. Actual width64 fixture

For the actual sparse-TM input width, choose k=a=64. Then

    q=2^64, Q=2^4096, B=2^4159,
    t=4224, m=4223,
    P=2^17567616, S=2^17567680,
    A=1+2^17301440,
    z=1+2^4032=spread64(1+2^63).

The script computes the actual integers J,K,A and every stated outer coordinate exactly. It then evaluates38 literal ancestor rows from each frozen757 and754 source, checking:

* its retained mask-scale, output-congruence and output-bound comparisons;
* the additional paid input-word repunit `(2^64−1)*input_repunit+1=Q`, with positive `input_repunit=(Q−1)/(2^64−1)`;
* its retained second AND padding;
* its computed input bound and P;
* its actual prescribed native scale16S and computed F3;
* its current checksum and first-padding units, both exactly+1.

Every test passes, and the selected38 literal rows are identical in the two compilers. Their difference in native index targets lies outside these outer dependencies. The existing input-word repunit therefore does not remove the alias. The source's program/history comparisons are outside this evaluation. Receipt entries for the large numbers give exact bit lengths, populations and SHA256 digests of unsigned big-endian bytes rather than millions of printed digits. The exact integers are regenerated by the Python recipe.

## 7. Frozen-source guards and replay

All53 local source modules imported transitively by the selected emitters are pinned by an ordered filename/hash manifest. Its canonical JSON SHA256 is

    1bf4ae94bb2db40242baf547b78ac715aedf28592cc2d4108dff76f7a82bc00c.

The guard checks these file bytes before the imports and before constructing a new cached source. The receipt also records each dependency hash and each selected full-source hash. In particular, the frozen757 source is `a8b213386863857dae8c98f06a2ab41b297e05e6742b91217f538efaf7087774` and754 is `80c5f06ef5ec43975369ed2f9737fdf0d75b44e5abba4c24e19a2bc4fba1f9e3`. Paths resolve relative to the checker; no workspace-specific path is needed by the executable.

`fixture(k,a,h=1,compiled_stage=None)` requires exact integers, k=2 or k>=4, a>=k, and h exactly0 or1. The optional compiled stage is exactly integer757 or754 and requires k=64. Width3 is included in the elementary family proof but has no imported emitter selected by this API. `subset` accepts only exact list/tuple instruction containers, unique string registers, supported binary arithmetic, exact integer constants and assignments, and a valid acyclic source order. It evaluates only literal ancestors of the demanded targets. Unsupplied demanded leaves, floats, Booleans, malformed operators, forward references and cycles are rejected; supplying a computed register value cannot disguise a forward reference. `digest` requires an exact nonnegative integer. The public source manifest is returned independently from the immutable expected digest.

The receipt contains44 exact imported-source fixtures:20 ordinary h=0 controls and20 false h=1 aliases across widths2,4,5,8,16, plus both h cases at width64 for each frozen757/754 source. It records their selected outer instruction rows, comparisons, scalar byte hashes, truth-field byte hashes and population mismatch. It additionally checks28,425 exact exponent/divisibility cases using modular exponentiation and40 malformed calls. The earlier independent scout had41 fixtures; this packet adds the width64 control and both754 cases.

From the repository root, normal execution recomputes all evidence and compares it to the receipt without writing it:

```sh
/tmp/diophantine-research-venv/bin/python Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/recoder_geometry_deletion_alias.py
```

`--write` regenerates the author receipt. The expected status is `PASS_RECODER_GEOMETRY_DELETION_ALIAS`. Finite evidence checks the instantiated arithmetic; Sections2–4 prove the infinite alias family. Neither is represented as a materialized full native Pell zero.

Independent integration review replayed that receipt and checked 111 cases
using intersections of sparse bit-position sets instead of the author's
large-integer construction. This includes the actual width64 intersection
at positions 0 and 17301440 and its output residues at positions 0 and 4032.
The reviewer also checked the family proof and the positive truth-field
extension against the retained prescribed-AND theorem.

## 8. Existing corpus and scope

Targeted searches across `Computability/HilbertTenthProblem/Papers` for geometry deletion/removal/redundancy, repunit aliases, unsynchronized periods, wrong durations and the family formulas found no existing explicit version of this alias. The closest existing material is:

* `native_binary_input_dilation129.md` Section3 and `gpcp_fixed_program_input_bridge.md` Section1 already explain that the population equation synchronizes t with a; their checkers test synchronized geometries while retaining that equation.
* `native_binary_population_width_recoder.md`, lines150–168, explicitly warns that typing independent powers of two does not itself synchronize repunits. Its alternative proof keeps additional population and positive-gap information and remains unaffected.
* `native_binary_population_width_bound188` removes only an independently redundant private geometry bound, not the geometry kernel; it is not the rejected shortcut here.
* Existing nonpower row geometry and tag geometry investigations concern different encodings.

This is a scoped novelty assessment from the repository search, not a claim of literature priority or exhaustive absence from every source. The original independent scout remains session provenance at `/tmp/recoder_geometry_deletion_alias_scout.{py,json,md}`; it is not a dependency of this packet.

No complete Pell witness, complete deleted universal polynomial, accepting history for the false recoded input or full universal false-positive zero has been constructed. The positive AND extension is justified by the retained complete component theorem. A smaller replacement geometry may still exist, but it must exclude these extra-duration solutions or validate an equivalent input relation by another paid condition. This family only refutes treating dyadic qP and the two repunit equations as a sufficient replacement.
