# Reparameterizing the paid program frame gives a 741-operation U15 polynomial

The complete GPCP-based U15 compiler now has a **741=347M+394A** polynomial, with three positive program parameters, ordinary positive input x, and the same122 positive existential coordinates as its computed-input744 parent. The certificate has718=339M+379A operations and eight comparisons. Its exact formal degree is **11237**, down from187625. The supplied-initial-value variant costs744=348M+396A with123 witnesses, nine comparisons and degree8481.

The change replaces seven paid frame operations with four. It retains the input recoder, the64-bit input-block geometry, the fixed57-tile U15 history, every native bound and sign argument, the computed history fields, and the complete integer-product finalizer. It changes the meaning and names of the three program parameters by an explicit positive formula. Corresponding positive program triples have exactly the same auxiliary positive zero sets. Arbitrary new parameter triples are not asserted to encode old programs, and there is no bijection between all old/new parameter tuples.

This improves the GPCP-based U15 route. The direct binary-tape route and other reviewed universal constructions are separate alternatives; the overall87-operation universal polynomial bound is unchanged.

## 1. Exact parent and literal private interface

The parent is `gpcp_history_computed_fields744.py`, SHA-256
`da3ec5d08068a9fcfa783f1ed0b0d97b2f2aa5b33cc63c218f003716b347f1ef`.
The transformer accepts only one of its eight complete exact-type canonical packets, determined by Boolean `inline_initial`, `and_bounds`, and `geometry_bounds`. The parent hash and its own ancestor guard are checked before use. Every current program/history descriptor is retained; ancestral projection/fiber claims are not copied as statements about741.

Let the old positive program parameters be

    p=program_prefix,
    a=program_suffix_scale,
    b=program_suffix_value.

The actual fixed block constants are

    M=2^64−1=18446744073709551615,
    c0=1229782938247565589,
    c1=1230908838154146069,
    δ=c1−c0=1125899906580480 > 0.

The unchanged repunit source is

    input_repunit_scaled=M*input_repunit,
    input_repunit_power=input_repunit_scaled+1,
    input_repunit_power=Q.                           (1)

Write J0 for the supplied `input_repunit`; it is distinct from the native geometry's `J`. The seven actual old frame rows are

    zero_blocks=c0*J0,
    one_correction=δ*z,
    encoded_body=zero_blocks+one_correction,
    framed_prefix=p*Q,
    framed_body=framed_prefix+encoded_body,
    framed_scaled=a*framed_body,
    input_bottom=framed_scaled+b.                    (2)

The guarded rewrite verifies every row, all private consumer sets, the literal repunit comparison and the complete old program-parameter list. The first six rows in(2) occur in no comparison and have no consumers outside(2). Each old program parameter occurs only in its indicated frame row.

The seventh register, `input_bottom`, is the intentional shared interface. In the computed-input variant its only source consumers are

    hist__height_sum__0=Ufinal+input_bottom,
    hist__V_lhs__316=hist__V_update__315+input_bottom.

In the supplied-input variant it has no source consumers and occurs only in the comparison `input_bottom=Vinitial`. That comparison remains. The rewrite checks both cases explicitly.

## 2. New positive program recipe and four operations

Replace the three supplied program numbers by

    A=a(pM+c0),     B=aδ,     C=ap+b.                 (3)

Their public names are `program_repunit_coefficient`, `program_bit_coefficient`, and `program_offset`. All are strictly positive for every positive old triple p,a,b. They are fixed program numerals when choosing a represented language. Formula(3) is part of the effective program-to-parameter recipe, not an extra online arithmetic subroutine in polynomial evaluation.

Compute the new interface with four paid rows:

    frame_repunit_term=A*J0,
    frame_bit_term=B*z,
    frame_partial=frame_repunit_term+frame_bit_term,
    input_bottom=frame_partial+C.                    (4)

Thus its value is positive on every supplied positive tuple, before any recoder or history equation is used. This preserves the parent's positive computed-initial-value precondition.

Equation(1) gives Q=MJ0+1. Substitution in(2) proves

    a(pQ+c0J0+δz)+b
      =a(pM+c0)J0+aδz+ap+b
      =AJ0+Bz+C.                                    (5)

Every other source row, comparison and unit factor is literally unchanged, once its operands use this shared `input_bottom`. The seven old rows cost4M+3A; the four new ones cost2M+2A. The saving is therefore exactly **2M+1A**, in both the certificate and complete polynomial. No comparison or supplied existential coordinate is deleted.

The old program triple can be recovered on the positive image of(3): B must be divisible by δ, giving a=B/δ>0; A must be divisible by a, and `(A/a−c0)` by M, giving p>0; then b=C−ap must be positive. These conditions characterize that image, and `decode_program` checks them exactly. They are an external proof/API utility, not extra constraints or uncharged operations in the new polynomial. For example arbitrary positive A=B=C=1 is outside the image. No parent-program meaning is claimed there.

## 3. Complete positive zero-set transfer and universality

Fix any positive old triple `(p,a,b)`, and the corresponding positive new triple(A,B,C) from(3). Keep x and every existential coordinate unchanged.

Both complete sources use the exact final form

    F=W(1+S)−1,
    S=Σ ordinary_residual_i²,

where W is the integer product of the retained unit factors. On any integer zero, S≥0 and W is an integer, so `W(1+S)=1` forces S=0 and W=1. In particular every ordinary comparison holds, including(1). This conclusion does not require a premature sign assumption on any individual native factor.

At a positive zero of either source, (5) therefore makes the two computed initial interfaces equal. The privacy checks from§1 then imply by source-DAG induction that every retained downstream register, comparison residual and unit factor is equal. Thus the other complete polynomial is also zero, on the same positive existential tuple. This proves **equality of the auxiliary positive zero sets at every pair of positive parameter triples linked by(3)**. The argument works for all eight bound/initial-interface configurations; it is not restricted to only those old triples describing well-formed programs.

For a c.e. set S, the already proved744 construction effectively supplies one valid old program triple `(p_S,a_S,b_S)` whose positive existential projection is x∈S on ordinary positive x. Choose its image by(3). The equality just proved yields

    x∈S  iff  ∃ y>0: F741(x,A_S,B_S,C_S,y)=0.

The fixed U15 table, prefix code, paired binary input convention, leading-zero padding and accepting cleanup are all inherited. In particular there is no new free bit recoding, no switch to raw half-tape inputs, and no new source-machine universality claim. The underlying primary machine remains [Neary–Woods, Four Small Universal Turing Machines](https://dna.hamilton.ie/assets/dw/NearyWoods-FI09.pdf), Table16 and the simulation/input construction already used by the parent. The production language proof uses the existing repository ordinary-input theorem, not the finite word fixtures below.

## 4. Exact off-zero identity, with the interface override stated

The full old and new polynomials are generally different on arbitrary integer tuples, even after mapping the parameters. Put

    r=Q−MJ0−1.

For every signed integer assignment to the old supplied coordinates, direct expansion gives

    Vold−Vnew=ap r.                                  (6)

Let `G(x,y,V)` be the common downstream source with `input_bottom` replaced by a supplied scalar V; it retains the same recoder, comparisons, unit factors and complete finalizer. In the supplied-input variant, G retains the comparison `V=Vinitial` and the independent supplied Vinitial used inside the history. The private-consumer audit proves exact polynomial identities

    Fold(x,p,a,b,y)=G(x,y,Vold),
    Fnew(x,A,B,C,y)=G(x,y,Vnew),
    Fold−Fnew=G(x,y,Vnew+ap r)−G(x,y,Vnew),            (7)

when A,B,C are obtained by the formal polynomial map(3). Equation(7) is division-free, and it makes the dependency on the retained repunit residual explicit. It does not assert that the new witness tuple makes that residual vanish off zero.

The API checks both useful forms:

- `interface_identity(packet,new_values)` executes the complete child polynomial and the complete parent schedule with `input_bottom` explicitly overridden to the child's computed value. It compares every common register and both outputs. That modified parent execution is labeled an interface experiment, not an evaluation of the original parent polynomial.
- `parameter_correction(packet,old_values)` executes the actual old and mapped new polynomials, verifies(6), then reexecutes the child with its initial value corrected by ap r. All common registers and full output agree with the actual parent. If r=0, the two actual unmodified polynomials agree too.

The public `map_assignment` is the exact signed polynomial parameter map, with every other supplied coordinate retained. Positivity of the mapped parameters is asserted only for positive old triples. There is no unconstrained child-to-parent assignment map, and no inherited744→754 two-fiber statement is asserted about this program-parameter transformation.

## 5. Complete counts and formal degrees

Both initial interfaces, both AND-bound choices and both geometry-bound choices are retained. “Computed” aliases the initial history value to the new positive expression(4); “supplied” retains Vinitial and its equality comparison.

| Initial | AND bound units | Geometry bound units | Polynomial operations | Certificate operations | Comparisons | Witnesses | Exact degree |
|---|---|---|---:|---:|---:|---:|---:|
| Supplied | No | No |748=348M+400A|710|13|123|8631|
| Supplied | No | Yes |746=348M+398A|714|11|123|8697|
| Supplied | Yes | No |746=348M+398A|714|11|123|8415|
| Supplied | Yes | Yes |744=348M+396A|718|9|123|8481|
| Computed | No | No |745=347M+398A|710|12|122|11660|
| Computed | No | Yes |743=347M+396A|714|10|122|11726|
| Computed | Yes | No |743=347M+396A|714|10|122|11171|
| Computed | Yes | Yes |741=347M+394A|718|8|122|11237|

These formal degrees treat the three *new* program parameters as independent variables and are measured before specializing a represented language. They are not asserted to be the exact degree after every possible numerical program specialization.

The old computed `input_bottom` has formal degree66 because of p·Q and the outer factor a; the new one has degree2. This changes the history height/geometry degrees and explains the large degree reduction in computed-input forms. Supplied-input forms retain their old degree because the history still sees the independent degree-one Vinitial.

`degree_dictionary` propagates the complete emitted polynomial, including its finalizer. It uses the parent's three literal, fully guarded main-norm expansions to account for their highest cancellation, then recomputes every downstream bound. The source evaluates the resulting top homogeneous forms at explicit integer weights modulo each of1000000007 and1000000009. Every unit-factor leader and the final output leader is nonzero. These16 stored certificates prove that the propagated bound is attained in all eight forms; no mere max-degree heuristic is called exact.

## 6. Guarded APIs, source closure and evidence

Public APIs are `build`, `canonical_parent`, `rewrite`, `checked`, `polynomial_source`, `ledger`, `degree_audit`, `evaluate`, `transform_program`, `decode_program`, `map_assignment`, `interface_identity`, and `parameter_correction`. The three build options are exact Booleans. Packets are checked by type-sensitive equality against the entire cached canonical object, including program/history metadata. Assignment maps require every exact integer key/value prescribed by that interface. Public build and parent accessors return deep copies; the source's private caches are not exposed through those APIs.

The writer and a fresh default replay passed on source SHA-256
`2785d8e318f253484346f8a55cda6fdb39e7dc1eb83d1a4ce361df66a857063a`.
The deterministic receipt SHA-256 is
`16bb6a0cba5d8ca8bc8b7a9c3369711f2668bc57c5ef8d27f41ab78897b0bafb`.
It stores all eight complete polynomial sources, parameter/witness lists, comparisons, factors, count ledgers, privacy descriptions and degree certificates.

The maintained replay checks:

- 96 complete signed/positive interface-override identities and96 parameter-correction identities, with48 signed cases in each family;
- 31 zero-repunit cases where the actual old/mapped new polynomials agree, and38 cases where their actual off-zero outputs differ;
- 216 positive parameter-image/decode roundtrips;
- all eight full source closures: every emitted gate reaches the output and every supplied coordinate is active;
- 494 malformed-caller rejections, including Boolean/float numerals, unsupported options, missing/extra assignment keys, tampered source/history metadata and a400-digit-input coefficient-type regression;
- 16 public nested-copy checks protecting both canonical caches.

A separate bounded checker, [check_gpcp741_program_words.py](check_gpcp741_program_words.py)
([receipt](check_gpcp741_program_words.json)), passed124 literal encoded-word comparisons using the actual existing sparse-U15 program recipe, its current prefix code and both padded input-block values. It compares the complete sentinel word with the old and new frame formulas. This is supplementary input-frame evidence, not a materialized native Pell solution or a fresh proof that those test programs recognize arbitrary c.e. languages.

Run `python gpcp_program_frame741.py --write` to regenerate its adjacent receipt; the default compares it. No full enormous positive native witness is materialized by these tests. The complete positive extension and universality are transferred from the guarded parent by§3.

The module explicitly refuses Python `-O` and `-OO` before importing guarded dependencies, because its complete canonical-source and type checks use assertions. Both optimized-import rejection paths were checked separately; normal source, operation counts and mathematical maps are unchanged.
