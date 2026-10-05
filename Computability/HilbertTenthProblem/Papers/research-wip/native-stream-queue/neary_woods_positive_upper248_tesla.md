# A positive selected upper history gives a complete U9 compiler in248 operations

The corrected geometry-scaled249 U9 source has a **248=129M+119A**
successor with the same **43 positive witnesses**, ordinary positive
input and four fixed positive program parameters. The separate fifth
duration-parameter interface has the same cost. The total degree is
**at most936**. Time remains existential and unbounded, with all input,
program, native, chronology and endpoint arithmetic paid.

The saving is one addition in a shared packed-word correction. Every
genuine nonempty matching tile word uses a b-upper tile, making its
selected upper-history word strictly positive. Supplying that word
directly allows two packs to use the same shorter correction and an
already paid group subtraction. The inverse global slack is proved
positive only after independent native typing. The result is a bijection
of complete positive zero tuples on valid inherited U9 program slices;
it is not an unconditional positive coordinate change.

## 1. Positive selected words on the actual language

Keep the accepted four-tile order

    0=P_c, 1=P_b, 2=D_b, 3=D_c.

The exceptional upper group is `{1,2}`. For a correctly typed history,
write `U_j` for its upper affine state and `S_i` for its selector words.
The upper state starts at1; all four upper affine maps have positive
slope and positive offset, so every `U_j>=1`. Its selected word is

    ZU=sum_j [tile_j in {1,2}]*U_j*b^j.             (1)

Thus ZU is strictly positive as soon as one b-upper tile occurs.

Here is a word-level proof of that occurrence, independent of any paid
integer representation. The accepted binary-tag theorem defines

    e(b)=1 0^beta 1, e(c)=1,
    h(s) 1 0^beta = E(w) g(s), beta>=2,             (2)

with input w and production words ending in b. Every nonempty match
has T>=1 production/deletion blocks. Its exact decoded word equation is

    d_1 ... d_T b = w v_1 ... v_T,                 (3)

where each v_i is b or the production u and hence contains a b. If
there were no b-upper tile, every d_i would consist entirely of c, so
the left side of(3) would contain exactly one b. The right side contains
at least T+1 b's. This contradiction proves ZU>0 for every such nonempty
matching history. This uses the word equation; it does not incorrectly
assert that every tile block remains a legal tag transition after the
first short queue. The inherited soundness conclusion is halting.

For the actual U9 slice there is also a shorter direct check. The loaded
tag word ends in u, and the pinned fixed U9 production begins bcb.
Consequently E(w) already has at least two zero runs, separated by ones.
If every upper tile were c, the left side of(2) would have only its final
zero run. Concatenating g(s) cannot erase the earlier two runs on the
right. Thus (2) cannot hold. The inherited U9 compiler uses the nonempty
matching-history branch; existence is asserted only at a zero or for an
accepted input. Its ordinary input and fixed terminal convention are unchanged.

## 2. The actual one-row saving and affine identity

Use the geometry-only scaled249 source, with its degree correction936.
Rename its positive supplied `hist__ZUhat0` to `hist__ZU0`, here ZU.
Write g for `hist__global_bound`. The intended old coordinates are

    ZUhat_old=ZU+1,     g_old=g-1.                  (4)

All other supplied coordinates are identical. The old global sum and
the new one agree identically under(4):

    P_old=HU+HV+ZUhat_old+ZVhat0+ZVhat1+g_old
         =HU+HV+ZU+ZVhat0+ZVhat1+g=P_new.          (5)

The inherited fixed upper slope difference and constant are

    upper_difference=2^(beta+2)-2,
    upper_constant_old=2^(beta+3)+2.

Change only that constant recipe to

    upper_constant_new=2^(beta+2)+4.              (6)

The identity `upper_constant_old=upper_constant_new+upper_difference`
compensates exactly for replacing ZUhat_old by ZU in its paid upper
linear coefficient. There is no runtime subtraction between fixed
numerals. The same one multiplication by upper_difference and one
subtraction of upper_constant remain paid. All eleven numeral roles
remain, and the complete fixed U9 recipe otherwise stays literal.

For the two selected packs, let `S_i=Shat_i-1`,
`G12=S1+S2` and `G03=S0+S3`. In the parent the already paid rows give

    group_hat=Shat1+Shat2-1,
    tree_group12=Shat1+Shat2-2,
    tail_old=P^2+P+1.

Replace the shared tail by `tail_new=P^2+P`, use `tree_group12` in
the upper pack, and delete the now-private group_hat subtraction.
The exact invariant packs are

    Ctree_old=group_hat+P*(Shat0+P*Shat1)-tail_old
             =G12+P*S0+P^2*S1
             =tree_group12+P*(Shat0+P*Shat1)-tail_new;

    Zb_old=ZUhat_old+P*(ZVhat0+P*ZVhat1)-tail_old
           =ZU+P*(ZVhat0-1)+P^2*(ZVhat1-1)
           =ZU+P*(ZVhat0+P*ZVhat1)-tail_new.       (7)

No new row computes tree_group12; its existing subtraction is moved
earlier in the topological order. The deleted group_hat had just the
one pack consumer. The shared tail has just the two displayed pack
consumers. The old ZUhat occurs only in the global sum, upper selected
coefficient and Zb pack. The receipt guards those exact consumer sets.

Equations(5)--(7) and the upper-linear identity make all exits of the
changed cones identical. Every other producer, factor and finalizer
remains the same. Hence the entire polynomial satisfies the all-ring
pullback

    F248(new)=F249_geo(ZUhat=ZU+1,g_old=g-1,others), (8)

with the fixed-numeral relation in(6). If numerals are treated as formal
independent ports, that relation is part of the substitution; identical
arbitrary upper_constant ports are not asserted to work. On the actual
compiled recipes the relation is exact.

## 3. Positive inverse without circular parent invocation

At a positive child zero, (4) gives ZUhat_old>=2 but only
g_old>=0. We therefore do not invoke the complete parent positive-zero
theorem yet. The geometry discriminant is unchanged and strictly
positive on all such tuples. The scaled finalizer can be cancelled, and
the sixteen parent-form integer factors are consequently units.

The only former use of g_old in the pretyping estimates was through
the global sum P and its positive lower bounds. The child supplies six
strictly positive summands in(5), so P>=6. Each history and each selected
word is below P; even the virtual old hat `ZU+1` is below P because
`P-ZU>=5` gives `P-(ZU+1)>=4`. Every other
old hat is likewise below P. Therefore the unchanged signed repunit
factor gives, before any bit typing,

    P=(b-1)J+epsilon_G, epsilon_G in {-1,1},
    b=c_h D, c_h>=32, D>=1,
    J>=1, J<=P/6, b<=P+2, 0<=(D-1)J<P.           (9)

The unchanged hierarchy mask is still

    Mtree=J+P*(J+(b-1)J*G12),

including its negative-repunit correction. The child Ctree and Zb in(7)
have exactly the same nonnegative meaning as before. Thus the complete
250 scalar proof applies with its hypotheses checked directly: both
repunit signs and D=1 are allowed, all lower blocks lie below P^8, the
joined truth fields are positive with residues1,4,2,8 and sum q-1, and
all native index/ratio hypotheses hold. This uses no positivity of g_old.

Apply the accepted individual native recovery and sign arguments in
their established order, before invoking the complete parent theorem:
norm signs, rank, coupled-linear sign, joint population/index sign,
dyadic factor recovery, geometry/low-mask signs, then the history
Mersenne sign. This gives

    epsilon_G=1, P=b^T, T>=1,
    J=1+b+...+b^(T-1),
    0<=U_j,V_j<D,

and the exact hierarchical selector partition and selected products.
These statements follow from the same literal native factors and the
unchanged pack exits (7). They precede the ordinary chronological
endpoint proof; no old full compiler is assumed at a tuple with g_old=0.

The selected upper word obeys ZU<=HU. The two lower selected words have
disjoint selectors0 and1, so `ZV0+ZV1<=HV`. The new global slack is
therefore

    g=P-HU-HV-ZU-ZV0-ZV1-2
      >=P-2HU-2HV-2
      >=((c_h-4)D+3)J-1
      >=30.                                      (10)

Here `HU,HV<=(D-1)J`, directly from the recovered ranges. This proves
`g_old=g-1>=29>0`. Every virtual parent coordinate is now positive.
Equation(8) is therefore an actual positive parent zero, on the same
ordinary input and valid program slice. The full parent theorem supplies
its genuine word match, chronology/halting conclusion and all endpoint
conditions. There is no additional native reconstruction.

## 4. Complete forward map and exact universal quantifiers

Conversely take any positive249 zero on a valid inherited U9 slice. The
parent theorem gives a nonempty matching four-tile word. Section1 proves
that its upper selected word is strictly positive. Set

    ZU_new=ZUhat_old-1>0,     g_new=g_old+1>0,

and leave every other coordinate fixed. The fixed constants obey(6),
and (8) then gives a child zero. These two maps are inverse. They retain
the raw input, program tuple, durations, heights, geometry and joint
native coordinates; only the two displayed positive witnesses shift.

Consequently for every recursively enumerable set S of positive
integers, the same effective valid shifted four-program-parameter tuple
and the adjusted fixed numeral recipe(6) give

    x in S iff exists w1,...,w43>0:
        F248(x,A_S,B_S,T_S,E'_S,w1,...,w43)=0.

The optional fifth fixed duration parameter retains its inherited
meaning. There is no externally supplied word length, native oracle,
input exponent, controller sequence or free iteration. The ordinary
loader still represents the actual fixed U9 machine and its exact counter.
The separate universal84 bound is unchanged.

**Remark 1 (the inverse is not positive off zero).** The claim that(4)
maps every positive child tuple into the positive parent domain is false:
at g_new=1 it gives g_old=0. For example take g_new=ZU_new=1 and every
other supplied variable positive. This is an off-zero domain example,
not a child zero or a compiler counterexample. The independent typing
and quantitative bound(10) are necessary to establish the inverse.

**Remark 2 (strict positivity is not a generic mask assumption).** A
typed selector group can be empty: `J=1,S0=1,S1=S2=S3=0` has G12=0
and selected ZU=0 for any positive one-row upper history. This is a
selector-interface example, not a matching U9 computation. Requiring
ZU>0 without Section1's matching-word argument would wrongly restrict
arbitrary affine-history predicates. No such unrestricted extension is
claimed here.

**Remark 3 (retained existence-quantifier correction).** The draft sentence
"The valid U9 loader has a nonempty matching history" was too strong
without an acceptance or zero hypothesis. A valid program for the empty
recursively enumerable language has no matching history on any ordinary
positive input, by the inherited compiler soundness theorem. The correct
statement in Section1 specifies the nonempty-history branch used by the
compiler, not unconditional existence on rejecting inputs.

**Remark 4 (retained unit-quantifier correction).** The draft opening
"At an arbitrary positive child tuple" incorrectly preceded the deduction
that the sixteen unscaled parent-form factors are units. Geometry
positivity does hold on every positive tuple; the unit deduction also
requires the child equation F248=0. For explicit symbolic counterevidence,
the native first factor is `tau_gap^2+4E*kY*(tau_gap-k)`. Taking the
positive coordinates eta=zeta=tau_gap=1 gives k=eta+zeta=2 and factor
`1-8EY<-1`, since E,Y>0. This is an off-zero factor calculation, not a
source-array evaluation or a compiler zero. Section3 now begins at a
positive child zero, and only there cancels the positive discriminant.

## 5. Complete counts, degree and verification scope

Each of the two saved sources contains248 live rows:129 multiplications
and119 additions/subtractions. Its certificate before the final
subtraction costs247=129M+118A, with one comparison to the already paid
geometry discriminant. The43 witness count is unchanged. Each source
has243 literal retained row records, five edited records and one deleted
row, with no new rows. One literal retained record uses the changed fixed
upper_constant recipe; literal record equality does not conceal that
coefficient change. All eleven numeral roles and every supplied port
remain live. The joint-only and both-core249 variants are not reoptimized.

The parent geometry-only bound is the corrected936, not its superseded
934 claim. The map(4) is affine in supplied coordinates and(6) changes
only fixed degree-zero numerals. Equation(8) thus gives total degree at
most936 directly. No source-array degree propagation, exact-degree
claim or global optimality statement is used.

The full249 proof and its correction, the complete250 proof, and the
literal two geometry-scaled249 arrays were read inertly. The binary-tag
word/affine proof lines1-230, actual U9 chain lines1-200 and initial-bound
proof lines1-185 provide the selected language and pretyping interfaces.
All older machine/Pell/complete native theorems retain their accepted
scopes. The repository census found no prior positive-ZU packing change;
this is a restricted search of the relevant current U9 notes, not a
novelty claim across the literature.

Fresh evidence consists of static complete-source editing and liveness,
four independently handwritten sparse-polynomial cuts, signed scalar
prefix bounds and a small word zero-run diagnostic. It neither evaluates
a parent/child array nor materializes an actual U9 or native Pell zero.
The helper imports no supplied, frozen, archived or predecessor program.
Only the author's new diagnostics run before freezing. No repository or
Git mutation is made; independent reviews are separate records.

The fresh author helper and saved receipt were compared in normal and
optimized Python modes from `/` before freezing, both PASS. They record
two complete248-row sources (496 rows), four handwritten polynomial-cut
identities, 1,428 signed scalar prefix contexts (including714 negative
repunit contexts and476 height-one contexts), and171 small word zero-run
examples. These bounded diagnostics support the displayed identities and
bounds; they do not replace the all-size proof above. No frozen program
was run and no saved source array was evaluated.

Frozen evidence SHA256:

- Helper: `ad9eb9991205261172cfd8e09537c75c05b153b3431b224ac1d4744319277d92`.
- Receipt: `bab6ba8d61e9fac494ca42124b043c358597d19bf1ebf8f8699b2c054ff476bc`.

The receipt authenticates the following dependencies in
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue`.
They are read as inert proof or source data, with mathematical read scope
stated above; a byte pin does not assert a new full proof review.

| Dependency | SHA256 |
| --- | --- |
| `neary_woods_scaled_strong249_tesla.md` | `2230f44faee7e2ecebb0ce29722462f121a49e85addf3740d8b8b54efd7bc8a4` |
| `neary_woods_scaled_strong249_tesla.json` | `e8fb322a18ec77cf9936ebb7d9e25d86414b66f8db561c4a64edb2ef16aba35c` |
| `neary_woods_scaled_strong249_degree_correction_tesla.md` | `ada1718ff4e93eb4b48e50d1362b8912973c6d629e1f724878a4e12804a39f11` |
| `neary_woods_scaled_strong249_degree_correction_tesla.json` | `573effd459ea14b1ca82b98cc3a61a5ba37e41ada68965200cf382f35ebe1366` |
| `neary_woods_hierarchical_history250_tesla.md` | `1bb41ed9eae9e77b2a9236c49508a55538f2ff84d1cd245f3bccec4dee39a330` |
| `neary_woods_universal_initial_bound254.md` | `9e1a0fd5559dc72420a5123eb4f67753576f7b06d93aff6b7b650cd40dba1f90` |
| `binary_tag_four_tile_history.md` | `2cb8d1736852d525d4668f40eacdc8fa090c426f100110421521c85910e1e4b2` |
| `neary_woods_universal_u9_tag_chain.md` | `7159fbae99ca020c2f9a10eb8560c13f56e53b6f81cd2f17f045097480f8ff03` |
