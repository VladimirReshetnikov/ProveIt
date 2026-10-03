# Three-mass core: shifting the local mass coordinate

**The candidate is sound over the declared natural domain.** For every valid literal source machine, external horizon, and supported input specification, replacing each local natural `u_(t,j)` by a natural `v_(t,j)=e_(t,j)+u_(t,j)` gives a bijection of complete natural zero fibres. The reverse formula `u=v−e` is natural at every transformed zero. It is not a map of the whole natural orthant. The clean forward/reverse witness lift composes on zero fibres; its existing off-zero limitation remains.

This is an independent mathematical audit, not a review of the forthcoming emitted arithmetic schedule. No complete `Bh` gate saving is certified here; that requires the author's full DAG, including sharing and all changed branch forms.

## Literal source inspected and pinned

Read `three-mass-release/code/certificate.py` in full, especially `branch_forms` (lines 94–107), the input loaders, complete step/finalizer construction, and source witness semantics. SHA-256:

`fed96578694af665258fca9eeab14fa94d8a56e810de8f684a2c9fdcd9d751e8`.

The clean-target package's vendored copy is byte-identical. Also read `clean-target-release/clean_targets.py` in full, especially `clean_source` and `affine_full_witness_lift`; SHA-256:

`a79405023df5a1038a69bc947314979093df39be8da7abcdf5588f77da848315`.

These are the already reviewed arrival `4e270aa4648c5fd7e18626507531046715976535` archives: `Three_Mass_Reversible_Computation.zip` SHA `fd86a8a6b71735ef08ebd7913498603213244484da8b23d81876b10c40ffd1de`, and `Exact_Targets_Three_Mass_Units.zip` SHA `d69d8df9ee3a2074bcff1ef400853724eafb679ada8b287ef397eb8891965dcc`. No author tests or repository files were changed or rerun.

## Exact transformed branch forms

Let `p` be 2 or 3. A zero-test branch has fixed residue `1<=r<p`. Substitution into every original affine form gives:

| Operation | Incoming raw mass | Outgoing raw mass | Native ticks |
|---|---|---|---|
| inc | `v` | `p v` | `108 v + 96 p v + 8e` |
| dec | `p v` | `v` | `96 p v + 108 v + 8e` |
| positive | `p v` | `p v` | `192 p v + 8e` |
| zero, residue r | `p v+(r−p)e` | same | `192[p v+(r−p)e]+8e` |
| nop | `v` | `v` | `192 v+8e` |

The negative coefficient `r−p` in a zero-test row is intentional. These forms need not be nonnegative away from zeros; they occur inside affine squares or endpoint/time expressions. The unsquared gate becomes exactly

`(E_t−e_(t,j)) v_(t,j)`, where `E_t=sum_j e_(t,j)`.

Both factors are nonnegative on the whole natural orthant, since the first is literally the sum of the other natural selectors. Replacing it by `1−e` before imposing one-hot selection would not have this property.

## Proof on every natural zero

Keep every selector square, source-control square, incoming-mass square, loader row, halt/output/time endpoint, and other finalizer term. On a transformed natural zero each square and each complementarity product vanishes independently.

At step t, the natural selectors sum to one. Exactly one branch j is selected, with `e_j=1`; all other selectors are zero. Every inactive gate has first factor one, so every inactive `v_j=0`. Thus every inactive incoming/outgoing/tick contribution vanishes, including the negative-coefficient zero-test forms.

The supported loaders give `N_0>=1`: fixed raw input requires a positive integer; free raw input is `x+1` with `x` natural; the bounded-counter loader has a natural one-hot selector and positive weights `2^a 3^b`. Assume inductively `N_t>0`. The selected incoming-mass row equals `N_t`. If its selected `v_j` were zero, its incoming form would be zero for inc/dec/positive/nop, or `r−p<0` for a zero test. Both contradict `N_t>0`. Hence integrality gives `v_j>=1=e_j`.

For inc/dec/positive/nop the outgoing mass is a positive multiple of this positive `v_j`. For a zero test it equals the already positive incoming mass. Therefore `N_(t+1)>0`, closing the induction. Consequently every selected `u_j=v_j−1` and every inactive `u_j=0` is natural. All transformed rows are literally the original rows evaluated at these restored coordinates, so restoration gives a complete original natural zero. Conversely, any original natural zero maps by `v=e+u` to a transformed natural zero. The two maps are inverse and preserve external input, endpoint and time coordinates.

This proof uses the actual allowed branch types and the retained positive loader. It does not assume a valid execution before proving positivity. Source-control equations then select the actual labelled instruction; source/target separated syntax gives the original unique witness in each accepting input fibre.

Arbitrary positive raw input is allowed. Its fixed cofactor coprime to six need not be one: the zero branches partition the nonzero residues modulo p, while dec/positive require divisibility and positive quotient. The proof uses positivity, not a pure `2^a 3^b` representation.

## Boundary cases and exact scope

- `h=0`: there are no shifted coordinates. The original and new packets are identical, including the halt and optional endpoints.
- `B=0, h>0`: each selector square is `(-1)^2`; the packet has no zero. For `B=h=0`, acceptance is exactly the original constant halt condition.
- A halt or other stuck initial state cannot acquire an outgoing branch. With positive horizon, source-control and one-hot selection rule it out even when other machine labels have branches. Missing inverse branches are treated the same way.
- Native time and the radius-one scale four are carried by the same affine substitution. No timestamp relaxation occurs.
- Hypothetically allowing `N_0=0` would break the proof: a selected inc/nop branch with `v=0` would give a transformed zero with `u=-1`. The declared loaders exclude this input.
- The natural restriction is essential. For one prime-two decrement from state s to halt, raw `N_0=1` (`x=0`), and no optional endpoint, `e=1,v=1/2` gives a nonnegative-rational/real transformed zero with final mass `1/2`. Restoration has `u=-1/2`; the old orthant packet cannot realize the decrement from mass one. Thus no nonnegative-real fibre equivalence is asserted.

If `T` is the affine substitution leaving all external coordinates fixed and setting old `u=v−e`, then the complete source polynomials satisfy

`P_new(w)=P_old(T(w))`

on **every integer tuple**, indeed as a formal polynomial identity over the integers. There is no correction term when substitution is applied to all source rows and products. This does not say `P_new(e,v)=P_old(e,v)` in unchanged coordinate values, nor that `T` is a globally natural map. Over all signed integer coordinates T is an affine bijection; the substantive result above is its natural-zero restriction.

## Clean reverse-witness lift

The clean source changes inc to dec and dec to inc on the backward copy, retaining zero/positive/nop. Its reversed occurrence uses exactly the same local `e,u`, and hence exactly the same `e,v`, in reverse chronological order. Incoming/outgoing mass is exchanged for inc/dec; the tick expressions are equal in the two directions. Test/nop masses and ticks are unchanged.

The two bridge nop instructions have old base `N_h−1` and `N_0−1`. In v-coordinates they therefore have selector one and `v=N_h` and `v=N_0`. Positivity proved above makes both natural on the compact zero fibre. The total clean time remains

`2 T_forward + 192 N_h + 192 N_0 + 16`,

with the same optional overall factor four. Copying forward/reverse coordinates, inserting these bridges, and using the existing hygienic external-coordinate renaming gives the unique full cleaned witness. Restriction to the forward coordinates is its inverse on the complete zero fibres.

No global natural-map claim follows: on an arbitrary natural tuple a zero-test outgoing form `p v+(r−p)e` may be negative, so a bridge value can be negative. Nor does this composition produce an off-zero identity between the compact clean polynomial and the larger naïve clean polynomial; the old clean lift never claimed such an identity.

## Independent finite source checks

`check_three_mass_mass_coordinate_math.py`, with companion `review_three_mass_mass_coordinate_math.json`, authenticates the literal core before source-only loading. It independently reconstructs and compares all eleven prime/operation/residue affine triples, including all tick terms. It evaluates complete transformed source packets using its own affine evaluator, without invoking the author's polynomial evaluator or witness constructor.

The bounded census covers **10,080** natural one-step tuples over all ten operation/counter choices (the prime-three zero case has two branches), finding **63** complete zeros, all with natural restored u and zero original polynomial. It explicitly rejects **368** selected-`v=0` tuples. It also checks eight empty-branch/horizon boundaries and rejects 150 full tuples starting at halt or a stuck source with branches elsewhere. Observed valid inputs include cofactors other than one. These are implementation checks supporting the general induction, not an exhaustive proof over all inputs or horizons.

```sh
python3 check_three_mass_mass_coordinate_math.py \
  --core /path/to/pinned/three-mass-release/code/certificate.py \
  --output /path/to/review_three_mass_mass_coordinate_math.json
```

The claimed saving is therefore mathematically available. Its size must still be established from the actual emitted complete schedule: sharing may already have paid `e+u`, and the zero-test coefficients and rewritten time/endpoint forms must not be treated as free.
