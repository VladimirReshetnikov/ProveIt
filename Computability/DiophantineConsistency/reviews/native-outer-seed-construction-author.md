# Fresh native outer Pell seed: author receipt and endpoint audit

The new packet constructs the native outer Pell seed from an odd rank R and
the exact binary population `sigma(R)=3u+2`, for positive u. All interval,
divisibility, positivity, and quotient conditions are proved. No existing
source-system solution or desired native equivalence is assumed. This is an
author receipt, not an independent review.

## Frozen packet

Paths are relative to `Computability/DiophantineConsistency/`.

| File | Lines | SHA-256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/NativeOuterSeedConstruction.lean` | 279 | `fd437b7d7d64c3371f4d0f2bc234d9e620526b0b1b3c4558ab6fbb47d6573159` |
| `Lean/DiophantineConsistency/NativeOuterSeedConstructionChecks.lean` | 57 | `e509d0835288c1a576e6847d15a19e3635090c133b3bd90b1ef955e044f5b16d` |

The direct imports are `NativeHalfBinomial` and
`Diophantine.Paper1982.Carries`. The former is freshly compiled against the
entire current `Diophantine.Paper1980.PellRatio90` source in a private overlay,
as recorded below. The author read all478 lines of that ratio module, all of
`NativeHalfBinomial`, and the reused population, congruence, growth, and Pell
identities before the final builds. The final new main was read in full after
corrections; the entire checks file was read before its first execution.

## Literal construction and API

The principal theorem is:

```
exists_outer_seed (u R r : Nat)
  (hu : 0 < u) (hR : R = 2*r+1)
  (hpop : sigma 2 R = 3*u+2) : Nonempty (Seed u R).
```

`Seed` retains named positive registers s,Y,a,k,c,D,tau,h,eta,zeta,gamma,
with their exact defining equations. Write `X=2^R`, `q=2^u`, and `E=XY`.
The returned facts are:

```
Y=s*q^3, a=Y*(X+1), k=eta+zeta, c=kY+eta,
k=1+R+E*h, D=X+a*c+gamma*(4a+3),
tau^2=1+(XY^2)(XY^2+1)k^2,
D^2=1+((a+2)^2-1)c^2,
c=psi_(a+2)(R).
```

Thus the six independent outer inputs s,tau,h,eta,zeta,gamma are positive,
and the actual native first norm, main norm, index row, and root-congruence
quotient all hold. The main theorem does not assume R congruent to3 modulo4;
that is a separate later auxiliary-seed requirement. This packet establishes
positive s and the exact common scale, but does not additionally assert that
s is odd.

The proof proceeds as follows.

1. `population_sizes` uses the odd-rank identity to obtain
   `sigma(r)=3u+1`. The elementary digit-sum bound therefore gives r at least4;
   the same bound at R gives `3u+1<R`. These are derived, not extra premises.
2. `scaled_half_floor` applies `Ratio90.binomial_floor_two` at X=2^R. Its
   integer part Q is `choose(2r,r)+wX`, with remainder v satisfying
   `4v<X^r`. `Jones1982.lemma_2_15` and the rank population imply
   `2^(3u+1)` divides both summands of Q. Set Q=2Y to obtain a positive
   `Y=s*q^3`. No previously supplied binomial divisibility is used.
3. `pell_interval` sets `P=2XY^2+1`, `c=psi_(a+2)(R)`, and
   `k=2*psi_P(r+1)`. The lower ratio estimate is strict. The accepted
   factor-two upper estimate and the quarter-unit remainder give
   `kY<c<k(Y+1)`. The base and error bounds are discharged by the explicit
   exponential X and the derived r bound. Hence eta=c-kY and zeta=k-eta
   are both positive.
4. The standard `psi_P(n)` congruence modulo P-1 descends to E=XY.
   Doubling gives `k=R+1 mod E`; Pell growth gives `k>R+1`, so the quotient
   h is positive. The congruence alone is not used to claim positivity.
5. `Diophantine.chi_modEq_pow` at p=2 gives
   `D=X+ac mod(4a+3)`. Growth gives c>X, and `chi_gt` gives
   `D>(a+1)c>X+ac`. The exact quotient gamma is therefore positive.
6. Both norm equations follow from `chi_sq`, retaining the doubled first
   ordinate. They use the literal native recipe, not the different recipe
   in `Jones1982.exists_B25core`.

## Remaining31-coordinate assembly: audited route, not yet a theorem here

The source-recovery modules `NativePellBootstrap`, `NativePellFirstIndex`,
`NativePellPower`, and `NativeHalfBinomial` primarily prove the soundness
direction from an existing source. Their source-solution premises cannot
serve as a constructive converse. Likewise `Jones1982.exists_B25core` has
different main/first parameters and an undoubled ordinate; it is not used
to substitute for the actual native recipe.

The new outer seed supplies the missing part of the following remaining
assembly, with existing exact APIs available for the other parts:

- Given separately established R mod4=3, invoke
  `ThirteenFreshSeed.auxiliary_exists (a+2) R 1`. It constructs positive
  f,i,T,V and a negative signed y, with the actual strong norm and
  `V=f^2*(cT-R)-c`. Use abs(y) as the positive parent coordinate; the
  auxiliary norm depends only on its square. This is fresh private data,
  with no compatibility assumption about an old witness.
- Supply the already constructed positive J,F,alpha,z, together with
  `q=beta*J+1=2^u`, `w=2^(R-u)`, and the authoritative ordinary transport
  equation. Since the new seed derives R>u, `w*q=2^R` follows by exponent
  addition. Deriving this exact rank-forced temporal multiplier from a
  packing/controller is still a separate obligation.
- Assemble the fifteen positive coordinates
  `(J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,abs(y),gamma)` and prove the
  literal `Carrier66.Canonical` factors. The exact rank binding to the
  supplied R must be retained. `Carrier66.canonical_zero` then gives the
  parent polynomial zero.
- `Carrier66Source.source_pos` and `Carrier66Source.canonical_rows`
  provide all31 positive coordinates and every literal source row from
  that canonical parent; `sourceNat_pos` and `sourceNat_rows` provide the
  natural-coordinate form. No new arbitrary-coordinate positivity
  assumption is needed.
- `FirstPellCarrier.restore_carrier` and
  `Carrier66.canonical_drops_to_positive_zero` provide the existing
  fourteen-coordinate transfer. The thirteen-coordinate converse can
  then use its already proved fresh-private-seed map under the actual
  current mask interface.

The last four bullets describe an audited implementation route. They are
not claimed as endpoints of this new module, and no complete polynomial
or consistency converse is asserted here.

## Current-source dependency rebuild

The initial staged build found that the shared `PellRatio90.olean` did not
expose `upper_estimate_factor`, although the current source contains it and
the current `NativeHalfBinomial` source uses it. This is evidence of a
source/object interface mismatch; its historical cause is not inferred.
The existing `NativeHalfBinomial.upper_estimate_scaled` interface was
available, but the final packet was still checked against fresh current
sources for both modules rather than relying on that cache discrepancy.

The complete current sources were read and compiled sequentially with
`lean -M6000 -j1` into `/tmp/native-outer-seed-deps-2i8pllz8`, ahead of
unchanged reused prerequisites on `LEAN_PATH`. No old shared dependency
object or source was overwritten. The persistent exact command/hash receipt
is `reviews/native-outer-seed-dependency-replay.json`, SHA-256
`b65f0efeab3739c8441ec0620923dae54f3a48777c558222edecf58f93de0905`.

| Dependency | Source SHA-256 | Old shared object SHA-256 | Fresh private object SHA-256 |
| --- | --- | --- | --- |
| `PellRatio90` | `5b790da2863fba41ac42b56675c77bc8404a2e5834e9a44ab255602e5a3fbbd0` | `101985b0c678b4014271885cbf931641e08af0c325184c6875d51b28113692ad` | `d54f59bc03a0648e360c124e18b7b0585cc98147553312b294a43c0fec67680b` |
| `NativeHalfBinomial` | `c816fb0395389dce45042aed6acbfd6c182355357de9d4b2abf660516bab3881` | `da693e1837acab5c4522824b52aea46276d4c5ef075176c5ae6af690d343961f` | `7ef4f6dc18292dc30cdea2f5a8e55228ee38c1d7f5a27319eba8db63a73efbfa` |

The ratio build passed in56.71 seconds, peak RSS3,304,712 KiB, with two
pre-existing unused-variable warnings. The half-binomial build passed in32.81
seconds, peak RSS3,264,960 KiB, without diagnostics. The rest of the import
closure was reused; no full fresh dependency replay is claimed.

## Fresh packet builds and controls

The new main and checks explicitly set `Elab.async false`. Both final builds
used the private fresh dependency overlay and direct bounded commands:

```sh
lake env bash -c 'export LEAN_PATH="/tmp/native-outer-seed-deps-2i8pllz8:$LEAN_PATH"; lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeOuterSeedConstruction.lean -o /tmp/native-outer-seed-deps-2i8pllz8/DiophantineConsistency/NativeOuterSeedConstruction.olean'
lake env bash -c 'export LEAN_PATH="/tmp/native-outer-seed-deps-2i8pllz8:$LEAN_PATH"; lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeOuterSeedConstructionChecks.lean -o /tmp/native-outer-seed-deps-2i8pllz8/DiophantineConsistency/NativeOuterSeedConstructionChecks.olean'
```

Main passed in12.66 seconds, peak RSS3,299,400 KiB; checks passed in2.77
seconds, peak RSS3,216,976 KiB. Both final builds are clean. All four axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, new axiom, or `native_decide` occurs. The two newly owned objects
were copied to the usual workspace object directory after PASS; no prior
dependency object was changed.

Checks instantiate actual ranks31 and61 at u=1, retaining both odd mod-four
classes. They expose all six positive independent witnesses, the exact root,
norm, interval, and index formulas, and the q-cubed divisibility derived from
the returned seed. Negative controls distinguish the doubled first ordinate
from its invalid undoubled replacement and show why u=0 does not imply r>=4.

Development corrections concerned imports, local definition normalization,
field syntax, commutation, and natural square normalization. One broad
arithmetic-search run was intentionally stopped and replaced with explicit
local premises; no resource cap was raised or mathematical premise added.

| Artifact | SHA-256 |
| --- | --- |
| Main `.olean` | `f15619430cc65f2744cef7ff49cb9cc512a4eaf6cec457b2d8eeba99b241f32d` |
| Checks `.olean` | `597f3e585613c98f8492a343adf74f71baac78aacff77c67298315faf63f1f8e` |
| `/tmp/native-outer-seed-stage5.log` | `43af87f2715d80f54866dd24514895a1dfaa93a7e7ce2ff352751ac0ddc1f502` |
| `/tmp/native-outer-seed-checks-stage1.log` | `a2907d6768141313a300605118e8387ea70fa9fa0d65779a351d407b0a6841fd` |

No existing Lean source, maintained equation, shared documentation, or git
state was changed by this task.
