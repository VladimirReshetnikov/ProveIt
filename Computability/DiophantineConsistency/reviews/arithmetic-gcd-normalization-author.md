# ArithmeticGcdNormalization: author validation

27 October 2026. The complemented47 agent authored and fully read the new
201-line main and 50-line Checks, then compiled only those two leaves in a
private overlay. Both passed on the first attempt. The main log is empty;
the eight axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. No accepted source, cache object, display, or Git state changed.

The main imports exactly `Foundation.FirstOrder.Arithmetic.IOpen.Basic`
and `Mathlib.Tactic.Ring`. All mathematical variables and witnesses are in
an arbitrary `[ORingStructure V]` model of IΣ1, including nonstandard values.
No natural-number evaluation or external gcd oracle supplies a witness.

`Bez a b g` is the natural coefficient certificate
`∃u v w z, g+a*u+b*v=a*w+b*z`. The fixed, model-independent Sigma1
`gcdDef` conjoins this with `g∣a` and `g∣b`; it has no model parameter or
unbounded universal greatest-divisor clause. `gcd_certificate_exists`
handles `a+b=0` directly. Otherwise the positive Sigma1 search
`0<g ∧ g≤a+b ∧ Bez a b g` has witness `a+b`. The actual hierarchy
least-number theorem supplies a least positive certificate. For
`a=g*q+r`, the coefficient tuple `(q*w,q*z,1+q*u,q*v)` supplies a
certificate for `r`. Thus either positive remainder would contradict
minimality, proving both divisibilities. The selected coefficients are
unbounded existential witnesses; only the searched positive value is
bounded. This is Sigma1, not an asserted Delta0 least-number argument.

`bez_divisor` proves greatestness for every common divisor, including zero.
The positive case reduces the actual coefficient equality modulo the
divisor; the zero case derives `a=b=g=0`. Mutual divisibility gives
`gcd_certificate_unique` and hence total unique `GcdCert`. The selected
`gcdValue` is represented by the same fixed syntax through `gcd_defined`;
`gcd_total` states internal total uniqueness directly in terms of its graph.
The use of Lean choice to name the already proved unique value does not
replace existence or supply a desired gcd property.

`norm_normalization` takes only `R>0`, `D>0`, `f>0` and the actual equation
`R*R+D=D*(f*f)`. It derives positive `d,s,t` and all three identities
`D=d*d*s`, `R=d*s*t`, and `f*f=1+s*t*t`. The proof chooses the derived
gcd of `R,D`, writes `R=g*t` and `D=g*d`, and cancels positive `g` in
its own coefficient equality to obtain `Bez t d 1`. The norm gives
`d∣g*t*t`. `unit_certificate_cancel` derives cancellation solely from the
coefficient identity; applying it twice gives `d∣g`. Writing `g=d*s`
and cancelling positive `d` produces the normalized norm. All positivity
of `g,d,s,t` is derived. The additive endpoint retains the requested
`f>0` assumption although its proof does not need it. The literal
`norm_normalization_tsub` endpoint uses `f>0` to justify
`(f*f-1)+1=f*f` before converting the truncated equation. No supplied
gcd, coprimality, minimality, factorization, Pell index, or source is used.

Focused checks cover fixed graph totality, both zero-input gcd identities,
arbitrary common divisors including zero, coefficient-based cancellation,
and the literal truncated norm endpoint. They audit the existence,
uniqueness, totality, represented graph, fixed-syntax totality, cancellation,
and both normalization theorems.

| Module | Source SHA256 | Object SHA256 |
| --- | --- | --- |
| ArithmeticGcdNormalization | 488783700b1663f66b4caee71e7121eb6c50ab4efe04b39f30d63727cc6c8627 | 517c17d6efc7aa6ef20c4f269c082252daf9c77051e402ddbbf5f085cd4ea0c7 |
| ArithmeticGcdNormalizationChecks | bfbda894ceb6ce5e0a1ab459c4e7f48ed897648d47356e7efda8e37476c05067 | 893a97138e58af2d5de1d81580491f1a20f337625c91841b145646fd79d64f02 |

The approved scope supplement is
`research/arithmetic-gcd-normalization-plan.md`, SHA256
`1000c69df3bccbf107e1d52a5d618e57d6e9b5f3d3bf20cd0c39d9eb3406d564`.
The frozen cache plan has SHA256
`1206727b503151356d3ba49f713e09bf88b84d3d6af131ca6a29625e221c2a14`.
It selects 86 custom modules, all Foundation, 344 custom artifacts,
37 external boundary names, and 111 recorded boundary artifacts
(37 primaries plus 74 companions). There are zero prerequisite refreshes.
The exact header/import closure and every selected source/object pin were
checked before compilation, including implicit Init. All 455 actual first
provider artifacts were resolved and rehashed. Providers retain their
accepted source/trace provenance; this is not a new Foundation or package
build. The historical parent inventory's misleading companion-field name
is not copied into the new plan: the new counts are explicit.

The author driver was read completely before execution. Each command uses
the pinned Lean4.32 executable with `-M6000 -j1 -DElab.async=false`, one
thread, and a 512MiB reserve. New outputs are regular files, not symlinks;
only cached prerequisites are linked. The sole attempt's main/check took
11.100/1.874 seconds with peak RSS 1,826,156/1,783,412 KiB. Final free space
was 1,358,000,128 bytes. There were no failed attempts or source corrections.
Both input snapshots were saved before the first compiler command.

The private provider is
`/tmp/arithmetic-gcd-normalization-author-dk1v4fv5/lib`.
The executed driver SHA256 is
`1496ba1dcd35fb3a08d6d4f0bd7ba5635550a02f7b108c6a5b051b6591fe2573`.
The [replay packet](arithmetic-gcd-normalization-replay.json) has SHA256
`a8ec6e58844265a43a250e513c31ff173ca8254097663e8542aba0f47254568b`.
The [15-file evidence manifest](arithmetic-gcd-normalization-author-replay/FILES.json)
has SHA256 `880135aa551c80afd49646c68c4c2fd261b09e0667bc8d8ccefc0e27456063d9`.
It retains exact sources, driver, plan, authentication, first providers,
commands, complete logs and timings. The final freeze rehashed 1,022
observations across 1,016 paths; all target and prerequisite pins agree.

This is author validation pending ROOT's independent review/replay.
Composition with KnownUnit, common-discriminant Pell coordinates, strong
divisibility, Jones integrality, cofinal witnesses, and the final HA equation
remain outside this packet.
