# ROOT review: literal scalar bounds and first Pell indices

Accepted on 27 October 2026. ROOT read the entire 423-line proof, 55-line
Checks and author receipt before independently compiling the unchanged pair
in a fresh private overlay. Main/Checks passed in 16.906/2.250 seconds with
an empty main log. Both objects, both complete logs and all five axiom
reports match the author run. Reports use only `propext`, `Classical.choice`
and `Quot.sound`.

## Mathematical scope

The proof first establishes simultaneous monotonicity of both coordinates
in the Pell base by genuine Sigma1 induction, including index zero. Its
finite recurrence calculation proves the exact sixth ordinate and the
strict bound needed to invoke the accepted half-index theorem.

`first_main_indices` takes the actual four additive norm equations and the
stated positive data and scalar window. It derives the first norm's common
index, both remainder bounds and the large-ordinate condition. Comparing
the first and main Pell bases forces the main index above the first one.
The accepted half-index theorem then identifies the main pair at the literal
rank R. Canonical quotient/remainder arguments prove `2*n = R+1` without
assuming the stronger remainder bound as a premise. They also retain a
positive omitted quotient `h` in `k = R+1+4*E*Y*h`.

`scalar_window` derives the window from the literal additive transport
identity and the port bounds. All natural subtractions are justified before
use. The proof allows the auxiliary K and ports to be zero. The final
`maintained_first_indices` adapter uses the maintained fourteen positive
fields, with the second port shifted exactly once. It derives the scalar
bounds and both index identities from the actual transport and four norms;
it accepts no desired-index premise.

This leaf does not extract the four norms from a zero of the object-language
polynomial, certify the concrete internal ports, recover the exponential
identity, or construct simultaneous cofinal witnesses. Those are separate
obligations before the full PA/HA equation equivalence.

## Reproduction and evidence

The approved profile contains 108 cached modules, 95 Foundation modules,
393 local artifacts, 38 external boundaries and 507 first providers. There
are zero prerequisite refreshes. Both new inputs were preserved before the
first compiler invocation. Commands use `-M6000 -j1 -DElab.async=false`, one
Lean thread, a fresh private overlay and package-only fallback paths.

The independent driver authenticates the frozen plan, the 44-file author
manifest, all four author attempts and the actual first providers. The
ROOT freeze separately rechecks the preserved historical inputs, both final
pairs, every full log and all five reports. Earlier elaboration failures
and the Checks correction are retained; the final main source is unchanged
from the preceding successful main build.

Canonical accepted ROOT provider:
`/tmp/arithmetic-pell-first-index-root-obnhr4v8/lib`.
The [ROOT packet](arithmetic-pell-first-index-root-replay.json) and
[manifest](arithmetic-pell-first-index-root-replay/FILES.json) pin independent
inputs, driver, snapshots, logs and timings. The
[author packet](arithmetic-pell-first-index-replay.json) and
[receipt](arithmetic-pell-first-index-author.md) retain the development history.
