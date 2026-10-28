# ArithmeticRadixAlignment — author construction and replay

27 October 2026. PASS. controller_certificate authored and fully read the
126-line main, 50-line Checks and full executed replay driver. The final
pair passed in 5.204/2.316 seconds. Main output is empty;
all eight reports use only propext, Classical.choice and Quot.sound. ROOT
independent replay remains pending. No accepted source, shared object or Git
state was changed.

## Exact internal arithmetic endpoint

The only imports are Foundation.FirstOrder.Arithmetic.Exponential.Log and
Mathlib.Tactic.Ring. Every theorem quantifies over arbitrary elements of an
arbitrary-universe IΣ1 arithmetic model. There is no standard-index or external
prime-factorization premise.

block_quotient uses genuine Sigma1 successor induction to construct z with
exp(d*n)=1+(exp(d)-1)*z. Its successor witness is 1+exp(d)*z, and its base
retains d=0. No complete-lattice or unbounded external-search existence is used.
The definability obligation for the existential exponential graph is discharged
in the actual accepted arithmetic syntax interface.

exp_mod_radix uses actual div_add_mod, the block witness, exp_add and the
positive-modulus remainder theorem. aligned_remainder assumes d>=2 and a
literal exp(u)=(exp(d)-1)*J+1. The proof establishes beta>1, bounds exp(u%d)
by beta, excludes its equality-to-beta case because that would have residue
zero, and then obtains exp(u%d)=1 and u%d=0 by exponential injectivity.
aligned_exponent derives a positive block count when J>0. The d>=2 condition
supports this residue proof; no claim that it is the weakest possible hypothesis
of the final factor theorem is made.

exponential_factor uses actual Pow2.of_dvd and exponential_of_pow2 at log(q).
The full public factor_alignment takes only d>=2, J>0 and the actual equality
exp(R)=w*((exp(d)-1)*J+1). It derives 0<w and a positive internal N with
(exp(d)-1)*J+1=exp(d*N), d*N<=R, and w=exp(R-d*N). The exponent bound is
proved from positive-divisor order before the truncated subtraction is used;
then exp_add and positive cancellation give the exact remaining factor.
There is no desired exponent-divisibility or positivity oracle.

Checks cover all-internal arbitrary-universe inputs, the zero-d block quotient,
J unrestricted in the remainder theorem, unit divisors, the full public endpoint,
and incompatibility of zero rank with a positive coefficient. The ordinary-Nat
modulus-one check documents why the residue-one proof needs beta>1. It is a
finite boundary check, not an arithmetic-model proof substitute.

This pair does not derive the literal current polynomial's zero-to-power
premises, native population/word/carry/tableau soundness, converse simultaneous
witnesses, a closed arithmetic theorem, or the final HA endpoint. Those remain
separate clients; this is the generic factor and exponent-alignment checkpoint.

## Validation and provenance

The immutable plan SHA is
4c995d04b1f5a0f3bd72e068b7232d8f57f3f485f671f78dfc4a372c1b972558;
its three-file manifest is
1627cfdfd40263656730a21e606daec8d59d3bf545a032082014e5fb34138d3c.
The separate ROOT authorization note is pinned. Exact scope is 90 cached
Foundation modules, 360 custom artifacts, 38 boundary primaries plus 76
companions, 474 first providers and zero prerequisite refresh. Only these two
new leaves were compiled. I authored none of these Foundation or Mathlib
prerequisites; my earlier independent proposal/provider review is separate
from this author construction.

The complete source-header DAG, immutable selected pins, compiler, actual first
providers and ROOT authorization were reauthenticated. The private LEAN_PATH
contains only pinned custom symlinks and explicit package/toolchain paths;
there is no shared project cache fallback. Both complete input snapshots precede
the first compiler command in each attempt. Fresh outputs are regular files.
Pinned Lean4.32 uses -M6000 -j1 -DElab.async=false with one thread and 512MiB
reserve checks. Full main/Checks/driver bytes were read before each attempt.

Both attempts and all three compiler invocations are retained. The first main
failed solely because unqualified lt_irrefl was ambiguous between the general
and arithmetic names. Qualifying it as Arithmetic.lt_irrefl is the only source
delta before the clean final pair. The intended statement, imports, caps and
mathematical argument were unchanged. No first main object was produced.
All final logs are warning/error-free, and all eight reports are standard-only.

Complemented47_review read the entire draft pair and challenged the exact
quotient, residue boundary and final cancellation route, reporting no finding.
That was a scoped source-only challenge, with no provenance or compiler claim.
This author receipt does not stand in for the requested independent replay.

The final driver authenticated 3627 observations across
1510 paths. Freeze rehashed 4936 observations across
2244 paths. Input snapshots, failed diagnostics, commands, full logs,
timings and all available objects are retained as immutable regular hardlinks,
with the original private paths intact. Final provider: /tmp/radix-alignment-controller-author-tni4qn76/lib.

Main source: 807288e39c326c305f3148e2b4a81458b347bc76c9df687b70da900464059934.
Checks source: dbc53f83590892e0313434cfa9e08cde7bdcb8c17124b5e7c32e5b4048141a62.
Main object: b3607a522ebcdf46c1001d5d9763a83208b5cab9614a027e2ccf75c39e0f0bc7.
Checks object: 110afcedc66dfce9ff569a89e69141662a3507695d059be6ad7e7a6f951f41f0.

Evidence: [replay](arithmetic-radix-alignment-replay.json), SHA
d7992406dc9e9a44e95622e0d0fe4eee36186e7b9e8c10b6428dc9ccaf70407b, and [manifest](arithmetic-radix-alignment-author-replay/FILES.json).
