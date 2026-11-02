# Isolated Mathlib primitive-recursion reproduction probe

This is an investigation of the unguarded direct package input that stopped
the [external-checker author attempt](../external-checker-author-failed-attempt/README.md).
It is not a replacement provider, proof replay or source-to-object provenance
audit, and it did not modify any package object.

The probe checked that the inherited mathlib checkout is at the revision
`81a5d257c8e410db227a6665ed08f64fea08e997` recorded by the Foundation provider
recovery and that the checkout's `Mathlib/Computability/Primrec/Basic.lean`
bytes match that Git blob. It copied only that source into a fresh temporary
source root, queried Lean's four direct imports, hashed them before and after,
and compiled the source into a separate temporary output directory using the
existing package overlay. The invocation used Lean 4.32.0 and the three main
options stated in the pinned mathlib `lakefile.lean`: `pp.unicode.fun=true`,
`autoImplicit=false` and `maxSynthPendingDepth=3`. The actual outer tool session
**71699** exited 0, and the inner Lean command recorded exit 0.

The existing cached `.olean` SHA-256 was
`33e972e2176e5ad98403651c38725d34843e5ed67a60e41e9986dd12a8d9eb6a`
(351,568 bytes); the isolated rebuild was
`e813f681d629a8b886fccd4cff434a858fb7bda06c1cdef8d2d9c1720751f3b3`
(351,480 bytes). Thus this experiment did **not** reproduce byte identity.
The exact command, four direct input hashes and before/after observations are
in [`observation.json`](observation.json); the complete compiler log is empty
and retained as `process.log`. Neither output has been substituted for the
other in the project provider.

The saved [`original.trace`](original.trace) has a dependency hash and output
identifiers, but no original command line, Lean setup or complete transitive
source/object provenance. The checkout's pinned Lake configuration gives
intended options, not independent evidence of the exact historical build
command. The two byte sequences may differ because the Lake setup or other
build context was not reproduced; this probe does **not** establish that
either object is incompatible or wrong. Conversely, it does not authenticate
the cached object against the historical parent's compile-time ancestry.
The external-comparison replay therefore remains blocked at this provider
boundary until compatible ancestry can be verified or the affected coherent
closure can be rebuilt. Existing completed project results are unaffected.

The reproducible probe source is
[`probe_mathlib_basic.py`](../../research/ipra-selected-native-bit/probe_mathlib_basic.py).
It refuses to overwrite its temporary output, requires the pinned source and
cached-object hashes, and checks direct inputs at observation points. To rerun
it, first choose a different fresh output directory in a copy of the script.
The 4 GiB preflight is a launch-time check, not a continuous space trace.
