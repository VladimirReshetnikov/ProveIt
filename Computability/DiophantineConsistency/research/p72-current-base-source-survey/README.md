# Source-declared current-base survey for P13/P14

The deterministic read-only survey traverses the source imports of
`Compact44.IPRAOrdinary72` and `IPRAOrdinary72P14`, using the pinned repository
scanner and `lakefile.toml`. Their union is 1,599 project modules; 918 occur in
the frozen current14 base snapshot with matching source hashes and import
lists, while 681 are outside it. It records a dependency-first order for the
681 sources, all source hashes/imports and the 80 declared external imports.
The three external names not in the current14 snapshot are
`Mathlib.Algebra.MvPolynomial.CommRing`, `Mathlib.Algebra.Order.Ring.Cone`,
and `Mathlib.Data.Fintype.BigOperators`.

The survey exited 0. Its SHA-256 is
`7cd42829676156ef3a414e4b462aa461109713661754a39c3440d6371fe6e636`;
the [result](result.json) SHA-256 is
`29cb091647eb0800936795ac0494e5cedcbe8d770c076814e8d52f9c7a738954`.
It is a source-declared inventory, not a fresh build, source-to-object
certification, immutable provider guard, package-transitive compatibility
check or dynamic import trace. In particular it does not justify mixing
captured compact-provider objects with the fresh current14 overlay. The
separate two-module [captured-provider replay](../p72-p13-p14-captured-endpoint-replay/README.md)
proves endpoints with its own narrower provenance scope.
