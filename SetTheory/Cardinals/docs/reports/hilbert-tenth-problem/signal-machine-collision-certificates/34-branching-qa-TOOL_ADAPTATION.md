# Report64 release-tool adaptation

The author inspected all three complete Report63 release-only helpers before adaptation. The new Report64 files change the report identity, module list, source-protection list and authenticated input/helper hashes. Their contract is otherwise retained: no scientific executable is run; outputs must be fresh, absolute and external to both release and protected original inputs; symlink and hardlink sources, path aliases, unsupported tree entries and changed files are rejected; snapshot preservation covers bytes, sizes, modes and nanosecond mtimes.

The builder uses a fresh isolated TeX format, no shell escape and an explicit temporary directory inside the external output. It records every format/typesetting recorder input across all passes, authenticates binaries and the full system-input union, validates PNG signatures/chunks/CRCs/raster dimensions, and can require byte identity with the packaged PDF. The lock excludes shared libraries, Python standard library and OS state. Deterministic ZIPs are authenticated against an externally supplied manifest pin; extraction restores file and directory modes and nanosecond mtimes.

The inherited synthetic selftests are not independent review. Fresh independent review of the exact Report64 helper bytes is required before sealing.
