# Source identity and permitted distribution

This is an integrated, portable Report32 release. It is not a byte-identical
republication of either source archive. `verification/source-lineage.json`
records every source-derived file, its original digest, released digest,
byte-exact status, archive or frozen source-tree identity, and any changes. The frozen original
manifests are preserved under `verification/source-manifests/` as historical
identity records; they are not the integrated release inventory.

The source archives used for assembly were:

- `universal-matrix-semigroup-20261003.zip`, SHA-256
  `914d12f80e2e092ce485a496d1480db400cda44e554a301f64b1d79b47fc271a`
- `paired-matrix-diophantine-20261003.zip`, SHA-256
  `74ce5df4c4a78cd9923dafc2f327d67878161bedb26e76f14559f065db24882e`

The additional frozen `matrix-factorization-fibers-20261003` source tree is
copied byte-exactly as `fiber/`, including its valid local manifest and
checksums. Its original manifest SHA-256 is
`b093257ce9f9a259aa9c465e4e7970f381d465f7bb8fded1075618e5a640bfbb`,
and its checksum-file SHA-256 is
`b7e0e8d465fd1aaf60d740de4fb837ff2f5b244365391d0953e7f3d467b03efa`.
Both were checked before copying and its numerical inputs share the same
pins as the other two packets.

Neither original archive is embedded. Its checksum was checked before
extracting any copied program, and each extracted distribution file was
checked against its frozen source manifest. Earlier releases were not changed
or executed as dependencies.

## Changes to source-derived human-readable material

Only three copied source files are adapted:

1. `core/PROVENANCE.json`: the private workspace prefix in the historical
   transition-table origin is replaced by `prior-artifact:`
2. `core/loader-audit/U15_DEPENDENCY_AUDIT.md`: the same replacement is made
   in five historical artifact citations
3. `core/README.md`: the obsolete per-packet checksum invocation is replaced
   by a reference to the integrated verifier

Historical artifact identifiers following `prior-artifact:` are provenance
citations, not portable runtime dependencies. Original source digests remain
available in the source-lineage file. No executable code, transition-table
data, matrix data, literal polynomial, witness, certificate, or audit receipt
has been adapted. All paired packet distribution files are byte-exact.

The release omits the two archived packets' original per-packet checksum lists, cached interpreter
bytecode, ephemeral build files, and copyrighted primary-PDF reading caches.
Public bibliographic URLs, PDF hashes, published-dependency limitations,
and the source authors' draft-specific page-locator conventions are retained.
The source core archive already excludes its primary-PDF cache; this release
does not infer permission to redistribute that cache.

## Mathematical scope

Replay checks the literal finite artifacts and named test families. It does
not turn a bounded simulation into a nonhalting test, implement the published
arbitrary-program-to-U15-tape translation, establish an optimal generator
count, or turn the fixed-r polynomial family into a single variable-r,
fixed-arity polynomial. See the report and both source proofs for the complete
arguments and their explicit dependencies.
