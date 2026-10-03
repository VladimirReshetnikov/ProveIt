# Portable audit adaptations

This release preserves the literal source tables, their source checkers, the core primitive certificate implementation, and the authored mathematical conclusions. The portable audit entry points and receipt metadata were deliberately adapted before the final seal. They are not represented as byte-identical copies of the earlier development-workspace audit artifacts.

## Changes

- The release-level auditor now locates `source/` relative to the bundle when no argument is supplied. Five mandatory SHA-256 checks replace optional comparisons with previous release directories. No audit silently skips those checks when an external directory is absent.
- The independent primitive auditor now finds `primitive-certificates/` and `source/source.json` relative to its location in the bundle. Explicit command-line overrides remain supported.
- The primitive source-ledger auditor and its README use the actual bundled relative source path. The core `certificate.py` is unchanged.
- The independent primitive audit document uses a relative implementation reference and explicitly records that the receipts were regenerated. Development logs are omitted.
- Both independent audit families were rerun in normal and optimized Python. Their bundled receipts are newly generated records for the shipped source tree, not redacted claims that historical receipt bytes stayed unchanged. Source metadata uses a relative identifier; hashes of omitted development logs are not shipped. The 30 mathematical source-file hashes in `audits/stabilized-hashes.json` are unchanged; its audit-artifact hashes were refreshed to the adapted files.
- `replay.py` tests relative defaults in normal mode and explicit path overrides in optimized mode inside temporary copies. It also repeats all source, certificate, regeneration, mutation-rejection and small-CA-orbit checks.

The original independent review did compare relevant files with earlier releases. That historical result remains documented in the proof review. The portable replay establishes the same five known digests directly from bundled files; it does not claim to read a previous release installation.

## Exact adapted artifact hashes

### `audits/release_audit.py`

Original SHA-256: 8df40afd54d8c8f49ad23767db4974e8d9613f07fd2dc0914d4d40e7f452e371

Portable SHA-256: 7abfe4e704418ca3d9bf24f36449d2a9a25a9a61713796d4f39d4493c53ce4d3

### `audits/primitive/audit_certificate.py`

Original SHA-256: eb1a49166157af77d6d0ab79b9cfe8b6e2d09e09fcb54d423b6b0a350cbe4225

Portable SHA-256: 0935f1ad2415b777136640f57b630418988c9609538ba4288a17ccab2a3c5cc9

### `primitive-certificates/audit_source.py`

Original SHA-256: 1147a839ed941bc9c6c49598c06b02dd261926315728939ddd4ad0abff48977f

Portable SHA-256: a079798ffe3bc0b272765b93ea1190a3b2c3eab7c99b885de373cb24e5705622

### `audits/primitive/AUDIT.md`

Original SHA-256: 4915c66e52119dd8ac5e4bc8d86b33460e638059350a5642c02568c3e98589fd

Portable SHA-256: 0c64223bff04ebf23a5fd5d7b1787e2cf8327b0ff573f210ae9f45d1e35dbd60

### `primitive-certificates/README.md`

Original SHA-256: 9c0196f751eaf196b930ff4263ca26c01d5071b794ee09ec5816ca5945fe5137

Portable SHA-256: 1a7cc81394b1f9b9d694778e40bd37c114ed4235de03318f32784fefe1d2eb85

## Mandatory bundled dependency pins

- `source/dependency/virtual3.json`: 24c771db50dc621068e470227802c2710a4531ce2e7ad3703a5cdb6b0543bbcf
- `source/dependency/virtual3.txt`: 72338fd033a31d61e261d6074e6524d35a8d56022f8bcece411efb764fb02b5a
- `source/dependency/tm_table.json`: 0c6d8ae506f503e2783f6ed2ee68db4cde2f501b9864f376ab3773f86b59428a
- `source/dependency/UniversalTM15x2.tm.txt`: ba70ab2c04c68d7ec2d31db4c007d7542c3854d1e02b79a4a5ce07f42fb278ae
- `source/compiler-reference/reversible_binary.py`: f95a6028c9d3cc6f8b0b497cfc0cad68104da6d70e55205df04ad234e5d0c76f

## Regenerated evidence

- `audits/release-audit-receipt.json`: 202850afcec9f69feff33299035f80d0f36e4bb4e359dc02c0be9b89cfad7893; status PASS
- `audits/release-audit-optimized-receipt.json`: 67ae0b4a2a13ea10ff2f6751138e86cca0b98680d871791d626f81b9184790e6; status PASS
- `audits/primitive/audit-normal-receipt.json`: fbbc2ada6d647d7888794d3a529ea7e098a74689c38e7e4b753541f97b0fbc42; status passed
- `audits/primitive/audit-optimized-receipt.json`: 5fd4be00eb7eb1f617835dfe82200a8cfbd25d5768c47f92db60fc9838c503ac; status passed

The final release manifest is the authority for all delivered bytes. No change here alters the universal source hash, clean loader domain, layer clocks, periodicity theorem, quartic formulas, or the fully checked small example.
