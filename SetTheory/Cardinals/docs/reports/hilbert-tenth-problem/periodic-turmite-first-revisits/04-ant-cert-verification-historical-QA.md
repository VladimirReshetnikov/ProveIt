# Recovered independent final Report44 v2 QA

Verdict on the bytes independently inspected and executed before 01:02:21 UTC on 4 October 2026: **PASS_FINAL_CORRECTED_V2**. No blocking manuscript, packaging, replay, rendering or preservation defect was found.

At 01:03:27 UTC the execution filesystem was observed to have reset. All release and original QA directories disappeared. This compact receipt is reconstructed from the successful tool results retained in the conversation. It is not a claim that those files are currently present. The original rendered PNGs, logs, independently authored scripts and full before/after inventories are no longer accessible here. Reacquire the original artifacts and authenticate against the exact hashes below before delivery or replay.

## Exact verified identity

- Manifest: `40421963581a67913f298ce88d48fcc4e56abc3fd77c5cf0e4f7eb9c0d5ec945`
- PDF: `d53fd838cc19335091d6d0257a7560be721048cd0fd540572f00a23e3915c512`, 362135 bytes
- TeX: `341e26bb7f17524f458cf034e0ac6df6584452294e7f24dce02cd61720b8389a`, 37771 bytes
- ZIP: `8fcc2c4ed67fbaf2d24eab1f0d16128a805aab0a0fd1ee4102739ff3feb35256`, 798572 bytes
- Frozen science manifest: `99032e3b73365abe00b77fb93348088ef8d2fece709b5d9da3fe5c183dc71d9d`
- Independent terminal replay receipt: `fae100bcf4b2f2d831deb4d9265dc5fb0e403ed5f0e24cf35c43c88d15e4b123`

## Established before the reset

1. Independently authenticated all 96 release files against the supplied enclosing author binding, including every SHA256, length and file mode. Authenticated ZIP bytes before extraction; checked CRC, safe unique names, ordinary-file modes, fixed timestamps, complete membership and exact member-byte equality.
2. Compared all 79 embedded science files against the frozen original packet. Science contents and modes were identical.
3. Read the entire final TeX and supplied scientific audit. Rechecked the manuscript's numerical ledger, positive witness partition, degree positions/gap, pairing charge, coefficient-prefix arithmetic and corrected initializer against the actual source. Page 5 correctly gives h_x=(3^(au)-1)/(3^u-1), a geometric repunit. The inherited mathematical theorem boundary remains explicit.
4. Inspected all eight executable files in the standard replay/build closure before invoking them. Ran the README's full isolated replay from a deliberately moved extraction, with working directory /tmp and all outputs external. Both complete source streams reproduced their reference receipts. Both normal and optimized history runs reproduced reference bytes, checked 264 bounded histories and rejected ten mutations. Three complete-tool optimized runs rejected early as intended. Eight fresh-output boundary cases were rejected.
5. Rebuilt the final PDF in a fresh external directory with the supplied no-shell-escape deterministic build. The result was byte-identical. Rebuilt the ZIP from the moved extraction; it was also byte-identical.
6. Independently rendered and individually inspected every one of the 12 final PDF pages at 110 dpi. No clipping, overlap, glyph failure, table overflow or footer collision was found. No overfull boxes occurred in the rebuild log. The final page contains concluding references with ordinary whitespace.
7. Independent before/after snapshots agreed exactly for bytes, modes and modification timestamps across five protected trees and seven standalone files, including final v2, superseded v1, frozen science and prior Reports 40 and 42. Both snapshot files had SHA256 `09a7da96db95486dc60e6005b5252fb7bd74f2128f1cb9b5b7f85d063d1bb012`.

Only inspected newly authored report/checking/reconstruction programs and normal local build/render/archive utilities ran. No upstream Python/Lean, saved upstream schedule, physical_program.py, atlas generator or coefficient recipe ran. The enormous literal coefficient prefix was neither expanded nor executed. This was final release QA, not an additional proof of the inherited all-integer theorems.

## Reproduction after artifact recovery

Use a fresh scratch directory. Authenticate the ZIP hash above with a trusted SHA256 implementation. Reject duplicate, absolute, traversal or nonregular archive members and safely extract to an arbitrary new path. Follow the external standard-library bootstrap in the release README using the trusted manifest hash above. Do not execute bundled code before authentication. Inspect the checker/build closure before running it.

For R set to the authenticated extracted directory and Q to a new external working directory, the operations successfully performed were:

```sh
H=40421963581a67913f298ce88d48fcc4e56abc3fd77c5cf0e4f7eb9c0d5ec945
cd /tmp
python -I -B "$R/verify_release.py" --manifest-sha256 "$H" --output "$Q/moved-replay"
python -I -B -O "$R/verify_release.py" --manifest-sha256 "$H" --verify-only
python -I -B "$R/build_pdf.py" --output "$Q/independent-pdf-build" --check-packaged --manifest-sha256 "$H"
python -I -B "$R/archive_release.py" --manifest-sha256 "$H" --output "$Q/independent-rebuilt.zip"
mkdir "$Q/rendered"
pdftoppm -r 110 -png "$R/Research_Report44.pdf" "$Q/rendered/page"
pdftotext -layout "$R/Research_Report44.pdf" "$Q/final-pdf-text.txt"
```

Record protected-tree snapshots before and after, compare rebuilt PDF and ZIP bytes with the authenticated originals, and visually inspect all 12 PNGs. Determinism was established on the recorded local toolchain, not on arbitrary future TeX/zlib implementations. Never re-hash modified release bytes and treat the new digest as the trusted release identity.
