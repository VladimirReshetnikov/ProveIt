# Independent review: Report 62 portable replay adapter

Date: 2026-10-04 UTC

## Verdict

**ACCEPTED within the explicitly limited release-replay scope. No correctness or execution-boundary blocker was found.**

The adapter authenticates the complete relocated science and independent-audit inventories, executes the byte-identical owned independent checker without disabling assertions, and compares its mathematical evidence, 44-rule evidence and stdout exactly with the authenticated originals. It distinguishes fresh transport preservation evidence from the immutable historical snapshots. All 24 supplemental CLI cases passed. Original science and audit bytes, modes, nanosecond mtimes, object identities and inventories remained unchanged in the review's before/after records.

This is a transport, authentication and evidence-reproduction review. It is not an additional proof of the science, a physical simulation, or a hostile-code sandbox audit.

## Exact reviewed revision

| Item | SHA-256 |
|---|---|
| `replay.py` | `d1917acf7ef7880e874d2e302095b893ddb2a2001b3e8d9f33119a50e9d29ba2` |
| `PINNED_INPUTS.json` | `d20b85535be14fb12c2494447b8326dc260310c2d9441677f48866eb6e2658f8` |
| Boundary/usage `README.md` | `8096ee054e368b1abbdab641565f2636739006125fb920933cca91b8e2e1b1ba` |
| Unchanged `independent_static_audit.py` | `a945491e115e5f96dfc11e3d6e714ef367ecc0daddfce425d8310cb5949f4fec` |
| Main science `PROOF.md` | `502e90e091eabc0a6c8eb6092e73f4407ae84f143d337be8a4a633a3f85a7c47` |

The adapter and pin hashes were recorded before testing and rechecked afterward. The final README was read in full; its scope and boundary descriptions agree with the implementation. The review applies to these bytes. `test_replay.py` was separately read as source; its 42-case result file was inspected but that suite was not represented as the reviewer's independently executed suite.

## Static findings

### Authentication and input ownership

- The pins file itself is authenticated against a SHA-256 literal in the inspected adapter.
- The science inventory contains 14 regular files, its root and two internal directories. Both dependency proofs, the author source, `MANIFEST.json`, `SHA256SUMS.txt`, and all other scientific evidence are included.
- The audit inventory contains nine regular files, its root and its evidence directory. It includes the checker, review, manifest, checksum file, both historical snapshots, and all three golden evidence products.
- Actual object names must exactly match the pinned directory/file sets. Additional empty directories are rejected, as are missing files, symlinks, nonregular files and regular files with multiple hard links.
- Root arguments require canonical absolute spellings without symlink components. Input/output overlap, output under a protected tree, existing output paths and detected object aliases are rejected before checker execution.
- File reads use `O_NOFOLLOW` and compare stat tuples around opening/reading. The complete source/audit inventories and pins file are reauthenticated after execution. This is useful defense in depth under the stated quiescent-filesystem assumption, not a claim to defeat arbitrary concurrent mutation.

### Exact execution and path routing

- Packet code execution is one `exec(compile(...))` of the authenticated independent checker bytes. The author's `static_algebra.py` and all science, proof, rules, manifests and historical evidence are inert data.
- Compilation explicitly sets `dont_inherit=True, optimize=0`. A supplemental compile-only inspection under outer Python `-OO` found three `LOAD_ASSERTION_ERROR` instructions across the checker and its functions at optimize=0, versus zero at optimize=2. No checker execution occurred in that probe.
- Only the executed checker's `from pathlib import Path` import receives the local facade. The global `pathlib` module and imports inside installed dependencies are not patched.
- Historical-root substitution occurs only for direct facade construction. Internal derived paths retain their actual relocated identity, including when the relocated audit root itself has the historical science-root spelling.
- The historical absolute science root routes to the authenticated relocated science tree. The unchanged checker self-read routes to its relocated authenticated file. Its `HERE / 'evidence'` routes to fresh output, so its writes and its preservation-baseline read never overwrite the original audit evidence.
- The facade exposes the operations used by this specific authenticated checker and restricts writes to the three expected generated evidence filenames with exclusive creation.

### Exact evidence and preservation

- `independent_checks.json`, `rule44_static_review.json`, and stdout are compared byte-for-byte against authenticated audit inputs. The checks reproduce all 157 named static checks and the recorded coefficient-one counts, with trusted SymPy 1.14.0.
- A fresh science metadata snapshot is generated in the new output directory. The checker computes a new after-snapshot of the actual relocated science tree; these JSON byte strings must agree exactly.
- The immutable audit `frozen_before.json` and `frozen_after.json` remain separately authenticated, untouched historical inputs. They are not substituted for the actual relocation metadata and their old timestamps are not written back to relocated files.
- In addition to the emitted science snapshot pair, the adapter compares before/after science and audit metadata tuples in memory. Those tuples include device, inode, full mode, link count, size and nanosecond mtime, and every regular file is rehashed.
- The emitted fresh JSON pair describes the science tree. There is no separate emitted before/after JSON pair for audit-tree metadata; exact in-memory comparison plus byte authentication covers the audit tree. This distinction should be retained in release descriptions.

## Independently executed supplemental tests

The fresh inspected `supplemental_tests.py` invokes the adapter with isolated Python (`-I -B`), using only disposable relocated copies. All 24 cases passed:

1. Read-only science/audit trees relocated into paths with spaces and Unicode, all mtimes deliberately changed, outer Python `-OO`, and untrusted module-name trap files in the launch working directory: success; golden outputs match exactly and no trap module executes
2. Ordinary relocated success: all golden outputs and fresh preservation snapshot bytes match
3–7. Same-length science tampering in each dependency proof, science manifest, science checksum file and author source: rejected
8–15. Same-length audit tampering in the checker, audit manifest, audit checksum file, both historical snapshots, mathematical evidence, rule evidence and stdout evidence: rejected
16–17. Additional empty audit directory and additional science Python file: rejected
18–20. Science symlink file, hard-linked checker, and FIFO replacing a regular input: rejected
21–22. Symlink output ancestor and output within audit: rejected
23–24. Altered pins file and missing dependency proof: rejected

All 22 negative cases failed before output creation. Every case independently compared its science/audit trees before and after the adapter invocation. Those comparisons included bytes, mode, mtime, size, device, inode and link count. They all passed, including the deliberately malformed disposable trees.

The changed-metadata read-only case confirms that the fresh science snapshot differs from the immutable historical snapshot while agreeing exactly with its own fresh after-snapshot. Thus the transport-success result does not depend on preserving or faking the historical filesystem metadata.

The adapter author identified and corrected one portability edge after the first passing revision: recursively applying the historical-root substitution could misroute the checker's derived parent if the relocated audit root happened to have the historical science-root spelling. The final revision restricts remapping to direct facade construction. All 24 CLI cases were rerun on the final hash above and passed.

A separate focused unit regression extracts only the exact inspected adapter facade class AST and supplies disposable path roots. Six checks passed: direct historical-root mapping, actual checker-self identity, resolved parent retaining actual audit identity, evidence routing from that parent, resolving that audit root without remapping, and globbing its actual checker path. This probe never executes or alters any science/audit packet source and does not touch either original tree.

Release evidence: `supplemental_results.json`, `facade_edge_test.py`, `facade_edge_result.json`, `assertion_bytecode_check.json`, and `original_inputs_before.json` / `original_inputs_after.json`. The supplemental JSON embeds all per-case stdout/stderr and preservation verdicts. Diagnostic fixture trees remain outside the release: they intentionally contain malformed objects such as a FIFO, symbolic link and hard link and must not be recursively packaged. Copy only the regular top-level artifacts named in `REVIEW_MANIFEST.json`, plus that manifest and `SHA256SUMS.txt`.

## Retained limits and nonclaims

1. **Trust the Python interpreter, standard library, installed SymPy 1.14.0, inspected adapter bytes, and filesystem/runtime environment.** A version string alone does not authenticate the installed SymPy implementation. Use the documented isolated Python invocation; this review tested that invocation.
2. **Use a quiescent POSIX filesystem.** `O_NOFOLLOW`, single-link requirements and before/after checks reduce accidental aliasing and detect many changes; they do not provide a race-free hostile-filesystem proof. A concurrent writer that changes and restores state can be outside these checks.
3. **The facade is specific path routing, not a generic path sandbox.** Its read-root membership check is lexical, and its surrounding execution retains normal builtins and trusted imports. It is safe within this assessed design because the exact fixed checker and exact fixed manifest bytes are authenticated before execution and their concrete accesses were inspected. Do not substitute arbitrary checker source or claim the facade confines adversarial Python code.
4. **There is no OS or network sandbox claim.** No network, process or system-call isolation is installed by this adapter.
5. **Metadata scope is explicit.** Modes, nanosecond mtimes, sizes, identities and link counts are compared as described; atimes, ctimes, extended attributes, ACLs, ownership and mount behavior are not all authenticated preservation properties. Reads may affect access times.
6. **Authentication has a trust root.** The inspected adapter contains the pins digest and checker digest. Replacing the trusted adapter together with its pin file is outside this release-authentication claim; release-level distribution/authentication remains necessary.
7. **Evidence reproduction is limited to the owned symbolic/static audit.** No author/upstream executable, physical simulator, constructor or saved schedule was executed. Successful replay does not broaden the mathematical claims or remove the proof's hypotheses.

## Original-input preservation

The reviewer's original-input before/after snapshots are byte-identical. They cover all 17 science objects and all 11 audit objects. No original input was edited. The checker source and complete original proof dependency bytes remain unchanged.
