# Research Report 33: portable bounded replay

This package accompanies the signed19 negative-index restoration **existence
proof**. It supplies independently authored, standard-library-only arithmetic
checks and immutable cached source evidence. The finite checks are corroboration,
not a computation of a complete nineteen-witness child zero.

## Run without installation

Python 3.9 or newer is sufficient. No third-party packages, network access,
compiler run, upstream import, or current working directory assumption is needed.
From any directory, run the launcher by its path:

```sh
python3 -I -B /path/to/repro/verify.py
python3 -I -B -O /path/to/repro/verify.py
python3 -I -B /path/to/repro/verify.py --replay
```

`--replay` launches both normal and optimized isolated Python processes with
working directory `/`, writes their results only in a temporary directory,
compares them with `CHECKS.json` byte-for-byte, tests fail-closed handling of four
modified evidence copies, and checks every packaged file's before/after byte
hash. Each command exits nonzero on failure. For a saved fresh output use
`--output /some/existing/directory/new-name.json`; the output must be outside
this package and the file must not already exist. With `--replay`, this writes
the replay-harness report; without it, it writes the recomputed `CHECKS.json`.

## Identity and execution boundary

1. `verify.py` is the small launcher trust root. Its literal SHA256 pins
   `FROZEN_HASHES.json`. The article package should independently pin the launcher.
2. Before compiling the newly authored `checks.py`, the launcher checks the
   manifest identity, all listed SHA256 hashes, safe paths, and exact inventory.
3. It then compiles the **already verified in-memory bytes** of `checks.py`.
   Source caches with `.py` extensions are never imported, compiled, or executed.
   JSON schedules are parsed only as data and never evaluated as programs.
4. The source receipt's SHA256 and Git blob SHA1 are recomputed for all 16 cached
   sources. All public URLs are pinned to the stated repository commit.
5. JSON parsing rejects duplicate keys and nonfinite constants. Saved-result
   comparison recursively requires identical JSON types: `true` is not `1`, and
   `1` is not `1.0`. Canonical output bytes must also match exactly.
6. Every check uses ordinary conditionals and exceptions, not Python `assert`;
   Python `-O` cannot remove them. The replay includes an explicit type-semantic
   self-test and modified-copy identity-gate tests under `-O`.

This is integrity relative to the frozen launcher and previously recorded source
receipts, not a digital signature or a new online authentication of the repository.
No hash file can authenticate itself. `FROZEN_HASHES.json` excludes itself and
`verify.py`; their binding is the launcher's literal digest and the enclosing
article manifest. Do not regenerate any hashes to make a failed replay pass.

## What is checked

- All 16 SHA256/Git-blob receipts and the exact reviewed proof/audit binding
- Literal 72-gate transfers for all three source forms, deletion of the supplied
  index and only its index comparison, replacement at both uses, exact signed19
  coordinates/eight comparisons, and arithmetic-operation **label counts**
- Full recursive Lucas `n-1` certificate for the 98-bit prime
  `178102175547812809030053265409`: 84 certificate nodes, 16 distinct primes
- Exact order of 2 modulo `3 ell`, derived only from the certified factorization:
  `22262771943476601128756658176`; all prime-divisor minimality tests
- Prime progression, crucial gcd, parity, CRT, repunit/scaling, transport,
  shifted-packing, positive-input-root and index-slack identities for 32 cases
- 451 main Pell/projection fixtures; 160 first-Pell/factored-norm fixtures
- 25 exact coefficientwise odd-quotient polynomial identities (degrees 0–24)
  and 200 corresponding integer evaluations
- Six strong-auxiliary divisibility/congruence fixtures at `(A,p)` equal to
  `(2,3),(3,3),(4,3),(5,3),(6,3),(2,7)`; the largest computed `f` has 38,715 bits
- One small **local auxiliary block** at `(A,p)=(2,3)`, including positive
  `i,j,o,f,y`, both linear equations, and the full strong auxiliary Pell residual

The last five auxiliary cases calculate `U` modulo `c` and `f`, using a binary
odd-quotient recurrence. They do not materialize the far larger `U,y`. No main
Pell value at the enormous outer CRT indices is materialized. The representative
`n` used in each outer case checks a congruence only; it is **not** claimed to
satisfy the main/first ratio interval.

## Exact limitations and mathematical proof

The outer fixture uses `d=5,N=1,b=1,x=1,K0=0,MC=2,MF_native=4`. These are
**toy values**, not an authenticated compiler export. They exercise arithmetic
identities without instantiating an accepting computation or the full child.
The unbounded theorem uses arbitrary actual fixed compiler exports unchanged.

The proof's use of Dirichlet's theorem and irrational-rotation density is
mathematical, not replaced by finite sampling or by a numerical search for ratio
hits. No complete signed19 child zero is numerically materialized. The local
auxiliary fixture is not a complete child counterexample. The replay establishes
no improved universal bound, no conclusion about a particular machine's accepted
language, and no negative-restoration result for positive21 or raw29.

Read `evidence/FULL-SIGNED-COUNTEREXAMPLE.md` together with
`evidence/INDEPENDENT-AUDIT.md` for the full quantified construction. The audit is
PASS for exactly the proof whose SHA256 is
`b109e2fd1142cdad84a5b519acc5dc5055160f1d8e7617d648a561538fd956cd`.
The older bootstrap/kernel records and the raw/positive reduction are context,
not substitutes for that final proof/audit.

## Files and provenance

- `checks.py`: newly authored bounded tests, with no external dependencies
- `verify.py`: frozen identity gate and isolated replay/tamper-test launcher
- `CHECKS.json`: deterministic, exact-typed, canonical expected test result
- `REPLAY.json`: observed successful normal/optimized isolated replay result
- `FROZEN_HASHES.json`: SHA256 inventory for all payload files
- `source_manifest.json`: original receipt, copied byte-for-byte
- `sources/`: all 16 authenticated cached source files, copied byte-for-byte
- `evidence/provenance.json`: original relative names and original/packaged hashes
- `evidence/prime-certificate.json`: original read-only certificate data
- `evidence/bounded-check-results.json`: original historical output, reproduced
  exactly with new code; its original SymPy/assert-based generator is excluded
- Other `evidence/` files: final proof, three independent reviews, two reviewed
  historical snapshots, and raw/positive boundary discussion

The upstream cache origin is `VladimirReshetnikov/ProveIt` at commit
`2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff`. Exact public URLs, SHA256 hashes,
and Git blob SHA1s are in `source_manifest.json`. The receipt was not rewritten.
Every packaged authored evidence file currently remains byte-identical to its
original; no sanitization was needed. Local absolute paths do not appear in
these evidence copies. Original hashes remain in `evidence/provenance.json`.
The historical audit uses some original relative links; its provenance record
identifies each included target even though the evidence files are flattened.
