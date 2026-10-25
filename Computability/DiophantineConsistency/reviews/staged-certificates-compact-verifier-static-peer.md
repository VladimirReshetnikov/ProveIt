# Static review of the staged compact84/85 finite verifier

The reviewed checker can be reused byte for byte as a selected finite audit
inside a new independently pinned packet. I find no algorithmic defect in
its checks of the supplied two circuits. It is not sufficient by itself to
authenticate that new packet's complete mathematical provenance or repaired
completeness statement. Keep it unchanged and add an independent closure,
binding and artifact-control layer. This review grants no execution release.

I read all260 lines of `133-staged-certificates/compact/verify.py`, its two
complete evaluator JSONs, parent, declared coefficient binding and runtime
receipt, and traced every import, file access and output. No incoming code
was imported, compiled or executed; no source file was restored. Missing
data were inspected in memory from the pinned Git ZIP only.

## Exact executable and data closure

The archive is `ConZFC_Staged_Certificates_2026-10-24.zip` from commit
`fd3e384e92ed4813a5536f877c5cd835ca4c75d2`, SHA256
`feca1bfc1d2f1ee9d8af7040e3bb61802d1218cc0760653e878bb7c22cbd5063`.
All paths in this table are relative to its
`ConZFC_Staged_Certificates_2026-10-24/compact/` directory.

| Runtime input | Bytes | SHA256 |
| --- | ---: | --- |
| verify.py | 12665 | 5d5c645ea19b16e9fac9b4169e21106779af6f5d309e7878009d6d98576d51bc |
| equation_84.json | 7322 | c7db162322ec4605f2bf68e73fad288ad0399d6cc9cce5fc80b95556e9f13630 |
| equation_85.json | 7379 | 75b34f2a6e1986656529da58da99b72b01265aeeb5691a69549aeac21ecea803 |
| parent-equation.json | 7486 | 954731033595b2816d3b852737ec1c05627cebf133b4621543b1c34488901670 |
| coefficients/K.bin.gz | 8694 | 35ad71ca5349bf78c996ac983a7cea6944260ed9f35c61c2b70770f5888d52ce |
| coefficients/MC.bin.gz | 193 | 71ecc4fe568471f83978d00ee7a4e03614203d6af36611c0660dbd4fd3eb2276 |
| coefficients/MF_source.bin.gz | 204 | ea069f55029bab743997b0a79b0535d5ad558686848a03cb41d72faf596a6a6a |
| coefficients/beta.bin.gz | 108 | 07d42a69e7593ac08bcb2957c965c02f179588b0c3b232c3c640258d0aaeab04 |

This is the entire application runtime closure: eight files,44051 bytes.
Imports are only Python standard-library `collections.Counter`,
`copy.deepcopy`, `hashlib.sha256`, `pathlib.Path`, `argparse`, `ast`, `gzip`,
`json` and `math`. There are no local/dynamic imports, subprocesses, network
calls, `eval` or `exec`. The restricted AST visitor parses hardcoded
polynomial strings; it does not execute their Python representation.
`main` reads the seven data files relative to the checker, prints JSON and
optionally writes the explicitly supplied `--output` path. It does not run
a generator, parent evaluator or other staged-certificate program.

Every existing placed runtime file is byte-identical to the archive.
The placed tree lacks the MC,MF_source,beta gzip inputs, so it cannot run
as placed. All three are present in the original archive. A future private
packet can copy these authenticated bytes, or the already byte-identical
accepted indexed payloads, without restoring the frozen incoming tree.

## What the checker establishes

* The exact positive ten-input/four-port signature and N output are fixed.
  Duplicate gates, non-topological operands and unknown operators are
  rejected. Backward liveness requires every gate,input and fixed port.
  Counts and all three operation subtotals are checked independently of
  their metadata:84=50 products+19 sums+15 differences and85=51+19+15.
* Its29 ordered semantic cuts expand literal gate definitions in a sparse
  polynomial ring over the integers, leaving every previously justified
  boundary and all four coefficient ports symbolic. Equality checks every
  coefficient of each cut, not values at test points. The union of expanded
  gates must be the whole circuit. This proves the complete composed
  polynomial identity without listing its enormous final expansion.
  The V cut is explicitly overridden at line120 to `Fsqr*cTR-c`; the
  unused `Df*cTR-c` spelling in `formulas` is not the audited formula.
* Coefficients are decompressed, checked against compressed and raw hashes,
  decoded little-endian, and required to have canonical byte/bit lengths.
  Both candidate bindings and the copied parent's whole binding agree.
  These are exactly the four indexed payloads already compared in full in
  the separate ordinary review,295388 raw bytes in total.
* Degree is not inferred from sampled integer evaluations. Gate propagation
  supplies a valid total-degree upper bound. `polynomial_ray` then computes
  the entire polynomial after all ten inputs become one indeterminate t,
  modulo2305843009213693951, using exact coefficient arithmetic. A nonzero
  coefficient at t^436 or t^328 proves attainment of the upper bound over
  the actual fixed tuple. Even without invoking primality, a nonzero
  residue proves the integer coefficient is nonzero. The expected ray
  coefficients agree with the independently derived homogeneous forms.
  This does not alone certify every multivariable coefficient of that
  homogeneous form; it does certify the claimed global degrees.
* Exact free-boundary identities check doubling, Q's G factor, the strong
  norm, complete carrier clearing, finalizer sharing and two elementary
  bound numerators. The5880 gcd controls are supplementary finite stress
  cases, not a replacement for the ordinary valuation/coprimality proof.
* Five genuine altered-gate controls per circuit are sent back through
  `audit`: wrong doubling factor, undoubled auxiliary base, wrong weight,
  missing n input and wrong final sign. Checks use `require`, not disabled
  assertions, so optimization does not remove their logic.

The two archived normal/optimized receipts are identical3713-byte files,
SHA256`4dff61b9a3321391d2fe82407e83a808287b7788efe0050ea5f848b3eb78ab0e`.
They were read as historical claims; neither receipt was reproduced here.

## Required independent packet layer and unresolved scope

The checker trusts the hashes and binding declared by its first input JSON.
It verifies their internal consistency, not an independently fixed accepted
tuple. A coordinated replacement of both circuits' binding, the copied
parent and payloads can satisfy its coefficient box without being the
approved whole native instance. It authenticates the parent using the
first candidate's declared parent hash; the second candidate's parent/proof
metadata and both candidates' source-commit/proof-status fields are not
independently checked. This is a provenance gap if this script is treated
as the entire release checker, not a defect in its free-port algebra.

A fresh packet should therefore pin this executable, both entire DAGs, all
four compressed AND raw payload identities, the exact accepted89 parent,
the complete indexed/native proof dependencies, and its own inventory
before running the unchanged checker. The compact directory has22 archived
members, but only the eight above are runtime inputs. None of the proof,
provenance, REVIEW_PINS or report files is read by this verifier.

In particular it cannot fix or detect the incoming generic shifted-T
positivity overstatement. Its ordinary license must explicitly retain the
actual canonical R>3q>=96 premise. At R=3 the generic construction gives
T*=1, so T*−alpha is not positive. With the retained larger canonical R,
the accepted growth argument supplies T*>alpha. See the independent
ordinary record `staged-certificates-compact-ordinary-peer.md`, SHA256
`2de80694e803dd2444771ffc5b62819053e4796c8cff654f7f9da1516c4cc22d`.
That qualification belongs in the new proof/binding, not as a silent edit
to this incoming script or its frozen proof.

The independent layer should also exercise actual closure/artifact
mutations: changed payload/hash, parent or proof binding, signature/domain,
forward/duplicate/dead gate, semantic gate error and declared count/degree.
It should include valid controls and deterministic normal/-O replay records
from private copies. The incoming five-per-point gate controls do not cover
these binding paths, nor do the historical receipts pin their own checker.
There is no compact circuit producer or deterministic rebuild check in
this runtime closure; a byte-exact fixed-input reconstruction check can be
specified separately without inventing a producer result.

No further independent algebra algorithm is required merely because the
degree witness is a ray: it is exact, not probabilistic. A separately
implemented collector or homogeneous-leading-form audit remains useful
additional evidence and should be accurately described if supplied.
This review accepts neither a new finite endpoint nor execution of this
script, and does not import the rest of the220-member archive's programs.
