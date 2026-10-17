# Arithmetic meanings of the actual per-instruction site checks

`ArithmeticSitePerm252.lean` turns an accepted Boolean check in the existing
`SitePerm252` module into a numeric execution contract in every model of
IΣ1. It reuses the actual `runTo`, `runHalt`, `checkSite`, physical register
map, path operations, overflow tests and fixed fuel. It introduces no new
site certificate format and does not replay the 233 coverage chunks.

For an externally fixed path and operation, the nine primary register values,
trailing zero-spare count, gap and execution clock range over the arithmetic
model. The register list has external length nine; this is not an internal
variable-length list representation. The concrete tape interpretation retains
the fixed eight zero spares followed by the spare of value one, then the
variable zero suffix and its final padding.

The checked contracts are:

- accepted `runTo` yields a positive internal clock reaching the entire
  requested numeric configuration;
- accepted `runHalt` yields a positive internal clock with state zero after
  the complete final write and move;
- accepted increment, decrement, break, continue and halt sites give those
  same endpoints, with the original path and overflow conventions;
- decrement tests the original physically selected value. Its zero branch
  leaves the registers unchanged. Its positive branch decrements that value
  and appends one zero spare inside the concrete effect, without a second
  update to the outer count;
- the original acceptance test entails the forty-cell external path bound
  and the register-selector bounds; node entries are rejected.

The execution result follows from the checked arithmetic interpretation of
`SymbolicPerm252.verifies` and `verifiesHalt`. The accepted-site premises remain
explicit. This module does not establish a represented internal program
counter, an arithmetic dispatch invariant, global runtime simulation, or a
new PA endpoint. It makes no new claim about a smaller machine. Mira-Cult,
Jeff and Wade retain their machine and framework attribution.

## Verification

The first source and audit check passed with the official absolute Lean
4.32.0 compiler, using one thread and a 4 GiB process limit. The source took
2.095 seconds and the audit 2.134 seconds. All twelve named axiom probes and
fourteen generic caller examples passed, using only `propext`,
`Classical.choice` and `Quot.sound`; neither command produced warnings.
`autoImplicit false` is enabled in both files.

The guarded checker reused exactly 55 project modules with matching source
and object hashes, five selected external boundary objects, and the actual
first toolchain providers for `Init` and `Lean.Elab.Tactic.Omega`. It checked
132 input paths before and after the commands and checked that the fresh
object was unchanged by the audit. It rebuilt no dependency, downloaded
nothing, and did not rebuild the native coverage or bootstrap proofs.

The source and audit hashes are respectively
`259254c134af4666c807f5c7b8da96b4bc623202a4431f72c2fd76874fd6d4bf`
and `549e31d659a0477d03cfc35ca7dcb25425750b13d2f53b980512a91084e13b2b`.
The successful original record is preserved byte for byte in
[the verification record](results/arithmetic-site-perm252-verification.json).
[Publication metadata](results/arithmetic-site-perm252-publication.json)
separates that proof check from the maintained-default prepare-only run and
four expected guard rejections. These checks ran no source or audit
compilations; compiler discovery does invoke `lean --version`. The historical
control record's phrase “no compiler commands” means no proof builds and is
corrected here. There were no failed proof attempts.

From the repository root, supply a full checkout containing the pinned,
already-built Foundation and Mathlib dependencies:

```sh
python3 Computability/BusyBeaver/Research/ZFC/check_arithmetic_site_perm252.py \
  --repo "$PWD" \
  --dependency-root /path/to/built/Proofs \
  --execution-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-symbolic-execution-perm252-verification.json \
  --native-evidence Computability/BusyBeaver/Research/ZFC/results/command-word254-integration-verification.json \
  --output /outside/empty/site-check
```

Add `--prepare-only` to validate the source and object providers without
compiling. The native prerequisite is the exact recorded 169-unit source
closure; the arithmetic prerequisite is the successful 25-probe/20-caller
SymbolicExecution check. `--cache` may relocate their project objects only
when every selected object still matches the recorded hash. The selected
external objects come from `--dependency-root`, or explicit repeated
`--library-path` arguments, and must match the recorded providers. This is
reuse of checked objects, rather than a fresh build of those dependencies.
