# Independent Lean review: Boolean auxiliary choice and residue lifting

Reviewed the complete `ControllerAuxiliaryChoice` and `ControllerResidueLift` modules and both focused check files, together with the complete imported `ControllerOrbitTransport` source. These four reviewed files were authored by the root agent; this reviewer did not author them. No source changes were requested or made.

## Mathematical findings

PASS within the stated interfaces. The first module constructs an actual Boolean choice using the nonzero projection of the optional coefficient to the prime factor. The least residue is then strictly positive, below the full modulus, and prime to every power of that prime. The characteristic-two case, exponent zero, and composite full modulus are retained. The nonzero coefficient hypothesis is essential and is tested negatively.

The lifting module derives the quotient coordinate from the actual modular projection, rather than assuming it. Nonzero `C0` and `T` give the division bound; `z.val % C0 = a` and Euclidean division reconstruct `z` exactly. This includes residue zero and `T = 1` for the coordinate lemma. In the final subset theorem the nested projection of `b` is exactly the one required by the preceding choice theorem. The chosen cardinality satisfies `0 < a < C0 < T`, is coprime to `T = p^n`, and the already proved affine transport constructs a distinct finite subset of that size. Adding back the chosen Boolean term gives the requested target.

The coordinate injection and its affine weight formula remain explicit structural hypotheses. These modules do not establish the actual power orbit, identify safe dummy positions, complete the native equation converse, or assert an internal ZFC theorem.

## Fresh replay

All four modules were replayed sequentially with the actual Lean binary selected by `lake env`, flags `-M 6000 -j 1`, and an isolated temporary object overlay. Dependency objects were symlinked read-only into the overlay; the four target links were removed before writing fresh objects. Checks imported the newly built main objects. All four exited zero, both main logs were empty, and all four printed theorem axiom reports contained only `propext`, `Classical.choice`, and `Quot.sound`. Every newly produced object was byte-identical to the existing shared object.

An initial overlay attempt had an import-path setup error: Lean selected the temporary package namespace but could not find its unsymlinked `ControllerOrbitTransport.olean`. It failed before elaborating the reviewed source. The corrected overlay supplied all dependency paths; no proof or reviewed source was changed.

Reproduction receipts and complete logs are in `/tmp/controller-choice-lift-peer-7y_4v2t6/`. Exact command shape: `LEAN_PATH=<isolated overlay>:<lake LEAN_PATH> <lake-selected lean> -M 6000 -j 1 -o <overlay>/DiophantineConsistency/<module>.olean <absolute source>`.

## Frozen identities

- `ControllerAuxiliaryChoice.lean`: source SHA-256 `e0ad958407b2888631f18c292a08c2de1af0b36297c9513e93d5f70ad4bcf251`; fresh object `e2ab2c2365303f88259e69c0de6f8bf1a9c9a719e93075bfe40d24e8ca99c157`; log `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`; exit 0 in 3.0 seconds.
- `ControllerAuxiliaryChoiceChecks.lean`: source SHA-256 `c9e0a7f6deca29550488b79f51eff60895a949a87ad207741c619379ddfd162d`; fresh object `b65f9eecfc92f7709ec3ce6bef33b2cb9b1a5976ddcbc37af8704035892457ee`; log `a6869191237788daf40ba490d499dd5ba11061f5c295b3279cc9a6299326ae13`; exit 0 in 2.78 seconds.
- `ControllerResidueLift.lean`: source SHA-256 `5b421650fb7565cb3c38f5e4819fdba7b46f61d8d1e37bc3ed786ac6ca2268cb`; fresh object `7f59df5e47fe941cd70767152db173b544203c9321da0101250f54c64f7f2918`; log `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`; exit 0 in 3.3 seconds.
- `ControllerResidueLiftChecks.lean`: source SHA-256 `1fa74f933a4bc4c2859a58734e341e028855e6027f9fd4eaf4bc092038daa328`; fresh object `6d73ac0923912e4cbb4073eee3ea9c1471e6fa25de3971bfed144bfe683b9ef1`; log `00d130703fdb29852b1a6444613e14ade9c2a178b1bcc3ef5980b4ebb2362dcb`; exit 0 in 3.26 seconds.

The authoritative durable evidence is the complete source and kernel-checked theorem statements. Temporary runtime receipts record this independent replay, not additional proof assumptions.
