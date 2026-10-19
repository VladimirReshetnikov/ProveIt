# Attribution, source pins, and license scope

This package combines the pinned K230 logical construction with reductions and verification machinery from the ProveIt research archives. The new work comprises the adapted source and machine reductions to 226 states, their executable certificates and independent audits, the E639 descriptor-binding improvement, and the accompanying report. It was prepared in this ChatGPT research session for incorporation into ProveIt.

## K230 and its proof dependencies

**Elliot Glazer's K230 construction** supplies the theory K, its consistency comparison with ordinary ZFC, the released 230-state table and source certificate, and the Rocq endpoint to which the smaller machine is calibrated. The vendored repository is pinned to:

- Repository: [elliotglazer/k230-rocq](https://github.com/elliotglazer/k230-rocq/tree/3142e4dd980f0be12f4abb636c4ae2528afc17eb).
- Commit: `3142e4dd980f0be12f4abb636c4ae2528afc17eb`.
- Table SHA-256: `e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8`.
- Source SHA-256: `400fad2b1c5f99ed8490f6346ff63088ba94fc39ada376962cee2f68c092e487`.
- Manifest SHA-256: `bbd4694416cef144c8cad8099148a08c5a81114a81e358ad3f0d2dd5cdea6119`.

Its reference proof development is [jeff87654/busy-beaver](https://github.com/jeff87654/busy-beaver/tree/c132d7eae8158cd3a9850ea3eb7251158c3dd821), commit `c132d7eae8158cd3a9850ea3eb7251158c3dd821`. That development verifies Mira-Cult's 254-state construction and supplies the logical and set-theoretic libraries adapted by K230. Compiler provenance includes **Andrew James Wade's Turing Machine Explorer** and the subsequent Mira-Cult, Jeff Ketchersid, K230, and ProveIt contributions.

The original [vendor/k230-rocq/THIRD_PARTY.md](vendor/k230-rocq/THIRD_PARTY.md) is retained. It identifies the adapted proof files, compiler lineage, and the following complete notices:

| Material | Preserved notice |
|---|---|
| BusyCoq, copyright 2023 Maja Kądziołka | [MIT](vendor/k230-rocq/LICENSES/BusyCoq-MIT.txt) |
| LibTactics, copyright 2018 Arthur Charguéraud | [MIT X11, including its additional name-use paragraph](vendor/k230-rocq/LICENSES/LibTactics-MIT-X11.txt) |
| Coq Library of Undecidability | [Mozilla Public License 2.0](vendor/k230-rocq/LICENSES/Undecidability-MPL-2.0.txt) |
| Andrew James Wade's compiler sources, copyright 2025 | [MIT No Attribution](vendor/k230-rocq/LICENSES/Wade-MIT-0.txt) |

Rocq and its standard library are separately installed dependencies with their own distribution notices. The supplied compiler and kernel logs describe the upstream K230 build, not a newly kernel-checked proof of the 226-state table.

## ProveIt reductions and runtime-engine lineage

The user-specified comparison point is [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/0128d662fd46f72dc84505176ae8ec28affb2d9d), commit `0128d662fd46f72dc84505176ae8ec28affb2d9d`. Its incoming archive is:

```text
docs/incoming/ZFC235_Construction_2026-10-19.zip
SHA-256 b85176325ea106e8b758aa8a7fa3c661af3e91d112bbe35af6da851eae5f71c9
```

That 235-state package retains the exact 236-state package from ProveIt commit `0b5fec6980cc3a5ba7dd47b404f0cbbe9a451c02`:

```text
docs/incoming/ZFC236_Construction_2026-10-19.zip
SHA-256 540305f4e805165e818290e82c5a6cba5faed25b5abb946fd9c750f6c45db9f5
```

The 236-state package in turn includes the 237-state work as `upstream/zfc237/`. Its recorded incoming 237-state archive pin is:

```text
ZFC_237_State_Construction_2026-10-19.zip
SHA-256 e5e368406a17400d86a94714b6fd6140c80b0f28550233da6e5b829f1fe80286
```

The 237-state provenance records inspected ProveIt commit `ce192939372ac7944fe2a0208c68a96d49fb5e3b` and inherited calibration pin `13ec39ed43148b1807f51ed6e6528e1c84659562`. This identifies the source lineage; the main 226-state logical endpoint is transported from the separately pinned K230 endpoint.

The two files in this package's `verification/engine/` are **byte-identical** to `upstream/zfc237/verification/` in that inherited chain:

```text
symbolic_runtime.py
c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145

independent_runtime.py
0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346
```

The K-label adapter, fresh baseline/final replay, source and machine audits, and dense-tape startup audit are part of the new transport package. Reuse of the unchanged engine is credited separately from those additions. The ProveIt predecessor notices credit Mira-Cult, Jeff Ketchersid, Andrew James Wade, and preceding ProveIt contributors.

## Equational supplement

[supplement/inherited_formalisms/](supplement/inherited_formalisms/) retains the ProveIt E663/E667 material, its predecessor E688/E692 references, and the original [attribution](supplement/inherited_formalisms/ATTRIBUTION.txt), [semantic audit](supplement/inherited_formalisms/AUDIT.txt), and [MIT No Attribution notice for ProveIt Contributors](supplement/inherited_formalisms/LICENSE.ProveIt). Its raw-EPSC/ZFC calibration is inherited from the explicitly cited ProveIt Sources 08 and 14 and their interpretation dependencies.

The Boolean single axiom Sh1 is due to **McCune, Veroff, Fitelson, Harris, Feist, and Wos**, *Short Single Axioms for Boolean Algebra*, Journal of Automated Reasoning 29 (2002), 1–16. The [primary paper](https://www.cs.unm.edu/~mccune/papers/basax/v12.pdf) is cited in the report. Sh1 is an inherited axiom, not a discovery of this package.

The new E639 supplement changes descriptor representation and proves the corresponding relative model calibration. It measures a complete 639-bit equational input under the inherited codec. It provides no new binary-machine state count and is separate from the 226-state K230 transplant.

## License scope

All retained notices apply according to their stated scope. As the pinned K230 `THIRD_PARTY.md` records, no root license or explicit license notice was found in the pinned reference's custom `ZF/m254`, `ZF/stdzf/coq`, `ZF/stdzf_r3/zfc`, or `ZF/stdzf_r3/regcon` sources. The MIT, MIT No Attribution, MIT X11, and MPL notices above do not assign a license to those custom files or to portions adapted from them.

This package does not assert a blanket MIT or other repository-wide license covering inherited material with unresolved license scope. Attribution and source availability do not themselves resolve that scope. The new mathematical contributions are identified separately so that incorporation can preserve all existing notices and contributor credit.
