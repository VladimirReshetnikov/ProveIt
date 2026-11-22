# Finite observations of continuous mathematics in iPRA

Open **report.pdf** for the arguments. The editable article begins at **report.tex** and includes the sections in **manuscript/**. The four applications concern metric-enriched composition, continuous model theory, Jordan crossings, and complex residues. The last section identifies the status of each mathematical and formal result.

## The checked arithmetic theorem

For any two fixed primitive-recursive binary score programs, if every candidate in the second row has a match in the first whose score is at most its score plus an error, the first minimum is at most the second minimum plus that error. The two last indices, score parameters, and error are all quantified inside iPRA. UniformMinimum.lean builds the closed derivation using two quantifier-free inductions. Its symmetric theorem gives the two-sided estimate used in both the metric and model-theoretic chapters.

## Formal files

| File in lean/ | Result |
|---|---|
| MetricKernel.lean | Actual iPRA minimum and diagonal-probe rules on unrolled rows |
| UniformMinimum.lean | Actual iPRA variable-horizon minimum transfer, including its two-sided form |
| ModelCase.lean | Standard Lean numerical comparison over nonempty lists for the nonexpansive language |
| ModelObject.lean | Actual iPRA upper-cut compiler for fixed finite nets and lattice formulas |
| TopologyCase.lean | Standard Lean bracket shrinking, geometric rate, polynomial difference and probe estimate |
| TopologyObject.lean | Actual iPRA polynomial difference identity for specified degree and arbitrary integer terms |
| ComplexCase.lean | Standard Lean strip cancellation, shell clearance, Gaussian multiplication and derivative estimate |
| ComplexObject.lean | Actual iPRA strip incidence identity, including the four-panel square |

The formal files cover the indicated lemmas. The completed-name category, general Jordan interface, and full analytic derivations have human proofs or explicitly identified upstream inputs. The report describes how to carry these interpretations through ProveIt's embedded proof system.

## Reproduction

Use Python 3.10 or later. The exact examples have no third-party dependencies.

    python3 verify.py

With Lean 4.32.0 installed, the following also checks the three standard-library modules.

    python3 verify.py --host-lean

For all eight modules, use the ProveIt root workspace at commit 5f3be02388442f16487d2dc5c2529961dd783d2b with its declared toolchain and pinned dependencies available. The following builds the required upstream module and checks the enclosed files in a temporary output directory.

    python3 verify.py --proveit /absolute/path/to/ProveIt

An environment with the same providers prebuilt can instead use the following.

    python3 verify.py --providers "$LEAN_PATH" --lean /path/to/lean

The verification receipt records the completed run on staged providers. Upstream source identities on the transitive ProveIt dependency closure are listed in verification/providers.tsv.

To rebuild the report with a standard TeX Live installation, run the following from this directory.

    latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

The PDF figure is included for ordinary TeX builds. The file figures/root_selection.py regenerates it with Matplotlib and the same exact bracket routine as the topology example. MANIFEST.sha256 gives the hashes of the files in this archive other than itself.
