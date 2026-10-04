# Report59 Five signal rational rotation family

The PDF and editable LaTeX document the arbitrary rational infinite-order planar rotation family with rational positive scaling. Exactly five live signals realize a fixed complete collision word for each compiled machine. The report includes exact finite guards, the strict-boundary infinite-validity formula, real/rational/integer sign obstructions, the separately audited all-real topological and mixed-certificate obstruction, fixed-machine rational membership in conservative O(L^3) bit time, exact Zeno classification, and the literal degree-12 positive-integer template.

## Read the report

- `Report59.pdf`: typeset report
- `manuscript/report59.tex`: editable main LaTeX
- `manuscript/fixture-table.tex` and `manuscript/geometry-figure.tex`: exact derived presentation inputs
- `manuscript/MANUSCRIPT_PINS.json`: source bindings

The main source uses the two adjacent LaTeX inputs. Build from that directory or use the isolated builder below. No 13,572-rule listing is printed in the PDF; the complete fixture rule tables are preserved under `science/evidence/`.

## Scientific evidence

- `science/`: exact frozen 60-file scientific packet, including the static physical constructor as inert source, 45 complete fixtures and the explicit arithmetic proof
- `independent-audit/`: exact frozen 9-file independent family audit and its independently authored checkers
- `dependencies/`: inert byte-identical copies of all seven external files pinned by the science packet
- `real-input/`: frozen real-input companion proof and source notes
- `real-input-audit/`: separate fresh audit of the topology, mixed existential certificate obstruction and finite-time BSS scope
- `real-input-dependencies/`: the additional inert Report57 guard text referenced by that companion
- `qa/`: release preservation, build, visual and review evidence

The original science README predates the completed independent physical audit. The final audit and receipt in `independent-audit/` are the authoritative later status. The real-input companion begins with the earlier Report57 instance and then proves a family corollary; Report59 specializes its admissible closed-arc argument and does not substitute Report57's physical machine. The new `(3,4,5)` scaled family has 174 events and squared radius `1/65`, while the earlier machine has 138 events and squared radius `4/1845`.

All 45 physical fixtures have one distinct nearest contact. The audit's separate four-contact synthetic polygon is only a geometry diagnostic. The full-family proof handles multiple, repeated, co-orbital and initial-order-face tangencies.

## Safe reproducibility commands

Use installed Python 3 and a standard TeX Live installation with the listed LaTeX packages and Poppler. These tools do not install packages. All output destinations must be new, canonical absolute paths outside this release, with an existing parent. Do not place replay outputs inside frozen inputs. Build commands require Python isolated/no-site/no-bytecode mode and no optimization.

Authenticate frozen scientific inputs without executing them:

    python3 -I -S -B tools/release59.py check-inputs

Rebuild in a fresh temporary workspace and render every page into a fresh external output directory:

    python3 -I -S -B tools/build_report59.py --output-dir /tmp/report59-build --require-packaged-match

Regenerate the analytic figure and fixture summary in a fresh external directory, then compare them with the manuscript inputs:

    python3 -I -S -B tools/derive_presentation.py --output-dir /tmp/report59-presentation

Verify a sealed release using its separately supplied manifest pin:

    python3 -I -S -B tools/release59.py verify --manifest-sha256 PIN

Create a deterministic external ZIP only after verification:

    python3 -I -S -B tools/release59.py archive --manifest-sha256 PIN --output /tmp/Report59-source-evidence.zip

`release59.py manifest` generates a prospective manifest at a fresh external file; it does not seal or rewrite the release. The SHA-256 manifest is not a signature: compare its hash with a trusted separately supplied release pin.

The independent portable replay has its own instructions and exact pins. It reconstructs static evidence by newly written independent symbolic/grammar code, without importing or executing the author constructor. It does not simulate physical trajectories.

## Limits

This is conventional mathematical proof with independent source and exact static evidence, not Lean certification. The physical static constructor is implemented and audited; no general arithmetic DAG/compiler or source-specific arithmetic gate count is claimed. Pell theorems are explicit constructive dependencies read as inert mathematics. Finite fixtures do not replace arbitrary-parameter chronology and invariants. No priority, optimal-count, finite-fold, arbitrary-matrix, Type-2/BSS completeness or post-accumulation claim is made.

The all-real obstruction is compatible with the encoded-rational decision algorithm and integer-input Diophantine representation. Its BSS claim is specifically for ordinary finite-time field-operation computation and exact tests, with finitely many arbitrary real constants allowed.
