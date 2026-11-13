# Same-index C residue

For the same positive 74 graph zero, positive beta/valuation and stated arithmetic-model hypotheses, with `q≥4`, `Trace74CResidue.graph_C_residue` proves that there is a first-Pell index n≥3 satisfying its first-Pell equation and the signed difference-ring congruence

```
q ∣ C + MC·J + 1 − 2n.
```

The ring identity `rank_mod_q` evaluates the actual 74 rank modulo q; the graph client combines it with the existing q⁴ signed rank congruence and index-at-least-three theorem, keeping the same p/v/n. No individual C or F bound, rank nonnegativity or reverse guard follows from this statement alone.

Reviewed attempt03 passed in actual tool session 96426, outer exit 0, with both named axiom reports clean. Terminal `observations/attempt03/terminal.json` SHA-256 `3d618b621b06278c6358525a3cca83da754b93574ec0e4e36fb46fddf50d3efc`; object `/tmp/trace74-c-residue-du_5k1ij/lib/Trace74CResidue.olean` SHA-256 `8b58585727e674403ec6fc058266e8d786b5df6650c75302242f95bff7622b0d`. Independent [result audit](../../reviews/trace74-c-residue-result-independent/README.md) passed, SHA-256 `1670a1cf7e08aea1a112e7f666022ea6b4ced2503806014ef29a774c31cb89fc`. Direct-pin/search-path and inherited project/package/dynamic ancestry limits remain.

Attempt01 was rejected after a folded local q simplification error and contained `sorryAx`. Attempt02's Lean proof and axiom reports passed, but the strict runner rejected an unnecessary sequencing warning; attempt03 made the warning-only correction. The [source review](../../reviews/trace74-c-residue-source-independent/README.md), [prelaunch](../../reviews/trace74-c-residue-prelaunch-independent/README.md), and [warning-only retry review](../../reviews/trace74-c-residue-warning-retry-independent/README.md) are separate.
