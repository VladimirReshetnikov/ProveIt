# Same-index F/C residue modulo q²

For the same positive 74 graph zero, positive beta/valuation and stated arithmetic-model hypotheses, with `q≥4`, `Trace74FCResidue.graph_FC_residue` proves there is a first-Pell index n≥3 satisfying its first-Pell equation and the signed difference-ring congruence

```
q² ∣ C + MC·J + q(F+MF·J) + 1 − 2n.
```

The generic ring identity `rank_mod_q2` gives the exact quotient `q(q−F)−C−1` for the difference between the actual 74 rank and its displayed low blocks. The graph client combines it with the existing signed q⁴ rank congruence and index-at-least-three theorem, preserving the same p/v/n. This strengthens the earlier C residue and mentions both F and C; it does not by itself bound either variable, establish rank nonnegativity or prove the reverse guard.

Reviewed author attempt01 passed in actual tool session 24872, outer exit 0, with both named axiom reports clean. Terminal `observations/attempt01/terminal.json` SHA-256 `94fea7c3b694ab6d732b4cf25ca0977fbab20a842de355a57794791f67ee2769`; object `/tmp/trace74-fc-residue-ipdf3fpx/lib/Trace74FCResidue.olean` SHA-256 `bf3a66f8d005f85680f8c25d2ab94c22796e9624387a731d8ed8b170467ef326`. Independent [result audit](../../reviews/trace74-fc-residue-result-independent/README.md) passed, SHA-256 `3afba219dec2122c0580dc11c704737bbf778eb26da5f0ea2944a8520e4f5eee`. Direct-pin/search-path and inherited project/package/dynamic ancestry limits remain.

The independent [source and prelaunch review](../../reviews/trace74-fc-residue-source-prelaunch-independent/README.md) is separately recorded.
