# A checked 196-state zero-jump variant and a rejected 195-state fold

This folder contains a new, validated **196-state** variant of the pinned PA196 machine, a finite inductive invariant that permits the change, and a complete-tape counterexample to a tempting **195-state** proposal. **It does not supply a valid machine with fewer than 196 working states.**

Run the complete portable check with Python 3.10 or later:

```sh
python verify.py
python -O verify.py
```

No third-party Python package, network connection, repository checkout, or Lean installation is required. The checker reads only files in this folder. Its default output is `receipts/reproduced.json`. Checks use explicit exceptions and remain active under Python's `-O` option.

## Contents

| Artifact | Role |
|---|---|
| `verify.py` | Reconstructs the invariant, synthesizes the 12 accepted local actions, checks the chosen machine, and reproduces the rejection witness. |
| `symbolic.py` | Portable adaptation of the supplied all-natural symbolic runtime checker. |
| `machines/zerojump196.tm` | The positive 196-state construction: native row `27/1` becomes `1 R 21`. |
| `machines/wrong_opcode_parent196.tm` | Explicitly rejected intermediate parent with native row `27/1 = 1 R 62`. |
| `machines/rejected195.tm` | Explicitly rejected fold of that parent; retains sparse old dense labels. |
| `reference/` | Pinned source, state correspondence, original table, seed definitions, and engine proof sources. |
| `reference_manifest.json` | Repository pin, upstream pin, and SHA-256 digests for all reference files. |
| `receipts/reproduced.json` | Recomputed evidence, including full finite-support tapes. |
| `newwork.md` | Mathematical argument, scope, and the failure diagnosis. |

The machine tables use five columns: current state, read symbol, written symbol, direction `L`/`R`, and next state. All use blank symbol zero, start state 0, and terminal label 196. The valid variant has working states 0 through 195. The rejected 195-state table omits old dense state 27; its label 196 remains a terminal, so the largest label is not its state count. The verifier counts rows and graph-reachable working states directly.

## Exact claims

The verifier reconstructs 274,880 abstract source configurations and checks both inclusion of the initial source configuration and closure under **every** abstract successor. It finds 14 forward-jump sites at which a register is forced zero. At site 26, logical registers 3, 6, and 7 are zero. The chosen literal replacement implements the original jump using the zero branch of a decrement of register 6.

The chosen machine satisfies all 4,959 symbolic instruction cases. These calculations quantify over arbitrary natural register values and arbitrary nonnegative gap parameters through the unchanged register-engine lemmas. Only site 26 is supplied the additional zero hypotheses justified by the invariant. The machine reaches the exact original whole-tape clean seed from the blank tape after 58,402 transitions. This proves a relative simulation of the original source computation; it supplies no state saving.

The rejected 195-state machine fails source case 26. On an explicit clean frame with all nine registers zero, the original jump reaches site 34 after 120 steps. The changed parent and its 195-state fold instead reach site 27 after 558 steps, incrementing logical register 6 and appending a spare register. The same wrong operation occurs on the folded machine's actual blank run, between steps 54,392 and 55,186.

The finite invariant and symbolic traces are executable ordinary mathematical certificates. The reference Lean sources explain the register summaries, but this folder does **not** rebuild Lean, provide a newly checked PA equivalence endpoint, or settle whether the rejected table could have some unrelated consistency interpretation. See `newwork.md` for the exact transfer argument and its dependency on the baseline source theorem.
