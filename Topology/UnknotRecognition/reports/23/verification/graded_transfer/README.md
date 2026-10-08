# Graded transfer validation

Run from the package root:

```bash
python verification/graded_transfer/validate_transfer.py
```

The script resolves the accompanying implementation and examples relative to
its own location, so it also runs from another current working directory. It
checks 86 diagrams in 258 diagram/order cases, comparing four engine modes,
including quantum-resolved ranks and eight exact cobordism contraction
identities at every tested eager-transfer stage. Further controls cover nonzero
radical maps, paused sparse cancellation, long corrections, source-band
vanishing, a transfer-capacity fallback, and deadline propagation.

`validation.json` records the delivered run. The default command writes the new
run to `validation_reproduced.json`; use `--output` to choose another location.
`synthetic.py` constructs the graded controls used here and in the benchmark.

The production integration tests are in
`implementation/fast/tests/test_graded_transfer_integration.py`.
