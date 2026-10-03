# Bounded-word matrix Diophantine compiler

This self-contained, authored Python packet gives a fully counted SOS polynomial for each **fixed numerical inner-word length r** in one pinned 229-generator semigroup. It does not alter or execute the source compiler.

- Signed 2x2 target: 4 external integer parameters, **130r natural auxiliaries**, **17r+4 residual squares**
- Joint total degree: 2 at r=0, exactly 4 at r>=1
- Natural canonical target variant: 8 external natural parameters, same auxiliaries, 17r+8 residuals, degree 4 at all r
- Roots are in bijection with matching sequences of r tile indices; generator length is 2r+1
- A sequence determines one complete auxiliary tuple. A target can have multiple such sequences

Read `PROOF.md` for the complete construction, invalid-input cases, coefficients, exact monomial/arithmetic counts, and bit-growth bounds. The main result is implemented by `paired_compiler.py`. It uses only the Python standard library; no package installation is needed.

## Run

From this directory:

```sh
python paired_compiler.py ledger 94
python paired_compiler.py export 1 > small-sos.json
python paired_compiler.py certificate '[20,109]' > certificate.json
python paired_compiler.py verify certificate.json
python paired_compiler.py verify examples/accepting-94-certificate.json
python tests/check_all.py
python -O tests/check_all.py
python audit/source_literal_check.py
python audit/independent_interface_check.py
```

The `certificate` command accepts `--target '[[157,4],[-6712,-171]]'` when checking a selected sequence against a specified signed target. If omitted, it computes that sequence's product target. Use `--mode natural` for canonical external natural pairs. Mode precedes no special global flags; `--source PATH` is the optional global input-file override, and still requires the exact pinned SHA-256. Commands use Python's arbitrary-size integers and remove its decimal-string digit limit at the CLI.

`verify` validates a complete certificate's schema, source pin, sequence/target metadata, canonical auxiliary encoding and SOS value. It exits 0 exactly for a valid zero certificate, 1 for a correctly structured nonzero one; malformed certificates raise a validation error. For arbitrary assignments without sequence metadata, import `evaluate(constants,r,values,mode)`.

## Literal polynomial format

The six `examples/r{0,1,2}-{signed,natural}-sos.json` files list every residual coefficient and monomial, and all variable domains. A residual polynomial is the sum of its listed `coefficient * product(variables)` terms; an empty variable list is the constant monomial 1. The polynomial F is exactly the sum of the squares of those listed residual polynomials. The representation is fully explicit without unnecessarily expanding the squares.

Names use zero-based matrix row/column indices and one-based step/tile indices. H/G names ending `_p` and `_n` are canonical nonnegative parts. At r=0 no auxiliaries are allocated. The four signed target names are `T_00,T_01,T_10,T_11`.

## Saved evidence

- `data/semigroup.json`: unchanged literal numerical source, SHA-256 506144b361b2bea634d468a94921644d91868dc089a257fe289a0bf51b74cec9
- `data/accepting-witness.json`: unchanged source witness, SHA-256 13a3857d28b0207d9baa83facac5b2e67bbaeb858d00b82ef9a91c4ab38df890
- `examples/accepting-94-certificate.json`: complete 12,220-variable natural certificate, SOS exactly zero
- `examples/accepting-94-ledger.json`: 1,602 residuals, 1,048,088 multiplication and 354,876 addition charges for the documented unoptimized evaluator
- `evidence/`: normal/optimized test results and CLI checks
- `audit/`: independent literal-formula, interface, arithmetic-instrumentation and invalid-input review

The first length-two target collision found is `[20,109]` versus `[110,20]`: these are distinct auxiliary roots for the same target. The finite-r fiber bound is 114^r; it does not imply unbounded finite-foldness. This family does not encode variable r at fixed arity, and it inherits no earlier constant-operation bound. The numerical source semigroup's universality is a separate theorem, not inferred from these finite tests.
