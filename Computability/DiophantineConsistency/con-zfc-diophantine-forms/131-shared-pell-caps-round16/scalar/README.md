# Round16 scalar equations

Four selected fixed integer polynomials, each in eleven unrestricted integer variables:

- product11_degree966.json: exact degree966,109 live binary operations.
- product11_degree882.json: exact degree882,110 operations.
- two_root/two_root11_degree810.json: exact degree810,112 operations.
- two_root_weak/two_root_weak11_degree654.json: exact degree654,117 operations.

PROOF.md gives the complete parity-normalized product proof. TWO_ROOT_PROOF.md gives the complete new nonzero-center two-root reduction and weak-scale restoration. The unreleased native two-root comparison degree906/111 is dominated and not recommended.

All six actual coefficient payloads and their full finite reconstruction recipe are present in coefficients/. The inherited mathematical and ordinary calibration dependency closure is present in inherited/ and source/, with retained licenses. These are ordinary proofs, not a new kernel-checked endpoint or consistency proof.

From this directory run:

    python build.py --check
    python build_two.py --check
    python build_two_weak.py --check
    python check.py
    python -O check.py
    python two_root/check.py
    python -O two_root/check.py
    python two_root_weak/check.py
    python -O two_root_weak/check.py
    python verify_coefficients.py
    python -O verify_coefficients.py

The generators use only standard Python; the sparse exact polynomial checker is included. The checkers do not import or run their producer. Normal and optimized mode use explicit error checks rather than Python asserts. Exact polynomial identities, all live arithmetic, actual coefficients, nonzero degree witnesses and corruption controls are checked. Unbounded Pell/interpolation and source calibration arguments remain the separately provided ordinary proofs.

RELEASE_WHITELIST.json is the exact portable selected-file list.
