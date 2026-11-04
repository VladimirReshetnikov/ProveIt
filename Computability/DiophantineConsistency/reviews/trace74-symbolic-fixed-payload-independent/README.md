# Independent external fixed-port payload check

The read-only [`check.py`](check.py) checks the exact retained `candidate.json`
bytes (SHA-256 `dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353`),
the ordered four port names and every compressed/raw coefficient hash and
bit length in its binding metadata. Interpreting raw payload bytes as the
specified little-endian natural numbers, it verifies

```text
beta = 2^(67*8807)−1 = 2^590069−1,
SHA256(raw K0) = 0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f,
gcd(K0+2^((r−590069) mod 590069), beta) = 1,
r = 3056651345,  (r−590069) mod 590069 = 93925.
```

Thus the `K0` used by the ordinary carrier CRT is the retained external
candidate's `K0` payload, and `beta` has the symbolic value used by the
construction. `MC` and `MF` are also hashed but the argument treats them
as arbitrary naturals. The checker validates two in-memory mutations and
refuses Python optimization.

Run from the repository root:

```text
python3 -I -S -B Computability/DiophantineConsistency/reviews/trace74-symbolic-fixed-payload-independent/check.py
```

It exited 0 reporting `PASS`; `python3 -I -S -B -O` was rejected with exit
1. Checker SHA-256 is
`892a5c8bbe2e8015560d94e87734b7fda538e5e179e70ee6bf59f1a0aacdddad`.
The exact raw hashes are recorded in its output. This is an external byte
and arithmetic check. It does not prove a Lean equality between these
files and symbolic ports, formalize file/PDF semantics, verify the
unmaterialized full graph witness, or establish an iPRA endpoint.
