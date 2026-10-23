# Bounded-checksum coefficient instance

This directory supplies the complete fixed K215 native tuple
`B=2^590069` using a single exact 41-bit checksum per clause. It preserves
the 943-tile language and native support of ProveIt package 36 while reducing
the four native coefficient payloads from 506,664 to **295,388 raw bytes**.

The full ordinary mathematical proof, including local decoding, changed
radix bounds, actual-rank controller and parity interface, is in `PROOF.md`.
It imports the inherited native compiler and K215 calibration. No new
end-to-end Lean/Rocq theorem is claimed.

Rebuild and independently audit with the Python standard library:

```sh
python3 build_coefficients.py
python3 audit_coefficients.py
```

The scripts work from any current directory. `COEFFICIENT_BINDING.json`
gives dimensions, exact hashes, finite interface certificates and the four
unsigned little-endian payloads under `coefficients/`, compressed using gzip.
The fourth port `MF_source` includes the shift by `B-1`.

Replace all four ports together in a compatible polynomial or system.
Recompute any later coefficient index after rebinding; old Jones/Sun fixed
indices cannot be reused with this tuple. The tuple does not change the
arithmetic skeleton's number of unknowns, degree or operation count.

The independent audit reconstructs every whole integer, checks 66,062
native-basis identities and rejects 38,663 one-bit mutations of canonical
clauses. These finite checks support the proof; they do not test halting or
the existence of a Diophantine solution.

`NOTICE.md`, `licenses/` and `upstream/` retain attribution and the imported
compiler interface proofs.
