# Exact compact44 coefficients for the free-J companions

`BINDING.json` maps every symbolic fixed port in both circuits to its
literal gzip payload and gives both compressed and uncompressed hashes.
Decompress each payload and read the bytes as an unsigned little-endian
integer. These are fixed numerals, not additional quantified variables.

The complete four-port tuple is retained together. In particular the
polynomial port `MF` already is `MF_source=MF_native+beta`; do not shift it
again. Here beta=2^590069-1. K0 is the retained K payload.

The unmodified original finite coefficient generator and its literal
430-transition input are included in `recipe/`. Running

```
python3 recipe/build_coefficients.py
```

reconstructs the Wang943 finite language, checks the finite layout and
padding controller, and writes fresh payloads below `recipe/coefficients/`.
The reconstructed **raw** byte hashes must equal `BINDING.json`; the gzip
container bytes may also depend on the Python version. The generator's
own coefficient binding is retained in its original format.

`recipe/PROOF.md` is the original compact44 ordinary coefficient/compiler
adapter proof. Its inherited semantic references are preserved; the
finite generator is not an execution of K215 or a consistency test.
All original native licenses/notices are included in `licenses/`.

The delivery copied and checked all four raw and compressed payloads
against the active ordinary parents' binding. `SHA256.json` authenticates
the copied recipe, inputs, payloads, and notices. This package does not
change the compact44 compiler or its calibration.
