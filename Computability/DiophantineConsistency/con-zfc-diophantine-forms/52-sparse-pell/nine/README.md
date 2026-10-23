# Nine-variable construction

Read PROOF.md for the mathematical theorem, imported dependencies, and exact
scope. No claim of global minimality or a newly rebuilt end-to-end kernel proof
is made. The domain is part of each equation's statement.

Recommended positive-domain frontier:

| Variant | Binary operations | Exact total degree |
|---|---:|---:|
| Interior regular, shared source | 548 | 15,502,748 |
| Interior packed + uniform target shift 186, shared source | 603 | 10,486,092 |
| Interior packed, sparse Horner | 655 | 10,127,484 |

The corresponding natural-domain equations have 551, 606 and 658 operations,
respectively, and the same degrees. All forms have exactly nine variables.

From the archive root, reproduce with:

```sh
python nine/build_nine.py packing/CERTIFICATE_174_regular.json packing/CERTIFICATE_174_packed.json packing/CERTIFICATE_174_interior_regular.json packing/CERTIFICATE_174_interior_packed.json packing/CERTIFICATE_174_interior_shifted.json
python nine/materialize_coefficients.py
python nine/verify_nine.py
python audit/verify_nine_independently.py
```

The last script is a separately authored audit and may also be invoked from its
own directory as documented by its author. The three local scripts use Python3
and SymPy. They read mathematical data; they do not execute upstream scripts.

Files:

- generated/nine_*_positive.json and *_natural.json: primary arithmetic circuits.
- generated/*_degree_certificate.json: algebraically equivalent,
  cancellation-resolved circuits; their gate costs are not the primary metrics.
- generated/VERIFICATION.json: local finite check receipt.
- COEFFICIENT_INSTANCE.json and generated/fixed/: all live fixed integer leaves.
- ../coefficients/COEFFICIENT_BINDING.json: single coherent four-port tuple.
- ../packing/CERTIFICATE_*.json: positional data and exact coefficient recipes.
- data/source_system60.json: the read-only shared quadratic compiler data.

The four new tail ideas are the exact F-divisibility reparameterization,
margin-first radical separation, a second-order Pell product majorant, and
removal of quotient offsets using the concrete majorant bound. Source savings
come from sparse active-support packing, a fixed-scale quadratic radix,
interior padding, and a shared homogeneous evaluator with diagonal correction.
