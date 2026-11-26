# Selected CM input certificates: provenance and replay scope

These two JSON files are copied **unchanged** from the earlier report
`grh_sparse_singular_moduli.zip` in
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/blob/6fe2c1bd450aa7f19eab17fb9a6e76170b4fce00/docs/incoming/grh_sparse_singular_moduli.zip),
at commit `6fe2c1bd450aa7f19eab17fb9a6e76170b4fce00`.
They are prior-work inputs, not results newly generated for this report.
No claim of worldwide novelty is made for their contents or for replaying them.

## Exact source files

Source repository path:

`docs/incoming/grh_sparse_singular_moduli.zip`

Archive SHA-256:

`2bc3722339b06081c8ef9480723c086372784738432d0d2be96789bed0037d21`

| Bundled file | Exact member path in the source ZIP | Bytes | SHA-256 |
| --- | --- | ---: | --- |
| `five_small_witnesses.json` | `grh_sparse_singular_moduli/checks/five_small_witnesses.json` | 21,070 | `aab16ac3f25da1421233f51e9b5e0984af2a58d6f5303fa61a1e2be8f9128d9a` |
| `class_polynomials.json` | `grh_sparse_singular_moduli/cm/class_polynomials.json` | 18,105 | `630a2f70beb275646ce54814255d75aa20ef6d37e199de66639ab9a6dbedb7a8` |

The checker was written independently for this synthesis. It reads only these
JSON files and does not import or run programs from the source archive.

## Replay

From the root of the extracted deliverable, using Python 3 without `-O`:

```sh
python3 code/check_selected_cm_inputs.py > validation/selected_cm_inputs.json
```

The program requires only the Python standard library. It resolves input paths
relative to its own location, so it can also be invoked by absolute path from
another working directory. It emits the full certificate to standard output
and does not modify the input files. A successful run reports `status: passed`
and counts of 18, 245, and 17 in the resulting JSON.

## What this replay verifies

The deliberately limited scope is:

1. **18 Newton disk certificates.** For the supplied polynomials, the checker
   recomputes the coefficients after the prescribed substitution, their exact
   prime-adic valuations and rational depth comparisons, and the associated
   factorial-valuation inequalities used in the sparse-root argument.
2. **245 stated quadratic forms.** It verifies each supplied discriminant,
   primitivity, and the reduced-form inequalities. This is a check of the
   listed forms, not a new census or a proof that every relevant discriminant
   has been listed.
3. **17 confluent period identities.** For the final quintic and four sextic
   cases, it checks the stated auxiliary primes and computes powers of the
   polynomial residue class modulo the supplied monic polynomial and `p^2`.
   It verifies scalar reduction modulo `p` with a nonzero scalar, and records
   the resulting lift coefficients. The exponents need not be minimal
   periods.

The supplied class-polynomial identities are **assumptions of this input
check**. The checker does not prove that the supplied polynomials are the
actual CM class polynomials. It also does not rerun analytic enclosures, the
large finite residue sieves, a complete class-number enumeration, or the
global classification proof. Passing these selected checks must not be
reported as independent verification of the full sparse-singular-moduli
classification.
