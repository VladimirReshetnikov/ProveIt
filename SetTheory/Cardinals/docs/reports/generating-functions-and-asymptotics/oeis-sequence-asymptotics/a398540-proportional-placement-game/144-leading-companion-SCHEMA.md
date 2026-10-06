# Closed fixture schema, version 1

`rate_certificate.json` is UTF-8 JSON. Duplicate names are rejected at every object level, before field lookup. JSON floats, exponents, NaN and Infinity are forbidden. JSON whitespace is accepted for alternate candidates; the supplied fixture uses sorted keys, two-space indentation, ASCII output and one final LF.

All objects have exactly the fields listed below: unknown and missing names are errors. Integer means a nonnegative JSON integer whose Python type is exactly `int`, excluding booleans. Boolean means exactly `true` or `false`, not `0` or `1`. Arrays must have the stated exact length. No numerical value is trusted merely because its type is valid: every field must subsequently equal the fresh independently computed certificate.

## Rational type

A rational is a JSON string matching

```
(?:0|[1-9a-f][0-9a-f]*)/[1-9a-f][0-9a-f]*
```

with the entire string consumed. Numerator and denominator are interpreted in base 16, must be relatively prime, and denominator must be positive. Thus `0/1` is the only encoding of zero, and `1/1` is the encoding of one. Uppercase, signs, `0x`, leading zeros, spaces and newlines are disallowed. The canonical encoding is checked again after construction of the exact rational.

## Root object

- `schema`: string, exactly `report144-placement-rate-certificate-v1`
- `last_probability_index`: integer, exactly 100
- `number_of_probabilities`: integer, exactly 101
- `parameters`: object described below
- `probabilities`: array of 101 canonical rational strings, for `W_0,...,W_100`
- `prefix`: array of six canonical rational strings, for `W_0,...,W_5`
- `vector_serialization`: string, exactly the verifier's `SERIALIZATION` constant
- `vector_sha256`: string of exactly 64 lowercase hexadecimal characters
- `square_root_floors`: array of 101 integers
- `certificate_values`: object described below
- `checks`: object described below

## `parameters`

- `m`: integer, exactly 101
- `N`: integer, exactly 101
- `kernel_upper_bound`: rational, value 1
- `strict_lower_bound`: rational, value 527/1000
- `strict_upper_bound`: rational, value 79/125
- `square_root_lower_scale`: integer, exactly 1000000000000

## `certificate_values`

All five fields have canonical rational type:

- `lower_left_hand_side`: `W_100`
- `lower_right_hand_side`: `16*101^2*(527/1000)^101`
- `upper_left_hand_side`: `4*(125/79)*P_upper(125/79)`
- `upper_auxiliary_bound`: 95111/1000
- `upper_right_hand_side`: 101

## `checks`

- `all_probabilities_in_open_closed_unit_interval`: boolean
- `all_101_independent_probabilities_match`: boolean
- `polynomial_weights_checked_with_reflections`: integer, exactly 2550
- `known_prefix_matches`: boolean
- `all_square_root_floors_exact`: boolean
- `strict_lower_certificate_passed`: boolean
- `strict_upper_certificate_passed`: boolean
- `strict_auxiliary_upper_bound_passed`: boolean

Every boolean must match the regenerated value `true`. Checking the schema alone is insufficient: the verifier recomputes both full probability vectors, all square-root floors and every exact certificate quantity, then compares the candidate against that entire result. The vector digest is independently calculated from the rational strings and checked against the previously frozen digest. Updating hashes cannot authorize a changed semantic field.
