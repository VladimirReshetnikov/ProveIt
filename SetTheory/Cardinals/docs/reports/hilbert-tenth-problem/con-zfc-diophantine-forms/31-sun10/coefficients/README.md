# Smaller Wang943 fixed coefficients

Complete new tuple: `B=2^1064921`, with `rho=2^121`, 8801 radix cells,
and arbitrary-odd-factor rank control using the prime 2341.

Run `python3 build_coefficients.py` with Python 3.10+; only the standard
library is needed. The builder rewrites payloads and the binding receipt.
`COEFFICIENT_PROOF.md` gives the ordinary mathematical adapter proof.
`coefficient_section.tex` is a report-ready section.

Load the four payloads using `int.from_bytes(gzip.decompress(bytes), 'little')`.
The ports are beta/Bm1, K/Kconstant, MC, and MF_source/MF. The fourth is
already shifted by B-1. Replace the whole tuple together.

| Measure | Previous smallest (25/27) | This tuple |
|---|---:|---:|
| Base exponent d | 1,953,125 | 1,064,921 |
| Largest port bits | 1,958,376 | 1,070,004 |
| Raw payload total | 977,220 bytes | 533,099 bytes |
| Native tiles | 943 | 943 |

The new adapter preserves variables, degree and operation count of compatible
arithmetic skeletons. It establishes no end-to-end proof-assistant certificate.
All source files are pinned at `8c6eec9d19ef80538c8e61ff6e0180040583446a`.

The new synthesis was prepared with AI assistance for Vladimir Reshetnikov's
ProveIt project. Original licenses and K215 notices are retained in `licenses/`.
New files are offered under the repository's MIT-0 license in `licenses/LICENSE`.
