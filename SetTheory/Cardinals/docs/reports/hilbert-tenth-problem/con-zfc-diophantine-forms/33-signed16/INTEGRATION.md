# Suggested repository integration

Place the complete extracted directory under
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/`
using the next available package name. No existing package needs to be replaced.

Suggested index paragraph:

> **Sixteen-integer synthesis and affine simplifications.** An explicitly bound
> polynomial in 16 unrestricted integers, degree `406528*5^32+10008`, with a
> 1,590-operation evaluator; absence of integer zeros is provably equivalent in
> ZFC to Con(ZFC). The package also supplies a 61-operation system of 22
> quadratics in 31 positive variables, its 126-operation quartic, a
> 108-operation evaluator for the existing twelve-positive-variable polynomial,
> 104/103-operation associated systems, and a separately proved complete
> native coefficient tuple with `B=2^1012625`. Ordinary proofs, exact algebra
> checks and actual coefficient bytes are supplied; no new end-to-end
> proof-assistant certificate or global optimality claim is made.

The baseline is immutable revision
`8c6eec9d19ef80538c8e61ff6e0180040583446a`. If a later source revision changes
the compiler contract or calibration, review those changes explicitly before
replacing any pinned source or binding.

Run `python3 reproduce.py --check-release` before editing, and
`python3 reproduce.py` after integration. Generated JSON files and compressed
integer payloads are part of the deliverable: preserve them even if a broader
repository ignore rule would otherwise omit them. The main PDF depends on
`coefficients_small/section.tex`, which must also be retained.

The main tuple and the smaller optional tuple have different identities.
Preserve their separate bindings. Rebinding the Jones circuit requires
regenerating its weighted coefficient recipes and index, not replacing only
the native gzip files.
