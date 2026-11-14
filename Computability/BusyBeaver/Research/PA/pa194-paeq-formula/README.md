# Current-Foundation arithmetic-to-PAeq formula code

This package ports the pinned upstream PA196 arithmetic-to-PAeq syntax and
formula-recursion graphs to current LO Foundation. It defines the PAeq target
language with zero, successor, addition, multiplication, and equality; proves
its numeric function and relation code ranges; and defines exact Σ₁ graphs for
the target equality, strict-order, and translated arithmetic-atom codes.

`formulaCode` has an explicit parameter-free Σ₁ graph and is total and unique
in every IΣ₁ arithmetic model, including nonstandard models. It maps invalid
source formula codes to zero. For valid source inputs the package proves the
exact positive-atom, negative-atom, truth, falsity, conjunction, disjunction,
universal, and existential constructor equations. The current LO formula
recursor differs from the pinned upstream one; its binder parameter-change
functions are explicitly set to the identity in this adaptation.

This is a syntax graph, not a fixed finite candidate-PRA code. The package
does not yet establish target-language formula validity, a bound for the
formula or term graph witnesses or outputs, compatibility with source/target
substitution, translation of PA proof codes, or machine calibration. The
upstream hashes identify the adapted inputs, not equality of FFL and LO APIs.

Run from the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-formula/check.sh
```

The standalone script has passed: it checked the upstream pins and rebuilt
the term, language, atom, and formula modules in a private tmpfs directory
against the audited project and Foundation objects, without `sorryAx`.

An independent complete standalone replay rebuilt the term, language, atomic
and formula graph modules from the pinned audited overlays and passed without
`sorryAx`.
