# Completing the exact Tarski logical layer

This package adds a checked propositional certificate port and a small
integration theorem to ProveIt snapshot
`4747142d5d15213eb711bdadfa3cc7e769fcb7a7`.

## Checked result

`TarskiCompleteRows.lean` proves `Tarski.completeness_from_rows` without the
two classical-propositional hypotheses required by the pinned
`TarskiComplete.completeness` declaration. For any formula predicate `Ax`
and named formula `f`, standard first-order validity of `f` in every model
of `Ax` implies derivability from the exact emitted Tarski rows. The
companion `Tarski.theorem_iff_valid` combines this with the existing soundness
theorem. The code uses primitive falsity and ordinary identity equality.
It does not identify numerical aliases or prove a Turing-machine endpoint.

The new proof objects are:

- `Lukasiewicz.lean`: the 107 numbered upstream implication derivations,
  then `row_k`, `row_s`, `row_peirce`, `row_efq` and `classical_from_rows`.
- `TarskiCompleteRows.lean`: `completeness_from_rows` and `theorem_iff_valid`.
- `PrimitiveBottomAudit.lean`: an axiom-free finite counterinterpretation
  proving that rho8, modus ponens and generalization alone do not prove
  `bot -> R(0,0)`.

The first and third modules' listed roots depend on no axioms. The two
completeness roots depend on the existing library's `propext`,
`Classical.choice` and `Quot.sound`. All ten source modules were rebuilt
serially with Lean 4.32.0, commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`. No admissions, custom axioms or
native evaluation were used. The old `TarskiComplete.lean` emits six
unused-variable linter warnings; the new modules compile without warnings.

## The falsity correction

The pinned `TarskiDerived.lean` header says that K, S, Peirce and ex falso
are discharged from rho8 alone. This overstates the role of that axiom.
Rho8 is a basis for classical implication. If `bot` is treated as a freely
designated atom, `bot -> p` is not an implicational tautology.

The complete calculus supplies the missing role through rho6. Put
`q = exists i (forall i p)`, where `exists i a` abbreviates
`(forall i (a -> bot)) -> bot`. K gives `bot -> q`. Rho6 gives `q -> p`.
K and S compose these two theorems to prove `bot -> p`. The code uses
the fixed label zero, which is legitimate because rho6 has no freshness
condition. This is a correction to the stated provenance of ex falso;
the prior completeness theorem correctly states its explicit hypotheses.

## Attribution and exact input

The implication proofs are an exact syntax port of Jeff's published
[`ZF/m254/coq/logic/CD254.v`](https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/coq/logic/CD254.v).
The original file credits `cdgen.py` and `cdsearch.py` for generating its
condensed-detachment proofs. It belongs to the Mira-Cult / Jeff machine
verification project. This package claims no new propositional derivation
or historical priority for the logical results. The contribution is the
checked Lean port, explicit rho6 bridge, counterinterpretation, and
integration with the pinned ProveIt completeness theorem.

The exact upstream file is retained as `CD254.v`, Git blob
`78dcc05ec4cd22e19b9ef12003b93eb787a408bc`, SHA-256
`898b6498cc50b81f465c2cac72fcfe1bb5eaf8e4af91359a02b18906202a8a4a`.
The seven existing ProveIt dependency modules are unchanged snapshots;
their exact hashes appear in `verification/verification.json`.
No new blanket license is assigned to the upstream or ProveIt sources.

## Reproduction and integration

The package is a self-contained ten-module source closure. With Lean 4.32.0
installed, run from this directory:

```sh
python check_propositional_bridge.py --repo . --lean /path/to/lean
```

The script compiles serially into a fresh directory and records every
source hash, compiler return code and axiom-audit output. Existing evidence
and complete logs are under `verification/`.

To regenerate the attributed port, run:

```sh
python generate_propositional_port.py
```

Before emission, this checks the exact upstream Git blob, parses all 107
conclusions and verifies all 106 MP steps by independent symbolic formula
substitution. The port replaces natural codes by named formulas, `wim`
by `imp`, dummy zero by primitive `bot`, and reverses the Coq MP premise
order to match Lean. The complete source theorem statements are unchanged
under this syntactic mapping.

For integration into the pinned repository, copy the three new modules
under `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`. Existing files need
no modification. Import `BusyBeaver.ZFC.TarskiCompleteRows` where the
unconditional logic theorem is wanted. `PrimitiveBottomAudit` is optional.
The seven frozen dependencies are included for reproducibility; they
should not overwrite newer repository versions without comparison.
