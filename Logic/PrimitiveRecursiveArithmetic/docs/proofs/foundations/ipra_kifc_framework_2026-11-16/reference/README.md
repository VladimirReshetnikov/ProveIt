# Exact finite reference code

These programs test the executable finite content of the report.  They are
independent regression oracles, **not** substitutes for object-language
`Prf PRAAx` derivations.

- `kifc_reference.py` implements Boolean folds, least search, bounded traces,
  reverse demands, relational viability, stable observers, guarded selection,
  exact cubic bisection, finite nets, and height/list conversion.
- `test_kifc_reference.py` tests those algorithms, including randomized
  viability checks against brute-force path enumeration.
- `negative_translation_reference.py` implements the atom-preserving negative
  translation, de Bruijn-aware simultaneous substitution, the retained syntax
  classifier, and finite classical evaluation.
- `test_negative_translation_reference.py` checks substitution commutation,
  QF preservation, retained classification, translation shape, and classical
  equivalence on deterministic random finite models.

Run all tests from the artifact root:

```sh
python3 -m unittest discover -s reference -p 'test_*.py' -v
```
