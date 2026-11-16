# Reference implementation

`reference_framework.py` is an exact finite regression model for the report's
algorithms:

- Boolean folds and least bounded search;
- backward precision schedules and finite-query envelopes;
- backward viability, forward reachability, full-horizon clouds, and least
  viable paths;
- independent stable-observable selection;
- shrinking-selector inequalities;
- finite-consumer metastability checks; and
- height-bound / complete-list conversion.

Run:

```bash
python -m unittest -v test_reference_framework.py
```

These executable checks are not object-language iPRA proofs. They validate the
finite algorithms and provide examples for the future Lean implementation.
