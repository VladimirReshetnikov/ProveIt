# Reproduce the independent twelve-integer audit

Requirements: Python 3 and SymPy. Tested with Python 3.12 and SymPy 1.14.0.

Keep the archive's `radicals12`, `radicals12_audit` and `radicals_audit` directories adjacent. Run:

    python radicals12_audit/check_twelve.py
    python -O radicals12_audit/check_twelve.py

The checker imports only generic arithmetic helpers from the earlier independent `radicals_audit/check_radicals.py`. It does not import or execute either construction builder or any upstream program. It checks the frozen twelve-variable packet, its actual payload bytes, exact universal identities, the rigorous degree upper bound, an explicit nonzero leading coefficient, two actual-coefficient line certificates and twelve deliberately corrupted algebraic variants.

The complete ordinary mathematical review is `AUDIT_REVIEW.md`. The two JSON receipts record the checked literal hash and results. The only expected difference between the normal and optimized receipts is `python_optimized`.
