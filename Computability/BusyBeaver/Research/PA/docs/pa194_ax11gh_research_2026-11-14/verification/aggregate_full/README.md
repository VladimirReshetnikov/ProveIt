# Fresh full aggregate replay

This is the observed full-mode replay of `verify_all.py` for the delivered machine tables and checkers. It rebuilt both tables, reran both construction runtimes and independent literal proofs, and checked source, commands, frame closure and the complete baseline graph comparison. Fresh literal certificate bytes matched the retained certificates.

The replay occurred before the final whole-package SHA256SUMS was generated, so its summary correctly records zero whole-package manifest entries. Delivery integrity is checked separately after final packaging. The later repository delta has its own receipt in `comparison_latest_head/`. No finite receipt is a proof-assistant kernel derivation of the consistency theorem.
