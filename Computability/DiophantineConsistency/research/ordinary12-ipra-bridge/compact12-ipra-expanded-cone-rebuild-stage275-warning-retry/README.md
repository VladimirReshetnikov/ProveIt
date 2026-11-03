# Stage 275: rejected warning-retry setup

The full six-warning baseline and five mutation checks were prepared, but this
retry stopped before invoking Lean or moving any object. Its quarantine guard
contained a copied object hash with incorrect bytes and rejected the actual
stage 275 object. The original stopped stage 275 receipt, which records the
correct object hash, remains unchanged. The separately captured next retry
corrects the guard and rechecks the existing source and dependency pins.
