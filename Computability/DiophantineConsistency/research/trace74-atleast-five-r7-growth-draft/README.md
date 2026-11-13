# Same-tuple growth for first index at least five: source draft

This source generalizes the audited `n=5,r=7` growth client. It assumes the same positive model tuple, `q≥2³⁰`, an explicit first ordinate equation at an index `n≥5`, and an explicit main ordinate equation at index 7. Monotonicity gives the fifth ordinate at most the supplied first ordinate, so the same strict scalar gap follows from positive slack. Its conclusion is `65532·ι(b)·ι(Y)<ι(X)`.

This source does not derive either ordinate equation, a graph zero, or fixed-port bounds.

The [independent source review](../../reviews/trace74-atleast-five-r7-growth-source-independent/README.md) passed the monotonicity and same-tuple argument. `selection.json` compares current first selections for direct source imports; the held runner rechecks them. Full serialized transitive/package and producer-time ancestry is not captured. The [independent prelaunch review](../../reviews/trace74-atleast-five-r7-growth-prelaunch-independent/README.md) approved one coordinated check.

One author check ran in actual tool session 50410, exit 0 and fully reaped. Its [terminal](observations/attempt01/terminal.json) SHA-256 is `635e23e4416f9fc8d969c138df0e53bbb434774e23eb5f7f6954ee101c041003`; the object `/tmp/trace74-atleast-five-r7-growth-0puw5fgd/lib/Trace74AtLeastFiveR7Growth.olean` SHA-256 is `2acccc51362891a787a9bd2e5bee0109d361fb911bda927a7bb23bdce1565d54`. The [independent result audit](../../reviews/trace74-atleast-five-r7-growth-result-independent/README.md) passed.
