# Free-J first factor forces q³ ∣ Y

For the exact 95-row free-J graph in any `IΣ₁` arithmetic model, Lean proves
that an internal zero, a positive first input J, and a positive first port β
imply `(1+Jβ)³ ∣ Y`, where Y is the graph's seventh variable. All four ports
are arbitrary natural numbers, interpreted as nonnegative integer constants;
only β is assumed positive. No restriction `J=1 mod 6`, no assumptions about
rank, the strong norm, Mersenne port equality, or checker calibration are used.

The proof binds the folded first root to its signed-pair representation,
derives its scaled norm from the first factor being +1, extracts an unsigned
root quotient using square divisibility, and adapts the historical first-root
modular argument to the graph's exact variable positions. The first-factor
unit itself comes from the previously replayed 95-row factor split. This is
not yet a main-factor q⁵ premise or an iPRA derivation.

Fresh bounded replay session 42582 exited 0 and printed
`PASS_BOUNDED_FREEJ_FIRST_DIVISIBILITY
ac23e8dfbf895294c909f34202c45327cf50dc583f61605ac08d086e68155e7b`.
The receipt preserves seven Lean axiom reports, direct dependencies, source
and object hashes, and the inherited historical provider/closure checks.
`observations/` records the warning-bearing successful attempt and earlier
failed attempts, with their limitations. This is a single-author model replay;
it is not a matched full-project build or dynamic dependency audit.
