# Contextual replay output-companion guard correction

The independent review at `c214189d7f` showed that both earlier contextual
variants accepted an injected emitted-object `.olean.private` file. The
variants remain unlaunched and require a new independent prelaunch review.

The corrected drivers check that every declared output companion slot is
absent before each child. After the child they require a regular, non-symlink
`.olean` and absence of all other companion slots, capture their full guard
map alongside the direct inputs, and recheck it after later steps and after
the final contextual parent callback. Thus an unexpected existing, newly
emitted, or late-created companion is rejected. This is point-in-time
checking; it does not authenticate transitive or dynamic inputs between
checks, nor replace a clean initial loader environment or protected HEAD.

Exact corrected SHA-256 values:

* inverse contextual driver: `37cd77db39cbdc732a80cec5ccc373a5cea05ac0ba6644788e2905525e5d7388`;
* exclusion contextual driver: `4e05a8a80989fc49fbd5a03f31f55e8e4681624d2520f3e9ba4a59fa36135913`.

The two new `*-output-guard-fake.py` scripts pin those exact bytes and extend
the prior fake loops. Actual inverse session exited 0 across 20 cases and
exclusion session 48712 exited 0 across 22 cases. Each includes the matching
good fake pair, the prior failure cases, pre-existing output companions,
child-injected companions, and late companion insertion by the final parent
callback. Exact output is retained in the two `*-output-guard-controls.log`
files; no Lean child was launched in these controls. The originals and their
failed review remain historical evidence. These tests substitute fake
compiler/dependency/parent operations and do not establish a real build.
