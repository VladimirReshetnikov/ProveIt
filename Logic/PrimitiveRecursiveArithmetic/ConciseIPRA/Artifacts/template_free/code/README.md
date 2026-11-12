# Strict tagged checker

Run the standalone checker with one JSON document on standard input:

    python3 code/global_rewrite.py < certificate.json

Acceptance is exit code zero and the exact line ACCEPT. An error or
resource failure is not acceptance. Python 3.10 or newer is required.
The checker imports no other project file.

## Header

The document has exactly four keys:

    {
      "variables": 0,
      "context": [],
      "goal": ["=", ["z"], ["z"]],
      "proof": [
        "rw",
        ["zero", ["z"], ["z"]],
        ["zero", ["z"], ["z"]]
      ]
    }

This is the primitive computation proof of zero reflexivity. The source
of both equations is I(0,0;u.0), so root joining produces 0=0.

The nonnegative integer variables declares the available numerical
parameters. Context is a list of retained formulas. Goal is one formula.
Proof is a finite primitive proof tree. Booleans are not integer indices.

## Numerical and formula syntax

| JSON form | Meaning | Scope |
|---|---|---|
| ["v", i] | Numerical variable | 0 <= i < current variable count |
| ["z"] | Zero | No arguments |
| ["s", a] | Successor of a | Same scope |
| ["i", n, a, h] | Iterator I(n,a;u.h) | Body h adds index zero; n and a do not |
| ["=", s, t] | Equation | Both terms in current scope |
| ["q", B] | Closure Q_y B | B adds one binder |
| ["d", B] | Pair D_{x,y} B | B adds two binders: y=0, x=1 |

Variables are de Bruijn indices. Under a new binder, an existing free
index increases by one; locally bound indices remain unchanged.

## Proof instructions

All premise proofs retain the same context unless the table says otherwise.

| Instruction | Result or requirement |
|---|---|
| ["hyp", i] | Context entry i |
| ["zero", a, h] | I(0,a;u.h)=a |
| ["succ", n, a, h] | I(Sn,a;u.h)=h[I(n,a;u.h)/u] |
| ["rw", p, q] | If p proves s=t and q proves u=v, returns v=R_s^t(u) |
| ["qe", t, p, q] | p proves Q_y B; q proves B(0); returns B(t) |
| ["de", A, p, q] | p proves D B; q proves lifted A under the new Q assumption and lifted old context |
| ["di", B, t, p] | Returns D B after checking the witness-sensitive successor branch |

For DE, the branch adds a fresh numerical parameter at index zero.
Its context entry zero is the opened Q formula. Other context entries
are shifted and follow it. The declared conclusion A must be well scoped
before this parameter is introduced, preventing escape.

For DI, the supplied B is the two-binder matrix, and t is checked in the
old numerical scope. The branch adds a fresh successor-case parameter at
index zero and lifts the old context. Its extra assumption is B(t,z)
exactly when B is an equation and t is literally ["z"]; otherwise it is
B(t,0). The checked branch conclusion is B(t,Sz). The extra assumption is
context entry zero.

## Replacement convention

The replacement traversal tests a node before descending into children.
A match returns the inserted target immediately. It never rewrites that
inserted target or revisits a newly created ancestor match. Under binders,
both the source and target are lifted before matching or insertion.
All unmatched indices stay fixed in replacement mode.

The ordinary lifting and substitution operations share this traversal.
Their index-offset arguments are internal implementation details, not
additional certificate parameters.

## Tests and proof producers

The generators and verification scripts are untrusted support:

    python3 tests/verify_strict.py

They produce ordinary primitive packets. The global checker never
imports them or trusts their claimed conclusions. The report supplies
the universal equivalence proof; the finite process suite exercises
representative derivations and rejection controls.
