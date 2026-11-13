# Fully validated checker, with the exact AST of checker_strict_procedure.py.
#
# c: verify the requested formula a under context g and scope floor k.
# v: one only while the initial public goal is being validated.
# i: simultaneous syntax traversal, scope validation, and binder opening.
# q: pop one certificate record from the end of the JSON array.
#
# Each record is (m, s, u, t).  The mathematical decoding and the roles
# of the record fields are specified in the report and frozen controls.
# Successful calls return None; a failed check raises an exception.

def c(g, a, k=0, v=0):
    m, s, u, t = q()

    (
        # Install the local opener and validate the goal before changing v.
        (i := (
            lambda a, t=c, d=0:
            [i(b, t, d + 5 - len(a)) for b in a]
            if a * 0 != 0 and v <= (len(a) in (1, 2 + d % 2))
            else a or 1
            if k <= a < d and v <= d & a % 2
            else d % 2 | v and i(t, d=3)
        ))(a)

        # Only after that traversal succeeds, switch to the auxiliary
        # grammar.  A leaf may use neutral truth, a retained assumption,
        # or the independently justified computation preview.
        in (
            (v := 0),
            *g,
            [
                [s and [s] or 1, u, t],
                i(t, [s, u, t], 3) if s else u
            ]
        )

        # Otherwise verify the major, create the local resource, open the
        # minor goal, and verify the minor under the enlarged context.
        or c(
            g + [
                i(
                    c(g, m, k) or m * 3 or (a := i(*a, t, 2)),
                    any((m, len(a) == 2 == u)) * (k := (~-k))
                )
            ],
            i(
                (a, i(t, s))[
                    (m, a) == (s and [s, u] or [t] * 3, i(t, u))
                ],
                [k]
            ),
            k
        )
    )

import json

p = json.load(open(0))
# This is the unchanged whole-certificate alphabet check.  A forbidden
# JSON type leaves a nonempty string, which fails when q is called.
q = str(p).strip('0123456789-[], ') or p.pop
c([], q(), v=1)
print('ACCEPT')

