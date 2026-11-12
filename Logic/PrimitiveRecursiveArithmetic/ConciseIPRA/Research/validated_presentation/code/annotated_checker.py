"""Annotated copy of the selected complete checker; comments do not change it."""
import json

# The inherited proof kernel. Its AST is unchanged from the pinned control.
# g contains reusable resources; k is the lowest allocated eigenvariable.
def c(a, g=[0], k=0):
    # i opens the designated numerical slot. Formula padding denotes truth.
    # Each list edge changes protected-slot depth by 5 minus its arity.
    i = lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 else a if k <= a < d else d % 2 and i(t, d=3)
    # A retained normalized resource closes the current obligation.
    if i(a) in g:
        return
    # Verify a four-field packet: major, source, seed/mode, template/witness.
    m, s, u, t = q()
    # Recognize equality transport or closure use and expose its minor.
    a = m == ([s, u] if s else [t] * 3) and i(t, u) == a and i(t, s) or a
    # First prove the major. Then export a closure, computation, or DI body.
    h = c(m, g, k) or m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2))
    # The opener closes over k: this change MUST precede final openings.
    k -= 1
    c(i(a, [k]), g + [i(h, (m or len(a) % 2 == u) and k)], k)

# The input is already an exact integer/list tree. This checks the closed
# goal grammar and scoped variable slots, without a separate raw-type mode.
def v(a, d=0):
    return d % 2 and (not a or (2 < a < d and a % 2)) if a * 0 == 0 else (len(a) in (1, 2 + d % 2) or a == [a[0]] * 3) and all((v(b, d + 5 - len(a)) for b in a))
# Read the complete certificate. No part of an unused prefix escapes typing.
q = json.load(open(0))
# A JSON-derived value has only this representation alphabet exactly when
# every node is an exact integer or list. This deliberately excludes bool.
if repr(q).strip('0123456789[], -') or not v((a := q.pop())):
    raise ValueError('The certificate must use integer/list syntax and have a canonical closed goal')
q = q.pop
c(a)
print('ACCEPT')
