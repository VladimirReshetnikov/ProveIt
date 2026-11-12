"""Untrusted producer for generic, fully expanded BJ equation certificates."""
import json
from pathlib import Path


def V(x): return ["v", x]
def B(a, b): return ["B", a, b]
def S(a): return B(0, a)
def h(a): return ["h", a]
def J(n, binder, body): return ["J", n, binder, body]
def W(n): return B(n, 0)
def sigma(n): return J(n, "s", S(0))
def C(n, a, b): return W(B(B(sigma(n), S(a)), b))
def P(n): return C(n, 0, W(n))
def H(u, a): return C(u, S(a), S(h(P(u))))
def orbit(n, a): return J(S(n), "u", H(V("u"), a))
def iterator(n, a): return P(orbit(n, a))


def ref(label, **images): return {"r": "ref", "name": label, "sub": images}
def sym(p): return {"r": "sym", "proof": p}
def cong(context, p):
    return {"r": "cong", "var": "hole", "context": context(V("hole")), "proof": p}
def chain(*proofs):
    result = proofs[0]
    for proof in proofs[1:]:
        result = {"r": "trans", "left": result, "right": proof}
    return result
def bstep(a, b): return {"r": "B", "a": a, "b": b}
def jzero(binder, body): return {"r": "J0", "binder": binder, "body": body}
def jstep(n, binder, body): return {"r": "JS", "n": n, "binder": binder, "body": body}


def build():
    a, b, n, x, z = map(V, ("a", "b", "n", "x", "z"))
    packet = {"format": "BJ-equations-v1", "lemmas": []}

    def add(label, left, right, proof):
        packet["lemmas"].append({"name": label, "equation": [left, right], "proof": proof})

    add("sign_zero", sigma(0), 0, jzero("s", S(0)))
    add("sign_successor", sigma(S(n)), S(0), jstep(n, "s", S(0)))
    add("weak_predecessor_successor", W(S(n)), n, bstep(n, 0))

    add("selector_zero", C(0, a, b), a,
        chain(cong(lambda v: W(B(B(v, S(a)), b)), ref("sign_zero")),
              cong(W, bstep(S(a), b)), bstep(a, 0)))
    add("selector_successor", C(S(n), a, b), b,
        chain(cong(lambda v: W(B(B(v, S(a)), b)), ref("sign_successor", n=n)),
              cong(lambda v: W(B(v, b)), bstep(0, S(a))), bstep(b, 0)))
    add("predecessor_zero", P(0), 0, ref("selector_zero", a=0, b=W(0)))
    add("predecessor_successor", P(S(n)), n,
        chain(ref("selector_successor", n=n, a=0, b=W(S(n))), bstep(n, 0)))

    add("reset_zero", H(0, a), S(a),
        ref("selector_zero", a=S(a), b=S(h(P(0)))))
    add("reset_successor", H(S(x), a), S(h(x)),
        chain(ref("selector_successor", n=x, a=S(a), b=S(h(P(S(x))))),
              cong(lambda v: S(h(v)), ref("predecessor_successor", n=x))))

    body = H(V("u"), a)
    add("orbit_zero", orbit(0, a), S(a),
        chain(jstep(0, "u", body),
              cong(lambda v: H(v, a), jzero("u", body)), ref("reset_zero", a=a)))
    add("orbit_successor", orbit(S(n), a), H(orbit(n, a), a), jstep(S(n), "u", body))

    # The sole induction is on the literal equation S(P(V(n))) = V(n).
    range_base = chain(cong(lambda v: S(P(v)), ref("orbit_zero", a=a)),
                       cong(S, ref("predecessor_successor", n=a)),
                       sym(ref("orbit_zero", a=a)))
    vz = orbit(z, a)
    qz = chain(ref("orbit_successor", n=z, a=a),
               cong(lambda v: H(v, a), sym({"r": "hyp", "index": 0})),
               ref("reset_successor", x=P(vz), a=a))
    range_step = chain(cong(lambda v: S(P(v)), qz),
                       cong(S, ref("predecessor_successor", n=h(P(vz)))), sym(qz))
    range_proof = {"r": "ind", "var": "n", "eigen": "z",
                   "lhs": S(P(orbit(n, a))), "rhs": orbit(n, a), "target": n,
                   "base": range_base, "step": range_step}
    add("orbit_range", S(P(orbit(n, a))), orbit(n, a), range_proof)

    add("initializer_zero", iterator(0, a), a,
        chain(cong(P, ref("orbit_zero", a=a)), ref("predecessor_successor", n=a)))
    vn = orbit(n, a)
    qn = chain(ref("orbit_successor", n=n, a=a),
               cong(lambda v: H(v, a), sym(ref("orbit_range", n=n, a=a))),
               ref("reset_successor", x=P(vn), a=a))
    add("initializer_successor", iterator(S(n), a), h(iterator(n, a)),
        chain(cong(P, qn), ref("predecessor_successor", n=h(P(vn)))))
    return packet


if __name__ == "__main__":
    destination = Path(__file__).resolve().parents[1] / "certificates" / "bj_equations.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(build(), separators=(",", ":")) + "\n")
    print(destination)
