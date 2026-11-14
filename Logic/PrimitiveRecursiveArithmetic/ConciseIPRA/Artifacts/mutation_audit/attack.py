"""Build a stream certificate of a false public goal for the variant of the 239-token stream
checker in which the discharge opens its hypothesis at the image 0 whenever the goal is
not an equation, and run it on the control and on the variant.

usage: attack.py <control.py> <out.jsonl>
"""
import ast, json, sys

K = 0


def leaf(p):
    global K
    K -= 1
    return [p]


def node(p, major, minor):
    global K
    out = [p] + major()
    name = K
    out += minor(name)
    K -= 1
    return out


Z3 = [0, 0, 0]
C0 = [0, 0, 0]                      # I(0, 0; u.0), a term other than the literal 0 with value 0
E_F = [[5, 0, [0]], [5, 0, 0]]      # I(y, 0; u.S0) = I(y, 0; u.0): false at y = 1
A = [E_F]                           # D_{x,y} E_F, a false public formula
B = [[5, 0, [9, [0], 0]], 0]        # I(y, 0; u.sel(x, 1, 0)) = 0
BD1 = [[C0], [0], 0]                # sel(S c0, 1, 0), value 0
BD0 = [0, [0], 0]                   # sel(0, 1, 0), value 1
B0 = [[5, 0, BD0], 0]               # the matrix at x = 0, with y bound
T = [[C0], 0, BD0]                  # I(S c0, 0; u.BD0)


def prove_DB():
    # D_{x,y} B at the witness S c0, in the mode of progress
    def minor(z):
        X = [[z], 0, BD1]
        return node([BD1, 0, [X, 3]],                       # X = 0 from BD1 = 0 and X = BD1
                    lambda: leaf([C0, [0], 0]),             # BD1 = 0, successor computation
                    lambda _: leaf([z, 0, BD1]))            # X = BD1, successor computation
    return node([0, 0, [C0]], lambda: leaf(Z3), minor)


def refute(_):
    # with Q_y B(0, y) in the context: introduce D_{x,y} E_F by progress
    def step(z):
        L = [[z], 0, [0]]
        WL = [0, L, 0]

        def one_zero():                                      # 1 = 0
            def bd0_zero(_):                                 # BD0 = 0
                def t_zero(_):                               # T = 0 by QE at S c0
                    return node([0, [C0], B0],
                                lambda: leaf(Z3),            # Q_y B(0, y), from the context
                                lambda _: leaf([0, 0, BD0])) # the instance at 0, zero computation
                return node([T, BD0, [3, 0]],
                            lambda: leaf([C0, 0, BD0]),      # T = BD0, successor computation
                            t_zero)
            return node([BD0, [0], [3, 0]],
                        lambda: leaf([0, [0], 0]),           # BD0 = 1, zero computation
                        bd0_zero)

        def refl(_):                                         # L = L
            return node([WL, L, [3, L]],
                        lambda: leaf([0, L, 0]),
                        lambda _: leaf([0, L, 0]))
        return node([[0], 0, [L, [[z], 0, 5]]], one_zero, refl)
    return node(Z3, lambda: leaf(Z3), step)


stream = [A] + node([[B], 0, 0], prove_DB, refute)
lines = [json.dumps(x) for x in stream]
open(sys.argv[2], "w", encoding="utf-8", newline="\n").write("\n".join(lines) + "\n")

control = ast.unparse(ast.parse(open(sys.argv[1], encoding="utf-8").read())) + "\n"
old = "k if c(g, s) or s or len(a) == 2 else 0"
assert control.count(old) == 1
variant = control.replace(old, "k if c(g, s) or len(a) == 2 else 0")


def run(code):
    it = iter(lines)
    out = []
    env = {"input": lambda: next(it), "print": lambda *a: out.append(a)}
    try:
        exec(code, env)
    except BaseException as e:
        return "reject (%s: %s), %d lines unread" % (type(e).__name__, e, len(list(it)))
    return "%s, %d lines unread" % (out, len(list(it)))


print("packets", len(lines) - 1)
print("control:", run(control))
print("variant:", run(variant))
