"""Generate and verify nontrivial certificates; this is not trusted by checker.py."""

import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

SEVEN = "--seven" in sys.argv
if SEVEN:
    import checker_seven as K
else:
    import checker as K

Z = K.ZERO
S = lambda x: ["s", x]
R = lambda n, a, h: ["r", n, a, h]
E = lambda a, b: ["=", a, b]
C = lambda n, a, b: R(n, a, K.lift(b, 2))


def embed(p, context_at, variables=1, hypotheses=1, depth=0):
    """Insert outer parameters and an assumption before the proof's local assumptions."""
    rule, *a = p
    term = lambda x, extra=0: K.lift(x, variables, depth+extra)
    child = lambda x, extra=0: embed(x, context_at, variables, hypotheses, depth+extra)
    if rule == "hyp":
        return [rule, a[0] + (hypotheses if a[0] >= context_at else 0)]
    if rule == "refl":
        return [rule, term(a[0])]
    if rule == "root":
        return [rule, term(a[0]), child(a[1])]
    if rule == "sub":
        return [rule, child(a[0]), child(a[1])]
    if rule == "qe":
        return [rule, child(a[0]), child(a[1]), term(a[2])]
    if rule == "de":
        return [rule, term(a[0]), child(a[1]), child(a[2], 1)]
    if rule == "di":
        return [rule, term(a[0], 2), term(a[1]), child(a[2], 1)]
    if rule == "qi":
        return [rule, term(a[0], 1), child(a[1], 1)]
    raise ValueError(rule)


def symmetry(n, count, equation, proof):
    trivial = ["di", E(Z, Z), Z, ["refl", Z]]
    branch = ["sub", ["refl", 0], embed(proof, count)]
    return ["de", E(equation[2], equation[1]), trivial, branch]


def change(n, count, equation, proof, side, target):
    if side == 0:
        return E(target, equation[2]), ["root", target, proof]
    reversed_proof = symmetry(n, count, equation, proof)
    converted = ["root", target, reversed_proof]
    after = E(target, equation[1])
    return E(equation[1], target), symmetry(n, count, after, converted)


def reduce_equation(n, count, equation, proof, target):
    for side in (0, 1):
        while equation[side+1] != target[side+1]:
            t = K.root(equation[side+1])
            assert t is not None, (equation, target)
            equation, proof = change(n, count, equation, proof, side, t)
    assert equation == target
    return proof


def expand_equation(n, count, equation, proof, target):
    for side in (0, 1):
        chain = [target[side+1]]
        while chain[-1] != equation[side+1]:
            t = K.root(chain[-1])
            assert t is not None, (chain, equation)
            chain.append(t)
        for t in reversed(chain[:-1]):
            equation, proof = change(n, count, equation, proof, side, t)
    assert equation == target
    return proof


def case_closure(n, count, matrix, step):
    dummy = K.lift(matrix, 1, 1)
    intro = ["di", dummy, S(Z) if SEVEN else Z, embed(step, count, variables=0)]
    return ["de", ["q", matrix], intro, ["hyp", count]]


def cases(n, count, matrix, t, base, step):
    return ["qe", case_closure(n, count, matrix, step), base, t]


def packet(counter, first, second):
    return R(counter, Z, C(1, K.lift(first, 2), K.lift(second, 2)))


def transport(n, context, s, t, h, r, major, minor):
    """Crossed transport: s=t, h(s)=r entail r=h(t), using root steps only."""
    count = len(context)
    hs, ht = K.inst(h, [s]), K.inst(h, [t])
    hx = K.inst(h, [1] + list(range(2, n+2)))
    body = E(packet(0, 1, hx), packet(0, K.lift(t, 2), K.lift(r, 2)))

    # Under the fresh z and unused base assumption, prove the successor row
    # by cases on z.  The two cases are exactly the given two equations.
    ss, tt, hh, rr = map(K.lift, (s, t, hs, r))
    test = E(C(0, K.lift(ss), K.lift(hh)),
             C(0, K.lift(tt), K.lift(rr)))
    base_equation = K.inst(test, [Z])
    base = expand_equation(n+1, count+1, E(ss, tt), embed(major, count), base_equation)
    successor = K.inst(test, [S(0)] + list(range(1, n+2)))
    step = expand_equation(n+2, count+1, E(K.lift(hh), K.lift(rr)),
                          embed(minor, count, variables=2), successor)
    selection = K.inst(test, [0])
    selected = cases(n+1, count+1, test, 0, base, step)
    outer_step = K.inst(body, [S(0), K.lift(s)] + list(range(1, n+1)))
    intro_step = expand_equation(n+1, count+1, selection, selected, outer_step)
    intro = ["di", body, s, intro_step]

    # Open at b. The rows at 0, 1 and 2 expose a reflexive base and
    # the two equations b=t and h(b)=r, by root contraction alone.
    zero_row = K.inst(body, [Z])
    zero_proof = expand_equation(n+1, count+1, E(Z, Z), ["refl", Z], zero_row)
    first_row = K.inst(body, [S(Z)])
    first = ["qe", ["hyp", count], zero_proof, S(Z)]
    first = reduce_equation(n+1, count+1, first_row, first, E(0, K.lift(t)))
    second_row = K.inst(body, [S(S(Z))])
    second = ["qe", ["hyp", count], zero_proof, S(S(Z))]
    second = reduce_equation(n+1, count+1, second_row, second, E(h, K.lift(r)))
    result = E(r, ht)
    proof = ["de", result, intro, ["sub", first, second]]
    assert K.check(n, context, proof) == result
    return result, proof


def rejected(n, context, proof):
    try:
        K.check(n, context, proof)
    except (ValueError, TypeError, KeyError, IndexError, RecursionError):
        return True
    return False


def main():
    directory = Path(__file__).resolve().parent
    certificates = directory / ("certificates_seven" if SEVEN else "certificates")
    certificates.mkdir(exist_ok=True)
    positives = []
    negatives = []

    # Nontrivial open transport, with a parameter in the initializer/body.
    context = [E(0, 1), E(S(0), 2)]
    target, p = transport(3, context, 0, 1, S(0), 2, ["hyp", 0], ["hyp", 1])
    positives.append({"name": "open_transport", "goal": target, "scope": 3})
    (certificates / "open_transport.json").write_text(json.dumps(
        {"scope": 3, "context": context, "goal": target, "proof": p}, separators=(",", ":")))

    context_zero = [E(Z, 0), E(S(Z), 1)]
    target_zero, p_zero = transport(2, context_zero, Z, 0, S(0), 1, ["hyp", 0], ["hyp", 1])
    positives.append({"name": "literal_zero_witness_transport", "goal": target_zero, "scope": 2})
    (certificates / "zero_witness_transport.json").write_text(json.dumps(
        {"scope": 2, "context": context_zero, "goal": target_zero, "proof": p_zero}, separators=(",", ":")))

    # Transport also crosses a genuine recursor binder without capturing its
    # state/counter or losing a retained outer parameter.
    bound_template = R(1, S(0), R(2, 0, 0))
    bound_context = [E(0, 1), E(K.inst(bound_template, [0]), 2)]
    bound_target, bound_proof = transport(3, bound_context, 0, 1, bound_template, 2,
                                        ["hyp", 0], ["hyp", 1])
    positives.append({"name": "transport_below_recursor_binder", "goal": bound_target, "scope": 3})
    (certificates / "binder_transport.json").write_text(json.dumps(
        {"scope": 3, "context": bound_context, "goal": bound_target, "proof": bound_proof}, separators=(",", ":")))

    # A nested zero redex is not a root redex. Full congruence must be derived.
    j = R(Z, Z, 0)
    major = ["root", j, ["refl", Z]]
    target, p = transport(0, [], j, Z, S(0), S(j), major, ["refl", S(j)])
    certificate = {"goal": target, "proof": p}
    (certificates / "nested_conversion.json").write_text(json.dumps(certificate, separators=(",", ":")))
    positives.append({"name": "nested_conversion_via_transport", "goal": target, "scope": 0})

    # A complete primitive-recursion induction rule really is available.
    body = E(R(0, Z, 0), Z)
    # Under E(z), unfold R(S z,0;i,u.u) at the left endpoint and use E(z).
    successor = K.inst(body, [S(0)])
    step = ["root", successor[1], ["hyp", 0]]
    if SEVEN:
        intro = ["di", K.lift(body, 1, 1), Z, step]
        closure = ["de", ["q", body], intro, ["hyp", 0]]
    else:
        closure = ["qi", body, step]
    closure_goal = ["q", body]
    assert K.check(0, [], closure) == closure_goal
    (certificates / "identity_iteration_induction.json").write_text(json.dumps(
        {"goal": closure_goal, "proof": closure}, separators=(",", ":")))
    positives.append({"name": "identity_iteration_induction", "goal": closure_goal, "scope": 0})

    tests = [
        ("nested_step_forbidden", 0, [], ["root", S(Z), ["refl", S(j)]]),
        ("unproved_false_equation", 0, [], ["root", S(Z), ["refl", Z]]),
        ("boolean_variable", 1, [], ["refl", True]),
        ("out_of_scope_variable", 0, [], ["refl", 0]),
        ("compound_induction_forbidden", 0, [], ["qi", ["d", E(Z, Z)], ["refl", Z]]),
        ("nonzero_witness_cannot_select_progress", 0, [],
         ["di", E(R(0, Z, 0), Z), S(Z),
          ["root", R(S(0), Z, 0), ["hyp", 0]]]),
        ("variable_source_required", 0, [], ["sub", ["refl", Z], ["refl", Z]]),
        ("fresh_witness_escape", 0, [], ["de", E(Z, Z),
         ["di", E(Z, Z), Z, ["refl", Z]], ["refl", 0]]),
        ("zero_step_cannot_compute_body", 0, [], ["root", R(Z, Z, S(0)), ["refl", S(Z)]]),
    ]
    for name, n, context, proof in tests:
        assert rejected(n, context, proof), name
        negatives.append(name)

    cli = []
    for file in sorted(certificates.glob("*.json")):
        if file.name in ("open_transport.json", "zero_witness_transport.json", "binder_transport.json"):
            continue
        for optimized in (False, True):
            checker_name = "checker_seven.py" if SEVEN else "checker.py"
            command = [sys.executable] + (["-O"] if optimized else []) + [str(directory / checker_name)]
            run = subprocess.run(command, input=file.read_bytes(), capture_output=True)
            assert run.returncode == 0 and run.stdout == b"ACCEPT\n", (file, run.stderr)
            cli.append({"file": file.name, "optimized": optimized, "accepted": True})

    source = (directory / ("checker_seven.py" if SEVEN else "checker.py")).read_bytes()
    normalized = (ast.unparse(ast.parse(source)) + "\n").encode()
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = sum(t.type not in ignored for t in tokenize.tokenize(io.BytesIO(normalized).readline))
    receipt = {
        "scope": "finite certificate checks, not a proof of universal soundness",
        "rule_families": 7 if SEVEN else 8,
        "positive_cases": positives, "negative_cases": negatives, "cli": cli,
        "checker_sha256": hashlib.sha256(source).hexdigest(),
        "raw_bytes": len(source), "normalized_bytes": len(normalized),
        "significant_tokens": tokens, "ast_nodes": len(list(ast.walk(ast.parse(normalized)))),
        "gzip9_raw_bytes": len(gzip.compress(source, compresslevel=9, mtime=0)),
        "gzip9_normalized_bytes": len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        "python": sys.version,
    }
    (directory / ("verification_seven.json" if SEVEN else "verification.json")).write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
