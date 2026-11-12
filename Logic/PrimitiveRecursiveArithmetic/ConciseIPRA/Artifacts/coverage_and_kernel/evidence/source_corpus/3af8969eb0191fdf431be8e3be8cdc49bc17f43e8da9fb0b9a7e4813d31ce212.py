"""Untrusted producer of focused all-starts certificates and negative controls."""
import ast
import copy
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CHECKER = ROOT / "code/all_starts_checker.py"


def core(path=CHECKER):
    tree = ast.parse(path.read_text())
    if not isinstance(tree.body[-1], ast.Try):
        raise ValueError("Expected the complete public driver as final statement")
    tree.body.pop()
    ns = {}
    exec(compile(tree, str(path), "exec"), ns)
    return ns


def run_core(packet, start=0, namespace=None):
    ns = core() if namespace is None else namespace
    data = copy.deepcopy(packet)
    ns.update(k=start, q=data.pop)
    try:
        accepted = bool(ns["c"](data.pop(), []))
        error = None
    except BaseException as exc:
        accepted, error = False, type(exc).__name__
    return accepted, ns["k"], len(data), error


def numeral(n):
    result = 0
    for _ in range(n):
        result = [result]
    return result


def equation(counter, seed):
    return [[counter, seed, 2], seed]


def identity_closure(seed, start=0):
    """Q_n[I(n,seed;u.u)=seed], using an actual induction hypothesis."""
    body = equation(5, seed)
    fresh = start - 1
    hypothesis = equation(fresh, seed)
    motive = [[[fresh], seed, 2], 1]
    return [[0, 0], [hypothesis, motive], [0, [0, 0, 0]],
            [[body, body, body], 0], [body]]


def instance_identity(n, seed):
    """A computation/transport proof of I(n,seed;id)=seed for a numeral n."""
    if n == 0:
        return [[0, 0], equation(0, seed)]
    previous = instance_identity(n - 1, seed)
    target = equation(numeral(n), seed)
    motive = [target[0], 1]
    return [[0, 0]] + previous[:-1] + [[previous[-1], motive], target]


def specialize_identity(r, v, seed):
    """Use the new all-starts branch at numeral start r and seed/shift v."""
    major = identity_closure(seed)
    minor = instance_identity(r, seed)
    trajectory = [numeral(r), numeral(v), [3]]
    return minor[:-1] + major[:-1] + [[major[-1], [numeral(r), numeral(v)]],
                                    equation(trajectory, seed)]


def reflexivity(term):
    source = [[0, term, 0], term]
    return [[0, 0], [0, 0], [source, [1, term]], [term, term]]


def compound_induction_counterexample():
    """A certificate needing the forbidden compound IH, not just its base.

    The formula is provable by another derivation. This packet must reject:
    it uses Q_u[I(z,1;id)=1] as if compound DI had supplied that hypothesis.
    A mutant granting compound induction accepts this exact packet.
    """
    seed = [0]
    before = [-1, seed, 2]
    after = [[-1], seed, 2]
    forward = [after, before]
    symmetric = reflexivity(after)[:-1] + [[0, 0], [forward, [1, after]],
                                         [before, after]]
    formula_motive = [[3, seed]]
    matrix = [[[7, seed, 2], seed]]
    return symmetric[:-1] + [[[before, after], formula_motive],
                             [0, [0, 0, 0]], [0, 0, matrix]]


def make():
    records = []

    def add(name, packet, accept, meaning):
        records.append(dict(name=name, packet=packet, accept=accept, meaning=meaning))

    add("zero_computation", [[0, 0], [[0, 0, 0], 0]], True,
        "The direct I0 equation.")
    add("successor_computation", [[0, 0], [[[0], 0, [3]], [[0, 0, [3]]]]], True,
        "The direct IS equation for the successor update.")
    add("identity_induction", identity_closure([0]), True,
        "Atomic DI genuinely uses its local induction equation.")
    for seed in (0, [0], numeral(3)):
        for r, v in ((0, 3), (1, 0), (2, 3)):
            add(f"all_starts_r{r}_v{v}_seed{len(str(seed))}",
                specialize_identity(r, v, seed), True,
                f"New atomic QE with start {r}, offset {v}, and a fixed initializer.")

    # A nested theorem from the inherited focused suite. The outer DI is
    # compound Case, the inner DI atomic progress, with a passive initializer.
    parameter_body = [[5, 7, 2], 3]
    inner_body = [[5, [-1], 2], [-1]]
    hypothesis = [[-2, [-1], 2], [-1]]
    motive = [[[-2], [-1], 2], 1]
    parameter_identity = [[0, 0], [hypothesis, motive], [0, [0, 0, 0]],
                          [[inner_body, inner_body, inner_body], 0],
                          [[], [0, 0, 0]],
                          [[[parameter_body], [parameter_body], [parameter_body]], 0],
                          [[parameter_body]]]
    add("passive_initializer_and_counter", parameter_identity, True,
        "Nested compound Case and atomic progress, with a captured initializer.")

    ok, floor, _, _ = run_core(parameter_identity)
    if not ok:
        raise RuntimeError("Parameter-identity producer failed")
    minor = identity_closure(0, start=floor)
    compound_elimination = minor[:-1] + parameter_identity[:-1] + [
        [parameter_identity[-1], [0]], identity_closure([0])[-1]]
    add("compound_closure_elimination", compound_elimination, True,
        "Compound QE retains its original numerical payload and zero-base premise.")

    for label, head in (("empty_list", []), ("null", None), ("false", False),
                        ("empty_object", {}), ("empty_string", "")):
        packet = identity_closure([0])
        packet[2][0] = head
        add("falsy_head_" + label, packet, True,
            "All falsy introduction markers now select the same deterministic rule.")

    add("canonical_false", [[0, 0], [0, [0]]], False, "0=1 is not a computation.")
    add("changed_zero_computation", [[0, 0], [[0, 0, 0], [0]]], False,
        "A forged I0 result.")
    add("free_negative_goal_parameter", [[0, 0], [[0, -1, 0], -1]], False,
        "The public goal must be closed at freshness floor zero.")
    add("four_child_goal", [[0, 0], [0, 0, 0, 0]], False,
        "No constructor has arity four.")

    broken = identity_closure([0]); broken.pop(0)
    add("missing_induction_minor", broken, False,
        "The required successor-computation minor is absent.")
    captured = copy.deepcopy(parameter_identity)
    captured[1][0][0][0] = -1
    add("captured_inner_counter", captured, False,
        "The inner eigenparameter is confused with the passive outer parameter.")

    retained_false_base = [[0, 0], [[0, [0]], [[5, [0], [-1]], [0]]],
                          [0, 0], [[[[0], [0], [-1]], [-1]], [1, [0]]],
                          [[], [0, 0, 0]], [[[1, [0]], [1, [0]], [1, [0]]], 0],
                          [[1, [0]]]]
    add("old_atomic_case_is_unavailable", retained_false_base, False,
        "The old proof of conditional Q_y(y=1) does not prove its new all-starts reading.")
    add("forbidden_compound_induction", compound_induction_counterexample(), False,
        "The packet incorrectly relies on a compound induction hypothesis.")

    failed_major = [[0, 0], [[[0, 0, 0], [0]], 0], [[0, 0, 0], 0]]
    add("failed_major_cannot_fall_through", failed_major, False,
        "A false-returning truthy major must reject before any fallback.")

    for field in (0, 1):
        for exposed in (1, 3):
            packet = specialize_identity(0, 0, [0])
            pair = [0, 0]; pair[field] = exposed
            packet[-2][1] = pair
            # These indices would become harmless dummy slots if endpoints
            # were only checked after being placed under the iterator.
            packet[-1] = equation([pair[0], pair[1], [3]], [0])
            add(f"exposed_endpoint_{field}_{exposed}", packet, False,
                "Each QE endpoint must validate at numerical root before trajectory construction.")

    for label, payload in (("scalar", 0), ("one_field", [0]),
                           ("three_fields", [0, 0, 0]),
                           ("string_endpoint", [0, "x"]),
                           ("object_endpoint", [0, {}]),
                           ("future_parameter", [0, -999])):
        packet = specialize_identity(0, 0, [0]); packet[-2][1] = payload
        add("malformed_qe_" + label, packet, False,
            "Malformed or out-of-scope atomic-Q endpoint data reject.")

    altered = specialize_identity(2, 3, [0])
    altered[-1][1] = numeral(2)
    add("changed_all_starts_result", altered, False,
        "The instantiated conclusion must match the requested goal exactly.")

    for row in records:
        actual, _, _, error = run_core(row["packet"])
        if actual != row["accept"]:
            raise RuntimeError(f"Unexpected {row['name']}: {actual}, {error}")
    target = ROOT / "evidence/focused_certificates.json"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps({"cases": records}, indent=2) + "\n")
    print(json.dumps({"cases": len(records),
                      "positive": sum(r["accept"] for r in records),
                      "negative": sum(not r["accept"] for r in records)}))
    return records


if __name__ == "__main__":
    make()
