from fractions import Fraction

from staged_contracts import (
    ContractError,
    StaticNode,
    bounded_demand_closure,
    check_strict_lex_descent,
    compile_static_schedule,
    complete_list_to_height,
    cubic_bisection,
    diameter_stable_observable,
    enumerate_bounded,
    exact_stable_observable,
    height_to_complete_list,
    least_search,
    least_viable_path,
    lex_rank,
    viable_sets,
)


def assert_raises(exc, fn):
    try:
        fn()
    except exc:
        return
    raise AssertionError(f"expected {exc.__name__}")


def test_bounded_search() -> None:
    assert least_search(20, lambda i: i * i >= 50) == 8
    assert least_search(8, lambda i: i * i >= 50) is None
    assert enumerate_bounded(13, lambda i: i % 3 == 1) == [1, 4, 7, 10]


def test_lexicographic_resource() -> None:
    caps = (2, 3, 4)
    run = [(2, 3, 4), (2, 3, 2), (2, 2, 4), (1, 3, 4), (0, 0, 0)]
    assert check_strict_lex_descent(run, caps)
    assert lex_rank((2, 3, 4), caps) == 59
    assert_raises(ContractError, lambda: lex_rank((3, 0, 0), caps))


def test_demand_closure() -> None:
    def transformer(q):
        a, b, c = q
        return (max(a, min(4, b + 1)), max(b, min(4, c + 1)), max(c, 2))

    fixed, trace = bounded_demand_closure((0, 0, 0), transformer, (4, 4, 4))
    assert fixed == (4, 3, 2)
    assert trace[-1] == trace[-2]
    assert len(trace) <= 14

    assert_raises(
        ContractError,
        lambda: bounded_demand_closure((1,), lambda q: (0,), (2,)),
    )


def test_static_compiler() -> None:
    nodes = [
        StaticNode("search", ("input",), "Found(w)"),
        StaticNode("sound", ("search",), "Correct(w)"),
        StaticNode("finish", ("sound",), "Goal"),
    ]
    built = compile_static_schedule(nodes, {"input"})
    assert set(built) == {"search", "sound", "finish"}
    assert built["finish"].node_count() >= 6
    assert_raises(
        ContractError,
        lambda: compile_static_schedule([StaticNode("bad", ("future",), "X")]),
    )


def test_viability() -> None:
    levels = [[0, 1, 2], [10, 11, 12], [20, 21]]
    edges = [lambda a, b: b == 10 + a, lambda a, b: (a, b) in {(10, 20), (12, 21)}]
    viable = viable_sets(levels, edges)
    assert viable == [{0, 2}, {10, 12}, {20, 21}]
    assert least_viable_path(levels, edges) == [0, 10, 20]

    disconnected = [lambda a, b: False]
    assert least_viable_path([[0], [1]], disconnected) is None


def test_stable_observables() -> None:
    assert exact_stable_observable([2, 4, 6], lambda _: "even-cluster") == "even-cluster"
    assert_raises(
        ContractError,
        lambda: exact_stable_observable([1, 2], lambda x: x % 2),
    )
    selected = diameter_stable_observable(
        [3, 5, 4], lambda x: Fraction(x, 10), Fraction(1, 5)
    )
    assert selected == Fraction(3, 10)
    assert_raises(
        ContractError,
        lambda: diameter_stable_observable(
            [0, 10], lambda x: Fraction(x), Fraction(1)
        ),
    )


def test_height_list() -> None:
    values = height_to_complete_list(40, lambda x: x * x <= 100 and x % 2 == 0)
    assert values == [0, 2, 4, 6, 8, 10]
    assert complete_list_to_height(values) == 10
    assert complete_list_to_height([]) == 0


def test_cubic_bisection() -> None:
    final, trace = cubic_bisection(Fraction(7, 3), 12)
    assert len(trace) == 13
    assert all(b.valid() for b in trace)
    assert all(trace[i + 1].width * 2 == trace[i].width for i in range(12))
    assert final.width == trace[0].width / (2**12)
    # Since f is strictly increasing with slope at least 1, any exact root in
    # the bracket is within the bracket width of the midpoint.
    midpoint = (final.lo + final.hi) / 2
    assert final.lo <= midpoint <= final.hi


def main() -> None:
    tests = [
        test_bounded_search,
        test_lexicographic_resource,
        test_demand_closure,
        test_static_compiler,
        test_viability,
        test_stable_observables,
        test_height_list,
        test_cubic_bisection,
    ]
    for test in tests:
        test()
        print(f"PASS {test.__name__}")
    print(f"PASS {len(tests)} test groups")


if __name__ == "__main__":
    main()
