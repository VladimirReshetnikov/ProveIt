"""Exact finite table evaluation for the nonexpansive metric-logic fragment.

Each unit is 1/D. Instructions are in postorder. The single metric predicate
and all constants are integer-valued in these units. For clarity this
executable instance stores the table explicitly instead of packing it.
"""
from itertools import product
from math import lcm


def evaluate(program, distance, denominator):
    size = len(distance)
    if size == 0 or denominator <= 0:
        raise ValueError("Expected a nonempty stage and positive denominator")
    if any(len(row) != size or any(not 0 <= v <= denominator for v in row)
           for row in distance):
        raise ValueError("Malformed distance table")
    arities = {"dist": 2, "const": 1, "neg": 1, "shift": 2, "min": 2,
               "max": 2, "inf": 1, "sup": 1}
    for index, (op, *args) in enumerate(program):
        if op not in arities or len(args) != arities[op] or any(
                not isinstance(arg, int) or arg < 0 for arg in args):
            raise ValueError(f"Malformed instruction {index}")
        if op in ("min", "max"):
            children = args
        elif op in ("neg", "shift", "inf", "sup"):
            children = args[:1]
        else:
            children = []
        if any(child >= index for child in children):
            raise ValueError(f"Forward reference in instruction {index}")
        if (op == "const" and args[0] > denominator
                or op == "shift" and args[1] > denominator):
            raise ValueError(f"Constant outside the truth-value grid at {index}")
    indices = [i for op, *args in program if op == "dist" for i in args]
    width = max(indices, default=-1) + 1
    assignments = list(product(range(size), repeat=width))
    rows = []
    for op, *args in program:
        row = {}
        for a in assignments:
            if op == "dist":
                left, right = args
                value = distance[a[left]][a[right]]
            elif op == "const":
                value, = args
            elif op == "neg":
                child, = args
                value = denominator - rows[child][a]
            elif op == "shift":
                child, amount = args
                value = max(0, rows[child][a] - amount)
            elif op in ("min", "max"):
                left, right = args
                combine = min if op == "min" else max
                value = combine(rows[left][a], rows[right][a])
            elif op in ("inf", "sup"):
                child, = args
                combine = min if op == "inf" else max
                value = combine(rows[child][((v,) + a)[:width]]
                                for v in range(size))
            else:
                raise ValueError(op)
            assert 0 <= value <= denominator
            row[a] = value
        rows.append(row)
    return rows


def line_grid(steps, denominator):
    assert denominator % steps == 0
    unit = denominator // steps
    return [[unit * abs(x-y) for y in range(steps+1)]
            for x in range(steps+1)]


def circle_grid(m):
    return [[min(abs(x-y), 4*m-abs(x-y)) for y in range(4*m)]
            for x in range(4*m)]


def distortion(left, right, relation):
    assert {i for i, _ in relation} == set(range(len(left)))
    assert {j for _, j in relation} == set(range(len(right)))
    return max(abs(left[i][k] - right[j][l])
               for i, j in relation for k, l in relation)


def main():
    radius = [("dist", 1, 0), ("sup", 0), ("inf", 1)]
    for m in (1, 2, 5):
        d = 2*m
        line = evaluate(radius, line_grid(2*m, d), d)[-1]
        circle = evaluate(radius, circle_grid(m), d)[-1]
        assert set(line.values()) == {m}
        assert set(circle.values()) == {2*m}
        print(f"m={m}: interval radius {m}/{d}; circle radius {2*m}/{d}")

    d = lcm(5, 8)
    left, right = line_grid(5, d), line_grid(8, d)
    rel = [(i, j) for i in range(6) for j in range(9)
           if abs(8*i - 5*j) <= 4]
    error = distortion(left, right, rel)
    assert error == 8
    # An extra shared row and connectives exercise the transfer of open formulas.
    program = radius + [("neg", 0), ("shift", 0, 4), ("max", 3, 4),
                        ("min", 5, 0), ("inf", 6), ("sup", 7), ("const", 9)]
    left_rows, right_rows = evaluate(program, left, d), evaluate(program, right, d)
    assignments = [(tuple(x for x, _ in a), tuple(y for _, y in a))
                   for a in product(rel, repeat=2)]
    for left_row, right_row in zip(left_rows, right_rows):
        assert all(abs(left_row[x] - right_row[y]) <= error for x, y in assignments)
    print(f"5- and 8-step interval grids: atomic distortion {error}/{d}, "
          f"radius discrepancy {abs(left_rows[2][(0,0)]-right_rows[2][(0,0)])}/{d}")
    print(f"Checked {len(program)} instruction rows on {len(assignments)} paired assignments.")


if __name__ == "__main__":
    main()
