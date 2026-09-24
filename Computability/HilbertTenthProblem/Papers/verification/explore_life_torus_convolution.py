"""Exact finite corroboration of the conditional Life torus interface.

No full universal operation bound is claimed. The source note proves the
unbounded conditional interface; this script checks its arithmetic and seams.
"""

from collections import Counter
from itertools import product
import json
from pathlib import Path


B = 64
SCHEDULE = [
    ("rightmask", "*", "A", "h"),
    ("leftsum", "+", "C", "h"),
    ("lefttwo", "*", 2, "L"),
    ("leftout", "+", "Xl", "lefttwo"),
    ("rightsum", "+", "C", "rightmask"),
    ("rightedge", "*", "A", "R"),
    ("righttwo", "*", 2, "rightedge"),
    ("rightout", "+", "Xr", "righttwo"),
    ("br", "*", 64, "R"),
    ("edge", "-", "L", "br"),
    ("correction", "*", "wm1", "edge"),
    ("centerconv", "*", 4161, "C"),
    ("horizontalnumerator", "+", "centerconv", "correction"),
    ("W2", "*", "W", "W"),
    ("K0", "+", "W2", "W"),
    ("K", "+", "K0", 1),
    ("conv", "*", "K", "horizontalnumerator"),
    ("u12", "+", "U1", "U2"),
    ("term12", "*", 384, "u12"),
    ("centerthird", "-", "C", "U3"),
    ("term7", "*", 448, "centerthird"),
    ("termY", "*", 1408, "Y"),
    ("term4", "*", 704, "U4"),
    ("term5", "*", 896, "U5"),
    ("rhs45", "+", "term4", "term5"),
    ("v0", "-", "rhs45", "termY"),
    ("v1", "-", "v0", "term12"),
    ("V64", "+", "v1", "term7"),
    ("WV64", "*", "W", "V64"),
    ("quotient", "*", "qm1", "z"),
    ("rhs", "+", "WV64", "quotient"),
]
EQUALITIES = [("leftsum", "leftout"), ("rightsum", "rightout"),
              ("conv", "rhs")]
NONNEGATIVE_INPUTS = ["C", "Y", "U1", "U2", "U3", "U4", "U5",
                      "L", "R", "Xl", "Xr"]


def pack(bits):
    return sum(bit * B**i for i, bit in enumerate(bits))


def local_witnesses(center, neighbors, output):
    return [u for u in product(range(2), repeat=5)
            if neighbors + 22*output + 6*(u[0]+u[1]-center) + 7*u[2]
            == 11*u[3]+14*u[4]]


def evaluate(inputs):
    env = dict(inputs)
    for name, op, left, right in SCHEDULE:
        assert name not in env
        a = env[left] if isinstance(left, str) else left
        b = env[right] if isinstance(right, str) else right
        env[name] = a+b if op == "+" else a-b if op == "-" else a*b
    assert all(env[a] == env[b] for a, b in EQUALITIES)
    return env


def check_torus(m, n, code):
    cells = [(code >> i) & 1 for i in range(m*n)]
    C = pack(cells)
    W, Q = B**m, B**(m*n)
    A, h = W//B, (Q-1)//(W-1)
    at = lambda i, j: cells[(i % m)+m*(j % n)]
    left = [at(0, j) for j in range(n)]
    right = [at(m-1, j) for j in range(n)]
    L = sum(bit*W**j for j, bit in enumerate(left))
    R = sum(bit*W**j for j, bit in enumerate(right))
    # Each XOR is checked directly on physical digits, never by a packed AND.
    Xl = pack([cells[i] ^ int(i % m == 0) for i in range(m*n)])
    Xr = pack([cells[i] ^ int(i % m == m-1) for i in range(m*n)])
    Hbits, Vbits, output, aux = [], [], [], [[] for _ in range(5)]
    for j in range(n):
        for i in range(m):
            horizontal = sum(at(i+di, j) for di in (-1, 0, 1))
            inclusive = sum(at(i+di, j+dj)
                            for di in (-1, 0, 1) for dj in (-1, 0, 1))
            neighbors = inclusive-at(i, j)
            y = int(neighbors == 3 or (at(i, j) == 1 and neighbors == 2))
            u = local_witnesses(at(i, j), neighbors, y)[0]
            Hbits.append(horizontal)
            Vbits.append(inclusive)
            output.append(y)
            for k in range(5):
                aux[k].append(u[k])
    H, V, Y = pack(Hbits), pack(Vbits), pack(output)
    assert B*H == 4161*C+(W-1)*(L-B*R)
    numerator = (W*W+W+1)*B*H-W*B*V
    assert numerator % (Q-1) == 0
    z = numerator//(Q-1)
    inputs = dict(C=C, Y=Y, A=A, h=h, L=L, R=R, Xl=Xl, Xr=Xr,
                  W=W, Q=Q, wm1=W-1, qm1=Q-1, z=z)
    inputs.update({f"U{k+1}": pack(aux[k]) for k in range(5)})
    env = evaluate(inputs)
    assert env["V64"] == B*V
    assert env["horizontalnumerator"] == B*H
    assert A*B == W and h*(W-1) == Q-1
    assert W*(Q//W) == Q and 63*((W-1)//63) == W-1
    # Explicit positive-domain reconstruction, including both signs of z.
    positive = {name: inputs[name]+1 for name in NONNEGATIVE_INPUTS}
    assert all(value > 0 for value in positive.values())
    reconstructed = dict(inputs)
    for name in NONNEGATIVE_INPUTS:
        reconstructed[name] = positive[name]-1
    zplus, zminus = max(z, 0)+1, max(-z, 0)+1
    reconstructed["z"] = zplus-zminus
    assert evaluate(reconstructed) == env
    return m*n, z


def verify():
    local_cases = 0
    for center, neighbors, output in product(range(2), range(9), range(2)):
        life = int(neighbors == 3 or (center == 1 and neighbors == 2))
        assert bool(local_witnesses(center, neighbors, output)) == (output == life)
        local_cases += 1
    totals, cells, negative_z, zero_z, positive_z = 0, 0, 0, 0, 0
    by_shape = []
    for m, n in product(range(1, 4), repeat=2):
        count = 1 << (m*n)
        for code in range(count):
            cell_count, z = check_torus(m, n, code)
            totals += 1
            cells += cell_count
            negative_z += z < 0
            zero_z += z == 0
            positive_z += z > 0
        by_shape.append({"width": m, "height": n, "presentations": count})
    W, C = B**2, B**3
    assert B*C == W+(W-1)*W
    assert B*C == 1+(W-1)*(1+W)
    histogram = Counter(row[1] for row in SCHEDULE)
    assert len(SCHEDULE) == 31 and histogram == {"*": 16, "+": 11, "-": 4}
    return {
        "status": "PASS_CONDITIONAL_INTERFACE",
        "scope": "Exact torus and local-rule interface; Booleanity, power decoding, "
                 "and uniform raw-target encoding are not included in operation counts.",
        "local_truth_table_cases": local_cases,
        "torus_presentations": totals,
        "physical_cell_checks": cells,
        "quotient_signs": {"negative": negative_z, "zero": zero_z,
                           "positive": positive_z},
        "shapes": by_shape,
        "conditional_schedule": {"total": 31, "multiplications": 16,
                                 "additions_subtractions": 15},
        "geometry": {"total": 6, "multiplications": 4,
                     "additions_subtractions": 2},
        "generic_positive_adapter": {"subtractions": 12},
        "combined_positive_interface": {"total": 49, "multiplications": 20,
                                       "additions_subtractions": 29},
        "boolean_words": ["C", "Y", "U1", "U2", "U3", "U4", "U5",
                          "L", "Xl", "Xr", "rightedge"],
        "schedule": [{"target": n, "operator": op, "left": a, "right": b}
                     for n, op, a, b in SCHEDULE],
        "equalities": EQUALITIES,
        "invalid_edge_shortcut_counterexamples": 2,
    }


if __name__ == "__main__":
    result = verify()
    path = Path(__file__).with_suffix(".json")
    path.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(f"PASS: {result['torus_presentations']} torus presentations, "
          f"{result['physical_cell_checks']} physical cells, "
          "31 conditional local primitives / 49 with geometry and positive adapters")
