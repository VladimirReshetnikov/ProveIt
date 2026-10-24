"""Additional audit checks; does not import the producer or supplied verifier.

Run from any directory: python norm_audit/independent_checks.py.
Input is the adjacent frozen norm release. Standard library plus SymPy.
"""
from collections import Counter
from pathlib import Path
import gzip
import hashlib
import json
import sympy as sp

ROOT = Path(__file__).resolve().parent.parent / "norm"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def read(name):
    return json.loads((ROOT / name).read_text())


hashes = read("RELEASE_SHA256.json")
for name, expected in hashes.items():
    require(hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == expected,
            "release hash: " + name)
fixed = {}
for name, info in read("FIXED_COEFFICIENTS.json").items():
    compressed = (ROOT / info["file"]).read_bytes()
    raw = gzip.decompress(compressed)
    require(raw[0] in (0, 1), "sign byte")
    require(hashlib.sha256(compressed).hexdigest() == info["gzip_sha256"], "compressed coefficient hash")
    require(hashlib.sha256(raw).hexdigest() == info["raw_sha256"], "raw coefficient hash")
    magnitude = int.from_bytes(raw[1:], "little")
    require(magnitude.bit_length() == info["bit_length"], "coefficient bit length")
    fixed[name] = (-1 if raw[0] else 1) * magnitude


def inspect_graph(graph):
    nodes = graph["nodes"]
    dependencies = []
    for index, node in enumerate(nodes):
        kind = node["kind"]
        require(kind in ("variable", "fixed", "literal", "add", "sub", "mul"), "node kind")
        if kind in ("add", "sub", "mul"):
            a, b = node["left"], node["right"]
            require(0 <= a < index and 0 <= b < index, "topology")
            dependencies.append(dependencies[a] | dependencies[b])
        else:
            dependencies.append({node["name"]} if kind == "variable" else set())
    reached, pending = set(), [graph["output"]]
    while pending:
        index = pending.pop()
        if index in reached:
            continue
        reached.add(index)
        if "left" in nodes[index]:
            pending += [nodes[index]["left"], nodes[index]["right"]]
    require(reached == set(range(len(nodes))), "every graph node is live")
    counts = Counter(nodes[index]["kind"] for index in reached if "left" in nodes[index])
    return dict(counts), dependencies


def degree_witnesses(graph, prime, direction):
    """Upper degrees plus coefficients after x_i = direction_i * T.

    A nonzero coefficient at the upper degree certifies exact multivariate
    degree. A zero is not interpreted as an attained degree.
    """
    upper, coefficient = [], []
    assignment = dict(zip(graph["variables"], direction))
    for node in graph["nodes"]:
        kind = node["kind"]
        if kind == "variable":
            degree, value = 1, assignment[node["name"]]
        elif kind in ("fixed", "literal"):
            degree = 0
            value = fixed[node["name"]] if kind == "fixed" else node["value"]
        else:
            a, b = node["left"], node["right"]
            if kind == "mul":
                degree, value = upper[a] + upper[b], coefficient[a] * coefficient[b]
            else:
                degree = max(upper[a], upper[b])
                value = (coefficient[a] if upper[a] == degree else 0)
                value += (1 if kind == "add" else -1) * (coefficient[b] if upper[b] == degree else 0)
        upper.append(degree)
        coefficient.append(value % prime)
    return {name: (upper[index], coefficient[index]) for name, index in graph["named_nodes"].items()}


metrics = []
for mode, old_count, new_count, degree in [
    ("polar", 471, 467, 1245324), ("linear", 475, 470, 1179788),
    ("cubic", 478, 473, 1114252), ("sixterm", 512, 507, 1080888)
]:
    parent = read("source/" + ("integer10_polar" if mode == "polar" else mode) + ".json")
    candidate = read("integer10_" + mode + ".json")
    parent_counts, parent_deps = inspect_graph(parent)
    counts, deps = inspect_graph(candidate)
    require(sum(parent_counts.values()) == old_count, "independent parent count")
    require(sum(counts.values()) == new_count, "independent candidate count")
    require(counts == candidate["operation_counts"], "operation metadata")
    require(candidate["variables"] == ["t", "g0", "c0", "k0", "l", "w", "x", "y", "z", "m"], "ten coordinates")
    require(len({n["name"] for n in candidate["nodes"] if n["kind"] == "fixed"}) == 12, "twelve fixed leaves")
    for name in ("Sigma_new", "Theta_new", "guard", "lucas", "shear"):
        if name in candidate["named_nodes"]:
            require("m" not in deps[candidate["named_nodes"][name]], "prefix and shear independent of m")
    metrics.append(dict(mode=mode, parent_operations=old_count, operations=new_count,
                        operation_breakdown=counts, exact_degree=degree))

# Independently write and expand the source formulas over Z[h,b,c,xi,y].
h, b, c, xi, y = sp.symbols("h b c xi y")
generators = (h, b, c, xi, y)
weights = (16384, 7942, 1, 2, 1)
u, A = c**2, 2*h
D = (A**2-4)*u+4
E0 = u*xi
E = E0*D
F = 4*(A**2-4)*u**2*D*xi**2+1
G = (h-1)*(F-1)-1
H = c+F*(b-c+16*E*y)
a1 = D*F*((G**2-1)*H**2+1)
qa = u*(2*h**2-11)+6
qb = u**2*(8*h**4-52*h**2+143)+u*(32*h**2-176)+48
T6 = xi*(b-c)*qa+16*E0*xi*y*qb+3*y
shifts = {
    "linear": 2*A*E*G*H,
    "cubic": 2*A*E0*(D-2*u)*G*H,
    "sixterm": 32768*u**3*E0**4*h**9*((h-1)*T6-2*y),
}
defects, defect_summaries = {}, {}
for mode, shift in shifts.items():
    poly = sp.Poly(sp.expand(a1-shift**2), *generators)
    weighted_degree = max(sum(a*b for a, b in zip(monomial, weights)) for monomial, coefficient in poly.terms())
    require(weighted_degree == {"linear": 426050, "cubic": 393282, "sixterm": 368449}[mode], "defect weighted degree")
    defects[mode] = poly
    tops = [(list(monomial), int(coefficient)) for monomial, coefficient in poly.terms()
            if sum(a*b for a, b in zip(monomial, weights)) == weighted_degree]
    defect_summaries[mode] = dict(weighted_degree=weighted_degree,
                                 integer_monomial_count=len(poly.terms()), top_terms=tops)

# Direct algebra checks of every announced local rewrite, without graph imports.
nn, sc, tc0, tk, ph, f, hh, s, z, sig, a0, a = sp.symbols("nn sc tc0 tk ph f hh s z sig a0 a")
identities = [
    nn*(sc+(tc0-2)+1)-sc-1 - (nn*(sc+tc0-1)-sc-1),
    (nn*(sc+tc0-1)-sc-1)+1+tk*(ph-1) - (nn*(sc+tc0-1)-sc+tk*(ph-1)),
    (h-1)*f-1 - (h*f-(f+1)),
    s**5 - s**2*(s*s**2),
    (a**2-1)*hh**2+1 - ((a*hh)**2-hh**2+1),
    u**7*xi**4-u**3*E0**4,
    u*xi**2-E0*xi,
    (z**2+sig**2*(a0-a))**2-4*sig**2*a0*z**2
        - ((z**2-sig**2*(a0+a))**2-4*sig**4*a0*a),
]
require(all(sp.expand(identity) == 0 for identity in identities), "announced exact ring identities")

base = read("source/integer10_polar.json")
degree_expected = dict(g=2, cap=233, K=28548, L=4220, r=114189,
                      guard=294382, lucas=458818, Sigma=81922,
                      Theta=81925, halfA=16384, B1=7942, C=1, xi=2)
witnesses = []
for prime, direction in [(1000039, [1]*10), (1000081, list(range(1, 11)))]:
    require(sp.isprime(prime), "independent witness modulus is prime")
    tops = degree_witnesses(base, prime, direction)
    for name, expected in degree_expected.items():
        require(tops[name][0] == expected and tops[name][1] != 0, "nonzero actual source leading witness: " + name)
    values = [tops[name][1] for name in ("halfA", "B1", "C", "xi")] + [direction[7]]
    def eval_weighted_top(poly, degree):
        return sum(int(coefficient) * sp.prod(pow(value, exponent, prime) for value, exponent in zip(values, monomial))
                   for monomial, coefficient in poly.terms()
                   if sum(a*b for a, b in zip(monomial, weights)) == degree) % prime
    defect_coefficients = {}
    shift_coefficients = {}
    for mode, poly in defects.items():
        coefficient = int(eval_weighted_top(poly, defect_summaries[mode]["weighted_degree"]))
        require(coefficient != 0, "actual specialized defect top: " + mode)
        defect_coefficients[mode] = coefficient
        shift_poly = sp.Poly(shifts[mode], *generators)
        require(max(sum(a*b for a, b in zip(monomial, weights))
                    for monomial, coefficient in shift_poly.terms()) == 229409,
                "shift weighted degree")
        coefficient = int(eval_weighted_top(shift_poly, 229409))
        require(coefficient != 0, "actual specialized shift top: " + mode)
        shift_coefficients[mode] = coefficient
    require((tops["lucas"][1]-shift_coefficients["linear"]**2) % prime == 0, "positive-square a1 witness")
    U = 3*tops["cap"][1]*tops["K"][1]*tops["L"][1]*tops["r"][1]*direction[8] % prime
    require((tops["guard"][1]+U**2) % prime == 0, "negative-square a0 witness")
    require(2+233+2*28548 == 57331 < 2*233+2*(28548+4220) == 66002, "strict guard dominance")
    require(66002+2*114189+2 == 294382, "guard degree")
    cross = -4*pow(tops["Sigma"][1], 4, prime)*tops["guard"][1]*tops["lucas"][1] % prime
    require(cross != 0, "nonzero cross term degree witness")
    inner_bounds = {}
    for mode, info in defect_summaries.items():
        bound = max(2*81922+info["weighted_degree"], 2*81922+294382,
                    81922+229409+81925, 2*81925)
        inner_bounds[mode] = bound
        require(bound == {"linear": 589894, "cubic": 557126, "sixterm": 532293}[mode], "inner upper degree")
    require(4*81922+294382+458818 == 1080888 > 2*inner_bounds["sixterm"], "sixterm attains bound")
    output_tops = {"polar": pow(tops["Sigma"][1],4,prime)*tops["lucas"][1]**2 % prime,
                   "linear": pow(tops["Sigma"][1],4,prime)*defect_coefficients["linear"]**2 % prime,
                   "cubic": pow(tops["Sigma"][1],4,prime)*defect_coefficients["cubic"]**2 % prime,
                   "sixterm": cross}
    require(all(output_tops.values()), "nonzero exact output degree witnesses")
    witnesses.append(dict(prime=prime, direction=direction, source_degree_witnesses=tops,
                          defect_leading_coefficients=defect_coefficients,
                          final_leading_coefficients=output_tops, inner_degree_bounds=inner_bounds))

print(json.dumps({"status": "PASS", "release_hash_count": len(hashes),
                  "fixed_leaf_count": len(fixed), "variants": metrics,
                  "direct_integer_ring_identities": len(identities),
                  "weighted_defects": defect_summaries,
                  "extra_actual_coefficient_degree_witnesses": witnesses,
                  "scope": "Exact degree and circuit audit for the supplied fixed short-guard family; not an independent proof of the inherited compiler/Pell/calibration theorems."}, indent=2))
