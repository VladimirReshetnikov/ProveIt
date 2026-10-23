#!/usr/bin/env python3
"""Regenerate the affine-sheared positive quartic; standard library only.

This verifier parses literal polynomial data.  It never imports or executes
the upstream generator.  Exact sparse arithmetic keeps all four coefficient
ports symbolic, and checks every transformed residual against its parent.
"""
import ast
import collections
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PIN = "8c6eec9d19ef80538c8e61ff6e0180040583446a"
VARS = "J F alpha z f h i o j s w tau eta zeta y gamma N Y P c a X D C2 L F2 V g I Baux Delta".split()
PORTS = "beta K0 MC MF".split()
AFFINE = {"rep": "beta*J", "q": "rep+1", "k": "eta+zeta", "H": "4*a+3", "qF": "q-F", "C": "qF-alpha", "E": "a-Y"}
PAIRS = [
    ("L", "q*q-1"),
    ("N", "q*L"),
    ("X", "w*q"),
    ("Y", "s*(N+q)"),
    ("E", "X*Y"),
    ("c", "k*Y+eta"),
    ("P", "E*(c-eta)"),
    ("tau*tau", "P*(P+k)+1"),
    ("D", "X+a*c+gamma*H"),
    ("Delta", "a*a+H"),
    ("C2", "c*c"),
    ("D*D", "Delta*C2+1"),
    ("k", "j*c-V+1+h*E"),
    ("j*c-V", "qF*N-C*L+(MC+q*MF)*J"),
    ("(K0+w)*C", "F+z*rep"),
    ("F2", "f*f"),
    ("V", "o*f-c"),
    ("g", "y*y-V*V"),
    ("I", "i*C2"),
    ("Baux", "I*I"),
    ("Baux", "Delta*(F2-1)"),
    ("y*y-Baux*g", "1"),
]

def require(condition, message):
    if not condition:
        raise ValueError(message)

def save(name, content):
    (ROOT / name).write_text(json.dumps(content, indent=2) + "\n")

class SparseRing:
    def __init__(self, names):
        self.names = names
        self.zero = (0,) * len(names)

    def constant(self, value):
        return {self.zero: value} if value else {}

    def variable(self, name):
        exponents = list(self.zero)
        exponents[self.names.index(name)] = 1
        return {tuple(exponents): 1}

    def add(self, left, right, sign=1):
        out = dict(left)
        for exponent, coefficient in right.items():
            value = out.get(exponent, 0) + sign * coefficient
            if value:
                out[exponent] = value
            else:
                out.pop(exponent, None)
        return out

    def multiply(self, left, right):
        out = {}
        for e, a in left.items():
            for f, b in right.items():
                g = tuple(x + y for x, y in zip(e, f))
                out[g] = out.get(g, 0) + a*b
        return {e: a for e, a in out.items() if a}

    def power(self, polynomial, exponent):
        out = self.constant(1)
        for _ in range(exponent):
            out = self.multiply(out, polynomial)
        return out

    def parse(self, expression, environment):
        def walk(node):
            if isinstance(node, ast.Constant) and type(node.value) is int:
                return self.constant(node.value)
            if isinstance(node, ast.Name):
                return environment[node.id]
            if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
                return self.add({}, walk(node.operand), -1)
            if isinstance(node, ast.BinOp):
                left = walk(node.left)
                if isinstance(node.op, ast.Pow):
                    require(isinstance(node.right, ast.Constant) and type(node.right.value) is int and 0 <= node.right.value <= 8, "invalid exponent")
                    return self.power(left, node.right.value)
                right = walk(node.right)
                if isinstance(node.op, ast.Add):
                    return self.add(left, right)
                if isinstance(node.op, ast.Sub):
                    return self.add(left, right, -1)
                if isinstance(node.op, ast.Mult):
                    return self.multiply(left, right)
            raise ValueError("unsupported expression: " + ast.dump(node))
        return walk(ast.parse(expression.replace("^", "**"), mode="eval").body)

    def degree(self, polynomial):
        return max((sum(e[:len(VARS)]) for e in polynomial), default=-1)

    def terms(self, polynomial):
        return [{"powers": list(e), "coefficient": a} for e, a in sorted(polynomial.items())]

class Circuit:
    def __init__(self, inputs):
        self.environment = {name: name for name in inputs}
        self.source = []
        self.cache = {}

    def gate(self, operation, left, right):
        if operation in ("+", "*") and str(left) > str(right):
            left, right = right, left
        key = (operation, left, right)
        if key not in self.cache:
            name = "g" + str(len(self.source) + 1)
            self.source.append([name, operation, left, right])
            self.cache[key] = name
        return self.cache[key]

    def parse(self, expression):
        def walk(node):
            if isinstance(node, ast.Constant) and type(node.value) is int:
                return node.value
            if isinstance(node, ast.Name):
                return self.environment[node.id]
            if isinstance(node, ast.BinOp):
                return self.gate({ast.Add: "+", ast.Sub: "-", ast.Mult: "*"}[type(node.op)], walk(node.left), walk(node.right))
            raise ValueError(ast.dump(node))
        return walk(ast.parse(expression, mode="eval").body)

    def ledger(self, outputs):
        live = set(outputs)
        for name, _, left, right in reversed(self.source):
            if name in live:
                live.update((left, right))
        require(all(row[0] in live for row in self.source), "dead gate")
        require(all(name in live for name in VARS+PORTS), "dead input")
        counts = collections.Counter(row[1] for row in self.source)
        return {"operations": len(self.source), "multiplications": counts["*"], "additions_subtractions": counts["+"]+counts["-"], "all_gates_live": True, "all_inputs_live": True}

def main():
    ring = SparseRing(VARS+PORTS)
    env = {name: ring.variable(name) for name in VARS+PORTS}
    for name, expression in AFFINE.items():
        env[name] = ring.parse(expression, env)
    residuals = [ring.add(ring.parse(left, env), ring.parse(right, env), -1) for left, right in PAIRS]
    require(len(VARS) == 31 and len(PAIRS) == 22, "wrong dimensions")
    require(all(ring.degree(r) == 2 for r in residuals), "nonquadratic residual")

    # Exact parent comparison under a simultaneous affine coordinate change.
    parent_path = ROOT / "upstream/quartic31.pinned.json"
    parent = json.loads(parent_path.read_text())
    replacement = dict(env)
    replacement["N"] = ring.parse("N+q", env)
    replacement["E"] = ring.parse("a-Y", env)
    replacement["P"] = ring.parse("P+k", env)
    replacement["z"] = ring.parse("z+1", env)
    old_names = parent["sparse_term_coordinate_order"]
    for index, equation in enumerate(parent["equations"]):
        reconstructed = {}
        for term in equation["terms"]:
            monomial = ring.constant(term["coefficient"])
            for name, exponent in zip(old_names, term["powers"]):
                monomial = ring.multiply(monomial, ring.power(replacement[name], exponent))
            reconstructed = ring.add(reconstructed, monomial)
        require(reconstructed == residuals[index], "parent residual mismatch at " + str(index+1))

    sos = {}
    for residual in residuals:
        sos = ring.add(sos, ring.multiply(residual, residual))
    require(ring.degree(sos) == 4, "not quartic")
    tau4 = list(ring.zero)
    tau4[VARS.index("tau")] = 4
    require(sos.get(tuple(tau4)) == 1, "missing exact degree certificate")
    # At all 31 positive coordinates equal to one, r5 = a-Y-XY = -1.
    # Its square alone proves that the shifted quartic's constant is positive.
    normalized_r5 = {}
    for exponent, coefficient in residuals[4].items():
        key = exponent[len(VARS):]
        normalized_r5[key] = normalized_r5.get(key, 0) + coefficient
    normalized_r5 = {e:c for e,c in normalized_r5.items() if c}
    require(normalized_r5 == {(0,)*len(PORTS): -1}, "normalization failure")

    circuit = Circuit(VARS+PORTS)
    for name, expression in AFFINE.items():
        circuit.environment[name] = circuit.parse(expression)
    comparisons = [[circuit.parse(left), circuit.parse(right)] for left, right in PAIRS]
    system_source = list(circuit.source)
    system_ledger = circuit.ledger([x for pair in comparisons for x in pair])
    # Independently evaluate the literal circuit in the symbolic ring.
    values = {name: ring.variable(name) for name in VARS+PORTS}
    def value(ref):
        return ring.constant(ref) if type(ref) is int else values[ref]
    for name, operation, left, right in circuit.source:
        values[name] = ring.multiply(value(left), value(right)) if operation == "*" else ring.add(value(left), value(right), -1 if operation == "-" else 1)
    for index, (left, right) in enumerate(comparisons):
        require(ring.add(value(left), value(right), -1) == residuals[index], "circuit residual mismatch")
    computed_residuals = [circuit.gate("-", left, right) for left, right in comparisons]
    squares = [circuit.gate("*", residual, residual) for residual in computed_residuals]
    output = squares[0]
    for square in squares[1:]:
        output = circuit.gate("+", output, square)
    polynomial_ledger = circuit.ledger([output])
    require(system_ledger["operations"] == 61, "unexpected system count")
    require(polynomial_ledger["operations"] == 126, "unexpected quartic count")

    metadata = {"name": "quartic31_affine_shears", "domain": "strictly positive integers", "variables": VARS, "constants": PORTS, "fixed_numerals": PORTS, "source_repository_pin": PIN, "coefficient_binding": "../upstream/compiler/binding.json", "formal_status": "Ordinary mathematical equivalence plus exact finite symbolic audit; no new proof-assistant certificate."}
    save("system61.json", dict(metadata, source=system_source, comparisons=comparisons, exact_maximum_degree=2, ledger=system_ledger))
    save("quartic126.json", dict(metadata, source=circuit.source, output=output, exact_degree=4, ledger=polynomial_ledger))
    save("polynomials.json", dict(metadata, affine_abbreviations=AFFINE, equations=[{"number":i+1,"left":p[0],"right":p[1],"residual":"("+p[0]+")-("+p[1]+")","degree":2,"terms":ring.terms(r)} for i,(p,r) in enumerate(zip(PAIRS,residuals))], sparse_term_coordinate_order=VARS+PORTS, quartic_terms=ring.terms(sos)))
    audits = {"status": "PASS", "parent_sha256": hashlib.sha256(parent_path.read_bytes()).hexdigest(), "parent_residuals_compared_exactly": 22, "all_coefficient_ports_symbolic": True, "affine_substitution": {"N_old":"N+q", "E_old":"a-Y", "P_old":"P+k", "z_old":"z+1"}, "residual_degrees": [ring.degree(r) for r in residuals], "quartic_degree": 4, "tau4_coefficient": 1, "normalization_residual5": -1, "quartic_term_count": len(sos), "system_ledger": system_ledger, "quartic_ledger": polynomial_ledger, "boundary": "Polynomial identities and circuit metrics only; source Pell/compiler theorem and the source transport-quotient positivity lemma remain mathematical dependencies."}
    save("CHECKS.json", audits)
    print(json.dumps(audits, indent=2))

if __name__ == "__main__":
    main()
