"""Fresh exact/static compiler; no collision selection, trajectory, or old imports.

All arithmetic uses the Python standard library Fraction class.  The constructor
emits a finite word chosen algebraically, rational endpoint rows, and rules.
It never tests which physical event happens next.  Run this file for fixtures.
"""
from fractions import Fraction as F
from math import ceil
import hashlib
import json
from pathlib import Path


ZERO = (F(0), F(0), F(0))


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def mul(c, a):
    return tuple(c * x for x in a)


def mm(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(2))
                       for j in range(2)) for i in range(2))


def shear(axis, t):
    return ((F(1), t), (F(0), F(1))) if axis == "x" else (
        (F(1), F(0)), (t, F(1)))


IDENTITY = ((F(1), F(0)), (F(0), F(1)))


def factor_sl2(matrix):
    """Return chronological (axis,parameter) pairs; keep zero factors."""
    (a, b), (c, d) = matrix
    if a * d - b * c != 1:
        raise ValueError("determinant must be one")
    if c:
        out = [("x", (d - 1) / c), ("y", c), ("x", (a - 1) / c)]
    elif b:
        out = [("y", (a - 1) / b), ("x", b), ("y", (d - 1) / b)]
    else:
        # Rightmost factor first; a is necessarily nonzero, even if a < 0.
        out = [("y", -a), ("x", 1 / a - 1), ("y", F(1)), ("x", a - 1)]
    product = IDENTITY
    for axis, t in out:
        product = mm(shear(axis, t), product)
    if product != matrix:
        raise AssertionError("factorization")
    return out


class Compiler:
    def __init__(self):
        self.positions = {"L": ZERO, "X": (F(1, 3), F(1), F(0)),
                          "Y": (F(2, 3), F(0), F(1)),
                          "D": (F(1), F(0), F(0))}
        self.anchor = "L"
        self.direction = 1
        self.speeds = {f"{z}0": F(0) for z in self.positions}
        self.labels = {z: f"{z}0" for z in self.positions}
        self.events = []
        self.guards = []
        self.phases = []
        self.duration = ZERO
        self.temporary_count = 0
        self.K = self.T = self.H = self.B = 0

    def emit(self, marker, new_direction, new_label=None):
        j = len(self.events)
        before = self.labels[marker]
        after = before if new_label is None else new_label
        self.events.append({"index": j, "marker": marker,
                            "messenger_in_speed": F(self.direction),
                            "messenger_out_speed": F(new_direction),
                            "marker_in": before, "marker_out": after})
        self.direction = new_direction
        self.labels[marker] = after

    def temp(self, speed):
        label = f"T{self.temporary_count}"
        self.temporary_count += 1
        self.speeds[label] = speed
        return label

    def distance(self, marker):
        if self.anchor == "L":
            return self.positions[marker]
        return sub(self.positions["D"], self.positions[marker])

    def set_distance(self, marker, value):
        self.positions[marker] = value if self.anchor == "L" else sub(
            self.positions["D"], value)

    def scale(self, target, u, inner=()):
        if u <= 0:
            raise ValueError("positive scale required")
        start_event = len(self.events)
        outward = 1 if self.anchor == "L" else -1
        if self.direction != outward:
            raise AssertionError("incorrect primitive entry phase")
        z = self.distance(target)
        new = mul(u, z)
        temporary = self.temp(outward * (u - 1) / (u + 1))
        for marker in inner:
            self.emit(marker, outward)
        self.emit(target, -outward, temporary)
        for marker in reversed(inner):
            self.emit(marker, -outward)
        self.emit(self.anchor, outward)
        for marker in inner:
            self.emit(marker, outward)
        self.emit(target, -outward, f"{target}0")
        for marker in reversed(inner):
            self.emit(marker, -outward)
        self.emit(self.anchor, outward)
        self.set_distance(target, new)
        self.duration = add(self.duration, mul(F(2), add(z, new)))
        self.phases.append({"kind": "L", "target": target, "anchor": self.anchor,
                            "parameter": u, "start": start_event,
                            "stop": len(self.events), "from": z, "to": new,
                            "inner_spectators": list(inner)})

    def reflector_homothety(self, target, reflector, v, spectators=()):
        if v <= 0:
            raise ValueError("positive homothety required")
        start_event = len(self.events)
        outward = 1 if self.anchor == "L" else -1
        if self.direction != outward:
            raise AssertionError("incorrect primitive entry phase")
        t, z = self.distance(target), self.distance(reflector)
        end = add(mul(v, t), mul(1 - v, z))
        temporary = self.temp(outward * (1 - v) / (1 + v))
        self.emit(target, outward, temporary)
        for marker in spectators:
            self.emit(marker, outward)
        self.emit(reflector, -outward)
        for marker in reversed(spectators):
            self.emit(marker, -outward)
        self.emit(target, -outward, f"{target}0")
        self.emit(self.anchor, outward)
        self.set_distance(target, end)
        self.duration = add(self.duration, mul(F(2), z))
        self.phases.append({"kind": "H", "target": target, "anchor": self.anchor,
                            "reflector": reflector, "parameter": v,
                            "start": start_event, "stop": len(self.events),
                            "from": t, "to": end,
                            "spectators": list(spectators)})

    def translate(self, target, reflector, e, spectators=()):
        if e >= 1:
            raise ValueError("translation parameter must be below one")
        self.scale(target, 1 / (1 - e))
        self.reflector_homothety(target, reflector, 1 - e, spectators)

    def transfer(self, anchor):
        if anchor == self.anchor:
            return
        start = len(self.events)
        for marker in (("X", "Y") if anchor == "D" else ("Y", "X")):
            self.emit(marker, self.direction)
        self.emit(anchor, -self.direction)
        self.duration = add(self.duration, self.positions["D"])
        self.anchor = anchor
        self.T += 1
        self.phases.append({"kind": "transfer", "anchor": anchor,
                            "start": start, "stop": len(self.events)})

    def guard(self, name, row):
        self.guards.append({"name": name, "row": row})

    def endpoint_guards(self, name, target, neighbor):
        self.guard(name + ":lower", target)
        self.guard(name + ":upper", sub(neighbor, target))

    def shear_block(self, axis, t):
        self.B += 1
        name = f"block{self.B}"
        self.transfer("L" if axis == "x" else "D")
        target, reflector = ("X", "Y") if axis == "x" else ("Y", "X")
        far = "D" if axis == "x" else "L"
        N = max(1, ceil(4 * abs(t)))
        delta = t / N
        self.K += N
        neighbor, diameter = self.distance(reflector), self.positions["D"]
        self.guard(name + ":neighbor_lower", neighbor)
        self.guard(name + ":neighbor_upper", sub(diameter, neighbor))
        self.endpoint_guards(name + ":0", self.distance(target), neighbor)
        for k in range(N):
            self.translate(target, reflector, delta)
            self.endpoint_guards(f"{name}:{2*k+1}", self.distance(target), neighbor)
            self.translate(target, far, -F(2, 3) * delta, (reflector,))
            self.endpoint_guards(f"{name}:{2*k+2}", self.distance(target), neighbor)

    def centered_x_factor(self, q):
        if not F(3, 4) <= q <= F(5, 4):
            raise ValueError("centered factor must be small")
        self.transfer("L")
        self.H += 1
        name = f"dilation{self.H}"
        neighbor, diameter = self.positions["Y"], self.positions["D"]
        self.guard(name + ":neighbor_lower", neighbor)
        self.guard(name + ":neighbor_upper", sub(diameter, neighbor))
        self.endpoint_guards(name + ":start", self.positions["X"], neighbor)
        self.scale("X", q)
        self.endpoint_guards(name + ":scaled", self.positions["X"], neighbor)
        self.translate("X", "D", (1 - q) / 3, ("Y",))
        self.endpoint_guards(name + ":end", self.positions["X"], neighbor)

    def global_scale(self, lam):
        self.transfer("L")
        order = ("X", "Y", "D") if lam < 1 else ("D", "Y", "X")
        for target in order:
            self.scale(target, lam, {"X": (), "Y": ("X",), "D": ("X", "Y")}[target])

    def finish(self, matrix, lam, factors, q_factors):
        self.transfer("L")
        if lam != 1:
            self.global_scale(lam)
        m = len(self.events)
        for j, event in enumerate(self.events):
            self.speeds[f"Q{j}"] = event["messenger_in_speed"]
            event["input"] = [f"Q{j}", event["marker_in"]]
            event["output"] = [f"Q{(j+1)%m}", event["marker_out"]]
        if self.anchor != "L" or self.direction != 1:
            raise AssertionError("return phase")
        if self.labels != {z: f"{z}0" for z in self.positions}:
            raise AssertionError("stationary restoration")
        (a, b), (c, d) = matrix
        expected = {"L": ZERO, "D": (lam, F(0), F(0)),
                    "X": (lam / 3, lam * a, lam * b),
                    "Y": (2 * lam / 3, lam * c, lam * d)}
        if self.positions != expected:
            raise AssertionError((self.positions, expected))
        scaling = int(lam != 1)
        counts = {"shear_blocks": self.B, "micro_shears": self.K,
                  "anchor_transfers": self.T, "centered_dilation_steps": self.H,
                  "events": 18*self.K+3*self.T+14*self.H+24*scaling,
                  "supplied_guards": 4*self.K+4*self.B+8*self.H,
                  "temporary_labels": 4*self.K+3*self.H+3*scaling,
                  "meta_signals": 22*self.K+3*self.T+17*self.H+27*scaling+4,
                  "live_signals": 5}
        if m != counts["events"] or len(self.guards) != counts["supplied_guards"]:
            raise AssertionError("word/guard counts")
        if self.temporary_count != counts["temporary_labels"]:
            raise AssertionError("temporary-label count")
        if len(self.speeds) != counts["meta_signals"]:
            raise AssertionError("meta-signal count")
        if self.T % 2:
            raise AssertionError("anchor closure transfer parity")
        if not all(g["row"][0] > 0 for g in self.guards):
            raise AssertionError("center is not strictly inside every guard")
        if not all(abs(speed) < 1 for name, speed in self.speeds.items()
                   if not name.startswith("Q")):
            raise AssertionError("marker speed range")
        for j, event in enumerate(self.events):
            if event["messenger_out_speed"] != self.speeds[f"Q{(j+1)%m}"]:
                raise AssertionError("messenger phase speed mismatch")
            if self.speeds[event["input"][0]] == self.speeds[event["input"][1]]:
                raise AssertionError("co-moving incoming pair")
            if self.speeds[event["output"][0]] == self.speeds[event["output"][1]]:
                raise AssertionError("co-moving outgoing pair")
        return {"matrix": matrix, "lambda": lam, "chronological_shears": factors,
                "centered_x_factors": q_factors, "counts": counts,
                "return_marker_rows": self.positions, "duration_row": self.duration,
                "guard_rows": self.guards, "primitive_phases": self.phases,
                "speeds": self.speeds, "binary_word": self.events,
                "completion": "Identity on every other collision input set with pairwise distinct speeds."}


def construct(matrix, lam=F(1)):
    matrix = tuple(tuple(F(x) for x in row) for row in matrix)
    if len(matrix) != 2 or any(len(row) != 2 for row in matrix):
        raise ValueError("2x2 matrix required")
    lam = F(lam)
    if lam <= 0:
        raise ValueError("positive global scale required")
    (a, b), (c, d) = matrix
    q = a * d - b * c
    if q <= 0:
        raise ValueError("positive determinant required")
    normalized = ((a / q, b / q), (c, d))
    factors = factor_sl2(normalized)
    compiler = Compiler()
    for axis, t in factors:
        compiler.shear_block(axis, t)
    compiler.transfer("L")
    q_factors = []
    if q != 1:
        H = max(1, ceil(4 * abs(q - 1) / min(F(1), q)))
        previous = F(1)
        for j in range(1, H + 1):
            current = 1 + F(j, H) * (q - 1)
            factor = current / previous
            q_factors.append(factor)
            compiler.centered_x_factor(factor)
            previous = current
        if previous != q:
            raise AssertionError("dilation telescoping")
    return compiler.finish(matrix, lam, factors, q_factors)


def serializable(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {key: serializable(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [serializable(item) for item in value]
    return value


def fixtures():
    # Includes all pivot branches, either shear sign, finite and infinite
    # elliptic order, Jordan/unit/stable/unstable modes, and nonsquare det.
    cases = {
        "identity": ((1, 0), (0, 1)),
        "negative_identity": ((-1, 0), (0, -1)),
        "diagonal_hyperbolic": ((2, 0), (0, F(1, 2))),
        "negative_diagonal": ((-2, 0), (0, F(-1, 2))),
        "upper_shear": ((1, 3), (0, 1)),
        "lower_shear": ((1, 0), (-3, 1)),
        "upper_nonunit_pivot": ((2, -3), (0, F(1, 2))),
        "zero_diagonal": ((0, -1), (1, 0)),
        "zero_a_pivot": ((0, -2), (F(1, 2), 3)),
        "zero_d_pivot": ((3, -2), (F(1, 2), 0)),
        "rotation_345": ((F(3, 5), F(-4, 5)), (F(4, 5), F(3, 5))),
        "elliptic_conjugate": ((F(3, 5), F(-8, 5)), (F(2, 5), F(3, 5))),
        "trace_one_finite": ((0, -1), (1, 1)),
        "trace_minus_one_finite": ((0, -1), (1, -1)),
        "irrational_hyperbolic": ((2, 1), (1, 1)),
        "negative_jordan": ((-1, 1), (0, -1)),
        "det_two": ((2, 1), (0, 1)),
        "det_three_halves": ((F(3, 2), -2), (0, 1)),
        "scalar_half": ((F(1, 2), 0), (0, F(1, 2))),
        "scalar_two": ((2, 0), (0, 2)),
        "unit_contracting": ((1, 2), (0, F(1, 2))),
        "negative_unit_contracting": ((-1, 2), (0, F(-1, 2))),
        "stable_complex": ((F(1, 4), F(-1, 2)), (F(1, 2), F(1, 4))),
        "unstable_complex": ((1, -2), (2, 1)),
        "mixed_hyperbolic": ((3, 1), (1, 1)),
    }
    outdir = Path(__file__).resolve().parent / "evidence"
    outdir.mkdir(exist_ok=True)
    summary = []
    for name, matrix in cases.items():
        for lam in (F(1), F(1, 2), F(2)):
            data = construct(matrix, lam)
            encoded = (json.dumps(serializable(data), indent=2, sort_keys=True) + "\n").encode()
            filename = f"{name}_lambda_{str(lam).replace('/', '_')}.json"
            # Full physical word for all fixtures, no actual trajectory.
            (outdir / filename).write_bytes(encoded)
            summary.append({"name": name, "lambda": str(lam), "file": filename,
                            "sha256": hashlib.sha256(encoded).hexdigest(),
                            "counts": data["counts"],
                            "center_duration": str(data["duration_row"][0])})
    report = {"status": "passed", "fixtures": len(summary),
              "checks": ["all three SL2 pivot branches", "centered dilation telescoping",
                         "center strict guard positivity", "exact endpoint return",
                         "all word/guard/label counts", "stationary-marker restoration",
                         "messenger entry/exit speed continuity including wraparound",
                         "binary distinct incoming/outgoing speeds", "even transfer closure"],
              "not_checked": ["physical simulation", "proof-assistant certification",
                              "arithmetic certificates", "global determinant-negative obstruction"],
              "results": summary}
    (outdir / "summary.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "passed", "fixtures": len(summary),
                      "summary": str(outdir / "summary.json")}, sort_keys=True))


if __name__ == "__main__":
    fixtures()
