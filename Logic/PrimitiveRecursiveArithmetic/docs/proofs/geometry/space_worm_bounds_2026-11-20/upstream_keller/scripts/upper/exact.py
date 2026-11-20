"""Exact geometry and untrusted certificate preparation (Python standard library)."""

from fractions import Fraction as Q
import hashlib
import json
from math import lcm
from pathlib import Path

from common import certificate_file, checked_hash, fingerprint


def inputs(directory):
    directory = Path(directory)
    manifest_bytes = (directory / "manifest.json").read_bytes()
    manifest = json.loads(manifest_bytes)
    if type(manifest.get("schema")) is not int or manifest["schema"] != 1:
        raise ValueError("unsupported upper manifest")
    files = manifest.get("files")
    if not isinstance(files, list) or not all(isinstance(n, str) for n in files):
        raise ValueError("invalid upper file list")
    required = ["header.json", "tree.json.gz", *files]
    hashes = manifest.get("sha256")
    if (
        len(set(required)) != len(required)
        or not isinstance(hashes, dict)
        or set(hashes) != set(required)
    ):
        raise ValueError("upper SHA256 map must cover exactly every input file")
    actual = {
        name: checked_hash(certificate_file(directory, name), hashes[name]) for name in required
    }
    header_bytes = (directory / "header.json").read_bytes()
    if hashlib.sha256(header_bytes).hexdigest() != actual["header.json"]:
        raise ValueError("upper header changed while reading")
    header = json.loads(header_bytes)
    if type(header.get("schema")) is not int or header["schema"] != 1:
        raise ValueError("unsupported upper header")
    if type(header.get("complete")) is not bool:
        raise ValueError("upper complete must be a boolean")
    if any(type(header.get(k)) is not int or header[k] < 0 for k in ("leaves", "kR", "kL")):
        raise ValueError("invalid upper counts")
    actual["manifest.json"] = hashlib.sha256(manifest_bytes).hexdigest()
    return fingerprint(actual), header, manifest


T = [Q("-631/58"), Q(-1), Q("7/16"), Q("37/56")]
H = [Q(0), Q(0), Q("130783/250000"), Q("446199/1000000")]
RAYS = [
    [Q("5541045/8027539"), Q("24427652/40137695"), Q(1), Q(0)],
    [Q("47299645/118570699"), Q("502233812/592853495"), Q(0), Q(1)],
]
ZERO = (Q(0), Q(0))


def add(u, v):
    return u[0] + v[0], u[1] + v[1]


def scale(a, u):
    return a * u[0], a * u[1]


def cross(u, v):
    return u[0] * v[1] - u[1] * v[0]


def unit(t):
    return (1 - t * t) / (1 + t * t), 2 * t / (1 + t * t)


NORMALS = list(map(unit, T))


def matrix(spec):
    kind, *args = spec
    if kind == "flush":
        side, flip, mirror = args
        x, y = NORMALS[side]
        mat = ((y, -x), (x, y)) if flip else ((-y, x), (-x, -y))
    else:
        t, mirror = args
        x, y = unit(Q(t))
        mat = ((x, -y), (y, x))
    if mirror:
        mat = ((-mat[0][0], -mat[0][1]), mat[1])
    return mat


def directions(spec):
    a, b = matrix(spec)
    return [(a[0] * x + a[1] * y, b[0] * x + b[1] * y) for x, y in NORMALS]


def sector(u):
    if u[1] == 0:
        return 0 if u[0] > 0 else 2
    return 1 if u[1] > 0 else 3


def angle_lt(u, v):
    a, b = sector(u), sector(v)
    return a < b if a != b else cross(u, v) > 0


class Geometry:
    """Reconstruct rows from exact shape data, never stored force summaries."""

    def __init__(self, specs):
        for spec in specs:
            if spec[0] == "flush":
                if (
                    len(spec) != 4
                    or spec[1] not in range(4)
                    or any(x not in (0, 1) for x in spec[2:])
                ):
                    raise ValueError("invalid flush placement")
            elif spec[0] in ("rot", "vrot"):
                if len(spec) != 3 or spec[2] not in (0, 1):
                    raise ValueError("invalid rotation placement")
                Q(spec[1])
            else:
                raise ValueError("unknown placement type")
        self.specs = specs
        dirs = {u for s in specs if s[0] != "vrot" for u in directions(s)}
        self.right = sorted((u for u in dirs if u[0] > 0), key=lambda u: u[1])
        self.left = sorted((u for u in dirs if u[0] < 0), key=lambda u: -u[1])
        self.kR, self.kL = len(self.right), len(self.left)
        self.normals = [(Q(0), Q(-1)), (Q(0), Q(-1)), (Q(0), Q(1))]
        self.normals += self.right + self.left
        self.n = len(self.normals)
        self.labels = {u: i for i, u in enumerate(self.normals)}
        from functools import cmp_to_key

        self.named = sorted(
            self.labels,
            key=cmp_to_key(lambda u, v: -1 if angle_lt(u, v) else (1 if angle_lt(v, u) else 0)),
        )
        self.erows = [self.escape(s, ray) for s in specs for ray in range(2)]
        self._rows = {}

    def expansion(self, u):
        if u in self.labels:
            return [(u, Q(1))]
        i = next((i for i, v in enumerate(self.named) if angle_lt(u, v)), 0)
        w1, w2 = self.named[i - 1], self.named[i]
        det = cross(w1, w2)
        a, b = cross(u, w2) / det, cross(w1, u) / det
        if a < 0 or b < 0 or add(scale(a, w1), scale(b, w2)) != u:
            raise ValueError("invalid direction expansion")
        return [(w1, a), (w2, b)]

    def escape(self, spec, ray):
        coeffs = []
        ds = directions(spec)
        for i in [0, 1, 2 + ray]:
            parts = self.expansion(ds[i]) if spec[0] == "vrot" else [(ds[i], Q(1))]
            for u, a in parts:
                coeffs.append((self.labels[u], scale(RAYS[ray][i] * a, u)))
        if (sum(v[0] for _, v in coeffs), sum(v[1] for _, v in coeffs)) != ZERO:
            raise ValueError("unbalanced escape row")
        return coeffs, -H[2 + ray]

    def row(self, key):
        if key in self._rows:
            return self._rows[key]
        floor = self.n**2
        if key < floor:
            d, p = divmod(key, self.n)
            if d == p:
                raise ValueError("diagonal support row")
            u = self.normals[d]
            row = [(d, u), (p, scale(-1, u))], Q(0)
        elif key == floor:
            row = [(1, (Q(1), Q(0))), (0, (Q(-1), Q(0)))], Q(0)
        else:
            row = self.erows[key - floor - 1]
        self._rows[key] = row
        return row

    def integer_rows(self, keys):
        rows = [self.row(k) for k in keys]
        den = 1
        for coeffs, b in rows:
            den = lcm(den, b.denominator)
            for _, v in coeffs:
                den = lcm(den, v[0].denominator, v[1].denominator)

        def integer(q):
            return q.numerator * (den // q.denominator)

        return [
            ([(i, integer(v[0]), integer(v[1])) for i, v in coeffs], integer(-b))
            for coeffs, b in rows
        ]

    def valid(self, weights, rows, rect):
        """Fast exact preflight only. Lean recomputes this independently."""
        force = [[0, 0] for _ in self.normals]
        bound = 0
        for weight, (coeffs, b) in zip(weights, rows):
            if weight < 0:
                return False
            if not weight:
                continue
            bound += weight * b
            for i, x, y in coeffs:
                force[i][0] += weight * x
                force[i][1] += weight * y
        if bound <= 0 or sum(v[0] for v in force) or sum(v[1] for v in force):
            return False
        bound2 = bound * bound

        def good(v):
            return v[0] * v[0] + v[1] * v[1] <= bound2

        a = [(0, 0)]
        b = [(0, 0)]
        for v in force[3 + self.kR :]:
            a.append(add(a[-1], v))
        for v in force[3 : 3 + self.kR]:
            b.append(add(b[-1], v))
        lo, hi, qlo, qhi = rect

        def sub(u, v):
            return u[0] - v[0], u[1] - v[1]

        return (
            all(
                good(sub(a[j], a[i]))
                for i in range(qlo, self.kL)
                for j in range(i + 1, self.kL + 1)
            )
            and all(good(add(sub(a[-1], a[j]), force[0])) for j in range(min(qhi, self.kL) + 1))
            and all(good(add(force[1], b[j])) for j in range(lo, self.kR + 1))
            and all(good(sub(b[j], b[i])) for i in range(hi + 1) for j in range(i, hi + 1))
        )
