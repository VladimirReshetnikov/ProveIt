"""Strict, exact helpers for the binary radius-six expanding shuttle.

No producer fixture is imported or changed. Natural-number parameters are exact
built-in ``int`` objects, excluding bool, float, and coercible numeric objects.
Certificate and coordinate inputs are copied before use; returned data is
immutable. Certificate verification checks every de Bruijn edge, not trajectories.
"""
from dataclasses import dataclass

__all__ = ["Certificate", "validate_certificate", "verify_certificate",
           "window_index", "vertex_index", "hit_time", "quartic", "step"]

_WINDOW_ENCODING = (
    "For window w_0...w_12 at coordinates -6...6, index=sum(w_i*2^i)."
)
_VERTEX_ENCODING = (
    "For a 12-bit vertex v_0...v_11, index=sum(v_i*2^i)."
)
_IDENTITY = "f(word)-word[6] = P(word>>1)-P(word & 4095)"
_FIELDS = frozenset(("alphabet", "radius", "encoding",
                     "rule_bits_indexed_by_window", "potential_index_encoding",
                     "potential_by_vertex", "verified_identity",
                     "verified_edges", "verified_vertices"))
_REWRITE = {
    (0, 1): (1, 2),
    (0, 2): (-1, 1),
    (0, 1, 3): (-1, 1, 4),
    (0, 2, 4): (0, 3, 4),
}


def _integer(value, name, *, natural=False):
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact built-in int (not bool or float)")
    if natural and value < 0:
        raise ValueError(f"{name} must be nonnegative")
    return value


def _sequence(value, name, size):
    if type(value) not in (list, tuple):
        raise TypeError(f"{name} must be a list or tuple")
    snapshot = tuple(value)
    if len(snapshot) != size:
        raise ValueError(f"{name} must have exactly {size} entries")
    return snapshot


def _index(bits, size, name):
    bits = _sequence(bits, name, size)
    for bit in bits:
        _integer(bit, name)
        if bit not in (0, 1):
            raise ValueError(f"{name} entries must be 0 or 1")
    return sum(bit << i for i, bit in enumerate(bits))


def window_index(bits):
    """Encode exactly 13 bits; bit i is at coordinate i-6 (little endian)."""
    return _index(bits, 13, "window")


def vertex_index(bits):
    """Encode exactly 12 bits using index = sum(bits[i] * 2**i)."""
    return _index(bits, 12, "vertex")


@dataclass(frozen=True)
class Certificate:
    """Immutable, structurally valid data; construction does not verify edges."""
    table: tuple
    potential: tuple

    def __post_init__(self):
        for name, value, size in (("table", self.table, 8192),
                                  ("potential", self.potential, 4096)):
            if type(value) is not tuple:
                raise TypeError(f"{name} must be an exact tuple")
            if len(value) != size:
                raise ValueError(f"{name} must have exactly {size} entries")
            for entry in value:
                _integer(entry, f"{name} entry")
                if name == "table" and entry not in (0, 1):
                    raise ValueError("table entries must be 0 or 1")


def validate_certificate(certificate):
    """Validate the exact exported JSON schema and return immutable snapshots.

    Input must be a plain dict; alphabet and potential may be lists or tuples.
    Unknown/missing fields and wrong encoding metadata are rejected. Integer
    fields are never coerced. This checks structure; use verify_certificate to
    check all conservation identities. Neither function authenticates a hash or
    proves that a table is the particular shuttle rather than another rule.
    """
    if type(certificate) is not dict:
        raise TypeError("certificate must be a plain dict")
    data = certificate.copy()
    if set(data) != _FIELDS:
        raise ValueError("certificate has missing or unknown fields")
    alphabet = _sequence(data["alphabet"], "alphabet", 2)
    for entry in alphabet:
        _integer(entry, "alphabet entry")
    if alphabet != (0, 1):
        raise ValueError("alphabet must be exactly [0, 1]")
    for name, expected in (("radius", 6), ("verified_edges", 8192),
                           ("verified_vertices", 4096)):
        if _integer(data[name], name, natural=True) != expected:
            raise ValueError(f"{name} must be {expected}")
    for name, expected in (("encoding", _WINDOW_ENCODING),
                           ("potential_index_encoding", _VERTEX_ENCODING),
                           ("verified_identity", _IDENTITY)):
        if type(data[name]) is not str:
            raise TypeError(f"{name} must be a string")
        if data[name] != expected:
            raise ValueError(f"unrecognized {name}")
    bits = data["rule_bits_indexed_by_window"]
    if type(bits) is not str:
        raise TypeError("rule_bits_indexed_by_window must be a string")
    if len(bits) != 8192 or any(bit not in "01" for bit in bits):
        raise ValueError("rule table must contain exactly 8192 ASCII bits")
    potential = _sequence(data["potential_by_vertex"], "potential_by_vertex", 4096)
    for entry in potential:
        _integer(entry, "potential entry")
    return Certificate(tuple(ord(bit) - ord("0") for bit in bits), potential)


def verify_certificate(certificate):
    """Return True iff the validated certificate satisfies all 8192 edges.

    Malformed inputs raise TypeError or ValueError; a failed identity raises
    ValueError identifying the word. Python integer arithmetic is unbounded.
    The potential's additive constant is deliberately not normalized.
    """
    snapshot = validate_certificate(certificate)
    for word, output in enumerate(snapshot.table):
        if output - ((word >> 6) & 1) != (
                snapshot.potential[word >> 1] - snapshot.potential[word & 4095]):
            raise ValueError(f"conservation identity fails at word {word}")
    return True


def hit_time(x, k):
    """Return k**2 + (2*x + 3)*k for natural x,k, with d = 7+x."""
    _integer(x, "x", natural=True)
    _integer(k, "k", natural=True)
    return k * (k + 2 * x + 3)


def quartic(x, t, k):
    """Return [k**2 + (2*x + 3)*k - t]**2 for natural x,t,k."""
    _integer(t, "t", natural=True)
    residual = hit_time(x, k) - t
    return residual * residual


def step(occupied):
    """Return the next finite occupied support as a frozenset of exact ints.

    Accept plain list, tuple, set, or frozenset and snapshot it before use.
    Duplicate coordinates are rejected; negative lattice sites are valid.
    Arbitrary iterators/mappings and nested or coercible inputs are rejected.
    """
    if type(occupied) not in (list, tuple, set, frozenset):
        raise TypeError("occupied must be a list, tuple, set, or frozenset")
    coordinates = tuple(occupied)
    for coordinate in coordinates:
        _integer(coordinate, "coordinate")
    if len(set(coordinates)) != len(coordinates):
        raise ValueError("occupied contains duplicate coordinates")
    components = []
    for coordinate in sorted(coordinates):
        if not components or coordinate - components[-1][-1] > 2:
            components.append([coordinate])
        else:
            components[-1].append(coordinate)
    result = set()
    for component in components:
        origin = component[0]
        normalized = tuple(coordinate - origin for coordinate in component)
        target = {origin + offset for offset in _REWRITE.get(normalized, normalized)}
        if result.intersection(target):
            raise RuntimeError("component outputs overlap")
        result.update(target)
    return frozenset(result)
