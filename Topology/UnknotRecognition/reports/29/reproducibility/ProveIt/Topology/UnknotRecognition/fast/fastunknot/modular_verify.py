"""Independent observer arithmetic after full replay of a modular knot claim.

The replay reconstructs the complete ComponentScan prefix over F2. It then
rebuilds each claimed suffix completion with the older ClosureShadow engine,
using integer determinants, and checks the recorded auxiliary-prime residues,
relative quantum shifts, multiplicities and norm witnesses against the exact
integer vectors. It never calls the modular observer, terminal response kernel
or production lattice minimizer.

This is a full prefix replay, not a short standalone NP certificate. The scanner
and its topological interpretation remain trusted program dependencies; they
are not independently formalized here. Optional object and time limits can
terminate replay inconclusively, and such resource exceptions propagate.
"""
from hashlib import sha256
import json
from math import isfinite, isqrt
from time import monotonic

from .component_scan import ComponentScan
from .diagram import Diagram, DiagramError
from .frobenius.subset import homogeneous_degree
from .geometry import ScanLimit
from .shadow_scan import ClosureShadow


class ModularVerificationError(ValueError):
    """A malformed or incorrect modular-observer claim failed replay."""


def _require(condition, message):
    if not condition:
        raise ModularVerificationError(message)


def _integer(value, name, minimum=None):
    _require(type(value) is int, name + " must be an integer")
    _require(minimum is None or value >= minimum, name + " is out of range")
    return value


def _integers(value, name, check, length=None, minimum=None):
    _require(isinstance(value, (list, tuple)), name + " must be a sequence")
    if length is not None:
        _require(len(value) == length, name + " has the wrong length")
    result = []
    for item in value:
        check()
        result.append(_integer(item, name + " entry", minimum))
    return tuple(result)


def _source(pd, check):
    raw = pd.pd if isinstance(pd, Diagram) else pd
    _require(isinstance(raw, (list, tuple)), "source PD must be a sequence")
    rows = []
    for row in raw:
        check()
        rows.append(_integers(row, "source crossing", check, 4))
    check()
    try:
        Diagram.from_pd(rows)
    except DiagramError as error:
        raise ModularVerificationError("invalid classical knot source: " + str(error)) from error
    check()
    return tuple(rows)


def _groups(scan, check):
    """Inventory whole differential components with explicit deadline polls."""
    seen, groups = set(), []
    for root, matching in enumerate(scan.mid):
        check()
        if matching is None or root in seen:
            continue
        group, stack = [], [root]
        seen.add(root)
        while stack:
            check()
            vertex = stack.pop()
            group.append(vertex)
            for row in (scan.out[vertex], scan.inc[vertex]):
                check()
                for other in row:
                    check()
                    if other not in seen:
                        seen.add(other)
                        stack.append(other)
        check()
        group.sort()
        groups.append(tuple(group))
    return tuple(groups)


def _prime_product(primes, check):
    values = _integers(primes, "auxiliary primes", check, minimum=3)
    _require(values, "at least one auxiliary prime is required")
    used, product = set(), 1
    for prime in values:
        check()
        _require(prime < (1 << 31) and prime % 2,
                 "auxiliary primes must be odd and below 2^31")
        _require(prime not in used, "auxiliary primes must be distinct")
        used.add(prime)
        for divisor in range(3, isqrt(prime) + 1, 2):
            check()
            _require(prime % divisor, "auxiliary modulus is composite")
        product *= prime
    return values, product


def _minimum_norm(residues, modulus, exact_sum, check):
    """Independent closed cost formula for the sum-constrained lift minimum.

    In the sign of the necessary sum correction, each oppositely signed
    centered coordinate offers one discount of twice its absolute value.
    All other unit corrections cost exactly modulus. The largest available
    discounts are selected; no production lift construction is imported.
    """
    centered = []
    for residue in residues:
        check()
        centered.append(residue - modulus if 2 * residue > modulus else residue)
    difference = exact_sum - sum(centered)
    _require(difference % modulus == 0, "exact Euler sum contradicts residues")
    steps = difference // modulus
    discounts = []
    for value in centered:
        check()
        if value * steps < 0:
            discounts.append(abs(value))
    check()
    discounts.sort(reverse=True)
    return (sum(abs(x) for x in centered) + modulus * abs(steps)
            - 2 * sum(discounts[:abs(steps)]))


def replay_modular_shadow(pd, result, *, seconds=None, max_objects=None):
    """Return verified replay details; raise on an invalid or limited claim.

    Only raw ``marked-residue-four-modular`` KNOTTED results are accepted.
    Closed-rank and ordinary Euler verdicts use other verification routes.
    A subset of distinct *whole* components suffices if its verified weighted
    lower bound is at least two. Runtime/statistical fields are not certificates
    and are not authenticated by this replay.
    """
    if seconds is not None:
        _require(type(seconds) in (int, float) and seconds >= 0,
                 "seconds must be a nonnegative finite number")
        try:
            seconds = float(seconds)
        except OverflowError as error:
            raise ModularVerificationError("seconds is too large") from error
        _require(isfinite(seconds), "seconds must be finite")
    if max_objects is not None:
        _integer(max_objects, "max_objects", 0)
    deadline = None if seconds is None else monotonic() + seconds

    def check():
        if deadline is not None and monotonic() > deadline:
            raise ScanLimit("time budget exhausted in modular claim replay")

    check()
    _require(isinstance(result, dict), "result must be an object")
    _require(result.get("status") == "KNOTTED", "only KNOTTED claims are accepted")
    _require(result.get("method") == "marked-residue-four-modular",
             "result is not a raw modular marked-observer claim")
    source = _source(pd, check)
    n = len(source)
    _require(_integer(result.get("crossings"), "crossings", 0) == n,
             "crossing count disagrees with the source")
    stage = _integer(result.get("stage"), "stage", 0)
    _require(stage < n, "a marked claim requires a proper prefix and nonempty suffix")
    order = _integers(result.get("order"), "order", check, n, 0)
    _require(set(order) == set(range(n)), "order is not a crossing permutation")
    _require(_integer(result.get("marked_label"), "marked_label") == source[order[-1]][0],
             "marked label disagrees with the surviving source crossing")
    _require(_integer(result.get("reduced_rank_lower_bound_capped"),
                      "reduced rank bound", 0) == 2, "modular decision must claim bound two")
    records = result.get("components")
    _require(isinstance(records, list) and records, "nonempty component records are required")
    observation = result.get("modular_observation")
    fields = {"stage", "modulus", "primes", "threshold_exact", "obstruction",
              "observed_components", "total_components"}
    _require(isinstance(observation, dict) and set(observation) == fields,
             "invalid modular observation fields")
    _require(_integer(observation["stage"], "observation stage", 0) == stage,
             "observation stage differs from replay stage")
    _require(observation["obstruction"] is True and observation["threshold_exact"] is True,
             "a positive observation must identify an exact threshold obstruction")
    primes, modulus = _prime_product(observation["primes"], check)
    _require(_integer(observation["modulus"], "modulus", 3) == modulus,
             "modulus is not the product of the stated primes")
    _require(_integer(observation["observed_components"], "observed components", 1)
             == len(records), "observed component count is incorrect")

    scan = ComponentScan(rank_cap=3, max_objects=max_objects, deadline=deadline,
                         shape_cache=False)
    check()
    if max_objects is not None and scan.live > max_objects:
        raise ScanLimit("object budget exhausted before modular claim replay")
    for i in range(stage):
        check()
        scan.add_crossing(source[order[i]])
    groups = _groups(scan, check)
    _require(_integer(observation["total_components"], "total components", 1) == len(groups),
             "recorded total component count disagrees with replay")
    group_set = set(groups)
    weights = []
    for weight in scan.weights:
        check()
        total = 0
        for count in weight.values():
            check()
            total += _integer(count, "replayed multiplicity", 1)
        _require(1 <= total <= 3, "replayed saturated multiplicity is invalid")
        weights.append(total)
    supplied_weights = _integers(result.get("multiplicities_capped"),
                                 "multiplicities_capped", check, len(weights), 1)
    _require(supplied_weights == tuple(weights), "capped multiplicities disagree with replay")
    exact = ClosureShadow(source, order, max_states=None, max_work=None, deadline=deadline)
    chi = [0] * len(weights)
    object_euler = {}
    for vertex, matching in enumerate(scan.mid):
        check()
        if matching is None:
            continue
        value = exact.evaluate_one(stage, scan.algebra.pairs[matching])
        _require(value % 2 == 0, "replayed completed Euler characteristic is odd")
        object_euler[vertex] = value // 2
        chi[scan.owner[vertex]] += -value if scan.deg[vertex] % 2 else value
    supplied_chi = _integers(result.get("euler_characteristics"),
                             "euler_characteristics", check, len(chi))
    _require(supplied_chi == tuple(chi), "ordinary component Euler values disagree with replay")

    seen, checked_records, verified_bound = set(), [], 0
    record_fields = {"objects", "residues", "minimum_lift", "modulus", "exact_euler",
                     "coordinate_bound", "relative_q", "multiplicity", "norm"}
    for record in records:
        check()
        _require(isinstance(record, dict) and set(record) == record_fields,
                 "invalid component record fields")
        group = _integers(record["objects"], "component objects", check, minimum=0)
        _require(group in group_set, "record must contain one entire replayed component")
        _require(group not in seen, "duplicate component record")
        seen.add(group)
        shifts = _integers(record["relative_q"], "relative_q", check, len(group))
        _require(shifts[0] == 0, "relative quantum shifts have the wrong normalization")
        q = dict(zip(group, shifts))
        owner = scan.owner[group[0]]
        for vertex in group:
            check()
            _require(scan.owner[vertex] == owner, "claimed component mixes independent owners")
            for target, value in scan.out[vertex].items():
                check()
                degree = homogeneous_degree(value, check=check)
                _require(degree is not None and degree >= 0,
                         "replayed differential entry is not homogeneous")
                circles = scan.algebra.basis(scan.mid[vertex], scan.mid[target])[1]
                delta = len(scan.points) // 2 - circles + 2 * degree
                _require(q[target] - q[vertex] == delta,
                         "recorded quantum phase violates a differential edge")
        multiplicity = _integer(record["multiplicity"], "multiplicity", 1)
        _require(multiplicity == weights[owner], "component multiplicity disagrees with replay")
        _require(_integer(record["modulus"], "record modulus", 3) == modulus,
                 "component modulus differs from the validated CRT product")
        residues = _integers(record["residues"], "residues", check, 4, 0)
        _require(all(x < modulus for x in residues), "residues must be canonical")
        lift = _integers(record["minimum_lift"], "minimum_lift", check, 4)
        exact_euler = _integer(record["exact_euler"], "exact_euler")
        norm = _integer(record["norm"], "norm", 0)
        coordinate_bound = _integer(record["coordinate_bound"], "coordinate_bound", 0)
        vector, expected_sum, expected_bound = [0] * 4, 0, 0
        tree_bound = 1 << (n - stage - 1)
        for vertex in group:
            check()
            sign = -1 if scan.deg[vertex] % 2 else 1
            value = exact.evaluate(stage, scan.algebra.pairs[scan.mid[vertex]])
            for j, coefficient in enumerate(value):
                check()
                vector[(j + q[vertex]) % 4] += sign * coefficient
            expected_sum += sign * object_euler[vertex]
            expected_bound += (abs(object_euler[vertex]) + tree_bound) // 2
        _require(exact_euler == expected_sum == sum(vector),
                 "exact Euler sum disagrees with the independent integer vector")
        _require(tuple(x % modulus for x in vector) == residues,
                 "component residues disagree with independent integer determinants")
        _require(coordinate_bound == expected_bound and max(map(abs, vector)) <= expected_bound,
                 "coordinate bound disagrees with the checked suffix bound")
        _require(sum(lift) == exact_euler, "minimum lift has the wrong exact sum")
        _require(tuple(x % modulus for x in lift) == residues,
                 "minimum lift has the wrong residue classes")
        _require(sum(map(abs, lift)) == norm, "claimed norm is not the lift norm")
        _require(_minimum_norm(residues, modulus, exact_euler, check) == norm,
                 "lift does not attain the minimum possible norm")
        exact_norm = sum(map(abs, vector))
        _require(norm <= exact_norm, "claimed lower bound exceeds the independent exact norm")
        verified_bound += multiplicity * norm
        checked_records.append(dict(objects=list(group), exact_vector=vector,
                                    exact_norm=exact_norm, verified_norm=norm,
                                    multiplicity=multiplicity))
    _require(verified_bound >= 2, "verified records do not establish reduced rank above one")
    check()
    raw = json.dumps(source, separators=(",", ":")).encode("ascii")
    return dict(verified=True, status="KNOTTED", stage=stage, crossings=n,
                source_sha256=sha256(raw).hexdigest(), modulus=modulus, primes=list(primes),
                verified_weighted_lower_bound=verified_bound,
                checked_components=len(checked_records), total_components=len(groups),
                components=checked_records, exact_observer_stats=dict(exact.stats),
                scope="Full ComponentScan prefix replay with independent integer observer arithmetic")


def verify_modular_shadow(pd, result, *, seconds=None, max_objects=None):
    """Return claim validity; propagate resource exhaustion and program errors."""
    try:
        replay_modular_shadow(pd, result, seconds=seconds, max_objects=max_objects)
    except ModularVerificationError:
        return False
    return True
