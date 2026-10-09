"""Checked local Montesinos obstructions in otherwise arbitrary knot PDs.

The imported topology is Nogueira--Salgueiro, arXiv:2110.15645, Theorem 4.9.
This module verifies an actual four-port disk subdiagram, not just a graph
cut or an unchecked fraction.  The initial implementation requires a
connected shadow, no closed tangle components, four distinct cut edges,
and source e=0 with at least two nonintegral finite summands.  A missed
pattern is inconclusive.  It never authorizes an UNKNOT verdict.

An exact occurrence is forced by the image and even rotation of one root
crossing.  Therefore a fixed k-crossing pattern can be searched in O(n*k)
word operations, rather than by general subgraph-isomorphism search.
"""
from __future__ import annotations

from collections import Counter
from functools import lru_cache
from time import monotonic

from .diagram import Diagram, DiagramError
from .rational import build_montesinos_tangle, canonical_source, continued_fraction


class PatternError(ValueError):
    """The source or claimed embedding does not meet the certificate contract."""


def _cycles(permutation):
    seen = bytearray(len(permutation))
    result = []
    for start in range(len(permutation)):
        if seen[start]:
            continue
        cycle, current = [], start
        while not seen[current]:
            seen[current] = 1
            cycle.append(current)
            current = permutation[current]
        result.append(cycle)
    return result


def _template_topology(rows, boundary):
    """Check a connected plane four-port diagram and its two open strands."""
    k = len(rows)
    if not k or len(boundary) != 4 or len(set(boundary)) != 4:
        raise PatternError("the template must have crossings and four distinct ports")
    labels = [label for row in rows for label in row] + list(boundary)
    count = Counter(labels)
    if any(multiplicity != 2 for multiplicity in count.values()):
        raise PatternError("template edge incidence is not two")
    where = [[] for _ in range(max(labels) + 1)]
    for dart, label in enumerate(labels):
        where[label].append(dart)
    alpha = [0] * (4 * k + 4)
    for occurrence in where:
        if occurrence:
            a, b = occurrence
            alpha[a], alpha[b] = b, a

    # Connectivity of the crossing shadow through internal edges.
    reached, pending = {0}, [0]
    while pending:
        crossing = pending.pop()
        for slot in range(4):
            partner = alpha[4 * crossing + slot]
            if partner < 4 * k and partner // 4 not in reached:
                reached.add(partner // 4)
                pending.append(partner // 4)
    if len(reached) != k:
        raise PatternError("the tangle crossing shadow is disconnected")

    sigma = [(4 * (d // 4) + (d + 1) % 4) if d < 4 * k else d
             for d in range(4 * k + 4)]
    faces = _cycles([sigma[alpha[d]] for d in range(4 * k + 4)])
    port_faces = [[d - 4 * k for d in face if d >= 4 * k] for face in faces]
    port_faces = [ports for ports in port_faces if ports]
    # V=k+4, E=2k+2, so a connected spherical rotation system has k faces.
    if len(faces) != k or len(port_faces) != 1 or len(port_faces[0]) != 4:
        raise PatternError("ports must lie on one face of a plane tangle")
    ports = port_faces[0]
    zero = ports.index(0)
    if ports[zero:] + ports[:zero] != [0, 3, 2, 1]:
        raise PatternError("the declared NW,NE,SE,SW port order is inconsistent")

    # Follow strings, rather than the shadow, to rule out closed components.
    parent = list(range(4 * k + 4))

    def find(item):
        while parent[item] != item:
            parent[item] = parent[parent[item]]
            item = parent[item]
        return item

    def join(a, b):
        parent[find(a)] = find(b)

    for d, partner in enumerate(alpha):
        join(d, partner)
    for i in range(k):
        join(4 * i, 4 * i + 2)
        join(4 * i + 1, 4 * i + 3)
    roots = {find(d) for d in range(4 * k + 4)}
    port_counts = Counter(find(4 * k + p) for p in range(4))
    if roots != set(port_counts) or sorted(port_counts.values()) != [2, 2]:
        raise PatternError("the source is not exactly two open strings")
    return tuple(alpha)


@lru_cache(maxsize=64)
def _compile(source):
    e, tangles = source
    if e != 0:
        raise PatternError("local patterns currently require e=0")
    slopes = tuple(continued_fraction(cf) for cf in tangles)
    if len(slopes) < 2 or any(q <= 1 for _, q in slopes):
        raise PatternError("local patterns need at least two nonintegral finite summands")
    if len(slopes) >= 3:
        arithmetic = {"criterion": "three-or-more-nonintegral-summands",
                      "summands": len(slopes)}
    else:
        (p, q), (r, s) = slopes
        residue = (p * s + r * q) % (q * s)
        if residue in (1, q * s - 1):
            raise PatternError("this Montesinos tangle admits an unknot closure")
        arithmetic = {"criterion": "two-summand-congruence-obstruction",
                      "residue": residue, "modulus": q * s}
    template = build_montesinos_tangle(e, tangles)
    alpha = _template_topology(template["pd"], template["boundary"])
    return template, alpha, arithmetic


def _source(certificate, n):
    if not isinstance(certificate, dict) or set(certificate) != {
            "version", "pattern", "crossings", "rotations"}:
        raise PatternError("invalid certificate fields")
    if type(certificate["version"]) is not int or certificate["version"] != 1:
        raise PatternError("unsupported certificate version")
    pattern = certificate["pattern"]
    if not isinstance(pattern, dict) or set(pattern) != {"e", "tangles"}:
        raise PatternError("pattern must contain exactly e and tangles")
    source = canonical_source(pattern["e"], pattern["tangles"])
    crossings = abs(source[0]) + sum(abs(a) for cf in source[1] for a in cf)
    if crossings > n:
        raise PatternError("pattern is larger than the diagram")
    return source


def _check_embedding(diagram, template, alpha, images, rotations, target_alpha=None):
    k, n = len(template["pd"]), diagram.crossings
    if not isinstance(images, (list, tuple)) or not isinstance(rotations, (list, tuple)):
        raise PatternError("crossings and rotations must be arrays")
    if len(images) != k or len(rotations) != k:
        raise PatternError("embedding length does not match the source")
    if any(type(x) is not int or not 0 <= x < n for x in images) or len(set(images)) != k:
        raise PatternError("crossing map must be injective and in range")
    if any(type(r) is not int or r not in (0, 2) for r in rotations):
        raise PatternError("rotations must preserve both cyclic order and the under-pair")
    selected = set(images)
    if target_alpha is None:
        target_alpha = diagram.alpha()
    ports = []
    for i in range(k):
        for j in range(4):
            source_partner = alpha[4 * i + j]
            target_dart = 4 * images[i] + (j + rotations[i]) % 4
            target_partner = target_alpha[target_dart]
            if source_partner < 4 * k:
                other, slot = divmod(source_partner, 4)
                expected = 4 * images[other] + (slot + rotations[other]) % 4
                if target_partner != expected:
                    raise PatternError("an internal edge or crossing slot does not match")
            else:
                if target_partner // 4 in selected:
                    raise PatternError("each of the four ports must be an actual cut edge")
                ports.append((source_partner - 4 * k, target_dart))
    if len(ports) != 4:
        raise PatternError("the occurrence has no four-port boundary")
    return [dart for _, dart in sorted(ports)]


def verify_subtangle_certificate(diagram, certificate):
    """Return rejection evidence only after checking source, topology and map.

    Invalid or inapplicable certificates raise PatternError (or DiagramError
    for an invalid whole PD).  Verification rebuilds the whole PD's validity
    independently of auxiliary provenance.  It does not trust input slopes,
    determinants, statuses, or a claimed boundary disk.
    """
    if not isinstance(diagram, Diagram):
        raise DiagramError("expected a Diagram")
    checked = Diagram.from_pd(diagram.pd)
    source = _source(certificate, checked.crossings)
    template, alpha, arithmetic = _compile(source)
    ports = _check_embedding(checked, template, alpha,
                             certificate["crossings"], certificate["rotations"])
    return {"status": "KNOTTED", "method": "certified-montesinos-subtangle",
            "theorem": "Nogueira-Salgueiro, Theorem 4.9",
            "pattern_crossings": len(template["pd"]),
            "diagram_crossings": checked.crossings,
            "cut_darts": ports, "arithmetic": dict(arithmetic)}


def _forced_embedding(target_alpha, alpha, k, root, root_rotation, stats, check):
    """Propagate one rooted rotation-system embedding through internal edges."""
    images, rotations = [-1] * k, [0] * k
    images[0], rotations[0] = root, root_rotation
    inverse = {root: 0}
    pending = [0]
    while pending:
        if check is not None:
            check()
        i = pending.pop()
        stats["crossings_visited"] += 1
        for j in range(4):
            partner = alpha[4 * i + j]
            if partner >= 4 * k:
                continue
            source_other, source_slot = divmod(partner, 4)
            target_dart = 4 * images[i] + (j + rotations[i]) % 4
            target_partner = target_alpha[target_dart]
            target_other, target_slot = divmod(target_partner, 4)
            rotation = (target_slot - source_slot) % 4
            if rotation not in (0, 2):
                return None
            if images[source_other] >= 0:
                if images[source_other] != target_other or rotations[source_other] != rotation:
                    return None
            else:
                if target_other in inverse:
                    return None
                images[source_other], rotations[source_other] = target_other, rotation
                inverse[target_other] = source_other
                pending.append(source_other)
    return images, rotations


DEFAULT_PATTERNS = (
    ((0, 3), (0, 3)),
    ((0, -3), (0, -3)),
    ((0, 2), (0, 5)),
    ((0, -2), (0, -5)),
    ((0, 3), (0, 4)),
    ((0, -3), (0, -4)),
)


def find_subtangle_obstruction(diagram, patterns=None, *, check=None):
    """Search exact disk occurrences; return (certificate, evidence, stats).

    `patterns` is a sequence of {e:0,tangles:[CF,...]} source records.  The
    default six-pattern catalogue is fixed and small.  No match returns
    (None, None, stats), not a knot verdict.  Pattern discovery for arbitrary
    rational decompositions is a separate, unsolved integration problem.
    """
    if not isinstance(diagram, Diagram):
        raise DiagramError("expected a Diagram")
    diagram = Diagram.from_pd(diagram.pd)
    if check is not None:
        check()
    target_alpha = diagram.alpha()
    if patterns is None:
        patterns = [{"e": 0, "tangles": tangles} for tangles in DEFAULT_PATTERNS]
    stats = {"patterns": 0, "root_trials": 0, "crossings_visited": 0}
    for pattern in patterns:
        if check is not None:
            check()
        if not isinstance(pattern, dict) or set(pattern) != {"e", "tangles"}:
            raise PatternError("pattern must contain exactly e and tangles")
        source = canonical_source(pattern["e"], pattern["tangles"])
        k = abs(source[0]) + sum(abs(a) for cf in source[1] for a in cf)
        if k > diagram.crossings:
            continue
        template, alpha, _ = _compile(source)
        stats["patterns"] += 1
        for root in range(diagram.crossings):
            for rotation in (0, 2):
                stats["root_trials"] += 1
                found = _forced_embedding(target_alpha, alpha, k, root, rotation, stats, check)
                if found is None:
                    continue
                images, rotations = found
                try:
                    _check_embedding(diagram, template, alpha, images, rotations, target_alpha)
                except PatternError:
                    continue
                certificate = {"version": 1,
                               "pattern": {"e": source[0], "tangles": [list(cf) for cf in source[1]]},
                               "crossings": images, "rotations": rotations}
                evidence = verify_subtangle_certificate(diagram, certificate)
                if check is not None:
                    check()
                return certificate, evidence, stats
    if check is not None:
        check()
    return None, None, stats


def recognize_with_subtangles(diagram, *, patterns=None, seconds=None, **options):
    """Opt-in local search followed by the ordinary exact recognizer."""
    from .geometry import ScanLimit
    from .recognize import Result, recognize
    if seconds is not None:
        from math import isfinite
        if type(seconds) not in (int, float) or not isfinite(seconds) or seconds < 0:
            raise ValueError("seconds must be finite and nonnegative, or None")
    start = monotonic()
    deadline = None if seconds is None else start + seconds

    def check():
        if deadline is not None and monotonic() > deadline:
            raise ScanLimit("time budget exhausted during subtangle search")

    try:
        check()
        certificate, evidence, stats = find_subtangle_obstruction(diagram, patterns, check=check)
        check()
    except ScanLimit as exc:
        return Result("UNKNOWN", "resource-limit", diagram.crossings, diagram.crossings,
                      monotonic() - start, {"subtangle_search": str(exc)})
    if certificate is not None:
        return Result("KNOTTED", "montesinos-subtangle", diagram.crossings, diagram.crossings,
                      monotonic() - start,
                      {"certificate": certificate, "verification": evidence, "search": stats})
    remaining = None if deadline is None else max(0.0, deadline - monotonic())
    result = recognize(diagram, seconds=remaining, **options)
    result.seconds = monotonic() - start
    result.evidence["subtangle_search"] = stats
    return result
