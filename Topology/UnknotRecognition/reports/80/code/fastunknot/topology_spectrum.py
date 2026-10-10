"""Recover compact-surface types from base and normal-double histograms.

The input signature is ``(Euler characteristic, number of boundary circles)``.
If ``H`` describes a normal surface and ``C`` describes its normal double in
an orientable ambient 3-manifold, then

    H(v) = O(v) + N(v),       C(v) = 2 O(v) + N(v / 2).

Here O and N count orientable and nonorientable components, respectively,
and N(v / 2) is zero when either coordinate is odd.  The zero signature
requires its own equation: it may represent both tori and Klein bottles.
No list of individual components is expanded.

Histogram arguments are mappings ``{(chi, boundary_circles): count}`` or the
weighted-orbit engine's JSON rows ``{'weight': [chi, b], 'orbits': count}``.
Outputs are canonical JSON rows, sorted by chi, boundary count, and then
orientable before nonorientable.  Exactly one of genus or crosscaps appears.
All integral inputs accept exact Python integers or signed hexadecimal strings;
booleans are rejected.  Callback exceptions propagate, including ValueError.

These routines establish algebraic consistency.  A caller must independently
certify the histograms and their normal-double geometric provenance.
"""

from collections.abc import Mapping
import re


class _InvalidSpectrum(ValueError):
    """An invalid source or purported spectrum, not a callback exception."""


def _integer(value, name, minimum=None):
    if type(value) is int:
        result = value
    elif isinstance(value, str) and re.fullmatch(r"[+-]?0[xX][0-9a-fA-F]+", value):
        result = int(value, 16)
    else:
        raise _InvalidSpectrum(f'{name} must be an exact integer')
    if minimum is not None and result < minimum:
        raise _InvalidSpectrum(f'{name} must be at least {minimum}')
    return result


def _poller(check):
    if check is None:
        return lambda: None
    if not callable(check):
        raise _InvalidSpectrum('check must be callable or None')
    return check


def _histogram(value, poll):
    """Decode a sparse histogram, rejecting repeated list signatures."""
    if isinstance(value, Mapping):
        records = value.items()
    elif isinstance(value, (list, tuple)):
        records = []
        for row in value:
            poll()
            if not isinstance(row, dict) or set(row) != {'weight', 'orbits'}:
                raise _InvalidSpectrum('a weight row requires weight and orbits')
            records.append((row['weight'], row['orbits']))
    else:
        raise _InvalidSpectrum('a histogram must be a mapping or an explicit row list')
    result, seen = {}, set()
    for signature, count in records:
        poll()
        if not isinstance(signature, (tuple, list)) or len(signature) != 2:
            raise _InvalidSpectrum('a signature must contain chi and boundary count')
        chi = _integer(signature[0], 'Euler characteristic')
        boundary = _integer(signature[1], 'boundary count', 0)
        count = _integer(count, 'component multiplicity', 0)
        key = chi, boundary
        if key in seen:
            raise _InvalidSpectrum('a histogram contains a repeated signature')
        seen.add(key)
        if count:
            if chi + boundary > 2:
                raise _InvalidSpectrum('a compact connected surface has chi + b <= 2')
            result[key] = count
    return result


def _row(chi, boundary, orientable, multiplicity):
    defect = 2 - chi - boundary
    answer = dict(chi=chi, boundary_components=boundary,
                  orientable=orientable, multiplicity=multiplicity)
    if orientable:
        if defect < 0 or defect % 2:
            raise _InvalidSpectrum('an orientable surface requires 2 - chi - b even')
        answer['genus'] = defect // 2
    else:
        if defect < 1:
            raise _InvalidSpectrum('a nonorientable surface has at least one crosscap')
        answer['crosscaps'] = defect
    return answer


def _order(key):
    chi, boundary, orientable = key
    return chi, boundary, not orientable


def _rows(counts, poll):
    answer = []
    for (chi, boundary, orientable), multiplicity in sorted(
            counts.items(), key=lambda item: _order(item[0])):
        poll()
        if multiplicity:
            answer.append(_row(chi, boundary, orientable, multiplicity))
    return answer


def _spectrum(value, poll):
    """Validate a canonical spectrum and decode its topological count map."""
    if not isinstance(value, (list, tuple)):
        raise _InvalidSpectrum('a spectrum must be an explicit row list')
    counts, previous = {}, None
    for row in value:
        poll()
        if not isinstance(row, dict) or type(row.get('orientable')) is not bool:
            raise _InvalidSpectrum('each topology row requires Boolean orientability')
        orientable = row['orientable']
        type_field = 'genus' if orientable else 'crosscaps'
        fields = {'chi', 'boundary_components', 'orientable', 'multiplicity', type_field}
        if set(row) != fields:
            raise _InvalidSpectrum('a topology row has missing or unexpected fields')
        chi = _integer(row['chi'], 'Euler characteristic')
        boundary = _integer(row['boundary_components'], 'boundary count', 0)
        multiplicity = _integer(row['multiplicity'], 'component multiplicity', 1)
        type_value = _integer(row[type_field], type_field, 0 if orientable else 1)
        expected = _row(chi, boundary, orientable, multiplicity)
        if type_value != expected[type_field]:
            raise _InvalidSpectrum('genus or crosscaps disagree with chi and boundary count')
        key = chi, boundary, orientable
        order = _order(key)
        if previous is not None and order <= previous:
            raise _InvalidSpectrum('topology rows must have sorted unique types')
        previous = order
        counts[key] = multiplicity
    return counts


def _reconstruct(counts, poll):
    """Forward covering equations, independent of the inversion recurrence."""
    base, double = {}, {}
    for (chi, boundary, orientable), multiplicity in counts.items():
        poll()
        key = chi, boundary
        base[key] = base.get(key, 0) + multiplicity
        if orientable:
            double[key] = double.get(key, 0) + 2 * multiplicity
        else:
            lifted = 2 * chi, 2 * boundary
            double[lifted] = double.get(lifted, 0) + multiplicity
    return base, double


def recover_topology_spectrum(base, double, *, check=None):
    """Return every compact-surface type and its exact binary multiplicity.

    Recovery uses one predecessor lookup per nonzero base signature.  There
    is no loop through the numerical distance between signatures.  With s
    histogram rows, sorting takes O(s log s) comparisons; all remaining
    arithmetic and dictionary work is linear in s, apart from integer costs.
    A missing predecessor has count zero.  Cover-only rows are checked by
    final forward reconstruction rather than silently discarded.
    """
    poll = _poller(check)
    poll()
    original, cover = _histogram(base, poll), _histogram(double, poll)
    nonorientable, counts = {}, {}
    for key in sorted(original, key=lambda v: (abs(v[0]) + v[1], v)):
        poll()
        chi, boundary = key
        total = original[key]
        if key == (0, 0):
            n = 2 * total - cover.get(key, 0)
        else:
            predecessor = (nonorientable.get((chi // 2, boundary // 2), 0)
                           if chi % 2 == 0 and boundary % 2 == 0 else 0)
            numerator = 2 * total + predecessor - cover.get(key, 0)
            if numerator % 2:
                raise _InvalidSpectrum('cover equations require integral component counts')
            n = numerator // 2
        if not 0 <= n <= total:
            raise _InvalidSpectrum('cover equations require 0 <= N(v) <= H(v)')
        nonorientable[key] = n
        if total - n:
            counts[chi, boundary, True] = total - n
        if n:
            counts[chi, boundary, False] = n
    answer = _rows(counts, poll)
    recovered_base, recovered_cover = _reconstruct(counts, poll)
    if recovered_base != original or recovered_cover != cover:
        raise _InvalidSpectrum('the supplied histograms do not obey the cover equations')
    poll()
    return answer


def verify_topology_spectrum(base, double, spectrum, *, check=None):
    """Independently verify rows by reconstructing both complete histograms.

    This function never calls the recovery routine.  It rejects malformed,
    noncanonical, impossible, or incomplete spectra.  The geometric meaning
    of the supplied histograms remains the caller's certification obligation.
    """
    poll = _poller(check)
    try:
        poll()
        original, cover = _histogram(base, poll), _histogram(double, poll)
        counts = _spectrum(spectrum, poll)
        reconstructed = _reconstruct(counts, poll)
        poll()
        return reconstructed == (original, cover)
    except _InvalidSpectrum:
        return False


def scale_core_spectrum(spectrum, divisor, *, vertex_link_disks=0,
                        vertex_link_spheres=0, check=None):
    """Lift a core spectrum under normal scaling and add removed vertex links.

    In an orientable ambient 3-manifold, g parallel sheets of an orientable
    component give g copies.  A nonorientable component gives floor(g/2)
    copies of its orientation double and one central original if g is odd.
    Boundary circles and Euler characteristic both double in that cover.
    Vertex-link discs and spheres are supplied separately as exact counts.
    ``divisor=0`` is allowed and leaves only the supplied vertex links.
    """
    poll = _poller(check)
    poll()
    divisor = _integer(divisor, 'divisor', 0)
    disks = _integer(vertex_link_disks, 'vertex-link disc count', 0)
    spheres = _integer(vertex_link_spheres, 'vertex-link sphere count', 0)
    original = _spectrum(spectrum, poll)
    counts = {}

    def add(key, multiplicity):
        if multiplicity:
            counts[key] = counts.get(key, 0) + multiplicity

    half, odd = divmod(divisor, 2)
    for (chi, boundary, orientable), multiplicity in original.items():
        poll()
        if orientable:
            add((chi, boundary, True), divisor * multiplicity)
        else:
            add((2 * chi, 2 * boundary, True), half * multiplicity)
            add((chi, boundary, False), odd * multiplicity)
    add((1, 1, True), disks)
    add((2, 0, True), spheres)
    result = _rows(counts, poll)
    poll()
    return result


def verify_scaled_spectrum(core, divisor, scaled, *, vertex_link_disks=0,
                           vertex_link_spheres=0, check=None):
    """Check a scaled spectrum by typewise equations, without its producer."""
    poll = _poller(check)
    try:
        poll()
        divisor = _integer(divisor, 'divisor', 0)
        disks = _integer(vertex_link_disks, 'vertex-link disc count', 0)
        spheres = _integer(vertex_link_spheres, 'vertex-link sphere count', 0)
        source, target = _spectrum(core, poll), _spectrum(scaled, poll)
        candidates = set(source) | set(target) | {(1, 1, True), (2, 0, True)}
        candidates.update((2 * chi, 2 * boundary, True)
                          for chi, boundary, orientable in source if not orientable)
        for chi, boundary, orientable in candidates:
            poll()
            if orientable:
                expected = divisor * source.get((chi, boundary, True), 0)
                if chi % 2 == 0 and boundary % 2 == 0:
                    expected += (divisor // 2) * source.get(
                        (chi // 2, boundary // 2, False), 0)
                if (chi, boundary) == (1, 1):
                    expected += disks
                elif (chi, boundary) == (2, 0):
                    expected += spheres
            else:
                expected = (divisor % 2) * source.get((chi, boundary, False), 0)
            if target.get((chi, boundary, orientable), 0) != expected:
                return False
        poll()
        return True
    except _InvalidSpectrum:
        return False
