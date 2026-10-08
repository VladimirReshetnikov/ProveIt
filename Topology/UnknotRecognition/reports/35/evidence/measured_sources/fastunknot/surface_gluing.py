"""Glue complete boundary covers using exact binary dihedral sheet maps.

Each piece is a canonical bordered surface as in ``surface_cover``.  Boundary
directions use a local orientation at the basepoint transported along the
canonical boundary whisker.  A seam carries a degree +/-1 boundary map and a
fibre bijection x -> sign*x + shift.  The seam is accepted only when the
boundary monodromies intertwine.  No sheet, component, or boundary cycle is
expanded; closed output surfaces are permitted.

This is a checked surface-cover assembly operation, not a knot recognizer,
normal-surface extractor, or verifier of an embedding in a 3-manifold.
"""

from __future__ import annotations

from collections import deque
from copy import deepcopy
from math import gcd

from .integer_codec import encoded_integer
from .surface_cover import (
    _cycles_for_boundary, _fixed_residues, _group_data, _integer,
    component_key as _component_key, compose, evaluate_word, inverse, parse_input,
)


def _poll(check):
    if check is not None:
        check()


def _map_equal(left, right, sheets):
    """Equality of permutations, including coincident formal signs at W<=2."""
    return ((left[0] - right[0]) % sheets == 0
            and (left[1] - right[1]) % sheets == 0)


def _affine(raw, sheets, name):
    if not isinstance(raw, dict) or set(raw) != {'sign', 'shift'}:
        raise ValueError(f'{name} requires sign and shift')
    sign = _integer(raw['sign'], f'{name}.sign')
    if sign not in (-1, 1):
        raise ValueError(f'{name}.sign must equal +1 or -1')
    return sign, _integer(raw['shift'], f'{name}.shift') % sheets


def _record(affine):
    return dict(sign=affine[0], shift=affine[1])


def _endpoint(raw, pieces, name):
    if not isinstance(raw, (list, tuple)) or len(raw) != 2:
        raise ValueError(f'{name} must be [piece, boundary]')
    piece = _integer(raw[0], f'{name}.piece', 0)
    boundary = _integer(raw[1], f'{name}.boundary', 0)
    if piece >= len(pieces) or boundary >= len(pieces[piece]['boundaries']):
        raise ValueError(f'{name} references a nonexistent boundary')
    return piece, boundary


def _parse(raw, check=None):
    if check is not None and not callable(check):
        raise ValueError('check must be callable or None')
    _poll(check)
    if not isinstance(raw, dict) or set(raw) != {'sheets', 'pieces', 'seams'}:
        raise ValueError('input requires exactly sheets, pieces and seams')
    sheets = _integer(raw['sheets'], 'sheets', 1)
    if not isinstance(raw['pieces'], list) or not raw['pieces']:
        raise ValueError('pieces must be a nonempty list')
    pieces, normalized_pieces = [], []
    for index, piece in enumerate(raw['pieces']):
        _poll(check)
        if not isinstance(piece, dict) or set(piece) != {'surface', 'monodromy'}:
            raise ValueError(f'pieces[{index}] requires surface and monodromy')
        n, labels, character, words, chi, maps = parse_input(
            {**piece, 'sheets': sheets}, check=check)
        assert n == sheets
        boundaries = [evaluate_word(word, maps, sheets, check=check) for word in words]
        surface = dict(orientable=piece['surface']['orientable'],
                       genus=encoded_integer(piece['surface']['genus']),
                       boundary_components=len(words))
        pieces.append(dict(surface=surface, labels=labels, character=character,
                           words=words, chi=chi, maps=maps, boundaries=boundaries))
        normalized_pieces.append(dict(surface=surface, monodromy=[_record(m) for m in maps]))
    if not isinstance(raw['seams'], list):
        raise ValueError('seams must be a list')
    seams, normalized_seams, used = [], [], {}
    for index, seam in enumerate(raw['seams']):
        _poll(check)
        if not isinstance(seam, dict) or set(seam) != {'left', 'right', 'direction', 'map'}:
            raise ValueError(f'seams[{index}] requires left, right, direction and map')
        left = _endpoint(seam['left'], pieces, 'seam.left')
        right = _endpoint(seam['right'], pieces, 'seam.right')
        if left == right or left in used or right in used:
            raise ValueError('each boundary can occur in at most one seam')
        direction = _integer(seam['direction'], 'seam.direction')
        if direction not in (-1, 1):
            raise ValueError('seam.direction must equal +1 or -1')
        affine = _affine(seam['map'], sheets, 'seam.map')
        bl = pieces[left[0]]['boundaries'][left[1]]
        br = pieces[right[0]]['boundaries'][right[1]]
        target = br if direction == 1 else inverse(br, sheets)
        if not _map_equal(compose(affine, bl, sheets),
                          compose(target, affine, sheets), sheets):
            raise ValueError(f'seam {index} does not intertwine its boundary monodromies')
        used[left], used[right] = (index, False), (index, True)
        seams.append(dict(left=left, right=right, direction=direction, affine=affine))
        normalized_seams.append(dict(left=list(left), right=list(right), direction=direction,
                                     map=_record(affine)))
    normalized = dict(sheets=sheets, pieces=normalized_pieces, seams=normalized_seams)
    _poll(check)
    return sheets, pieces, seams, used, normalized


def _forest(sheets, pieces, seams, check):
    adjacency = [[] for _ in pieces]
    for edge, seam in enumerate(seams):
        _poll(check)
        u, v = seam['left'][0], seam['right'][0]
        adjacency[u].append((v, edge, False))
        adjacency[v].append((u, edge, True))
    roots = [-1] * len(pieces)
    gauges, parities = [None] * len(pieces), [0] * len(pieces)
    records, tree_edges = [None] * len(pieces), set()
    groups = []
    for root in range(len(pieces)):
        _poll(check)
        if roots[root] != -1:
            continue
        roots[root], gauges[root] = root, (1, 0)
        records[root] = dict(piece=root, root=root, parent=None, seam=None, reverse=False,
                             map=_record((1, 0)), orientation_bit=0)
        queue, group = deque([root]), []
        while queue:
            _poll(check)
            u = queue.popleft()
            group.append(u)
            for v, edge, reverse_edge in adjacency[u]:
                _poll(check)
                if roots[v] != -1:
                    continue
                seam = seams[edge]
                step = inverse(seam['affine'], sheets) if reverse_edge else seam['affine']
                roots[v] = root
                gauges[v] = compose(step, gauges[u], sheets)
                parities[v] = parities[u] ^ int(seam['direction'] == 1)
                records[v] = dict(piece=v, root=root, parent=u, seam=edge,
                                 reverse=reverse_edge, map=_record(gauges[v]),
                                 orientation_bit=parities[v])
                tree_edges.add(edge)
                queue.append(v)
        groups.append(sorted(group))
    return roots, gauges, parities, groups, tree_edges, records


def verify_gauge_certificate(raw, certificate, *, check=None):
    """Independently check tree transports; no producer forest or gcd classifier.

    This checks the stated spanning-forest and transport data against a freshly
    validated gluing presentation.  It does not accept serialized genus or
    component claims as a topology certificate.  JSON hexadecimal integers are
    accepted in exactly the specified integer fields.  Cancellation propagates.
    """
    sheets, pieces, seams, _, _ = _parse(raw, check)
    if not isinstance(certificate, list) or len(certificate) != len(pieces):
        return False
    decoded = []
    try:
        for index, item in enumerate(certificate):
            _poll(check)
            if not isinstance(item, dict) or set(item) != {
                'piece', 'root', 'parent', 'seam', 'reverse', 'map', 'orientation_bit'
            }:
                return False
            piece = _integer(item['piece'], 'certificate.piece', 0)
            root = _integer(item['root'], 'certificate.root', 0)
            bit = _integer(item['orientation_bit'], 'certificate.orientation_bit', 0)
            if piece != index or root >= len(pieces) or bit not in (0, 1):
                return False
            if type(item['reverse']) is not bool:
                return False
            affine = _affine(item['map'], sheets, 'certificate.map')
            parent = item['parent']
            edge = item['seam']
            if parent is not None:
                parent = _integer(parent, 'certificate.parent', 0)
                edge = _integer(edge, 'certificate.seam', 0)
                if parent >= len(pieces) or edge >= len(seams):
                    return False
            elif edge is not None:
                return False
            decoded.append((root, parent, edge, item['reverse'], affine, bit))
    except (ValueError, TypeError):
        return False
    # Each chain is checked once, so long trees do not make verification quadratic.
    settled, active = set(), set()
    for vertex in range(len(pieces)):
        trail, here = [], vertex
        while here not in settled:
            _poll(check)
            if here in active:
                return False
            active.add(here)
            trail.append(here)
            root, parent, edge, reverse_edge, affine, bit = decoded[here]
            if parent is None:
                if root != here or edge is not None or reverse_edge or bit:
                    return False
                if not _map_equal(affine, (1, 0), sheets):
                    return False
                break
            pr, _, _, _, pg, pb = decoded[parent]
            seam = seams[edge]
            source = seam['right'][0] if reverse_edge else seam['left'][0]
            target = seam['left'][0] if reverse_edge else seam['right'][0]
            if (source, target) != (parent, here) or pr != root:
                return False
            step = inverse(seam['affine'], sheets) if reverse_edge else seam['affine']
            if not _map_equal(affine, compose(step, pg, sheets), sheets):
                return False
            if bit != (pb ^ int(seam['direction'] == 1)):
                return False
            here = parent
        for here in trail:
            settled.add(here)
            active.remove(here)
    for seam in seams:
        _poll(check)
        if decoded[seam['left'][0]][0] != decoded[seam['right'][0]][0]:
            return False
    return True


def _classify_action(sheets, maps, character, chi, boundary_maps, check):
    """Existing dihedral orbit arithmetic, now with checked sewn peripherals.

    A general action plus invented Euler data would not define a surface.
    This private entry is called only after complete boundary gluing has
    constructed that surface and verified its covering relations.
    """
    divisor, degree, reference, consistent, tau = _group_data(
        sheets, maps, character, check)
    if reference is None:
        descriptors, fixed = [('single-residues', None, divisor)], []
    else:
        fixed = _fixed_residues(divisor, reference[0])
        count = (divisor - len(fixed)) // 2
        descriptors = [('paired-residues', None, count)] if count else []
        descriptors.extend(('fixed-residue', residue, 1) for residue in fixed)
    families = []
    for kind, residue, multiplicity in descriptors:
        _poll(check)
        cover_degree = degree * (2 if kind == 'paired-residues' else 1)
        orientable = consistent
        if orientable and kind == 'fixed-residue':
            shift, bit = reference
            orientable = (bit + ((2 * residue - shift) // divisor) * tau) % 2 == 0
        profiles = []
        for affine in boundary_maps:
            _poll(check)
            profiles.append(_cycles_for_boundary(kind, residue, divisor, degree, affine))
        boundaries = sum(item['multiplicity'] for profile in profiles for item in profile)
        euler = cover_degree * chi
        twice_or_crosscap_genus = 2 - boundaries - euler
        if orientable:
            if twice_or_crosscap_genus < 0 or twice_or_crosscap_genus % 2:
                raise ArithmeticError('assembled orientable cover has invalid Euler data')
            genus = twice_or_crosscap_genus // 2
        else:
            if twice_or_crosscap_genus < 1:
                raise ArithmeticError('assembled nonorientable cover has invalid Euler data')
            genus = twice_or_crosscap_genus
        family = dict(family=kind, multiplicity=multiplicity, cover_degree=cover_degree,
                      orientable=orientable, genus=genus,
                      genus_convention='handles' if orientable else 'crosscaps',
                      boundary_components=boundaries, euler_characteristic=euler,
                      boundary_lifts=profiles)
        if residue is not None:
            family['residue'] = residue
            key = (residue,)
        elif reference is None:
            key = (0,)
        else:
            seed = next(r for r in range(min(divisor, 3)) if r not in fixed)
            key = tuple(sorted((seed, (reference[0] - seed) % divisor)))
        family['representative_component_key'] = key
        families.append(family)
    generic = any(f['family'] == 'paired-residues' for f in families)
    for family in families:
        if reference is None or family['family'] == 'paired-residues':
            family['type_id'] = 0
        else:
            exception = 0 if degree % 2 else fixed.index(family['residue'])
            family['type_id'] = int(generic) + exception
    if sum(f['multiplicity'] * f['cover_degree'] for f in families) != sheets:
        raise ArithmeticError('assembled component degrees do not sum to sheet count')
    return dict(sheets=sheets, translation_divisor=divisor,
                translation_orbit_size=degree,
                reference_reflection=None if reference is None else dict(
                    shift=reference[0], orientation_bit=reference[1]),
                translation_orientation_character=dict(
                    well_defined=consistent, value_on_divisor=tau if consistent else None),
                fixed_residues=fixed, component_count=sum(f['multiplicity'] for f in families),
                cover_isomorphism_type_count=len({f['type_id'] for f in families}),
                generator_monodromy=[_record(m) for m in maps],
                orientation_character=list(character), base_euler_characteristic=chi,
                boundary_monodromy=[_record(m) for m in boundary_maps], families=families)


def _freeze(value):
    if isinstance(value, dict):
        return tuple((key, _freeze(item)) for key, item in sorted(value.items()))
    if isinstance(value, list):
        return tuple(_freeze(item) for item in value)
    return value


class GluedCoverIndex:
    """Validated assembly, compressed topology, provenance and marking queries.

    All endpoints are zero based.  A point ``(piece, sheet)`` is over that
    piece's fixed basepoint.  Comparing marked signatures means isomorphism
    over the identity of this fixed sewn base; the piece of every mark matters.
    Serial summaries are output records, never accepted as trusted topology.
    """

    def __init__(self, raw, *, check=None):
        if check is not None and not callable(check):
            raise ValueError('check must be callable or None')
        sheets, pieces, seams, used, normalized = _parse(raw, check)
        roots, gauges, parity, groups, tree_edges, certificate = _forest(
            sheets, pieces, seams, check)
        self._check, self._sheets, self._pieces = check, sheets, pieces
        self._seams, self._used, self._normalized = seams, used, normalized
        self._roots, self._gauges, self._parity = roots, gauges, parity
        self._certificate = certificate
        self._model = _freeze(normalized)
        self._results = {}
        self._open_indices = {}
        cycle_edges = {group[0]: [] for group in groups}
        for edge, seam in enumerate(seams):
            _poll(check)
            if edge not in tree_edges:
                cycle_edges[roots[seam['left'][0]]].append(edge)
        for group in groups:
            _poll(check)
            root = group[0]
            maps, character, generators, peripherals, ports = [], [], [], [], []
            for vertex in group:
                _poll(check)
                piece, gauge = pieces[vertex], gauges[vertex]
                back = inverse(gauge, sheets)
                for index, (affine, bit) in enumerate(zip(piece['maps'], piece['character'])):
                    _poll(check)
                    maps.append(compose(back, compose(affine, gauge, sheets), sheets))
                    character.append(bit)
                    generators.append(dict(kind='piece', piece=vertex, generator=index,
                                           label=piece['labels'][index]))
                for boundary, affine in enumerate(piece['boundaries']):
                    _poll(check)
                    if (vertex, boundary) not in used:
                        self._open_indices[vertex, boundary] = len(ports)
                        ports.append([vertex, boundary])
                        peripherals.append(compose(back, compose(affine, gauge, sheets), sheets))
            for edge in cycle_edges[root]:
                _poll(check)
                seam = seams[edge]
                u, v = seam['left'][0], seam['right'][0]
                maps.append(compose(inverse(gauges[v], sheets),
                                    compose(seam['affine'], gauges[u], sheets), sheets))
                character.append(parity[u] ^ int(seam['direction'] == 1) ^ parity[v])
                generators.append(dict(kind='seam', seam=edge))
            chi = sum(pieces[vertex]['chi'] for vertex in group)
            orientable = not any(character)
            numerator = 2 - len(ports) - chi
            if (orientable and (numerator < 0 or numerator % 2)) or (
                not orientable and numerator < 1
            ):
                raise ArithmeticError('sewn base has invalid Euler data')
            result = _classify_action(sheets, maps, character, chi, peripherals, check)
            result.update(root_piece=root, pieces=list(group), generators=generators,
                          remaining_boundaries=ports,
                          base_surface=dict(orientable=orientable,
                                            genus=numerator // 2 if orientable else numerator,
                                            boundary_components=len(ports),
                                            euler_characteristic=chi))
            self._results[root] = result
        _poll(check)

    @property
    def summary(self):
        _poll(self._check)
        result = dict(input_model='whole-boundary-dihedral-cover-gluing',
                      sheets=self._sheets, normalized_input=self._normalized,
                      gauge_certificate=self._certificate,
                      base_component_count=len(self._results),
                      component_count=sum(r['component_count'] for r in self._results.values()),
                      base_components=list(self._results.values()))
        result = deepcopy(result)
        _poll(self._check)
        return result

    @property
    def gauge_certificate(self):
        _poll(self._check)
        result = deepcopy(self._certificate)
        _poll(self._check)
        return result

    def with_seams(self, additional, *, check=None):
        """Return a checked extension, preserving all piece and sheet coordinates.

        Existing seams and the original index remain unchanged.  The complete
        assembly is recomputed; this promises polynomial bit cost per state,
        not an incremental or amortized running-time bound across many states.
        The prepared index's callback is retained unless another is supplied.
        """
        active_check = self._check if check is None else check
        if active_check is not None and not callable(active_check):
            raise ValueError('check must be callable or None')
        _poll(active_check)
        if not isinstance(additional, list):
            raise ValueError('additional seams must be a list')
        raw = deepcopy(self._normalized)
        raw['seams'].extend(deepcopy(additional))
        _poll(active_check)
        return GluedCoverIndex(raw, check=active_check)

    def _point(self, raw):
        if not isinstance(raw, (tuple, list)) or len(raw) != 2:
            raise ValueError('point must be [piece, sheet]')
        piece = _integer(raw[0], 'point.piece', 0)
        sheet = _integer(raw[1], 'point.sheet', 0)
        if piece >= len(self._pieces) or sheet >= self._sheets:
            raise ValueError('point is outside the covering presentation')
        return piece, sheet

    def to_root(self, piece, sheet):
        """Tree-whisker transport to the connected base component's root fibre."""
        _poll(self._check)
        piece, sheet = self._point((piece, sheet))
        sign, shift = inverse(self._gauges[piece], self._sheets)
        return self._roots[piece], (sign * sheet + shift) % self._sheets

    def component_key(self, piece, sheet):
        root, root_sheet = self.to_root(piece, sheet)
        return root, _component_key(self._results[root], root_sheet)

    def _family(self, root, key):
        for family in self._results[root]['families']:
            if family['family'] == 'fixed-residue':
                if key == (family['residue'],):
                    return family
            elif len(key) == (2 if family['family'] == 'paired-residues' else 1):
                return family
        raise ArithmeticError('component is absent from assembled families')

    def component_family(self, piece, sheet):
        root, key = self.component_key(piece, sheet)
        result = deepcopy(self._family(root, key))
        _poll(self._check)
        return result

    def transport_across_seam(self, seam, sheet, *, reverse=False):
        """Transport a boundary reference fibre point across a specified seam."""
        _poll(self._check)
        seam = _integer(seam, 'seam', 0)
        sheet = _integer(sheet, 'sheet', 0)
        if seam >= len(self._seams) or sheet >= self._sheets or type(reverse) is not bool:
            raise ValueError('invalid seam transport query')
        record = self._seams[seam]
        affine = inverse(record['affine'], self._sheets) if reverse else record['affine']
        target = record['left'] if reverse else record['right']
        return dict(port=list(target), sheet=(affine[0] * sheet + affine[1]) % self._sheets)

    def _cycle(self, piece, boundary, sheet):
        sign, shift = self._pieces[piece]['boundaries'][boundary]
        if sign == 1:
            divisor = gcd(self._sheets, shift)
            return (sheet % divisor,), self._sheets // divisor
        partner = (shift - sheet) % self._sheets
        key = (sheet,) if partner == sheet else tuple(sorted((sheet, partner)))
        return key, len(key)

    def port_lift_key(self, piece, boundary, sheet):
        """Identify a surviving boundary or an internal seam circle exactly.

        A seam key is canonicalized to the seam's recorded left port.  Thus
        queries from its two sides agree after the prescribed sheet transport.
        Keys retain the original port/seam identifiers and never merge merely
        homeomorphic components or circles.
        """
        _poll(self._check)
        piece, sheet = self._point((piece, sheet))
        boundary = _integer(boundary, 'boundary', 0)
        if boundary >= len(self._pieces[piece]['boundaries']):
            raise ValueError('boundary is out of range')
        component = self.component_key(piece, sheet)
        cycle, degree = self._cycle(piece, boundary, sheet)
        port = (piece, boundary)
        if port not in self._used:
            return dict(kind='boundary', key=('boundary', port, cycle),
                        covering_degree=degree, component_key=component,
                        source_port=list(port))
        edge, reverse_edge = self._used[port]
        seam = self._seams[edge]
        left_sheet = sheet
        if reverse_edge:
            a, b = inverse(seam['affine'], self._sheets)
            left_sheet = (a * sheet + b) % self._sheets
        left = seam['left']
        left_cycle, left_degree = self._cycle(*left, left_sheet)
        if degree != left_degree:
            raise ArithmeticError('a checked seam changed covering degree')
        return dict(kind='seam', key=('seam', edge, left_cycle), covering_degree=degree,
                    component_key=component, source_port=list(port), seam=edge,
                    paired_port=list(seam['right'] if not reverse_edge else seam['left']))

    def boundary_lift_key(self, piece, boundary, sheet):
        result = self.port_lift_key(piece, boundary, sheet)
        if result['kind'] != 'boundary':
            raise ValueError('this boundary was consumed by a seam; use port_lift_key')
        return result

    def marked_signature(self, component_piece, component_sheet, marks=()):
        """Exact signature for an ordered list of points on a fixed sewn base."""
        root, key = self.component_key(component_piece, component_sheet)
        if not isinstance(marks, (list, tuple)):
            raise ValueError('marks must be a finite list or tuple of [piece, sheet] points')
        pieces, points = [], []
        for mark in marks:
            _poll(self._check)
            piece, sheet = self._point(mark)
            if self.component_key(piece, sheet) != (root, key):
                raise ValueError('all marked points must lie in the selected component')
            pieces.append(piece)
            points.append(self.to_root(piece, sheet)[1])
        header = (self._model, root, self._family(root, key)['type_id'])
        if not points:
            return header + ('unmarked',)
        result = self._results[root]
        d, m = result['translation_divisor'], result['translation_orbit_size']
        reflection = result['reference_reflection']
        anchor, coordinates = points[0], []
        if len(key) == 2:
            reflected = (reflection['shift'] - anchor) % self._sheets
            for point in points:
                _poll(self._check)
                side = int((point - anchor) % d != 0)
                origin = reflected if side else anchor
                coordinates.append((side, ((point - origin) // d) % m))
            kind, stabilizer = 'paired', None
        else:
            for point in points:
                _poll(self._check)
                coordinates.append(((point - anchor) // d) % m)
            kind = 'translation' if reflection is None else 'fixed'
            stabilizer = (None if reflection is None else
                          ((2 * anchor - reflection['shift']) // d) % m)
        return header + ('marked', tuple(pieces), kind, stabilizer, tuple(coordinates))

    def transport_point(self, source_anchor, target_anchor, point):
        """Evaluate the unique deck isomorphism with the specified rooted image.

        Anchors must be over the same piece basepoint.  The query may be over
        any piece of the source component.  Return None if the rooted covering
        isomorphism does not exist; otherwise return [query_piece, image_sheet].
        """
        _poll(self._check)
        source_anchor = self._point(source_anchor)
        target_anchor = self._point(target_anchor)
        point = self._point(point)
        if source_anchor[0] != target_anchor[0]:
            raise ValueError('anchors must lie over the same piece basepoint')
        source = self.component_key(*source_anchor)
        target = self.component_key(*target_anchor)
        if self.component_key(*point) != source:
            raise ValueError('query point is outside the source component')
        root = source[0]
        if source[0] != target[0] or len(source[1]) != len(target[1]):
            return None
        x = self.to_root(*source_anchor)[1]
        y = self.to_root(*target_anchor)[1]
        z = self.to_root(*point)[1]
        result = self._results[root]
        d, n = result['translation_divisor'], self._sheets
        reflection = result['reference_reflection']
        if reflection is None:
            answer = (z - x + y) % n
        elif len(source[1]) == 1:
            if (2 * (y - x)) % n:
                return None
            answer = (z - x + y) % n
        elif (z - x) % d == 0:
            answer = (z - x + y) % n
        else:
            answer = (z + x - y) % n
        a, b = self._gauges[point[0]]
        _poll(self._check)
        return [point[0], (a * answer + b) % n]


def assemble_cover(raw, *, check=None):
    """Validate and classify a whole-boundary assembly without expanding sheets."""
    return GluedCoverIndex(raw, check=check).summary


def main(argv=None):
    import argparse
    import json
    from math import isfinite
    from pathlib import Path
    from time import monotonic
    from .integer_codec import json_safe

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--port', nargs=3, metavar=('PIECE', 'BOUNDARY', 'SHEET'))
    parser.add_argument('--seconds', type=float)
    args = parser.parse_args(argv)
    if args.seconds is not None and (not isfinite(args.seconds) or args.seconds < 0):
        parser.error('--seconds must be finite and nonnegative')
    deadline = None if args.seconds is None else monotonic() + args.seconds

    def check():
        if deadline is not None and monotonic() >= deadline:
            raise TimeoutError('surface gluing query time allowance exhausted')

    try:
        index = GluedCoverIndex(json.loads(args.input.read_text()), check=check)
        result = index.summary
        if args.port:
            values = [encoded_integer(v) if 'x' in v.lower() else int(v, 10)
                      for v in args.port]
            result['port_query'] = index.port_lift_key(*values)
        output = json.dumps(json_safe(result), indent=2, sort_keys=True)
        check()
    except (ValueError, TimeoutError, MemoryError) as exc:
        parser.exit(2, f'surface gluing query failed: {exc}\n')
    print(output)
    return 0


if __name__ == '__main__':
    main()
