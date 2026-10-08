"""Exact transports of marked boundary lifts in a binary dihedral cover.

This extends ``surface_cover.CoverIndex`` from ordered fibre points to
ordered, unparameterized lifted boundary circles.  Each boundary circle is
specified by a base boundary index and one sheet in its peripheral orbit.
The selected source/target component sheets are selectors, not extra marks.

The answer contains every covering isomorphism over the *fixed* base
presentation.  Maps are represented by at most two arithmetic progressions
of possible images of a canonical source root; there is no sheet expansion.
This kernel does not certify arbitrary attaching maps or embeddings, extract
covering presentations from a knot exterior, or decide whether it is an unknot.
"""

from __future__ import annotations

from math import gcd

from .surface_cover import CoverIndex, _integer, _poll


def _linear_congruence(coefficient, value, modulus, check):
    """Return (a,l) for all x=a mod l solving coefficient*x=value mod modulus."""
    _poll(check)
    common = gcd(coefficient, modulus)
    if value % common:
        return None
    reduced = modulus // common
    if reduced == 1:
        return 0, 1
    answer = ((value // common)
              * pow(coefficient // common, -1, reduced)) % reduced
    _poll(check)
    return answer, reduced


def _intersect_congruences(left, right, check):
    """Generalized CRT; all moduli in this module divide the translation degree."""
    _poll(check)
    if left is None or right is None:
        return None
    a, modulus = left
    b, other = right
    common = gcd(modulus, other)
    if (b - a) % common:
        return None
    reduced = other // common
    multiplier = (0 if reduced == 1 else
                  ((b - a) // common) * pow(modulus // common, -1, reduced))
    combined = modulus * reduced
    answer = (a + modulus * (multiplier % reduced)) % combined
    _poll(check)
    return answer, combined


class BoundaryTransportIndex(CoverIndex):
    """A checked cover with exact boundary-circle and fibre-point constraints.

    ``transports`` accepts point pairs ``(source_sheet, target_sheet)`` and
    boundary pairs ``(base_boundary, source_sheet, target_sheet)``.  A boundary
    pair means that the whole source peripheral orbit maps onto the target
    peripheral orbit; the supplied sheets themselves need not map to each
    other.  Repetitions and mixed point/circle constraints are permitted.
    """

    def _pairs(self, values, arity, label, source, target):
        if not isinstance(values, (list, tuple)):
            raise ValueError(f'{label} must be a finite list or tuple')
        result = []
        for item in values:
            _poll(self._check)
            if not isinstance(item, (list, tuple)) or len(item) != arity:
                raise ValueError(f'each {label} entry requires {arity} integers')
            if arity == 3:
                boundary = _integer(item[0], 'base boundary', 0)
                if boundary >= len(self._result['boundary_monodromy']):
                    raise ValueError('base boundary index is out of range')
            x = _integer(item[-2], 'source marked sheet', 0)
            y = _integer(item[-1], 'target marked sheet', 0)
            if self.component_key(x) != source:
                raise ValueError('source mark is outside the selected component')
            if self.component_key(y) != target:
                raise ValueError('target mark is outside the selected component')
            result.append((boundary, x, y) if arity == 3 else (x, y))
        return result

    def transports(self, source_component, target_component, *,
                   point_pairs=(), boundary_pairs=()):
        """Return all constrained isomorphisms in at most two root progressions.

        Each output progression represents ``first + j*step`` for
        ``0 <= j < count`` as the image of ``source_root``.  The progressions
        are disjoint and sorted by ``first``.  ``transport_sheet(source_root,
        root_image, sheet)`` evaluates the corresponding unique map.  An empty
        list means no compatible covering isomorphism; malformed data raises.

        After cover preparation, q constraints cost O(q B^3) bit operations
        conservatively, where B bounds the integer bit lengths.  Output size
        is O(B).  Neither query work nor storage depends on the sheet count,
        component count, lifted boundary count, or number of returned maps.
        """
        source = self.component_key(source_component)
        target = self.component_key(target_component)
        points = self._pairs(point_pairs, 2, 'point_pairs', source, target)
        boundaries = self._pairs(boundary_pairs, 3, 'boundary_pairs', source, target)
        n = self._result['sheets']
        d = self._result['translation_divisor']
        m = self._result['translation_orbit_size']
        reference = self._result['reference_reflection']
        root = source[0]

        def affine_at(sheet):
            if len(source) == 2 and (sheet - root) % d:
                return -1, sheet + root
            return 1, sheet - root

        progressions = []
        if len(source) == len(target):
            for residue in target:  # One or two residues, independent of n.
                _poll(self._check)
                congruence = (0, 1)
                if reference is not None and len(source) == 1:
                    # A translation between reflection-fixed components is
                    # equivariant precisely when twice its displacement is zero.
                    congruence = _linear_congruence(
                        2*d, 2*(root-residue), n, self._check)
                for x, y in points:
                    _poll(self._check)
                    sign, offset = affine_at(x)
                    constraint = _linear_congruence(
                        sign*d, y-sign*residue-offset, n, self._check)
                    congruence = _intersect_congruences(
                        congruence, constraint, self._check)
                reflections = []
                for boundary, x, y in boundaries:
                    _poll(self._check)
                    peripheral = self._result['boundary_monodromy'][boundary]
                    sign, offset = affine_at(x)
                    if peripheral['sign'] == 1:
                        modulus = gcd(n, peripheral['shift'])
                        constraint = _linear_congruence(
                            sign*d, y-sign*residue-offset, modulus, self._check)
                        congruence = _intersect_congruences(
                            congruence, constraint, self._check)
                    else:
                        reflections.append((sign, offset, y, peripheral['shift']))
                if congruence is None:
                    continue
                a, modulus = congruence
                if not reflections:
                    progressions.append({'first': residue+d*a,
                                         'step': d*modulus,
                                         'count': m//modulus})
                    continue

                # One reflection orbit has at most two points.  It therefore
                # restricts the root to at most two *values*, not 2^q branches.
                sign, offset, y, shift = reflections[0]
                candidates = set()
                for image in (y, (shift-y) % n):
                    constraint = _linear_congruence(
                        sign*d, image-sign*residue-offset, n, self._check)
                    if constraint is not None:
                        value, period = constraint
                        if period != m:
                            raise ArithmeticError('root equation lost its full modulus')
                        if (value-a) % modulus == 0:
                            candidates.add(value)
                for sign, offset, y, shift in reflections[1:]:
                    _poll(self._check)
                    allowed = {y, (shift-y) % n}
                    candidates = {value for value in candidates
                                  if (sign*(residue+d*value)+offset) % n in allowed}
                if candidates:
                    ordered = sorted(candidates)
                    # In a fixed component two surviving candidates differ by
                    # m/2; in a paired component each residue gives at most one.
                    if len(source) == 2 and len(ordered) != 1:
                        raise ArithmeticError('reflection orbit did not fix a residue root')
                    if len(ordered) == 2 and 2*(ordered[1]-ordered[0]) != m:
                        raise ArithmeticError('fixed-component root stabilizer is invalid')
                    step = n if len(ordered) == 1 else d*(ordered[1]-ordered[0])
                    progressions.append({'first': residue+d*ordered[0],
                                         'step': step, 'count': len(ordered)})

        progressions.sort(key=lambda item: item['first'])
        if len(progressions) > 2:
            raise ArithmeticError('dihedral transport requires more than two progressions')
        count = sum(item['count'] for item in progressions)
        _poll(self._check)
        return {'input_model': 'fixed-base-dihedral-boundary-transport',
                'source_component': source, 'target_component': target,
                'source_root': root, 'root_progressions': progressions,
                'isomorphism_count': count,
                'witness_target_anchor': progressions[0]['first'] if progressions else None}

    def cyclic_marked_signature(self, component_sheet, *, point_marks=(), boundary_marks=()):
        """Canonical key and exact marking-type count for pure translation covers.

        Boundary marks are ordered ``(base_boundary, sheet)`` pairs.  The key
        classifies components with both ordered lists of marks over this fixed
        presentation; arbitrary permutations of marks are not allowed.  The
        canonical component is the residue-zero component.  The returned root
        image explicitly transports the marked component to its canonical form.

        If the mark periods are q_i | m, the exact number of marking types
        for that list of base boundary labels/point slots is prod(q_i)/lcm(q_i).
        The compatible-map count to each canonical form is m/lcm(q_i).
        For no marks, the empty product and lcm are both one.
        """
        source = self.component_key(component_sheet)
        if self._result['reference_reflection'] is not None:
            raise ValueError('cyclic signatures require a pure translation presentation')
        if not isinstance(point_marks, (list, tuple)):
            raise ValueError('point_marks must be a finite list or tuple')
        if not isinstance(boundary_marks, (list, tuple)):
            raise ValueError('boundary_marks must be a finite list or tuple')
        root = source[0]
        n = self._result['sheets']
        d = self._result['translation_divisor']
        m = self._result['translation_orbit_size']
        schema, coordinates = [], []
        for point in point_marks:
            _poll(self._check)
            point = _integer(point, 'marked point', 0)
            if self.component_key(point) != source:
                raise ValueError('marked point is outside the selected component')
            schema.append(('point',))
            coordinates.append((((point-root)//d) % m,m))
        for item in boundary_marks:
            _poll(self._check)
            if not isinstance(item, (list, tuple)) or len(item) != 2:
                raise ValueError('each boundary mark requires a boundary index and sheet')
            boundary = _integer(item[0], 'base boundary', 0)
            if boundary >= len(self._result['boundary_monodromy']):
                raise ValueError('base boundary index is out of range')
            sheet = _integer(item[1], 'marked boundary sheet', 0)
            if self.component_key(sheet) != source:
                raise ValueError('boundary mark is outside the selected component')
            period = gcd(n,self._result['boundary_monodromy'][boundary]['shift'])//d
            schema.append(('boundary',boundary))
            coordinates.append((((sheet-root)//d) % period,period))

        phase, phase_modulus, configurations = 0,1,1
        canonical = []
        for value, period in coordinates:
            _poll(self._check)
            configurations *= period
            common = gcd(phase_modulus,period)
            minimum = (value+phase) % common
            merged = _intersect_congruences((phase,phase_modulus),
                                           ((minimum-value) % period,period),self._check)
            if merged is None:
                raise ArithmeticError('canonical phase restriction became inconsistent')
            phase, phase_modulus = merged
            canonical.append(minimum)
        _poll(self._check)
        return {'signature': (self._model,'cyclic-boundary-marking',
                              tuple(schema),tuple(canonical)),
                'canonical_component': (0,), 'source_root': root,
                'canonical_root_image': d*phase, 'phase_modulus': phase_modulus,
                'isomorphism_count_to_canonical': m//phase_modulus,
                'marking_type_count': configurations//phase_modulus}


def main(argv=None):
    """Read a checked cover and one boundary-transport query from JSON."""
    import argparse
    import json
    from math import isfinite
    from pathlib import Path
    from time import monotonic
    from .integer_codec import json_safe

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path,
                        help='JSON with exactly cover and query objects')
    parser.add_argument('--seconds', type=float, help='cooperative query time allowance')
    args = parser.parse_args(argv)
    if args.seconds is not None and (not isfinite(args.seconds) or args.seconds < 0):
        parser.error('--seconds must be finite and nonnegative')
    deadline = None if args.seconds is None else monotonic()+args.seconds

    def check():
        if deadline is not None and monotonic() >= deadline:
            raise TimeoutError('boundary-transport time allowance exhausted')

    try:
        check()
        raw = json.loads(args.input.read_text())
        if not isinstance(raw, dict) or set(raw) != {'cover', 'query'}:
            raise ValueError('input must contain exactly cover and query')
        query = raw['query']
        required = {'source_component', 'target_component'}
        allowed = required | {'point_pairs', 'boundary_pairs'}
        if not isinstance(query, dict) or not required <= set(query) <= allowed:
            raise ValueError('query requires component selectors and optional mark pairs')
        index = BoundaryTransportIndex(raw['cover'], check=check)
        result = index.transports(**query)
        output = json.dumps(json_safe(result), indent=2, sort_keys=True)
        check()
    except (ValueError, TimeoutError, MemoryError) as exc:
        parser.exit(2, f'boundary-transport query failed: {exc}\n')
    print(output)
    return 0


if __name__ == '__main__':
    main()
