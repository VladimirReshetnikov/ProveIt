"""Exact topology of binary-encoded dihedral covers of bordered surfaces.

The input is a canonical compact connected surface with nonempty boundary,
and a permutation x -> sign*x + shift modulo `sheets` for each free generator.
No sheet is expanded. At most three component-family records are returned.
The exact number of cover-isomorphism types and each family's type ID are
also returned; distinct exceptional records can describe isomorphic covers.

This is a restricted covering-space kernel. It does not discover such a
presentation in a normal surface or verify a proposed embedding in a 3-manifold.
"""

from __future__ import annotations

from copy import deepcopy
from math import gcd
from typing import Any

from .integer_codec import encoded_integer


def _poll(check):
    if check is not None:
        check()


def _integer(value: Any, name: str, minimum: int | None = None) -> int:
    try:
        value = encoded_integer(value)
    except ValueError as exc:
        raise ValueError(f"{name} must be an integer or signed hexadecimal string") from exc
    if minimum is not None and value < minimum:
        raise ValueError(f"{name} must be at least {minimum}")
    return value


def compose(left: tuple[int, int], right: tuple[int, int], sheets: int):
    """The affine map `left` after `right`."""
    sign_left, shift_left = left
    sign_right, shift_right = right
    return sign_left * sign_right, (sign_left * shift_right + shift_left) % sheets


def inverse(affine: tuple[int, int], sheets: int):
    sign, shift = affine
    return sign, (-sign * shift) % sheets


def evaluate_word(word: list[int], maps: list[tuple[int, int]], sheets: int, *, check=None):
    """Follow a signed, one-based word in the given order."""
    result = (1, 0)
    for letter in word:
        _poll(check)
        if type(letter) is not int or not 1 <= abs(letter) <= len(maps):
            raise ValueError("boundary word references a nonexistent generator")
        step = maps[abs(letter) - 1]
        if letter < 0:
            step = inverse(step, sheets)
        result = compose(step, result, sheets)
    return result


def canonical_schema(orientable: bool, genus: int, boundaries: int, *, check=None):
    """Canonical free generators, orientation character and boundary words.

    In the nonorientable case `genus` means the number of crosscaps.
    Boundary words are based loops; the final one is the inverse of the
    product of commutators (or squares) and the earlier boundary generators.
    """
    if type(orientable) is not bool:
        raise ValueError("surface.orientable must be a boolean")
    genus = _integer(genus, "surface.genus", 0 if orientable else 1)
    boundaries = _integer(boundaries, "surface.boundary_components", 1)
    labels = []
    character = []
    relation_prefix = []
    if orientable:
        for index in range(genus):
            _poll(check)
            a, b = len(labels) + 1, len(labels) + 2
            labels.extend([f"a{index + 1}", f"b{index + 1}"])
            character.extend([0, 0])
            relation_prefix.extend([a, b, -a, -b])
        euler = 2 - 2 * genus - boundaries
    else:
        for index in range(genus):
            _poll(check)
            x = len(labels) + 1
            labels.append(f"x{index + 1}")
            character.append(1)
            relation_prefix.extend([x, x])
        euler = 2 - genus - boundaries
    words = []
    for index in range(boundaries - 1):
        _poll(check)
        c = len(labels) + 1
        labels.append(f"c{index + 1}")
        character.append(0)
        words.append([c])
        relation_prefix.append(c)
    words.append([-letter for letter in reversed(relation_prefix)])
    return labels, character, words, euler


def parse_input(raw: dict, *, check=None):
    _poll(check)
    if not isinstance(raw, dict):
        raise ValueError("input must be an object")
    allowed = {"surface", "sheets", "monodromy"}
    if set(raw) != allowed:
        raise ValueError(f"input fields must be exactly {sorted(allowed)}")
    sheets = _integer(raw["sheets"], "sheets", 1)
    surface = raw["surface"]
    if not isinstance(surface, dict) or set(surface) != {
        "orientable", "genus", "boundary_components"
    }:
        raise ValueError("surface requires orientable, genus and boundary_components")
    orientable = surface["orientable"]
    if type(orientable) is not bool:
        raise ValueError("surface.orientable must be a boolean")
    genus = _integer(surface["genus"], "surface.genus", 0 if orientable else 1)
    boundaries = _integer(surface["boundary_components"], "surface.boundary_components", 1)
    rank = (2 * genus if orientable else genus) + boundaries - 1
    supplied = raw["monodromy"]
    if not isinstance(supplied, list) or len(supplied) != rank:
        raise ValueError(f"monodromy requires {rank} maps in canonical generator order")
    labels, character, words, euler = canonical_schema(orientable, genus, boundaries, check=check)
    maps = []
    for index, item in enumerate(supplied):
        _poll(check)
        if not isinstance(item, dict) or set(item) != {"sign", "shift"}:
            raise ValueError(f"monodromy[{index}] requires sign and shift")
        sign = _integer(item["sign"], f"monodromy[{index}].sign")
        if sign not in (-1, 1):
            raise ValueError("an affine sign must equal +1 or -1")
        shift = _integer(item["shift"], f"monodromy[{index}].shift")
        maps.append((sign, shift % sheets))
    return sheets, labels, character, words, euler, maps


def _bezout(a: int, b: int, check=None):
    """Return d,u,v with d=gcd(a,b)=u*a+v*b, for a>0 and b>=0."""
    r0, r1, u0, u1, v0, v1 = a, b, 1, 0, 0, 1
    while r1:
        _poll(check)
        quotient = r0 // r1
        r0, r1 = r1, r0 - quotient * r1
        u0, u1 = u1, u0 - quotient * u1
        v0, v1 = v1, v0 - quotient * v1
    return r0, u0, v0


def _group_data(sheets: int, maps: list[tuple[int, int]], character: list[int], check=None):
    reflections = [(shift, bit) for (sign, shift), bit in zip(maps, character)
                   if sign == -1]
    reference = reflections[0] if reflections else None
    translations = [(shift, bit) for (sign, shift), bit in zip(maps, character)
                    if sign == 1]
    if reference is not None:
        b0, t0 = reference
        translations.extend(((shift - b0) % sheets, bit ^ t0)
                            for shift, bit in reflections[1:])

    # Compute a Bezout expression for d and its orientation bit without
    # retaining the potentially long vector of Bezout coefficients.
    divisor, tau = sheets, 0
    for shift, bit in translations:
        _poll(check)
        new_divisor, u, v = _bezout(divisor, shift, check)
        tau = (u * tau + v * bit) % 2
        divisor = new_divisor
    degree = sheets // divisor

    # An inconsistent relation gives an orientation-reversing closed lift
    # at every sheet. If consistent, translation by d has orientation tau.
    consistent = (degree * tau) % 2 == 0
    consistent = consistent and all(
        bit == ((shift // divisor) * tau) % 2 for shift, bit in translations
    )
    return divisor, degree, reference, consistent, tau


def _fixed_residues(divisor: int, reflection_shift: int):
    """Solve 2r = reflection_shift modulo divisor in at most two records."""
    common = gcd(2, divisor)
    if reflection_shift % common:
        return []
    modulus = divisor // common
    if modulus == 1:
        first = 0
    else:
        first = ((reflection_shift // common)
                 * pow(2 // common, -1, modulus)) % modulus
    return [first + index * modulus for index in range(common)]


def _cycles_for_boundary(kind: str, residue: int | None, divisor: int,
                         degree: int, affine: tuple[int, int]):
    """Cycle-degree profile for one component over one base boundary."""
    sign, shift = affine
    if sign == 1:
        if shift % divisor:
            raise ArithmeticError("boundary translation is outside monodromy group")
        count = gcd(degree, shift // divisor)
        multiplier = 2 if kind == "paired-residues" else 1
        return [{"degree": degree // count, "multiplicity": multiplier * count}]
    if kind == "paired-residues":
        return [{"degree": 2, "multiplicity": degree}]
    if residue is None or (shift - 2 * residue) % divisor:
        raise ArithmeticError("boundary reflection does not preserve the component")
    reflection_on_class = (shift - 2 * residue) // divisor
    common = gcd(2, degree)
    fixed_points = common if reflection_on_class % common == 0 else 0
    result = []
    if fixed_points:
        result.append({"degree": 1, "multiplicity": fixed_points})
    pairs = (degree - fixed_points) // 2
    if pairs:
        result.append({"degree": 2, "multiplicity": pairs})
    return result


def classify_cover(raw: dict, *, check=None):
    """Return at most three exact component families in binary arithmetic."""
    sheets, labels, character, words, euler, maps = parse_input(raw, check=check)
    divisor, degree, reference, consistent, tau = _group_data(sheets, maps, character, check)
    boundary_maps = [evaluate_word(word, maps, sheets, check=check) for word in words]

    if reference is None:
        descriptors = [("single-residues", None, divisor)]
        fixed = []
    else:
        b0, _ = reference
        fixed = _fixed_residues(divisor, b0)
        descriptors = []
        paired_count = (divisor - len(fixed)) // 2
        if paired_count:
            descriptors.append(("paired-residues", None, paired_count))
        descriptors.extend(("fixed-residue", residue, 1) for residue in fixed)

    families = []
    for kind, residue, multiplicity in descriptors:
        _poll(check)
        component_degree = degree * (2 if kind == "paired-residues" else 1)
        orientable = consistent
        if orientable and kind == "fixed-residue":
            b0, t0 = reference
            k = (2 * residue - b0) // divisor
            orientable = (t0 + k * tau) % 2 == 0
        profiles = []
        for affine in boundary_maps:
            _poll(check)
            profiles.append(_cycles_for_boundary(kind, residue, divisor, degree, affine))
        boundary_count = sum(item["multiplicity"] for profile in profiles for item in profile)
        chi = component_degree * euler
        genus_numerator = 2 - boundary_count - chi
        if orientable:
            if genus_numerator < 0 or genus_numerator % 2:
                raise ArithmeticError("computed orientable surface has invalid Euler data")
            genus = genus_numerator // 2
        else:
            if genus_numerator < 1:
                raise ArithmeticError("computed nonorientable surface has invalid Euler data")
            genus = genus_numerator
        record = {
            "family": kind,
            "multiplicity": multiplicity,
            "cover_degree": component_degree,
            "orientable": orientable,
            "genus": genus,
            "genus_convention": "handles" if orientable else "crosscaps",
            "boundary_components": boundary_count,
            "euler_characteristic": chi,
            "boundary_lifts": profiles,
            "orientation_interval_bundle": "product" if orientable else "twisted",
        }
        if residue is not None:
            record["residue"] = residue
            representative = (residue,)
        elif kind == "single-residues":
            representative = (0,)
        else:
            # At most two residues are fixed, so checking 0,1,2 suffices.
            seed = next(r for r in range(min(divisor, 3)) if r not in fixed)
            representative = tuple(sorted((seed, (reference[0] - seed) % divisor)))
        record["representative_component_key"] = representative
        families.append(record)

    # The two exceptional covers are isomorphic precisely when m is odd.
    # Keep their distinct residue records for attachment queries, while
    # assigning the same cover type to them in that case.
    generic_present = any(item["family"] == "paired-residues" for item in families)
    for record in families:
        if reference is None or record["family"] == "paired-residues":
            type_id = 0
        else:
            exception_id = 0 if degree % 2 else fixed.index(record["residue"])
            type_id = int(generic_present) + exception_id
        record["type_id"] = type_id

    if sum(item["multiplicity"] * item["cover_degree"] for item in families) != sheets:
        raise ArithmeticError("component degrees do not sum to the number of sheets")
    _poll(check)
    return {
        "input_model": "canonical-bordered-surface-dihedral-cover",
        "base_surface": {"orientable": raw["surface"]["orientable"],
                         "genus": encoded_integer(raw["surface"]["genus"]),
                         "boundary_components": len(words)},
        "sheets": sheets,
        "generator_labels": labels,
        "generator_monodromy": [{"sign": sign, "shift": shift} for sign, shift in maps],
        "orientation_character": character,
        "base_euler_characteristic": euler,
        "boundary_words": words,
        "boundary_monodromy": [{"sign": sign, "shift": shift} for sign, shift in boundary_maps],
        "translation_divisor": divisor,
        "translation_orbit_size": degree,
        "reference_reflection": (None if reference is None else {
            "shift": reference[0], "orientation_bit": reference[1]
        }),
        "translation_orientation_character": {
            "well_defined": consistent,
            "value_on_divisor": tau if consistent else None,
        },
        "fixed_residues": fixed,
        "component_count": sum(item["multiplicity"] for item in families),
        "cover_isomorphism_type_count": len({item["type_id"] for item in families}),
        "families": families,
    }


def component_key(classification: dict, sheet: int):
    """A canonical label for the connected component containing a root sheet.

    Labels are computed on demand; the output never allocates one per sheet.
    """
    sheet = _integer(sheet, "sheet", 0)
    if sheet >= classification["sheets"]:
        raise ValueError("sheet is outside the covering fibre")
    divisor = classification["translation_divisor"]
    residue = sheet % divisor
    reflection = classification["reference_reflection"]
    if reflection is None:
        return (residue,)
    partner = (reflection["shift"] - residue) % divisor
    return (residue,) if partner == residue else tuple(sorted((residue, partner)))


def boundary_lift_key(classification: dict, boundary: int, sheet: int):
    """Identify a lifted boundary circle without expanding its other sheets.

    `boundary` is a zero-based base boundary index. The sheet is at the
    common basepoint, using the paths of the canonical boundary words.
    The returned key distinguishes all lifts of that chosen base boundary.
    """
    sheet = _integer(sheet, "sheet", 0)
    component = component_key(classification, sheet)
    boundary = _integer(boundary, "boundary", 0)
    boundary_maps = classification["boundary_monodromy"]
    if boundary >= len(boundary_maps):
        raise ValueError("base boundary index is out of range")
    affine = boundary_maps[boundary]
    sheets = classification["sheets"]
    if affine["sign"] == 1:
        cycle_divisor = gcd(sheets, affine["shift"])
        key = (sheet % cycle_divisor,)
        degree = sheets // cycle_divisor
    else:
        partner = (affine["shift"] - sheet) % sheets
        key = (sheet,) if sheet == partner else tuple(sorted((sheet, partner)))
        degree = len(key)
    return {"base_boundary": boundary, "cycle_key": key,
            "covering_degree": degree, "component_key": component}


class CoverIndex:
    """Prepared, checked presentation with exact ordered-point marking queries.

    Signatures classify marked components over this fixed base presentation.
    They do not classify arbitrary embeddings or external attaching maps.
    The selected component sheet identifies a component; it is not an extra
    marked point. Mark order is significant and repetitions are permitted.
    """

    def __init__(self, raw, *, check=None):
        if check is not None and not callable(check):
            raise ValueError('check must be callable or None')
        self._check = check
        self._result = classify_cover(raw, check=check)
        surface = self._result['base_surface']
        self._model = (surface['orientable'], surface['genus'],
                       surface['boundary_components'], self._result['sheets'],
                       tuple((m['sign'], m['shift'])
                             for m in self._result['generator_monodromy']))
        _poll(check)

    @property
    def summary(self):
        """A defensive copy; serialized summaries are not accepted as proofs."""
        _poll(self._check)
        result = deepcopy(self._result)
        _poll(self._check)
        return result

    def component_key(self, sheet):
        _poll(self._check)
        return component_key(self._result, sheet)

    def boundary_lift_key(self, boundary, sheet):
        _poll(self._check)
        result = boundary_lift_key(self._result, boundary, sheet)
        _poll(self._check)
        return result

    def _family(self, key):
        for family in self._result['families']:
            if family['family'] == 'fixed-residue':
                if key == (family['residue'],):
                    return family
            elif len(key) == (2 if family['family'] == 'paired-residues' else 1):
                return family
        raise ArithmeticError('component is absent from the classified families')

    def marked_signature(self, component_sheet, marks=()):
        """Exact equality key for ordered point-marked components in this cover.

        Construction costs O(q) big-integer operations after preparation. The
        full normalized input is part of the key, preventing comparisons across
        different base presentations from being mistaken for this equivalence.
        """
        key = self.component_key(component_sheet)
        if not isinstance(marks, (list, tuple)):
            raise ValueError('marks must be a finite list or tuple of sheets')
        points = []
        for mark in marks:
            _poll(self._check)
            mark = _integer(mark, 'marked sheet', 0)
            if self.component_key(mark) != key:
                raise ValueError('all marked points must lie in the selected component')
            points.append(mark)
        header = (self._model, self._family(key)['type_id'])
        if not points:
            _poll(self._check)
            return header + ('unmarked',)
        n = self._result['sheets']
        d = self._result['translation_divisor']
        m = self._result['translation_orbit_size']
        reflection = self._result['reference_reflection']
        anchor = points[0]
        coordinates = []
        if len(key) == 2:
            reflected = (reflection['shift'] - anchor) % n
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
        _poll(self._check)
        return header + ('marked', kind, stabilizer, tuple(coordinates))

    def transport_sheet(self, source_anchor, target_anchor, sheet):
        """Evaluate the unique equivariant map sending one anchor to the other.

        Return None if such a covering isomorphism does not exist. Invalid
        sheets or a query outside the source component raise ValueError.
        No fibre permutation or individual component is expanded.
        """
        source_anchor = _integer(source_anchor, 'source anchor', 0)
        target_anchor = _integer(target_anchor, 'target anchor', 0)
        sheet = _integer(sheet, 'sheet', 0)
        source = self.component_key(source_anchor)
        target = self.component_key(target_anchor)
        if self.component_key(sheet) != source:
            raise ValueError('query sheet is outside the source component')
        if len(source) != len(target):
            return None
        n = self._result['sheets']
        d = self._result['translation_divisor']
        reflection = self._result['reference_reflection']
        if reflection is None:
            answer = (sheet - source_anchor + target_anchor) % n
        elif len(source) == 1:
            if (2 * (target_anchor - source_anchor)) % n:
                return None
            answer = (sheet - source_anchor + target_anchor) % n
        elif (sheet - source_anchor) % d == 0:
            answer = (sheet - source_anchor + target_anchor) % n
        else:
            answer = (sheet + source_anchor - target_anchor) % n
        _poll(self._check)
        return answer


def main(argv=None):
    """Standalone geometry query; never a knot-recognition command."""
    import argparse
    import json
    from math import isfinite
    from pathlib import Path
    from time import monotonic
    from .integer_codec import json_safe

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--component', help='sheet selecting a component for marked comparison')
    parser.add_argument('--mark', action='append', default=[], help='ordered marked sheet (repeatable)')
    parser.add_argument('--seconds', type=float, help='cooperative geometry-query time allowance')
    args = parser.parse_args(argv)
    if args.mark and args.component is None:
        parser.error('--mark requires --component')
    if args.seconds is not None and (not isfinite(args.seconds) or args.seconds < 0):
        parser.error('--seconds must be finite and nonnegative')
    deadline = None if args.seconds is None else monotonic() + args.seconds

    def check():
        if deadline is not None and monotonic() >= deadline:
            raise TimeoutError('surface-cover query time allowance exhausted')

    def cli_integer(text):
        # Decimal shell arguments are accepted explicitly; JSON strings remain
        # hexadecimal-only, matching the existing exact transport convention.
        return encoded_integer(text) if 'x' in text.lower() else int(text, 10)

    try:
        check()
        index = CoverIndex(json.loads(args.input.read_text()), check=check)
        result = index.summary
        if args.component is not None:
            result['marked_signature'] = index.marked_signature(
                cli_integer(args.component), [cli_integer(v) for v in args.mark])
        output = json.dumps(json_safe(result), indent=2, sort_keys=True)
        check()
    except (ValueError, TimeoutError, MemoryError) as exc:
        parser.exit(2, f'surface-cover query failed: {exc}\n')
    print(output)
    return 0


if __name__ == '__main__':
    main()
