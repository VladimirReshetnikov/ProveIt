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

import argparse
import json
from math import gcd
from pathlib import Path
from typing import Any


def _integer(value: Any, name: str, minimum: int | None = None) -> int:
    if type(value) is not int:
        raise ValueError(f"{name} must be an integer")
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


def evaluate_word(word: list[int], maps: list[tuple[int, int]], sheets: int):
    """Follow a signed, one-based word in the given order."""
    result = (1, 0)
    for letter in word:
        if not 1 <= abs(letter) <= len(maps):
            raise ValueError("boundary word references a nonexistent generator")
        step = maps[abs(letter) - 1]
        if letter < 0:
            step = inverse(step, sheets)
        result = compose(step, result, sheets)
    return result


def canonical_schema(orientable: bool, genus: int, boundaries: int):
    """Canonical free generators, orientation character and boundary words.

    In the nonorientable case `genus` means the number of crosscaps.
    Boundary words are based loops; the final one is the inverse of the
    product of commutators (or squares) and the earlier boundary generators.
    """
    if type(orientable) is not bool:
        raise ValueError("surface.orientable must be a boolean")
    _integer(genus, "surface.genus", 0 if orientable else 1)
    _integer(boundaries, "surface.boundary_components", 1)
    labels = []
    character = []
    relation_prefix = []
    if orientable:
        for index in range(genus):
            a, b = len(labels) + 1, len(labels) + 2
            labels.extend([f"a{index + 1}", f"b{index + 1}"])
            character.extend([0, 0])
            relation_prefix.extend([a, b, -a, -b])
        euler = 2 - 2 * genus - boundaries
    else:
        for index in range(genus):
            x = len(labels) + 1
            labels.append(f"x{index + 1}")
            character.append(1)
            relation_prefix.extend([x, x])
        euler = 2 - genus - boundaries
    words = []
    for index in range(boundaries - 1):
        c = len(labels) + 1
        labels.append(f"c{index + 1}")
        character.append(0)
        words.append([c])
        relation_prefix.append(c)
    words.append([-letter for letter in reversed(relation_prefix)])
    return labels, character, words, euler


def parse_input(raw: dict):
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
    labels, character, words, euler = canonical_schema(orientable, genus, boundaries)
    maps = []
    for index, item in enumerate(supplied):
        if not isinstance(item, dict) or set(item) != {"sign", "shift"}:
            raise ValueError(f"monodromy[{index}] requires sign and shift")
        sign = _integer(item["sign"], f"monodromy[{index}].sign")
        if sign not in (-1, 1):
            raise ValueError("an affine sign must equal +1 or -1")
        shift = _integer(item["shift"], f"monodromy[{index}].shift")
        maps.append((sign, shift % sheets))
    return sheets, labels, character, words, euler, maps


def _bezout(a: int, b: int):
    """Return d,u,v with d=gcd(a,b)=u*a+v*b, for a>0 and b>=0."""
    r0, r1, u0, u1, v0, v1 = a, b, 1, 0, 0, 1
    while r1:
        quotient = r0 // r1
        r0, r1 = r1, r0 - quotient * r1
        u0, u1 = u1, u0 - quotient * u1
        v0, v1 = v1, v0 - quotient * v1
    return r0, u0, v0


def _group_data(sheets: int, maps: list[tuple[int, int]], character: list[int]):
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
        new_divisor, u, v = _bezout(divisor, shift)
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


def classify_cover(raw: dict):
    """Return at most three exact component families in binary arithmetic."""
    sheets, labels, character, words, euler, maps = parse_input(raw)
    divisor, degree, reference, consistent, tau = _group_data(sheets, maps, character)
    boundary_maps = [evaluate_word(word, maps, sheets) for word in words]

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
        component_degree = degree * (2 if kind == "paired-residues" else 1)
        orientable = consistent
        if orientable and kind == "fixed-residue":
            b0, t0 = reference
            k = (2 * residue - b0) // divisor
            orientable = (t0 + k * tau) % 2 == 0
        profiles = [
            _cycles_for_boundary(kind, residue, divisor, degree, affine)
            for affine in boundary_maps
        ]
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
    return {
        "input_model": "canonical-bordered-surface-dihedral-cover",
        "base_surface": dict(raw["surface"]),
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
    _integer(sheet, "sheet", 0)
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
    component = component_key(classification, sheet)
    _integer(boundary, "boundary", 0)
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="JSON file in the canonical surface schema")
    parser.add_argument("--compact", action="store_true", help="compact JSON output")
    args = parser.parse_args()
    result = classify_cover(json.loads(args.input.read_text()))
    print(json.dumps(result, indent=None if args.compact else 2, sort_keys=True))


if __name__ == "__main__":
    main()
