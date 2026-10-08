"""Connectedness optimization for affine families of cyclic surface covers.

This compiles actual full-boundary surface assemblies into modular linear
constraints and loop voltages.  Local covers may be disconnected.  All fibre
maps are translations on a common Z/m, and every shift is an affine expression
in the same listed parameters.  It does not extract a family from a 3-manifold,
optimize genus, or issue a knot verdict.
"""

from __future__ import annotations

from collections import deque
from copy import deepcopy
from math import gcd

from .integer_codec import encoded_integer, json_safe
from .surface_cover import canonical_schema


def _poll(check):
    if check is not None:
        check()


def _fields(value, fields, name):
    if not isinstance(value, dict) or set(value) != set(fields):
        raise ValueError(f"{name} requires exactly {sorted(fields)}")


def _integer(value, name, minimum=None):
    try:
        result = encoded_integer(value)
    except ValueError as exc:
        raise ValueError(f"{name} requires an integer") from exc
    if minimum is not None and result < minimum:
        raise ValueError(f"{name} must be at least {minimum}")
    return result


def _expression(value, variables, modulus, name):
    _fields(value, {"constant", "coefficients"}, name)
    coefficients = value["coefficients"]
    if not isinstance(coefficients, list) or len(coefficients) != variables:
        raise ValueError(f"{name}.coefficients requires {variables} entries")
    return tuple(_integer(x, name) % modulus for x in
                 [value["constant"], *coefficients])


def _add(left, right, modulus, sign=1):
    return tuple((a + sign * b) % modulus for a, b in zip(left, right))


def _evaluate(expression, parameters, modulus):
    return (expression[0] + sum(a * b for a, b in
                               zip(expression[1:], parameters))) % modulus


def _endpoint(value, pieces, name):
    if not isinstance(value, list) or len(value) != 2:
        raise ValueError(f"{name} requires [piece, boundary]")
    piece, boundary = (_integer(x, name, 0) for x in value)
    if piece >= len(pieces) or boundary >= len(pieces[piece]["boundary"]):
        raise ValueError(f"{name} is outside the listed boundary ports")
    return piece, boundary


def compile_family(raw, *, check=None):
    """Compile a checked connected assembly into Az=b and h=c+Hz modulo m.

    The returned loop list retains provenance.  Tree potentials and all
    coefficients have bounded residues; no sheet or phase is enumerated.
    """
    if check is not None and not callable(check):
        raise ValueError("check must be callable or None")
    _poll(check)
    _fields(raw, {"sheets", "variables", "pieces", "seams", "constraints"}, "family")
    modulus = _integer(raw["sheets"], "sheets", 1)
    variables = _integer(raw["variables"], "variables", 0)
    if not isinstance(raw["pieces"], list) or not raw["pieces"]:
        raise ValueError("pieces must be a nonempty list")
    pieces = []
    zero = (0,) * (variables + 1)
    for index, piece in enumerate(raw["pieces"]):
        _poll(check)
        _fields(piece, {"surface", "monodromy"}, f"piece {index}")
        surface = piece["surface"]
        _fields(surface, {"orientable", "genus", "boundary_components"}, "surface")
        orientable = surface["orientable"]
        if type(orientable) is not bool:
            raise ValueError("surface.orientable requires a boolean")
        genus = _integer(surface["genus"], "genus", 0 if orientable else 1)
        boundaries = _integer(surface["boundary_components"], "boundary_components", 1)
        rank = (2 * genus if orientable else genus) + boundaries - 1
        if not isinstance(piece["monodromy"], list) or len(piece["monodromy"]) != rank:
            raise ValueError(f"piece {index} requires {rank} generator expressions")
        labels, _, words, euler = canonical_schema(orientable, genus, boundaries,
                                                   check=check)
        loops = [_expression(x, variables, modulus, "monodromy")
                 for x in piece["monodromy"]]
        peripheral = []
        for word in words:
            shift = zero
            for letter in word:
                _poll(check)
                shift = _add(shift, loops[abs(letter) - 1], modulus,
                             1 if letter > 0 else -1)
            peripheral.append(shift)
        pieces.append({"loops": loops, "boundary": peripheral, "labels": labels,
                       "euler": euler})

    constraints = raw["constraints"]
    _fields(constraints, {"matrix", "rhs"}, "constraints")
    if (not isinstance(constraints["matrix"], list)
            or not isinstance(constraints["rhs"], list)
            or len(constraints["matrix"]) != len(constraints["rhs"])):
        raise ValueError("constraints requires equally long matrix and rhs")
    matrix, rhs, constraint_sources = [], [], []
    for index, (row, value) in enumerate(zip(constraints["matrix"], constraints["rhs"])):
        _poll(check)
        if not isinstance(row, list) or len(row) != variables:
            raise ValueError("constraint row has the wrong length")
        matrix.append([_integer(x, "constraint coefficient") % modulus for x in row])
        rhs.append(_integer(value, "constraint rhs") % modulus)
        constraint_sources.append({"kind": "supplied", "index": index})

    if not isinstance(raw["seams"], list):
        raise ValueError("seams must be a list")
    used, seams = set(), []
    adjacency = [[] for _ in pieces]
    for index, seam in enumerate(raw["seams"]):
        _poll(check)
        _fields(seam, {"left", "right", "direction", "shift"}, f"seam {index}")
        left = _endpoint(seam["left"], pieces, "seam.left")
        right = _endpoint(seam["right"], pieces, "seam.right")
        if left == right or left in used or right in used:
            raise ValueError("each boundary port may occur in at most one seam")
        used.update((left, right))
        direction = _integer(seam["direction"], "seam.direction")
        if direction not in (-1, 1):
            raise ValueError("seam.direction must be +1 or -1")
        shift = _expression(seam["shift"], variables, modulus, "seam.shift")
        # Translation intertwiners commute with all fibre translations.
        # Boundary compatibility is a_L = direction * a_R, regardless of shift.
        difference = _add(pieces[left[0]]["boundary"][left[1]],
                          pieces[right[0]]["boundary"][right[1]], modulus, -direction)
        matrix.append(list(difference[1:]))
        rhs.append(-difference[0] % modulus)
        constraint_sources.append({"kind": "seam", "index": index})
        seams.append({"left": left, "right": right, "shift": shift})
        adjacency[left[0]].append((right[0], index, 1))
        adjacency[right[0]].append((left[0], index, -1))

    potentials, parents, tree_edges = [None] * len(pieces), [None] * len(pieces), set()
    potentials[0] = zero
    queue = deque([0])
    while queue:
        vertex = queue.popleft()
        _poll(check)
        for other, edge, sign in adjacency[vertex]:
            if potentials[other] is not None:
                continue
            potentials[other] = _add(potentials[vertex], seams[edge]["shift"], modulus, sign)
            parents[other] = {"piece": vertex, "seam": edge, "sign": sign}
            tree_edges.add(edge)
            queue.append(other)
    if any(x is None for x in potentials):
        raise ValueError("the base assembly graph must be connected")

    holonomies, loop_sources = [], []
    for index, piece in enumerate(pieces):
        for label, shift in zip(piece["labels"], piece["loops"]):
            holonomies.append(shift)
            loop_sources.append({"kind": "piece", "piece": index, "generator": label})
    for index, seam in enumerate(seams):
        if index in tree_edges:
            continue
        _poll(check)
        shift = _add(potentials[seam["left"][0]], seam["shift"], modulus)
        shift = _add(shift, potentials[seam["right"][0]], modulus, -1)
        holonomies.append(shift)
        loop_sources.append({"kind": "seam-cycle", "seam": index})
    return {"modulus": modulus, "variables": variables, "matrix": matrix, "rhs": rhs,
            "constant": [x[0] for x in holonomies],
            "linear": [list(x[1:]) for x in holonomies],
            "constraint_sources": constraint_sources, "loop_sources": loop_sources,
            "tree_parents": parents, "tree_potentials": potentials,
            "base_euler_characteristic": sum(piece["euler"] for piece in pieces),
            "base_unsewn_boundary_count": sum(len(p["boundary"]) for p in pieces) - 2 * len(seams)}


def realize_family(raw, parameters, *, check=None):
    """Return a concrete assembly in the prior surface_gluing input schema.

    Feasibility is checked directly against every compiled seam and supplied
    equation.  The result can be fed to the earlier dihedral assembly kernel.
    """
    compiled = compile_family(raw, check=check)
    modulus, variables = compiled["modulus"], compiled["variables"]
    if not isinstance(parameters, (list, tuple)) or len(parameters) != variables:
        raise ValueError("parameter vector has the wrong length")
    parameters = [_integer(x, "parameter") % modulus for x in parameters]
    for row, value in zip(compiled["matrix"], compiled["rhs"]):
        _poll(check)
        if sum(a * b for a, b in zip(row, parameters)) % modulus != value:
            raise ValueError("parameter vector violates a seam or supplied constraint")
    def shift(expression):
        return _evaluate(_expression(expression, variables, modulus, "expression"),
                         parameters, modulus)
    pieces = [{"surface": deepcopy(piece["surface"]),
               "monodromy": [{"sign": 1, "shift": shift(x)} for x in piece["monodromy"]]}
              for piece in raw["pieces"]]
    seams = [{"left": list(seam["left"]), "right": list(seam["right"]),
              "direction": seam["direction"], "map": {"sign": 1, "shift": shift(seam["shift"])}}
             for seam in raw["seams"]]
    return {"sheets": modulus, "pieces": pieces, "seams": seams}


def component_count_at(raw, parameters, *, check=None):
    """Exact count for one feasible member; no sheet expansion."""
    compiled = compile_family(raw, check=check)
    realize_family(raw, parameters, check=check)
    modulus = compiled["modulus"]
    parameters = [_integer(x, "parameter") % modulus for x in parameters]
    divisor = modulus
    for constant, row in zip(compiled["constant"], compiled["linear"]):
        _poll(check)
        divisor = gcd(divisor, (constant + sum(a * b for a, b in
                                              zip(row, parameters))) % modulus)
    return divisor


def optimize_cover_family(raw, *, check=None):
    """Return an exact minimum and a replayable modular optimality witness."""
    from .affine_modular import optimise_cyclic_affine_family
    compiled = compile_family(raw, check=check)
    result = optimise_cyclic_affine_family(
        compiled["modulus"], compiled["constant"], compiled["linear"],
        compiled["matrix"], compiled["rhs"],
        variable_count=compiled["variables"], check=check)
    return {"input_model": "affine-cyclic-surface-assembly", "optimization": result,
            "compilation": compiled}


def verify_cover_family_certificate(raw, proposed, *, check=None):
    """Check an optimum or infeasibility from a fresh geometric compilation.

    This deliberately ignores the producer's compilation and solution count.
    Feasible certificates prove an attained optimal component count; infeasible
    certificates prove that the seam system has no solution.  Integer fields
    accept the same signed hexadecimal transport as the input.  No affine-space
    computation or optimization is rerun.
    """
    from .affine_modular import (
        verify_infeasibility_certificate, verify_optimality_certificate,
    )
    compiled = compile_family(raw, check=check)
    if not isinstance(proposed, dict) or "optimization" not in proposed:
        return False
    optimization = proposed["optimization"]
    if not isinstance(optimization, dict):
        return False

    def integers(value, name):
        if not isinstance(value, (list, tuple)):
            raise ValueError(f"{name} requires a sequence of integers")
        return [_integer(item, name) for item in value]

    # Decode only documented integer fields, leaving booleans and ignored
    # metadata untouched.  In particular, no arbitrary string is interpreted
    # as an integer merely because it appears inside the proposed certificate.
    try:
        if optimization.get("feasible") is False:
            obstruction = optimization["obstruction"]
            if not isinstance(obstruction, dict):
                return False
            decoded = {
                "feasible": False,
                "obstruction": {
                    "multipliers": integers(obstruction["multipliers"], "multipliers"),
                    "residue": _integer(obstruction["residue"], "obstruction.residue"),
                },
            }
        elif optimization.get("feasible") is True:
            dual_rows = optimization["dual_rows"]
            if not isinstance(dual_rows, (list, tuple)):
                return False
            decoded = {
                "feasible": True,
                "minimum_components": _integer(optimization["minimum_components"],
                                               "minimum_components"),
                "parameters": integers(optimization["parameters"], "parameters"),
                "holonomies": integers(optimization["holonomies"], "holonomies"),
                "dual_rows": [integers(row, "dual row") for row in dual_rows],
            }
            if "connected_member_exists" in optimization:
                decoded["connected_member_exists"] = optimization["connected_member_exists"]
        else:
            return False
    except (KeyError, TypeError, ValueError):
        return False

    if decoded["feasible"] is False:
        return verify_infeasibility_certificate(
            compiled["modulus"], compiled["matrix"], compiled["rhs"], decoded,
            variable_count=compiled["variables"], check=check)
    return verify_optimality_certificate(
        compiled["modulus"], compiled["constant"], compiled["linear"],
        compiled["matrix"], compiled["rhs"], decoded,
        variable_count=compiled["variables"], check=check)


def main():
    import argparse
    import json
    from pathlib import Path
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    arguments = parser.parse_args()
    raw = json.loads(arguments.input.read_text())
    print(json.dumps(json_safe(optimize_cover_family(raw)), indent=2))


if __name__ == "__main__":
    main()
