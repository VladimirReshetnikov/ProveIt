#!/usr/bin/env python3
"""Independently certify simultaneous time and space via mapped boundary supports.

This only imports the sibling independent support reconstructor. It uses no
optimizer, upstream packet, or scratch file. Integer arithmetic checks every
new mixed pair inequality; exact conservation is checked for every support.
"""
from argparse import ArgumentParser
from fractions import Fraction
from pathlib import Path
import json
import independent_audit as audit

ROOT = Path(__file__).resolve().parents[1]


def boundary_supports(rows):
    boundaries, mappings = [], []
    for index, row in enumerate(rows):
        if set(row) <= {0, 1400007}:
            boundary = tuple(int(value != 0) for value in row)
            if boundary not in boundaries:
                boundaries.append(boundary)
                mappings.append(index)
    audit.require(len(boundaries) == 17, "Unexpected boundary support count")
    return boundaries, mappings


def verify_joint(certificate, time_result, numerator=21, denominator=20):
    r, q = certificate["r"], certificate["q"]
    scale = certificate["support_scale"]
    weight_denominator = certificate["mixing_denominator"]
    potential_denominator = certificate["potential_denominator"]
    audit.require((r, q, scale, weight_denominator, potential_denominator) ==
                  (10, 9, 1400000, 100000, 10 ** 12), "Unexpected proof model")
    common = (q - 1) * weight_denominator ** 2 * scale ** 2
    audit.require(common * denominator ** 2 % potential_denominator == 0,
                  "Incompatible augmented denominator")
    times = [audit.fresh_supports(r, plan) for plan in certificate["plans"]]
    mappings, rows = [], []
    for menu in times:
        boundaries, mapping = boundary_supports(menu)
        mappings.append(mapping)
        rows.append([tuple(denominator * value for value in row) for row in menu]
                    + [tuple(numerator * scale * value for value in boundary)
                       for boundary in boundaries])
    potentials = {}
    for edge, pair in enumerate(certificate["pairs"]):
        for plan in pair:
            original = certificate["potentials"][f"{edge},{plan}"]
            potentials[edge, plan] = original + [original[index]
                                                for index in mappings[plan]]
    for plan in range(q):
        incident = [edge for edge, pair in enumerate(certificate["pairs"])
                    if plan in pair]
        for support in range(89):
            audit.require(sum(potentials[edge, plan][support]
                              for edge in incident) == 0,
                          "Augmented potential conservation failed")
    norms = [[audit.inner(row, row) for row in menu] for menu in rows]
    receipts, minimum_margin = [], None
    for edge, (left, right) in enumerate(certificate["pairs"]):
        wi = certificate["mixing_weights"][left]
        wj = certificate["mixing_weights"][right]
        target = time_result["pair_receipts"][edge]["maximum"] * denominator ** 2

        def cost(h, k):
            return (wi * wi * norms[left][h] + wj * wj * norms[right][k]
                    + 2 * (q - 1) * wi * wj * audit.inner(rows[left][h], rows[right][k])
                    + (potentials[edge, left][h] + potentials[edge, right][k])
                    * (common * denominator ** 2 // potential_denominator))

        maximum, h, k = max((cost(h, k), h, k)
                            for h in range(89) for k in range(89)
                            if h >= 72 or k >= 72)
        audit.require(maximum <= target, "Mixed support exceeds time certificate")
        margin = target - maximum
        minimum_margin = margin if minimum_margin is None else min(minimum_margin, margin)
        receipts.append({"pair": [left, right], "target": target,
                         "mixed_maximum": maximum, "witness": [h, k], "margin": margin})
    beta_squared = Fraction(certificate["beta_squared"])
    time_interval = audit.coefficient_bounds([2 * beta_squared / Fraction(301, 20000)])
    space_interval = tuple(value * denominator / numerator for value in time_interval)
    level_one = audit.coefficient_bounds([Fraction(50304, 20111)])
    level_two = audit.coefficient_bounds([
        2 * Fraction(632, 1225) * Fraction(2, 65) ** 2 / Fraction(1549, 324000)])
    audit.require(max(level_one[1], level_two[1]) < space_interval[0],
                  "Descendant storage exceeds root bound")
    audit.require(time_interval[1] < Fraction(29747, 1000), "Time bound 29.747 failed")
    audit.require(space_interval[1] < Fraction(28330, 1000), "Space bound 28.330 failed")
    return {"status": "PASS", "rho": str(Fraction(numerator, denominator)),
            "time_coefficient_display_only": float(time_interval[0]),
            "space_coefficient_display_only": float(space_interval[0]),
            "time_rational_interval": audit.short_interval(time_interval),
            "space_rational_interval": audit.short_interval(space_interval),
            "safe_eventual_time_coefficient": "29.747",
            "safe_eventual_space_coefficient": "28.330",
            "augmented_conservation_equalities_checked": q * 89,
            "mixed_pair_choices_checked": 36 * (89 * 89 - 72 * 72),
            "boundary_to_IO_support_maps": mappings,
            "minimum_mixed_margin": minimum_margin, "pair_receipts": receipts,
            "descendant_space_display_only": [float(level_one[0]), float(level_two[0])]}


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path,
                        default=ROOT / "data" / "support_consistency_certificate.json")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    certificate = json.loads(args.certificate.read_text())
    time_result = audit.verify_certificate(certificate)
    result = verify_joint(certificate, time_result)
    try:
        verify_joint(certificate, time_result, numerator=6, denominator=5)
    except ValueError as error:
        audit.require(str(error) == "Mixed support exceeds time certificate",
                      "Unexpected excessive-rho rejection")
    else:
        raise RuntimeError("Invalid rho 6/5 was accepted")
    result["negative_controls"] = ["rho 6/5 exceeds fixed time certificate"]
    output = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output is None:
        print(output, end="")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output)


if __name__ == "__main__":
    main()
