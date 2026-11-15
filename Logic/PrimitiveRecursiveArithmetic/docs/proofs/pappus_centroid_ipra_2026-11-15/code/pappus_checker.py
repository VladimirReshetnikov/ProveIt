#!/usr/bin/env python3
"""Exact finite-certificate checker for the Pappus iPRA package.

The checker deliberately uses only Python's standard library and exact
``fractions.Fraction`` arithmetic.  It verifies the finite algebraic kernel:

* supplied rational segment lengths satisfy the Pythagorean equation;
* polygonal radial moments and centroid identities are exact;
* rectangular-cell shell coefficients equal radial first moments;
* grid area, moment, and centroid identities are exact;
* optional expected totals in the JSON certificate match the recomputation.

It does *not* verify the regular-polygon convergence, represented-real limit
machinery, or the object-level iPRA derivation.  Those are the Lean obligations
listed in ``FORMALIZATION_PLAN.md``.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable, Sequence


class CertificateError(ValueError):
    """Raised when a certificate is malformed or an identity fails."""


def frac(value: Any, *, field: str) -> Fraction:
    """Parse an integer or a ``p/q`` string as an exact fraction."""
    if isinstance(value, bool):
        raise CertificateError(f"{field}: Boolean is not a rational number")
    if isinstance(value, int):
        return Fraction(value)
    if isinstance(value, str):
        try:
            result = Fraction(value)
        except (ValueError, ZeroDivisionError) as exc:
            raise CertificateError(f"{field}: invalid rational {value!r}") from exc
        return result
    raise CertificateError(
        f"{field}: expected an integer or rational string, got {type(value).__name__}"
    )


def show(q: Fraction) -> str:
    """Canonical human-readable form."""
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


@dataclass(frozen=True)
class Point:
    r: Fraction
    z: Fraction

    @staticmethod
    def parse(obj: Any, *, field: str) -> "Point":
        if not isinstance(obj, dict):
            raise CertificateError(f"{field}: expected an object")
        try:
            r_raw, z_raw = obj["r"], obj["z"]
        except KeyError as exc:
            raise CertificateError(f"{field}: missing key {exc.args[0]!r}") from exc
        point = Point(frac(r_raw, field=f"{field}.r"), frac(z_raw, field=f"{field}.z"))
        if point.r < 0:
            raise CertificateError(f"{field}: radial coordinate must be nonnegative")
        return point


@dataclass(frozen=True)
class Segment:
    start: Point
    end: Point
    length: Fraction

    @staticmethod
    def parse(obj: Any, *, field: str) -> "Segment":
        if not isinstance(obj, dict):
            raise CertificateError(f"{field}: expected an object")
        try:
            start = Point.parse(obj["start"], field=f"{field}.start")
            end = Point.parse(obj["end"], field=f"{field}.end")
            length = frac(obj["length"], field=f"{field}.length")
        except KeyError as exc:
            raise CertificateError(f"{field}: missing key {exc.args[0]!r}") from exc
        if length < 0:
            raise CertificateError(f"{field}: length must be nonnegative")
        segment = Segment(start, end, length)
        dr = end.r - start.r
        dz = end.z - start.z
        if length * length != dr * dr + dz * dz:
            raise CertificateError(
                f"{field}: supplied length {show(length)} fails the Pythagorean equation"
            )
        return segment

    @property
    def moment(self) -> Fraction:
        return (self.start.r + self.end.r) * self.length / 2

    @property
    def sweep_coefficient(self) -> Fraction:
        """Coefficient of the formal circle constant tau."""
        return (self.start.r + self.end.r) * self.length / 2


@dataclass(frozen=True)
class Cell:
    a: Fraction
    b: Fraction
    c: Fraction
    d: Fraction

    @staticmethod
    def parse(obj: Any, *, field: str) -> "Cell":
        if not isinstance(obj, dict):
            raise CertificateError(f"{field}: expected an object")
        try:
            cell = Cell(
                frac(obj["a"], field=f"{field}.a"),
                frac(obj["b"], field=f"{field}.b"),
                frac(obj["c"], field=f"{field}.c"),
                frac(obj["d"], field=f"{field}.d"),
            )
        except KeyError as exc:
            raise CertificateError(f"{field}: missing key {exc.args[0]!r}") from exc
        if cell.a < 0:
            raise CertificateError(f"{field}: a must be nonnegative")
        if cell.a > cell.b:
            raise CertificateError(f"{field}: require a <= b")
        if cell.c > cell.d:
            raise CertificateError(f"{field}: require c <= d")
        return cell

    @property
    def area(self) -> Fraction:
        return (self.b - self.a) * (self.d - self.c)

    @property
    def moment(self) -> Fraction:
        return (self.a + self.b) * self.area / 2

    @property
    def shell_coefficient(self) -> Fraction:
        """Coefficient of tau in the annular-cylinder volume."""
        return (self.b * self.b - self.a * self.a) * (self.d - self.c) / 2

    def overlaps_interior(self, other: "Cell") -> bool:
        radial_overlap = max(self.a, other.a) < min(self.b, other.b)
        axial_overlap = max(self.c, other.c) < min(self.d, other.d)
        return radial_overlap and axial_overlap


def require_list(obj: Any, *, field: str) -> list[Any]:
    if not isinstance(obj, list):
        raise CertificateError(f"{field}: expected a list")
    return obj


def check_expected(section: dict[str, Any], key: str, actual: Fraction) -> None:
    expected_block = section.get("expected", {})
    if not isinstance(expected_block, dict):
        raise CertificateError("expected: expected an object")
    if key in expected_block:
        expected = frac(expected_block[key], field=f"expected.{key}")
        if actual != expected:
            raise CertificateError(
                f"expected.{key}: certificate says {show(expected)}, recomputed {show(actual)}"
            )


def check_surface(section: Any) -> list[str]:
    if not isinstance(section, dict):
        raise CertificateError("surface: expected an object")
    raw_segments = require_list(section.get("segments"), field="surface.segments")
    segments = [
        Segment.parse(obj, field=f"surface.segments[{i}]")
        for i, obj in enumerate(raw_segments)
    ]
    if not segments:
        raise CertificateError("surface.segments: at least one segment is required")

    for i in range(len(segments) - 1):
        if segments[i].end != segments[i + 1].start:
            raise CertificateError(
                f"surface.segments[{i}] and [{i + 1}] are not endpoint-contiguous"
            )

    for i, segment in enumerate(segments):
        if segment.sweep_coefficient != segment.moment:
            raise CertificateError(f"surface.segments[{i}]: segment Pappus identity failed")

    total_length = sum((s.length for s in segments), Fraction(0))
    total_moment = sum((s.moment for s in segments), Fraction(0))
    total_sweep_coeff = sum((s.sweep_coefficient for s in segments), Fraction(0))
    if total_sweep_coeff != total_moment:
        raise CertificateError("surface: finite additivity identity failed")
    if total_length <= 0:
        raise CertificateError("surface: positive total length is required for a centroid")
    centroid = total_moment / total_length
    if total_length * centroid != total_moment:
        raise CertificateError("surface: centroid cancellation identity failed")

    check_expected(section, "length", total_length)
    check_expected(section, "moment", total_moment)
    check_expected(section, "centroid", centroid)
    check_expected(section, "sweep_coefficient", total_sweep_coeff)

    return [
        f"surface segments: {len(segments)}",
        f"surface length: {show(total_length)}",
        f"surface radial moment: {show(total_moment)}",
        f"surface centroid radius: {show(centroid)}",
        f"surface area: tau * {show(total_sweep_coeff)}",
    ]


def check_volume(section: Any) -> list[str]:
    if not isinstance(section, dict):
        raise CertificateError("volume: expected an object")
    raw_cells = require_list(section.get("cells"), field="volume.cells")
    cells = [Cell.parse(obj, field=f"volume.cells[{i}]") for i, obj in enumerate(raw_cells)]
    if not cells:
        raise CertificateError("volume.cells: at least one cell is required")

    for i, cell in enumerate(cells):
        if cell.shell_coefficient != cell.moment:
            raise CertificateError(f"volume.cells[{i}]: shell identity failed")
        for j in range(i):
            if cell.overlaps_interior(cells[j]):
                raise CertificateError(
                    f"volume.cells[{i}] overlaps the interior of volume.cells[{j}]"
                )

    total_area = sum((c.area for c in cells), Fraction(0))
    total_moment = sum((c.moment for c in cells), Fraction(0))
    total_volume_coeff = sum((c.shell_coefficient for c in cells), Fraction(0))
    if total_volume_coeff != total_moment:
        raise CertificateError("volume: finite additivity identity failed")
    if total_area <= 0:
        raise CertificateError("volume: positive total area is required for a centroid")
    centroid = total_moment / total_area
    if total_area * centroid != total_moment:
        raise CertificateError("volume: centroid cancellation identity failed")

    check_expected(section, "area", total_area)
    check_expected(section, "moment", total_moment)
    check_expected(section, "centroid", centroid)
    check_expected(section, "volume_coefficient", total_volume_coeff)

    return [
        f"volume cells: {len(cells)}",
        f"lamina area: {show(total_area)}",
        f"lamina radial moment: {show(total_moment)}",
        f"lamina centroid radius: {show(centroid)}",
        f"swept volume: tau * {show(total_volume_coeff)}",
    ]


def load_json(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise CertificateError(f"cannot read {path}: {exc}") from exc
    except json.JSONDecodeError as exc:
        raise CertificateError(f"{path}: invalid JSON at line {exc.lineno}: {exc.msg}") from exc
    if not isinstance(data, dict):
        raise CertificateError("top level: expected a JSON object")
    return data


def run(path: Path) -> str:
    data = load_json(path)
    schema = data.get("schema")
    if schema != "pappus-finite-certificate-v1":
        raise CertificateError(
            "schema: expected 'pappus-finite-certificate-v1'"
        )
    lines = ["Pappus finite certificate: PASS", f"certificate: {path}"]
    lines.extend(check_surface(data.get("surface")))
    lines.extend(check_volume(data.get("volume")))
    lines.append("all checked identities use exact rational arithmetic")
    return "\n".join(lines)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path, help="JSON certificate to verify")
    args = parser.parse_args(argv)
    try:
        print(run(args.certificate))
    except CertificateError as exc:
        print(f"Pappus finite certificate: FAIL\n{exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
