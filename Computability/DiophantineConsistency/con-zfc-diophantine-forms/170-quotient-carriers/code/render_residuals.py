#!/usr/bin/env python3
"""Render and check the complete P217 quadratic-residual appendix.

Only the Python standard library is used. Paths default relative to this
script, so generation and --check work from any current directory. The
renderer also parses its generated TeX back into all signed coefficients
and monomials before writing any artifact.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SOURCE = ROOT / "equations" / "P217" / "equation.json"
DEFAULT_REPORT = ROOT / "report"
FONT_SIZE_PT = 10
LINE_BUDGET_PT = 410


def require(condition: bool, detail: str) -> None:
    if not condition:
        raise ValueError(detail)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_bytes(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def read_source(path: Path) -> tuple[dict, bytes]:
    raw = path.read_bytes()
    equation = json.loads(raw)
    n = len(equation["variables"])
    rows = equation["residuals"]
    require(n == 217 and len(rows) == 154, "Expected the canonical 217-coordinate, 154-residual source")
    require(equation.get("domain") == "unrestricted integers", "Unexpected source domain")
    for j, row in enumerate(rows):
        require(isinstance(row.get("terms"), list) and bool(row["terms"]), f"Empty or missing residual R_{j}")
        seen = set()
        for item in row["terms"]:
            require(isinstance(item, list) and len(item) == 2, f"Malformed term in R_{j}")
            coefficient, monomial = item
            require(type(coefficient) is int and coefficient != 0, f"Nonintegral or zero coefficient in R_{j}")
            require(isinstance(monomial, list) and len(monomial) <= 2, f"Nonquadratic monomial in R_{j}")
            require(all(type(i) is int and 0 <= i < n for i in monomial), f"Invalid coordinate in R_{j}")
            require(monomial == sorted(monomial), f"Unsorted monomial in R_{j}")
            key = tuple(monomial)
            require(key not in seen, f"Duplicate monomial in R_{j}")
            seen.add(key)
    return equation, raw


def tex_unsigned_term(coefficient: int, monomial: list[int]) -> str:
    magnitude = abs(coefficient)
    if not monomial:
        return str(magnitude)
    if len(monomial) == 2 and monomial[0] == monomial[1]:
        product = rf"x_{{{monomial[0]}}}^{{2}}"
    else:
        product = "".join(rf"x_{{{i}}}" for i in monomial)
    return (str(magnitude) if magnitude != 1 else "") + product


def text_unsigned_term(coefficient: int, monomial: list[int]) -> str:
    magnitude = abs(coefficient)
    if not monomial:
        return str(magnitude)
    if len(monomial) == 2 and monomial[0] == monomial[1]:
        product = f"x_{monomial[0]}^2"
    else:
        product = "*".join(f"x_{i}" for i in monomial)
    return (f"{magnitude}*" if magnitude != 1 else "") + product


def estimated_width_pt(coefficient: int, monomial: list[int], first: bool) -> float:
    """Conservative widths for 10-point Latin Modern math.

    Estimates deliberately exceed ordinary glyph/spacing widths: 6 pt per
    full-size numeral, 4 pt per script numeral, 6.5 pt for x, and 17 pt for
    a binary sign with its surrounding spacing. The 410-pt right-hand-side
    budget leaves over 40 pt for the left label and margin within 6.7 in.
    No special font-measurement or TeX executable is required.
    """
    magnitude = abs(coefficient)
    width = (0.0 if coefficient > 0 else 9.0) if first else 17.0
    if not monomial or magnitude != 1:
        width += 6.0 * len(str(magnitude))
    if len(monomial) == 2 and monomial[0] == monomial[1]:
        width += 7.5 + 4.0 * len(str(monomial[0])) + 4.5
    else:
        width += sum(7.5 + 4.0 * len(str(i)) for i in monomial)
    return width


def split_row(terms: list[list]) -> tuple[list[list[list]], list[float]]:
    chunks: list[list[list]] = []
    widths: list[float] = []
    current: list[list] = []
    width = 0.0
    for index, term in enumerate(terms):
        coefficient, monomial = term
        # A continuation retains its binary + or - sign, even when it is
        # the first term on its physical line.
        estimate = estimated_width_pt(coefficient, monomial, first=index == 0)
        require(estimate <= LINE_BUDGET_PT, "A single term exceeds the line budget")
        if current and width + estimate > LINE_BUDGET_PT:
            chunks.append(current)
            widths.append(width)
            current, width = [], 0.0
        current.append(term)
        width += estimate
    chunks.append(current)
    widths.append(width)
    return chunks, widths


def signed_expression(terms: list[list], formatter, first_term: bool) -> str:
    rendered = []
    for index, (coefficient, monomial) in enumerate(terms):
        if first_term and index == 0:
            sign = "-" if coefficient < 0 else ""
        else:
            sign = "- " if coefficient < 0 else "+ "
        rendered.append(sign + formatter(coefficient, monomial))
    return " ".join(rendered)


def parse_tex_rows(tex: str) -> list[list[list]]:
    """Recover the displayed signed monomials, independent of formatting."""
    result = []
    blocks = re.findall(r"% BEGIN_RESIDUAL ([0-9]+)\n(.*?)% END_RESIDUAL \1\n", tex, flags=re.S)
    for expected, (label, body) in enumerate(blocks):
        require(int(label) == expected, "Missing, duplicated, or reordered residual label")
        lines = body.splitlines()
        require(lines and lines[0].startswith(rf"R_{{{expected}}} ={{}}&"), "Wrong displayed residual label")
        expression = "".join(lines)
        expression = expression.replace(rf"R_{{{expected}}} ={{}}&", "", 1)
        expression = re.sub(r"\\\\(?:\*|\[[0-9]+pt\])?", "", expression)
        expression = expression.replace("&", "").replace("{}", "")
        expression = re.sub(r"\s+", "", expression)
        parsed = []
        pieces = re.findall(r"[+-]?[^+-]+", expression)
        require("".join(pieces) == expression, "Unparsed TeX expression")
        for piece in pieces:
            sign = -1 if piece.startswith("-") else 1
            body = piece[1:] if piece[:1] in "+-" else piece
            coefficient_match = re.match(r"[0-9]+", body)
            if coefficient_match:
                coefficient = int(coefficient_match.group())
                body = body[len(coefficient_match.group()):]
            else:
                coefficient = 1
                require(bool(body), "Empty monomial")
            factors = list(re.finditer(r"x_\{([0-9]+)\}(?:\^\{([0-9]+)\})?", body))
            require("".join(m.group() for m in factors) == body, "Unexpected TeX token in residual")
            monomial = []
            for match in factors:
                exponent = int(match.group(2) or "1")
                require(exponent in (1, 2), "Unexpected displayed exponent")
                monomial.extend([int(match.group(1))] * exponent)
            parsed.append([sign * coefficient, monomial])
        result.append(parsed)
    return result


def render(equation: dict, source_raw: bytes) -> dict[str, bytes]:
    rows = equation["residuals"]
    tex = [
        "% Generated by code/render_residuals.py; edit the JSON source, not this file.",
        "% Exact source SHA256: " + sha256(source_raw),
        "% Ten-point math; conservative 410-pt right-hand-side wrapping.",
        "% Starred line breaks keep each individual residual together.",
        r"\begingroup",
        r"\fontsize{10}{12}\selectfont",
        r"\allowdisplaybreaks[4]",
        r"\setlength{\jot}{2pt}",
        r"\begin{align*}",
    ]
    plain = [
        "P217 quadratic residuals over independent integer coordinates x_0,...,x_216.",
        "P217 = R_0^2 + ... + R_153^2.",
        "Source SHA256: " + sha256(source_raw),
        "",
    ]
    row_metadata = []
    for j, row in enumerate(rows):
        chunks, widths = split_row(row["terms"])
        tex.append(f"% BEGIN_RESIDUAL {j}")
        for index, chunk in enumerate(chunks):
            prefix = rf"R_{{{j}}} ={{}}& " if index == 0 else "&{} "
            expression = signed_expression(chunk, tex_unsigned_term, first_term=index == 0)
            if index + 1 < len(chunks):
                suffix = r" \\*"
            elif j + 1 < len(rows):
                suffix = r" \\[4pt]"
            else:
                suffix = ""
            tex.append(prefix + expression + suffix)
        tex.append(f"% END_RESIDUAL {j}")
        plain.append(f"R_{j} = " + signed_expression(row["terms"], text_unsigned_term, first_term=True))
        row_metadata.append({
            "index": j,
            "source_label": row["label"],
            "terms": len(row["terms"]),
            "display_lines": len(chunks),
            "maximum_estimated_line_width_pt": max(widths),
            "canonical_terms_sha256": sha256(canonical_bytes(row["terms"])),
        })
    tex.extend([r"\end{align*}", r"\endgroup", ""])
    tex_text = "\n".join(tex)
    recovered = parse_tex_rows(tex_text)
    require(recovered == [r["terms"] for r in rows], "Displayed TeX does not reconstruct every source term exactly")
    tex_bytes = tex_text.encode("utf-8")
    text_bytes = ("\n".join(plain) + "\n").encode("utf-8")
    manifest = {
        "schema": "complete-quadratic-residual-display-v1",
        "source": "equations/P217/equation.json",
        "source_sha256": sha256(source_raw),
        "variables": len(equation["variables"]),
        "residuals": len(rows),
        "terms": sum(len(r["terms"]) for r in rows),
        "maximum_residual_degree": max(len(m) for r in rows for _, m in r["terms"]),
        "font_size_pt": FONT_SIZE_PT,
        "line_budget_pt": LINE_BUDGET_PT,
        "display_lines": sum(r["display_lines"] for r in row_metadata),
        "maximum_estimated_line_width_pt": max(r["maximum_estimated_line_width_pt"] for r in row_metadata),
        "tex_sha256": sha256(tex_bytes),
        "text_sha256": sha256(text_bytes),
        "all_displayed_terms_reparsed_exactly": True,
        "rows": row_metadata,
    }
    return {
        "residuals.tex": tex_bytes,
        "residuals.txt": text_bytes,
        "residuals_manifest.json": (json.dumps(manifest, indent=2) + "\n").encode("utf-8"),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--report-dir", type=Path, default=DEFAULT_REPORT)
    parser.add_argument("--check", action="store_true", help="Regenerate in memory and compare all three existing files")
    args = parser.parse_args()
    equation, raw = read_source(args.source)
    outputs = render(equation, raw)
    if args.check:
        for name, expected in outputs.items():
            path = args.report_dir / name
            require(path.is_file(), f"Missing generated artifact: {path}")
            require(path.read_bytes() == expected, f"Generated artifact differs: {path}")
        # Parse the actual existing TeX too, independently of its hash.
        actual = (args.report_dir / "residuals.tex").read_text(encoding="utf-8")
        require(parse_tex_rows(actual) == [r["terms"] for r in equation["residuals"]], "Existing TeX differs mathematically")
    else:
        args.report_dir.mkdir(parents=True, exist_ok=True)
        for name, data in outputs.items():
            (args.report_dir / name).write_bytes(data)
    manifest = json.loads(outputs["residuals_manifest.json"])
    print(json.dumps({
        "result": "PASS" if args.check else "GENERATED",
        "variables": manifest["variables"],
        "residuals": manifest["residuals"],
        "terms": manifest["terms"],
        "display_lines": manifest["display_lines"],
        "font_size_pt": manifest["font_size_pt"],
        "maximum_estimated_line_width_pt": manifest["maximum_estimated_line_width_pt"],
        "all_terms_reparsed_exactly": True,
        "tex_sha256": manifest["tex_sha256"],
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, KeyError, TypeError, OSError, json.JSONDecodeError) as error:
        print(f"Residual rendering failed: {error}", file=sys.stderr)
        sys.exit(1)
