#!/usr/bin/env python3
"""Independently verify the printed residuals, expansion, and report metrics.

No producer or other project module is imported. The accepted TeX is a
deliberately small grammar: numbered BEGIN/END RESIDUAL comments, align*
environments, the specified R_{j} ={}& and &{} prefixes, line breaks,
integer coefficients, x_{i}, x_{i}^{2}, juxtaposition, and explicit signs.
Whitespace and the TeX thin-space command \\, are allowed between tokens.
The optional exact outer layout wrapper is {\\small followed by
\\setlength{\\jot}{2pt}, optionally then \\allowdisplaybreaks[0],
with its closing brace after the last residual.
Unknown TeX, duplicate monomials, zero terms, and nonquadratic rows fail.

Usage:
    python3 code/check_printed_equation.py [PACKAGE_ROOT] [--receipt FILE]

PACKAGE_ROOT defaults to the directory above this script's directory.
Built-in negative controls are always run, including under python -O.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import sys


class VerificationError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def is_integer(value):
    return type(value) is int


def unique_json_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON object key: " + repr(key))
        result[key] = value
    return result


def json_from_text(text):
    return json.loads(text, object_pairs_hook=unique_json_object)


def check_sparse_terms(terms, nvars, max_degree, where):
    require(isinstance(terms, list) and terms, where + ": empty/non-list terms")
    result = {}
    for position, item in enumerate(terms):
        label = where + ", term " + str(position)
        require(isinstance(item, list) and len(item) == 2, label + ": malformed term")
        coefficient, monomial = item
        require(is_integer(coefficient) and coefficient != 0,
                label + ": coefficient must be a nonzero integer")
        require(isinstance(monomial, list), label + ": monomial must be a list")
        require(all(is_integer(i) and 0 <= i < nvars for i in monomial),
                label + ": variable index out of range or nonintegral")
        require(len(monomial) <= max_degree, label + ": degree exceeds bound")
        require(monomial == sorted(monomial), label + ": noncanonical monomial order")
        key = tuple(monomial)
        require(key not in result, label + ": duplicate monomial")
        result[key] = coefficient
    return result


def skip_space(text, position):
    while position < len(text):
        if text[position].isspace():
            position += 1
        elif text.startswith(r"\,", position):
            position += 2
        else:
            break
    return position


INTEGER_TOKEN = re.compile(r"(?:0|[1-9][0-9]*)")
VARIABLE_TOKEN = re.compile(r"x_\{(0|[1-9][0-9]*)\}(?:\^\{(2)\})?")


def parse_polynomial(text, nvars, where):
    position = skip_space(text, 0)
    result = {}
    first = True
    while position < len(text):
        sign = 1
        if text[position] in "+-":
            sign = -1 if text[position] == "-" else 1
            position = skip_space(text, position + 1)
        else:
            require(first, where + ": missing explicit sign between monomials")
        coefficient = None
        match = INTEGER_TOKEN.match(text, position)
        if match:
            coefficient = int(match.group())
            position = skip_space(text, match.end())
        factors = []
        while True:
            match = VARIABLE_TOKEN.match(text, position)
            if not match:
                break
            index = int(match.group(1))
            require(index < nvars, where + ": printed variable index out of range")
            factors.extend([index] * (2 if match.group(2) else 1))
            position = skip_space(text, match.end())
        require(coefficient is not None or factors,
                where + ": expected integer or variable near " + repr(text[position:position+45]))
        if coefficient is None:
            coefficient = 1
        require(coefficient != 0, where + ": explicit zero monomial is not canonical")
        require(len(factors) <= 2, where + ": printed residual degree exceeds two")
        monomial = tuple(sorted(factors))
        require(monomial not in result, where + ": duplicate printed monomial")
        result[monomial] = sign * coefficient
        first = False
        if position < len(text):
            require(text[position] in "+-",
                    where + ": unauthorized token near " + repr(text[position:position+45]))
    require(result, where + ": empty printed polynomial")
    return result


BEGIN_ROW = re.compile(r"% BEGIN RESIDUAL (0|[1-9][0-9]*)")
END_ROW = re.compile(r"% END RESIDUAL (0|[1-9][0-9]*)")
FIRST_LINE = re.compile(r"R_\{(0|[1-9][0-9]*)\}\s*=\{\}\s*&\s*(.*)")
CONTINUATION = re.compile(r"&\{\}\s*(.*)")


def parse_printed_rows(text, nvars, nrows):
    require(not any(ord(c) < 32 and c not in "\n\r\t" for c in text),
            "Printed TeX contains an unauthorized control character")
    lines = text.splitlines()
    rows = []
    position = 0
    layout_opened = False
    layout_closed = False
    while position < len(lines):
        line = lines[position].strip()
        if not line:
            position += 1
            continue
        if line.startswith("%") and "BEGIN RESIDUAL" not in line and "END RESIDUAL" not in line:
            position += 1
            continue
        if line == r"{\small":
            require(not rows and not layout_opened, "Misplaced or repeated outer layout wrapper")
            require(position + 1 < len(lines)
                    and lines[position+1].strip() == r"\setlength{\jot}{2pt}",
                    "Unauthorized outer layout command")
            layout_opened = True
            position += 2
            if position < len(lines) and lines[position].strip() == r"\allowdisplaybreaks[0]":
                position += 1
            continue
        if line == "}":
            require(layout_opened and not layout_closed and len(rows) == nrows,
                    "Misplaced closing layout brace")
            layout_closed = True
            position += 1
            continue
        require(not layout_closed, "Material after the closed residual layout")
        match = BEGIN_ROW.fullmatch(line)
        require(match is not None, "Expected BEGIN RESIDUAL at line " + str(position+1))
        index = int(match.group(1))
        require(index == len(rows), "Missing, duplicated, or out-of-order printed residual " + str(index))
        position += 1
        require(position < len(lines) and lines[position].strip() == r"\begin{align*}",
                "Residual " + str(index) + ": expected align* environment")
        position += 1
        segments = []
        line_breaks = []
        while position < len(lines) and lines[position].strip() != r"\end{align*}":
            line = lines[position].strip()
            if not segments:
                match = FIRST_LINE.fullmatch(line)
                require(match is not None, "Residual " + str(index) + ": malformed first alignment line")
                require(int(match.group(1)) == index, "Printed row label disagrees with marker")
                segment = match.group(2)
            else:
                match = CONTINUATION.fullmatch(line)
                require(match is not None, "Residual " + str(index) + ": unauthorized continuation wrapper")
                segment = match.group(1)
            segment = segment.rstrip()
            has_break = segment.endswith(r"\\")
            if has_break:
                segment = segment[:-2].rstrip()
            require(segment, "Residual " + str(index) + ": empty alignment line")
            segments.append(segment)
            line_breaks.append(has_break)
            position += 1
        require(segments and position < len(lines), "Residual " + str(index) + ": unterminated alignment")
        require(all(line_breaks[:-1]), "Residual " + str(index) + ": missing TeX line break")
        position += 1
        require(position < len(lines), "Residual " + str(index) + ": missing END marker")
        match = END_ROW.fullmatch(lines[position].strip())
        require(match is not None and int(match.group(1)) == index,
                "Residual " + str(index) + ": incorrect END marker")
        position += 1
        rows.append(parse_polynomial("\n".join(segments), nvars, "Printed residual " + str(index)))
    require(len(rows) == nrows, "Wrong number of printed residuals")
    require(not layout_opened or layout_closed, "Unclosed outer residual layout")
    return rows


def same_polynomial(actual, expected, where):
    if actual == expected:
        return
    differences = sorted(set(actual) | set(expected), key=lambda m: (len(m), m))
    for monomial in differences:
        if actual.get(monomial, 0) != expected.get(monomial, 0):
            raise VerificationError(
                where + ": coefficient mismatch at " + repr(monomial)
                + "; actual=" + str(actual.get(monomial, 0))
                + ", expected=" + str(expected.get(monomial, 0)))
    raise VerificationError(where + ": polynomial representation mismatch")


def collect_squares(rows):
    collected = {}
    for row in rows:
        items = list(row.items())
        for i, (left_monomial, left_coefficient) in enumerate(items):
            for j in range(i, len(items)):
                right_monomial, right_coefficient = items[j]
                monomial = tuple(sorted(left_monomial + right_monomial))
                coefficient = left_coefficient * right_coefficient * (1 if i == j else 2)
                collected[monomial] = collected.get(monomial, 0) + coefficient
    return {monomial: coefficient for monomial, coefficient in collected.items() if coefficient}


METRIC_ALIASES = {
    "variables": "variables",
    "rows": "rows",
    "residuals": "rows",
    "degree": "degree",
    "monomials": "monomials",
    "collected_terms": "monomials",
    "height": "height",
    "coefficient_height": "height",
    "row_height": "row_height",
    "residual_coefficient_height": "row_height",
    "residual_terms": "residual_terms",
}


def check_metrics(supplied, actual):
    require(isinstance(supplied, dict), "Metrics must be a JSON object")
    covered = set()
    for key, value in supplied.items():
        if key in ("schema", "description"):
            require(isinstance(value, str), "Metric metadata must be a string")
            continue
        if key == "domain":
            require(value == "unrestricted integers", "Metrics domain mismatch")
            continue
        require(key in METRIC_ALIASES, "Unrecognized metric key: " + key)
        target = METRIC_ALIASES[key]
        require(is_integer(value) and value == actual[target], "Incorrect metric: " + key)
        covered.add(target)
    require({"variables", "rows", "degree", "monomials", "height"} <= covered,
            "Metrics omit one or more required counts")


MACRO_NAMES = ("NV", "NR", "NT", "Height", "LastVar", "LastRow")
MACRO_LINE = re.compile(r"\\newcommand\s*\{\s*\\([A-Za-z]+)\s*\}\s*\{(.*)\}\s*")


def check_macros(text, metrics):
    expected = {
        "NV": metrics["variables"],
        "NR": metrics["rows"],
        "NT": metrics["monomials"],
        "Height": metrics["height"],
        "LastVar": metrics["variables"] - 1,
        "LastRow": metrics["rows"] - 1,
    }
    seen = {}
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("%"):
            continue
        match = MACRO_LINE.fullmatch(line)
        require(match is not None, "Unauthorized metrics.tex line")
        name, body = match.groups()
        require(name in expected, "Unrecognized numeric report macro: " + name)
        require(name not in seen, "Duplicate report macro: " + name)
        body = re.sub(r"\s+", "", body.replace(r"\,", "").replace("{,}", ","))
        require(re.fullmatch(r"(?:[0-9]+|[0-9]{1,3}(?:,[0-9]{3})+)", body) is not None,
                "Nonliteral numeric report macro: " + name)
        value = int(body.replace(",", ""))
        require(value == expected[name], "Incorrect report metric macro: " + name)
        seen[name] = value
    require(set(seen) == set(expected), "Missing numeric report macro")
    return seen


def verify_bundle(bundle):
    equation = bundle["equation"]
    require(isinstance(equation, dict), "Equation must be a JSON object")
    require(equation.get("domain") == "unrestricted integers", "Wrong equation domain")
    require(equation.get("polynomial") == "sum(square(row) for row in residuals)",
            "Wrong polynomial interpretation")
    variables = equation.get("variables")
    residuals = equation.get("residuals")
    require(isinstance(variables, list) and variables, "Missing variable list")
    require(isinstance(residuals, list) and residuals, "Missing residual list")
    nvars, nrows = len(variables), len(residuals)
    rows = []
    for index, row in enumerate(residuals):
        require(isinstance(row, dict) and "terms" in row, "Malformed source residual")
        rows.append(check_sparse_terms(row["terms"], nvars, 2, "Source residual " + str(index)))
    used = {i for row in rows for monomial in row for i in monomial}
    require(used == set(range(nvars)), "Equation declares unused variables")
    printed = parse_printed_rows(bundle["tex"], nvars, nrows)
    for index, (actual, expected) in enumerate(zip(printed, rows)):
        same_polynomial(actual, expected, "Printed residual " + str(index))
    printed_used = {i for row in printed for monomial in row for i in monomial}
    require(printed_used == set(range(nvars)), "Printed equation omits declared variables")
    expansion = collect_squares(printed)
    require(expansion, "Collected polynomial is zero")
    expanded_file = bundle["expanded"]
    require(isinstance(expanded_file, dict), "Expansion must be a JSON object")
    require(is_integer(expanded_file.get("variables")) and expanded_file["variables"] == nvars,
            "Expanded polynomial variable count mismatch")
    supplied_expansion = check_sparse_terms(expanded_file.get("terms"), nvars, 4, "Expanded polynomial")
    same_polynomial(supplied_expansion, expansion, "Collected sum of printed squares")
    metrics = {
        "variables": nvars,
        "rows": nrows,
        "degree": max(map(len, expansion)),
        "monomials": len(expansion),
        "height": max(map(abs, expansion.values())),
        "row_height": max(abs(c) for row in rows for c in row.values()),
        "residual_terms": sum(map(len, rows)),
    }
    require(metrics["degree"] == 4, "Principal polynomial is not quartic")
    check_metrics(bundle["metrics"], metrics)
    macros = check_macros(bundle["macros"], metrics)
    return {"status": "PASS", "metrics": metrics, "report_macros": macros}


def control_polynomial_text(row):
    """Tiny canonical formatter used only to manufacture negative controls."""
    pieces = []
    for monomial, coefficient in sorted(row.items(), key=lambda item: (len(item[0]), item[0])):
        sign = "-" if coefficient < 0 else "+"
        factors = " ".join("x_{" + str(i) + "}" for i in monomial)
        magnitude = str(abs(coefficient)) if not factors or abs(coefficient) != 1 else ""
        pieces.append(sign + magnitude + factors)
    return " ".join(pieces)


def replace_first_printed_row(text, expression=None, drop=False):
    lines = text.splitlines()
    begin = next((i for i, line in enumerate(lines) if line.strip() == "% BEGIN RESIDUAL 0"), None)
    end = next((i for i, line in enumerate(lines) if line.strip() == "% END RESIDUAL 0"), None)
    require(begin is not None and end is not None and begin < end, "Cannot construct printed negative control")
    replacement = [] if drop else [
        "% BEGIN RESIDUAL 0", r"\begin{align*}", r"R_{0} ={}& " + expression,
        r"\end{align*}", "% END RESIDUAL 0",
    ]
    return "\n".join(lines[:begin] + replacement + lines[end+1:]) + "\n"


def run_mutation_controls(bundle):
    source = bundle["equation"]
    nvars = len(source["variables"])
    first = check_sparse_terms(source["residuals"][0]["terms"], nvars, 2, "Control source row")
    first_monomial = next(iter(first))
    changed = dict(first)
    changed[first_monomial] += 1 if changed[first_monomial] > 0 else -1
    ordinary = control_polynomial_text(first)
    duplicate = control_polynomial_text({first_monomial: first[first_monomial]})
    cases = []

    def changed_tex(name, tex):
        mutated = dict(bundle)
        mutated["tex"] = tex
        cases.append((name, mutated))

    changed_tex("printed coefficient changed",
                replace_first_printed_row(bundle["tex"], control_polynomial_text(changed)))
    changed_tex("printed residual dropped", replace_first_printed_row(bundle["tex"], drop=True))
    changed_tex("printed monomial duplicated",
                replace_first_printed_row(bundle["tex"], ordinary + " " + duplicate))
    changed_tex("printed variable out of range",
                replace_first_printed_row(bundle["tex"], ordinary + " +x_{" + str(nvars) + "}"))
    changed_tex("printed cubic term",
                replace_first_printed_row(bundle["tex"], ordinary + r" +x_{0}^{2} x_{0}"))
    changed_tex("unauthorized TeX command", r"\input{untrusted}" + "\n" + bundle["tex"])
    changed_tex("printed row label changed", bundle["tex"].replace("R_{0}", "R_{1}", 1))

    mutated = copy.deepcopy(bundle)
    coefficient = mutated["expanded"]["terms"][0][0]
    mutated["expanded"]["terms"][0][0] = coefficient + (1 if coefficient > 0 else -1)
    cases.append(("expanded coefficient changed", mutated))
    mutated = copy.deepcopy(bundle)
    mutated["equation"]["residuals"][0]["terms"].append(copy.deepcopy(source["residuals"][0]["terms"][0]))
    cases.append(("source monomial duplicated", mutated))
    mutated = copy.deepcopy(bundle)
    mutated["equation"]["variables"].append({"name": "unused-control-coordinate"})
    cases.append(("unused variable declared", mutated))
    mutated = copy.deepcopy(bundle)
    mutated["metrics"]["variables"] = nvars + 1
    cases.append(("metric count changed", mutated))
    mutated = dict(bundle)
    mutated["macros"] = bundle["macros"] + r"\newcommand{\NV}{0}" + "\n"
    cases.append(("report macro redefined", mutated))
    mutated = dict(bundle)
    mutated["macros"] = re.sub(
        r"\\newcommand\s*\{\s*\\NV\s*\}\s*\{[^\n]*\}",
        lambda match: r"\newcommand{\NV}{" + str(nvars+1) + "}",
        bundle["macros"], count=1)
    cases.append(("report macro value changed", mutated))

    receipt = []
    for name, mutated in cases:
        try:
            verify_bundle(mutated)
        except VerificationError as error:
            receipt.append({"mutation": name, "rejected": True, "reason": str(error)})
        else:
            raise VerificationError("Negative control was accepted: " + name)
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package_root", nargs="?", type=Path,
                        default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--receipt", type=Path, help="Write the complete JSON verification receipt")
    args = parser.parse_args()
    root = args.package_root.resolve()
    paths = {
        "equation": root / "equations/principal/equation.json",
        "expanded": root / "equations/principal/expanded_polynomial.json",
        "metrics": root / "equations/principal/metrics.json",
        "tex": root / "report/residuals.tex",
        "macros": root / "report/metrics.tex",
    }
    try:
        raw = {key: path.read_bytes() for key, path in paths.items()}
        bundle = {
            key: json_from_text(value.decode("utf-8")) if key in ("equation", "expanded", "metrics")
            else value.decode("utf-8")
            for key, value in raw.items()
        }
        receipt = verify_bundle(bundle)
        receipt["schema"] = "independent-printed-equation-audit-v1"
        receipt["mutation_controls"] = run_mutation_controls(bundle)
        receipt["files"] = [
            {"path": str(paths[key].relative_to(root)), "bytes": len(value),
             "sha256": hashlib.sha256(value).hexdigest()}
            for key, value in raw.items()
        ]
        receipt["verification_scope"] = [
            "Strict printed quadratic grammar and exact numbered residual list.",
            "Every printed coefficient equals the machine-readable source coefficient.",
            "All declared variables occur; all indices and residual degrees are valid.",
            "Independent complete collection of the sum of residual squares.",
            "Every collected coefficient, supplied metric, and six report macros checked.",
            "No producer imports, removable assertions, or proof-assistant claims.",
        ]
        if args.receipt:
            args.receipt.parent.mkdir(parents=True, exist_ok=True)
            args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(json.dumps({
            "status": "PASS", **receipt["metrics"],
            "report_macros_checked": len(receipt["report_macros"]),
            "mutation_controls_rejected": len(receipt["mutation_controls"]),
        }, sort_keys=True))
        return 0
    except (VerificationError, OSError, UnicodeError, json.JSONDecodeError) as error:
        print(json.dumps({"status": "FAIL", "reason": str(error)}, sort_keys=True))
        return 1


if __name__ == "__main__":
    sys.exit(main())
