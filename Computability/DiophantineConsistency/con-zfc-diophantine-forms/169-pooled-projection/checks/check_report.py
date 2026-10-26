#!/usr/bin/env python3
"""Parse the printed TeX appendix back into integer polynomials."""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]

def require(condition, message):
    if not condition:
        raise ValueError(message)

def validate_terms(terms, n, max_degree):
    require(type(terms) is list, "term list")
    out = {}
    for item in terms:
        require(type(item) is list and len(item) == 2, "coefficient/monomial pair")
        c, m = item
        require(type(c) is int and c != 0, "nonzero integer coefficient")
        require(type(m) is list and len(m) <= max_degree, "monomial degree")
        require(all(type(i) is int and 0 <= i < n for i in m), "monomial index")
        require(m == sorted(m), "sorted monomial")
        require(tuple(m) not in out, "unique monomial")
        out[tuple(m)] = c
    return out

def parse_expression(text):
    text = text.replace(r"\\", "").replace(r"&\quad {}", "").replace(r"\,", "")
    text = re.sub(r"\s+", "", text)
    pieces = re.findall(r"[+-]?[^+-]+", text)
    require("".join(pieces) == text, "complete signed-term coverage")
    result = {}
    for piece in pieces:
        sign = -1 if piece.startswith("-") else 1
        body = piece.lstrip("+-")
        coefficient = re.match(r"\d+", body)
        if coefficient:
            value = sign * int(coefficient.group())
            body = body[len(coefficient.group()):]
        else:
            value = sign
        monomial = []
        while body:
            match = re.match(r"x_\{(\d+)\}(?:\^\{(\d+)\})?", body)
            require(match is not None, "unexpected TeX in polynomial: " + body)
            index = int(match.group(1))
            power = int(match.group(2) or 1)
            require(1 <= power <= 2, "quadratic printed power")
            monomial += [index] * power
            body = body[len(match.group()):]
        key = tuple(sorted(monomial))
        require(key not in result and value != 0, "unique nonzero printed monomial")
        result[key] = value
    return result

def check():
    eq = json.loads((ROOT / "algebra/equation218.json").read_text())
    tex = (ROOT / "report/residuals218.tex").read_text()
    blocks = re.findall(r"\\begin\{align\*\}(.*?)\\end\{align\*\}", tex, flags=re.S)
    require(len(blocks) == 155, "all 155 displayed residuals")
    count = 0
    for j, (block, row) in enumerate(zip(blocks, eq["residuals"])):
        match = re.fullmatch(r"\s*R_\{(\d+)\}\s*&=\s*(.*?)\s*", block, re.S)
        require(match is not None and int(match.group(1)) == j, "residual numbering")
        printed = parse_expression(match.group(2))
        actual = validate_terms(row["terms"], 218, 2)
        require(printed == actual, "printed coefficient mismatch at residual " + str(j))
        count += len(actual)
    for n in [218, 216]:
        equation = json.loads((ROOT / "algebra" / f"equation{n}.json").read_text())
        require(equation["domain"] == "unrestricted integers", "integer domain")
        require(len(equation["variables"]) == n, "coordinate count")
        for row in equation["residuals"]:
            validate_terms(row["terms"], n, 2)
        expanded = json.loads((ROOT / "algebra" / f"expanded{n}.json").read_text())
        validate_terms(expanded["terms"], n, 4)
    # This parser's controls cover signs, coefficients, and ignored trailing syntax.
    require(parse_expression(r"-3x_{2}\,x_{7}+x_{9}^{2}-1") ==
            {(2, 7): -3, (9, 9): 1, (): -1}, "parser sanity")
    try:
        parse_expression("x_{1}+unparsed")
    except ValueError:
        pass
    else:
        raise ValueError("parser accepted unknown text")
    for n, prefix in [(218, "Main"), (216, "Few")]:
        metrics = json.loads((ROOT / "algebra" / f"metrics{n}.json").read_text())
        mt = (ROOT / "report/metrics.tex").read_text()
        for key, suffix in [("monomials", "Terms"), ("height", "Height"), ("row_height", "RowHeight")]:
            expected = r"\newcommand{\%s%s}{%s}" % (prefix, suffix, format(metrics[key], ","))
            require(expected in mt, "typeset metric " + prefix + suffix)
    return {"status": "passed", "residuals": len(blocks), "residual_terms": count,
            "domain": "unrestricted integers", "strict_final_json_schema": True,
            "tex_appendix_sha256": hashlib.sha256(tex.encode()).hexdigest()}

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    result = check()
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.receipt:
        args.receipt.write_text(text)
    print(text, end="")
