"""Parse the printed LaTeX residuals back into sparse polynomials."""
import json
from collections import defaultdict
from pathlib import Path
import re


def require(ok, text):
    if not ok:
        raise ValueError(text)


def parse(expression):
    expression = expression.replace(r"\quad{}", "").replace(r"\,", "")
    expression = "".join(expression.split()).replace("&", "").replace("\\", "")
    terms = defaultdict(int)
    for chunk in re.split(r"(?=[+-])", expression):
        if not chunk:
            continue
        sign = -1 if chunk.startswith("-") else 1
        if chunk[0] in "+-":
            chunk = chunk[1:]
        lead = re.match(r"\d*", chunk)[0]
        coefficient = int(lead) if lead else 1
        body = chunk[len(lead):]
        monomial = []
        consumed = ""
        for match in re.finditer(r"x_\{(\d+)\}(?:\^\{(\d+)\})?", body):
            consumed += match[0]
            index, degree = int(match[1]), int(match[2] or "1")
            require(0 <= index < 608 and degree in (1, 2), "Bad printed coordinate")
            monomial.extend([index] * degree)
        require(consumed == body and (body or lead), "Unparsed printed term: " + chunk)
        terms[tuple(sorted(monomial))] += sign * coefficient
    return {m: c for m, c in terms.items() if c}


def check(root):
    source = json.loads((root / "artifacts/natural/equation.json").read_text())
    text = (root / "natural_rows.tex").read_text()
    blocks = re.split(r"r_\{(\d+)\}\s*&=", text)
    require(len(blocks) == 1 + 2 * 491, "Printed residual count")
    for pos in range(1, len(blocks), 2):
        index = int(blocks[pos])
        require(index == (pos - 1) // 2, "Printed residual order")
        body = blocks[pos + 1].split(r"\end{align*}")[0]
        actual = parse(body)
        expected = {tuple(m): c for c, m in source["residuals"][index]["terms"]}
        require(actual == expected, "Printed residual mismatch: " + str(index))
    indices = list(map(int, re.findall(r"\d+", (root / "integer_indices.tex").read_text())))
    expected = [i for i, v in enumerate(source["variables"]) if v["kind"] != "gate"]
    require(indices == expected, "Printed integer guard index set")
    return {"parsed_residuals": 491, "parsed_guard_indices": 359, "status": "PASS"}


if __name__ == "__main__":
    print(json.dumps(check(Path(__file__).resolve().parents[1]), indent=2))
