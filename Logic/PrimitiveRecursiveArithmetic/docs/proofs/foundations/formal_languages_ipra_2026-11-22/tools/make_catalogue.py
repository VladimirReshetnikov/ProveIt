#!/usr/bin/env python3
"""Build a theorem inventory and check cross-references from the LaTeX source."""
from pathlib import Path
from collections import Counter
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
ORDER = ["foundations", "words", "regular", "monoids", "context_free",
         "effective", "counting", "lean_plan", "scope_audit", "bibliography"]
pattern = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary)\}"
    r"(?:\[([^\]]*)\])?\s*\\label\{([^}]+)\}", re.S)
items, labels, refs, citations, bibkeys = [], [], [], [], []
chapters = []
for name in ORDER:
    path = ROOT / "chapters" / f"{name}.tex"
    source = path.read_text()
    chapters.append({"path": str(path.relative_to(ROOT)),
                     "sha256": hashlib.sha256(source.encode()).hexdigest()})
    labels.extend(re.findall(r"\\label\{([^}]+)\}", source))
    refs.extend(re.findall(r"\\(?:ref|eqref)\{([^}]+)\}", source))
    for group in re.findall(r"\\cite\{([^}]+)\}", source):
        citations.extend(group.split(","))
    bibkeys.extend(re.findall(r"\\bibitem\{([^}]+)\}", source))
    for kind, title, label in pattern.findall(source):
        items.append({"id": label, "kind": kind,
                      "title_tex": " ".join(title.split()),
                      "source": str(path.relative_to(ROOT)),
                      "proof_status": "human-readable proof; Lean not compiled"})
duplicates = [key for key, n in Counter(labels).items() if n > 1]
missing_refs = sorted(set(refs) - set(labels))
missing_citations = sorted(set(citations) - set(bibkeys))
assert not duplicates, duplicates
assert not missing_refs, missing_refs
assert not missing_citations, missing_citations
assert len(items) == 100, len(items)
aux = ROOT / "build" / "formal_languages_ipra.aux"
if aux.exists():
    numbers = dict(re.findall(r"\\newlabel\{([^}]+)\}\{\{([^}]+)\}", aux.read_text()))
    for item in items:
        item["report_number"] = numbers.get(item["id"])
result = {"result_count": len(items), "by_chapter": dict(Counter(x["source"] for x in items)),
          "items": items, "chapters": chapters,
          "cross_references": {"duplicate_labels": duplicates,
              "missing_labels": missing_refs, "missing_bibliography_keys": missing_citations}}
(ROOT / "evidence" / "theorem_catalogue.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({key: result[key] for key in ("result_count", "by_chapter", "cross_references")}, indent=2))
