"""Offline text/provenance scan of the nine bundled current draft archives.

Run with Python 3; no git executable, checkout, network, or third-party package
is required. The original frozen evidence is never modified.
"""

from pathlib import Path
import hashlib
import io
import json
import re
import zipfile

BASE = Path(__file__).resolve().parents[1]
DRAFTS = BASE / "sources"
EVIDENCE = BASE / "evidence"
COMMIT = "2fdcf5bf988bead821c416649f713f98b7ed8776"
PINNED_SCAN = EVIDENCE / "J_novelty_scan.json"

PATTERNS = {
    "successor_seed": r"successor[\s~-]*(?:seeded|initiali[sz])",
    "scalar_near_successor": r"(?:scalar[\s\S]{0,100}successor|successor[\s\S]{0,100}scalar)",
    "one_variable_seed": r"(?:one[\s~-]*variable|single[\s~-]*(?:variable|input)|one[\s~-]*input)[\s\S]{0,160}(?:seed|initial|successor)",
    "seed_equation": r"[JRI]\\?\(0\s*,\s*a\s*;[^\n]{0,35}[\)\}]\s*[&=]{1,2}\s*S\s*\(?a",
    "capped_predecessor": r"capped[\s~-]*predecessor|max\s*\\?\{?\s*1[^\n]{0,30}(?:n|m)\s*[-−]\s*1",
    "finite_correction": r"finite[\s~-]*correction|three[\s~-]*(?:small|exceptional)[\s~-]*(?:inputs|arguments)|correc[^\n]{0,60}predecessor",
    "unresolved_candidate": r"(?:unresolved|left[\s~-]*inverse)[\s\S]{0,160}(?:scalar|seed|predecessor|candidate)",
    "shifted_selector": r"shifted[\s~-]*selector|unshifted[\s~-]*(?:zero|selector|initial)",
}

archives = {}
documents = {}
errors = []


def sha(data):
    return hashlib.sha256(data).hexdigest()


def walk(data, chain):
    digest = sha(data)
    if digest in archives:
        archives[digest]["occurrences"].append(chain)
        return
    archives[digest] = {"sha256": digest, "size_bytes": len(data), "occurrences": [chain]}
    try:
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            for item in archive.infolist():
                if item.is_dir():
                    continue
                name = item.filename
                if not name.lower().endswith((".zip", ".tex", ".md", ".txt")):
                    continue
                payload = archive.read(item)
                location = chain + [name]
                if name.lower().endswith(".zip"):
                    walk(payload, location)
                    continue
                try:
                    text = payload.decode("utf-8")
                except UnicodeDecodeError as error:
                    errors.append({"location": location, "error": str(error)})
                    text = payload.decode("utf-8", errors="replace")
                key = sha(payload)
                if key in documents:
                    documents[key]["locations"].append(location)
                    continue
                matches = []
                for label, pattern in PATTERNS.items():
                    for match in re.finditer(pattern, text, re.IGNORECASE):
                        start = text.rfind("\n", 0, max(0, match.start() - 500)) + 1
                        end = text.find("\n", min(len(text), match.end() + 700))
                        if end == -1:
                            end = len(text)
                        matches.append({
                            "pattern": label,
                            "line": text.count("\n", 0, match.start()) + 1,
                            "excerpt": text[start:end],
                        })
                documents[key] = {
                    "sha256": key,
                    "size_bytes": len(payload),
                    "locations": [location],
                    "suffix": Path(name).suffix.lower(),
                    "matches": matches,
                }
    except Exception as error:
        errors.append({"location": chain, "error": str(error)})


direct = []
for path in sorted(DRAFTS.glob("*.zip")):
    relative = "docs/drafts/" + path.name
    data = path.read_bytes()
    # Git's object identity is SHA-1 of its canonical blob header plus bytes.
    git_blob = hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()
    direct.append({
        "path": relative,
        "sha256": sha(data),
        "git_blob_sha": git_blob,
        "size_bytes": len(data),
    })
    walk(data, [relative])

result = {
    "repository": "VladimirReshetnikov/ProveIt",
    "commit": COMMIT,
    "provenance": "Fixed inspected commit; bundled archive bytes independently checked against the original frozen inventory.",
    "direct_archives": direct,
    "summary": {
        "direct_archive_count": len(direct),
        "unique_archives_including_embedded": len(archives),
        "unique_text_documents": len(documents),
        "unique_tex_md_documents": sum(d["suffix"] in (".tex", ".md") for d in documents.values()),
        "documents_with_matches": sum(bool(d["matches"]) for d in documents.values()),
        "errors": len(errors),
    },
    "patterns": PATTERNS,
    "archives": list(archives.values()),
    "documents": list(documents.values()),
    "errors": errors,
    "scope_limit": "Text retrieval aids a manual novelty audit; it does not prove absence of an unrecognized equivalent construction or establish global priority.",
}
pinned = json.loads(PINNED_SCAN.read_text())
comparison = {
    "commit": pinned["commit"] == COMMIT,
    "direct_archive_records": result["direct_archives"] == pinned["direct_archives"],
    "archive_inventory": result["archives"] == pinned["archives"],
    "document_inventory_and_matches": result["documents"] == pinned["documents"],
    "summary": result["summary"] == pinned["summary"],
    "no_errors": not errors,
}
result["matches_original_frozen_scan"] = comparison
(EVIDENCE / "reproduced_novelty_scan.json").write_text(json.dumps(result, indent=2) + "\n")
lines = []
for document in documents.values():
    for match in document["matches"]:
        if match["pattern"] == "scalar_near_successor":
            continue
        lines += [
            "LOCATION: " + " :: ".join(document["locations"][0]),
            "SHA256: " + document["sha256"],
            "MATCH: " + match["pattern"] + " at line " + str(match["line"]),
            match["excerpt"],
            "",
        ]
(EVIDENCE / "reproduced_novelty_matches.txt").write_text("\n".join(lines))
print(json.dumps({"summary": result["summary"],
                  "matches_original_frozen_scan": comparison}, indent=2))
if not all(comparison.values()):
    raise SystemExit("Bundled corpus differs from the pinned original scan; see reproduced evidence.")
