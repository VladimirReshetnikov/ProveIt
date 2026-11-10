# HISTORICAL ORIGINAL: retained to document the repository-backed first scan.
# It expects a ./proveit checkout and invokes git; it is not the packaged
# reproduction entry point. Run ../code/audit_novelty.py for the offline,
# portable scan of the bundled sources/ archives and new evidence outputs.
"""Reproducible text/provenance scan of current draft ZIPs and embedded ZIPs."""

from pathlib import Path
import hashlib
import io
import json
import re
import subprocess
import zipfile

BASE = Path(__file__).resolve().parent
REPO = BASE / "proveit"
DRAFTS = REPO / "docs" / "drafts"

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
    relative = str(path.relative_to(REPO))
    data = path.read_bytes()
    git_blob = subprocess.check_output(
        ["git", "-C", str(REPO), "rev-parse", "HEAD:" + relative], text=True
    ).strip()
    direct.append({
        "path": relative,
        "sha256": sha(data),
        "git_blob_sha": git_blob,
        "size_bytes": len(data),
    })
    walk(data, [relative])

commit = subprocess.check_output(
    ["git", "-C", str(REPO), "rev-parse", "HEAD"], text=True
).strip()
result = {
    "repository": "VladimirReshetnikov/ProveIt",
    "commit": commit,
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
(BASE / "J_novelty_scan.json").write_text(json.dumps(result, indent=2) + "\n")
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
(BASE / "J_novelty_matches.txt").write_text("\n".join(lines))
print(json.dumps(result["summary"], indent=2))
for document in documents.values():
    relevant = [m for m in document["matches"] if m["pattern"] in
                ("capped_predecessor", "finite_correction", "one_variable_seed", "unresolved_candidate")]
    if relevant:
        print(json.dumps({"path": document["locations"][0], "matches":
                          [{"pattern": m["pattern"], "line": m["line"]} for m in relevant]}))
