"""Statically inventory the pinned draft ZIPs, including nested ZIP members.

No archived code is executed. Use --archives /path/to/ProveIt/docs/drafts.
Source metrics use the attributed normalizer shipped in implementation/.
"""
import argparse
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("measure", ROOT / "implementation/source_measure.py")
measure = importlib.util.module_from_spec(spec)
spec.loader.exec_module(measure)


def audit(folder):
    archives, sources, occurrences, seen_archives = [], {}, [], set()

    def visit(data, origin):
        digest = hashlib.sha256(data).hexdigest()
        if digest in seen_archives:
            archives.append({"origin": origin, "sha256": digest, "reused": True})
            return
        seen_archives.add(digest)
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            archives.append({"origin": origin, "sha256": digest,
                             "member_count": len(archive.infolist()), "reused": False})
            for member in archive.infolist():
                if member.is_dir() or not member.filename.endswith((".py", ".zip")):
                    continue
                value = archive.read(member)
                name = origin + "!" + member.filename
                if member.filename.endswith(".zip"):
                    visit(value, name)
                    continue
                sha = hashlib.sha256(value).hexdigest()
                occurrences.append({"origin": name, "sha256": sha})
                if sha not in sources:
                    row = measure.metrics(value)
                    row["first_origin"] = name
                    row["accept_literal"] = b"ACCEPT" in value
                    sources[sha] = row

    direct = sorted(Path(folder).glob("*.zip"))
    for path in direct:
        visit(path.read_bytes(), path.name)
    return {"snapshot": "fb2dbd2a33c6b132671a54b029d0bf3cd98c633d",
            "direct_archives": len(direct), "unique_archives": len(seen_archives),
            "python_occurrences_in_unique_archives": len(occurrences),
            "unique_python_sources": len(sources), "archives": archives,
            "sources": sorted(sources.values(), key=lambda row: row["normalized_bytes"]),
            "occurrences": occurrences}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archives", required=True, type=Path)
    parser.add_argument("--output", type=Path, default=ROOT / "evidence/recursive_corpus.json")
    args = parser.parse_args()
    result = audit(args.archives)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in (
        "direct_archives", "unique_archives", "python_occurrences_in_unique_archives",
        "unique_python_sources")}, indent=2))
    print("Sources carrying ACCEPT below the previous 616-byte boundary:")
    for row in result["sources"]:
        if row["normalized_bytes"] < 616 and row["accept_literal"]:
            print(row["normalized_bytes"], row["first_origin"])
