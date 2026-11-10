"""Remeasure exact comparator sources; no checker is executed or imported."""
from pathlib import Path
import gzip
import hashlib
import io
import json
import platform
import zlib

from source_measure import metrics, StripDocstrings
import ast

ROOT = Path(__file__).resolve().parent


def compressed_size(data):
    buffer = io.BytesIO()
    with gzip.GzipFile(fileobj=buffer, mode="wb", filename="",
                      compresslevel=9, mtime=0) as stream:
        stream.write(data)
    return len(buffer.getvalue())


def main():
    manifest = json.loads((ROOT / "comparators.json").read_text())
    results = []
    for record in manifest["programs"]:
        path = ROOT / record["local_file"]
        raw = path.read_bytes()
        if hashlib.sha256(raw).hexdigest() != record["sha256"]:
            raise SystemExit("Comparator source changed: " + str(path))
        current = metrics(path)
        current.pop("core", None)
        tree = ast.fix_missing_locations(StripDocstrings().visit(ast.parse(raw)))
        normalized = (ast.unparse(tree) + "\n").encode()
        current["gzip9_raw_bytes"] = compressed_size(raw)
        current["gzip9_normalized_bytes"] = compressed_size(normalized)
        for key, expected in record["metrics"].items():
            if current[key] != expected:
                raise SystemExit(f"Metric changed for {path}: {key}: "
                                 f"{current[key]} != {expected}")
        results.append({"file": record["local_file"], **current})
    print(json.dumps({"python": platform.python_version(),
                      "zlib": zlib.ZLIB_VERSION,
                      "commit": manifest["commit"],
                      "programs": results}, indent=2))


if __name__ == "__main__":
    main()
