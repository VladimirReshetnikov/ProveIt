"""Reproduce complete-program metrics and verify the frozen source census.

Only source text is measured. Historical source files are never executed.
Gzip level 9 is an informational metric, not an optimization objective.
"""
import gzip
import importlib.util
import json
from pathlib import Path
import platform
import sys
import zlib

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def collect():
    audit = module("source_measure", ROOT / "reference/source_measure.py")
    census = json.loads((ROOT / "evidence/corpus_metrics.json").read_text())
    for row in census["sources"]:
        raw = (ROOT / "reference/corpus_sources" / (row["sha256"] + ".py")).read_bytes()
        measured = audit.measure(raw)
        if measured != {key: row[key] for key in measured}:
            raise ValueError("Frozen-source measurement mismatch: " + row["sha256"])
    boundary = json.loads((ROOT / "evidence/boundary_classification.json").read_text())
    minima = boundary["coordinate_minima"]
    selected = {row["sha256"] for row in census["sources"]
                if any(row[key] <= value for key, value in minima.items())}
    if selected != {row["sha256"] for row in boundary["sources"]}:
        raise ValueError("Incomplete boundary classification")
    rows = []
    for name in ("checker.py", "checker_bytes.py", "checker_structure.py"):
        path = ROOT / "code" / name
        raw = path.read_bytes()
        exact_gzip = gzip.compress(raw, compresslevel=9, mtime=0)
        if path.with_suffix(".py.gz").read_bytes() != exact_gzip:
            raise ValueError("Gzip bytes do not match source: " + name)
        rows.append({"file": "code/" + name, **audit.measure(raw)})
    ablation_module = module("kernel_ablations", ROOT / "reference/kernel_measure_original.py")
    result = {
        "commit": boundary["commit"],
        "python": platform.python_version(),
        "implementation": platform.python_implementation(),
        "zlib": zlib.ZLIB_RUNTIME_VERSION,
        "gzip_level": 9,
        "gzip_mtime": 0,
        "direct_archives": census["archive_count"],
        "python_occurrences": census["occurrences"],
        "distinct_sources": len(census["sources"]),
        "boundary_sources": len(boundary["sources"]),
        "baseline_coordinate_minima": minima,
        "new_coordinate_minima": {key: min(row[key] for row in rows) for key in minima},
        "programs": rows,
        "ablations": ablation_module.ablations(),
    }
    return result


def main():
    result = collect()
    (ROOT / "evidence/measurements.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
