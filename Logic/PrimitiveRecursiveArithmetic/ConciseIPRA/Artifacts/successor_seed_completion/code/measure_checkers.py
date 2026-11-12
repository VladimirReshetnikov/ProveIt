"""Reproduce complete-checker metrics under the inherited normalizer."""
import importlib.util
import json
from pathlib import Path
import platform

ROOT = Path(__file__).resolve().parent.parent


def main():
    spec = importlib.util.spec_from_file_location("source_measure", ROOT / "reference/source_measure.py")
    measure = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(measure)
    candidates = ["code/checker.py", "code/checker_direct.py", "code/checker_ast.py",
                  "code/checker_ast_total.py"]
    controls = ["reference/prior_scalar_checker.py", "reference/prior_scalar_ast.py"]
    rows = [{"file": name, **measure.metrics(ROOT / name)} for name in candidates + controls]
    fields = ["normalized_tokens", "ast_nodes", "normalized_bytes"]
    old = {key: min(row[key] for row in rows[len(candidates):]) for key in fields}
    new = {key: min(row[key] for row in rows[:len(candidates)]) for key in fields}
    total_profiles = [row for row in rows[:len(candidates)]
                      if row["file"] != "code/checker_ast.py"]
    total_envelope = {key: min(row[key] for row in total_profiles) for key in fields}
    result = {
        "python": platform.python_version(),
        "implementation": platform.python_implementation(),
        "metric": "Whole module, genuine docstrings removed, ast.unparse plus final newline",
        "programs": rows,
        "old_current_corpus_envelope": old,
        "new_separate_profile_envelope": new,
        "new_total_input_profile_envelope": total_envelope,
        "total_input_profile_files": [row["file"] for row in total_profiles],
        "strict_coordinate_improvement": {key: new[key] < old[key] for key in fields},
        "single_program_dominates_all_old_coordinates": any(
            all(row[key] < old[key] for key in fields) for row in rows[:len(candidates)]),
        "scope": "Observed complete-source upper bounds, not global minimality or a universal lower bound",
    }
    (ROOT / "evidence/checker_metrics.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: value for key, value in result.items() if key != "programs"}, indent=2))


if __name__ == "__main__":
    main()
