"""Load exact pure definitions from the two pinned, unchanged source files.

The full research module imports compiler experiments which this check never
uses.  Parsing its selected definitions avoids importing that unrelated closure.
No dependency of spec.py's numeric/fingerprint runner is loaded or executed.
"""
from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path
from types import SimpleNamespace


FUNCTIONS = frozenset(("Imp", "Rel", "Eq", "All", "Not", "And", "Ex",
                       "Or", "Iff", "symbolic", "published_spec", "emit"))
CONSTANTS = frozenset(("MACROS", "TAIL"))


def load_theory(repo: Path | None = None):
    packet = Path(__file__).resolve().parent
    manifest = json.loads((packet / "vendor/manifest.json").read_text())
    paths, source_records = {}, []
    for record in manifest["files"]:
        path = (repo.resolve() / record["repository_path"] if repo is not None
                else packet / record["path"])
        source = path.read_bytes()
        digest = hashlib.sha256(source).hexdigest()
        if digest != record["sha256"] or len(source) != record["bytes"]:
            raise ValueError(f"Pinned source identity mismatch: {path}")
        paths[record["source_path"]] = path
        source_records.append({"path": record["path"], "sha256": digest})

    module_path = paths["Computability/BusyBeaver/Research/ZFC/theory_backend_experiment.py"]
    spec_path = paths["ZF/m254/tools/logic/spec.py"]
    tree = ast.parse(module_path.read_bytes())
    selected, function_names, constant_names = [], set(), set()
    for node in tree.body:
        if isinstance(node, ast.FunctionDef) and node.name in FUNCTIONS:
            selected.append(node)
            function_names.add(node.name)
        elif (isinstance(node, ast.Assign) and len(node.targets) == 1
              and isinstance(node.targets[0], ast.Name)
              and node.targets[0].id in CONSTANTS):
            ast.literal_eval(node.value)  # ensure these remain literal data
            selected.append(node)
            constant_names.add(node.targets[0].id)
    if function_names != FUNCTIONS or constant_names != CONSTANTS:
        raise ValueError("The selected source interface is incomplete")
    module = ast.Module(body=selected, type_ignores=[])
    namespace = {"ast": ast, "hashlib": hashlib,
                 "SNAPSHOT": spec_path.parents[4]}
    exec(compile(module, str(module_path), "exec"), namespace)
    provenance = dict(
        source_mode="repository" if repo is not None else "vendored",
        pinned_sources=source_records,
        selected_definitions=sorted(FUNCTIONS),
        selected_constants=sorted(CONSTANTS),
        selected_ast_sha256=hashlib.sha256(
            ast.dump(module, include_attributes=False).encode()).hexdigest(),
        full_module_imported=False,
        numeric_or_fingerprint_runner_imported=False,
    )
    return SimpleNamespace(**{key: namespace[key] for key in FUNCTIONS | CONSTANTS}), provenance
