"""Recover batch 149 from Git and replay finite checks outside the checkout.

Default: both mathematical suites, source 01's independent RM/table checks,
its pinned-template/parameter audits, and source 02's fixed 268-state replay.
Checksum-manifest calls are disabled only in memory. Functional source pins,
formula contracts, RM edges, negative controls and exact table comparisons
remain enabled. No network, proof assistant or unbounded proof search runs.
"""
from __future__ import annotations

import argparse
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time
from zipfile import ZipFile


ARRIVALS = (
    ("de047657e", "zfc_consistency_research.zip", "zfc_consistency_research"),
    ("be9e617d2", "zfc_substitution_engine.zip", "zfc_substitution_engine"),
)
PIN = "96836f9eea3540e96322c3d28c7127a582aae223"
RESEARCH = "Computability/BusyBeaver/Research/ZFC"
DEPENDENCIES = tuple(
    f"{RESEARCH}/{name}.py" for name in (
        "recover_wade_dag", "theory_backend_experiment", "psc_backend_experiment",
        "pairing_backend_experiment", "psc_adapter_checks", "kernel_metrics",
        "audit_raw_candidate",
    )
) + tuple(
    f"lib/jeff-busy-beaver-zfc254/{path}" for path in (
        "ZF/generator/TMBuilder.py", "ZF/generator/tm.py", "ZF/generator/tmdb.py",
        "ZF/generator/LICENSE.wade", "ZF/m254/coq/prog/Dag254.v",
        "ZF/m254/tools/logic/spec.py",
    )
)

# Omit exactly the archive-manifest call and its misleading success message.
# The original file, comparison routines, RM self-test and table checks remain.
SOURCE01_REPLAY = """
from pathlib import Path
import sys
p = Path('reproduce.py').resolve()
source = p.read_text()
old = '    checked_files = manifest_check()\\n    print("Distributed file hashes: OK")'
assert source.count(old) == 1
new = '    checked_files = 0\\n    print("Checksum-manifest validation skipped by intake policy")'
sys.argv = ['reproduce.py', '--output', sys.argv[1]]
exec(compile(source.replace(old, new), str(p), 'exec'),
     {'__file__': str(p), '__name__': '__main__'})
"""

# The fixed replay calls verify(..., False), already omitting ARTIFACT_SHA256.
# Suppress only PINNED_INPUTS.json's bulk loop; intrinsic compiler/source pins,
# the six byte-exact generated outputs and the independent RM check still run.
SOURCE02_REPLAY = """
import runpy
import sys
import verify
verify.pinned_inputs = lambda: 0
ns = runpy.run_path('reproduce.py', run_name='intake149_engineering')
sys.argv = ['reproduce.py', '--output', sys.argv[1], *sys.argv[2:]]
print('Checksum manifests skipped; functional compilation checks retained', flush=True)
ns['main']()
"""


def main() -> None:
    if not __debug__:
        raise SystemExit("Run without -O/PYTHONOPTIMIZE: finite checks use assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-only", action="store_true")
    parser.add_argument("--source01-controls", action="store_true",
                        help="also regenerate the fixed 269/283-state controls")
    parser.add_argument("--searches", action="store_true",
                        help="also repeat source 02's 53,760-case grid and 8,192 PSC choices")
    args = parser.parse_args()
    repo = next(p for p in Path(__file__).resolve().parents if (p / ".git").exists())
    scratch = Path(tempfile.mkdtemp(prefix="zfc-batch149-reproduce-"))
    print(f"Scratch: {scratch}", flush=True)
    roots = []
    for number, (arrival, archive, wrapper) in enumerate(ARRIVALS, 1):
        raw = subprocess.check_output([
            "git", "show", f"{arrival}:docs/incoming/{archive}"
        ], cwd=repo)
        destination = scratch / f"{number:02d}"
        with ZipFile(io.BytesIO(raw)) as zipped:
            for name in zipped.namelist():
                path = Path(name)
                if path.is_absolute() or ".." in path.parts:
                    raise ValueError(f"Archive path escapes scratch: {name}")
            zipped.extractall(destination)
        root = destination / wrapper
        if not root.is_dir():
            raise ValueError(f"Missing expected wrapper: {wrapper}")
        roots.append(root)
    dependencies = scratch / "pinned-repo"
    for path in DEPENDENCIES:
        data = subprocess.check_output(["git", "show", f"{PIN}:{path}"], cwd=repo)
        output = dependencies / path
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(data)
    summary = dict(
        batch=149, python=sys.version, scratch=str(scratch),
        arrivals=[dict(commit=a, archive=n, wrapper=w) for a, n, w in ARRIVALS],
        dependency_pin=PIN, dependency_files=list(DEPENDENCIES),
        checksum_manifests_checked=False, proof_assistant_invoked=False,
        network_used=False, unbounded_search_run=False,
        source01_controls_requested=args.source01_controls,
        source02_searches_requested=args.searches, prepare_only=args.prepare_only,
        checks=[],
    )

    def save() -> None:
        (scratch / "reproduction.json").write_text(json.dumps(summary, indent=2) + "\n")
        (scratch / "runs.json").write_text(json.dumps(summary["checks"], indent=2) + "\n")

    save()
    if args.prepare_only:
        return

    def run(name: str, root: Path, command: list[str]) -> None:
        begin = time.monotonic()
        result = subprocess.run([sys.executable, "-B", *map(str, command)], cwd=root,
                                capture_output=True, text=True)
        log = scratch / f"{name}.log"
        log.write_text(result.stdout + result.stderr)
        summary["checks"].append(dict(
            check=name, cwd=str(root), command=command, returncode=result.returncode,
            elapsed_seconds=time.monotonic() - begin, log=str(log),
        ))
        save()
        print(f"{name}: exit {result.returncode}", flush=True)
        if result.returncode:
            print(result.stdout + result.stderr, file=sys.stderr)
            raise SystemExit(result.returncode)

    first, second = roots
    run("01-core-rm-tables", first,
        ["-c", SOURCE01_REPLAY, str(scratch / "source01-reproduction.json")])
    run("01-actual-template", first, [
        "code/psc_identity_obstruction_check.py", "--repo", str(dependencies),
        "--limit", "100000", "--output", str(scratch / "source01-template.json"),
    ])
    run("01-parameter-acquisition", first, [
        "compiler/check_parameter_acquisition.py", "--repo", str(dependencies),
        "--output", str(scratch / "source01-parameter-acquisition.json"),
    ])
    for name, script in (
        ("02-checker", "code/verify_artifacts.py"),
        ("02-independent", "code/independent_review.py"),
        ("02-diagonal", "code/diagonal_obstruction.py"),
    ):
        run(name, second, [script])
    run("02-prefix", second, ["code/certificate_codec.py", "--limit", "10000"])
    engine = second / "engineering"
    run("02-fixed-control", engine,
        ["-c", SOURCE02_REPLAY, str(scratch / "source02-fixed-control")])
    if args.source01_controls:
        generated = scratch / "source01-controls"
        run("01-fixed-controls", first, [
            "compiler/compiler_controls.py", "--repo", str(dependencies),
            "--prior-grammar", str(engine / "vendor/one_schema_machine/rebracket_axioms.py"),
            "--output", str(generated),
        ])
        names = ["original-reference-dag.json", "original-rm-bisimulation.json"]
        for lane, states in (("original", 269), ("psc_ir", 283)):
            names.extend((f"{lane}-{states}.tm", f"{lane}-named.tm",
                          f"{lane}-dag.json", f"{lane}-labels.json"))
        for name in names:
            if (generated / name).read_bytes() != (first / "compiler" / name).read_bytes():
                raise ValueError(f"Source 01 fixed artifact differs: {name}")
        summary["source01_generated_artifacts_equal"] = names
        save()
    if args.searches:
        run("02-grid-and-psc-searches", engine, [
            "-c", SOURCE02_REPLAY, str(scratch / "source02-searches"),
            "--full-grid", "--psc-controls",
        ])
    summary["all_passed"] = True
    save()


if __name__ == "__main__":
    main()
