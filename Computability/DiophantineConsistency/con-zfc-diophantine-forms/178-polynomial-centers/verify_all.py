#!/usr/bin/env python3
"""Portable, standard-library verification of the complete research package.

All subprocesses operate on a disposable copy. Rebuilding cannot overwrite
the released equations or report inputs. Optional receipts are the only
outputs written outside that copy. Run with Python -O to propagate optimized
mode to every subprocess, including scripts launched by a child.
"""
from __future__ import annotations
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def snapshot(directory):
    return {
        str(p.relative_to(directory)): digest(p.read_bytes())
        for component in ("compact", "whole_product", "direct")
        for p in sorted((directory / component).rglob("*"))
        if p.is_file() and "__pycache__" not in p.parts and p.suffix != ".pyc"
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipts", type=Path,
                        help="Optional directory for detailed receipts and the final aggregate JSON.")
    parser.add_argument("--skip-report", action="store_true",
                        help="Development only: omit report input binding; not a complete release verification.")
    args = parser.parse_args()
    receipt_directory = args.receipts.resolve() if args.receipts else None
    if receipt_directory:
        receipt_directory.mkdir(parents=True, exist_ok=True)
    mode = "OPTIMIZED" if sys.flags.optimize else "NORMAL"
    mode_directory = receipt_directory / mode.lower() if receipt_directory else None
    if mode_directory:
        mode_directory.mkdir(parents=True, exist_ok=True)
    python_command = [sys.executable, "-B"]
    if sys.flags.optimize:
        python_command.append("-" + "O" * min(sys.flags.optimize, 2))
    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["PYTHONOPTIMIZE"] = str(sys.flags.optimize)
    before = snapshot(ROOT)
    result = {
        "status": "RUNNING", "mode": mode.lower(),
        "python_optimize": sys.flags.optimize,
        "child_optimization_propagated": True,
        "verification_scope": "full release" if not args.skip_report else "development; report omitted",
        "checks": [],
        "limits": [
            "Exact finite source, coefficient, polynomial and report-input checks do not prove the unbounded arithmetic lemmas.",
            "The ordinary mathematical and inherited logical calibrations are supplied separately; no new end-to-end proof-kernel certificate is asserted.",
        ],
    }

    def record(name, payload):
        result["checks"].append({"name": name, "status": "PASS", **payload})
        print(name + ": PASS", flush=True)

    try:
        with tempfile.TemporaryDirectory(prefix="conzfc-release-check-") as temporary:
            temporary = Path(temporary)
            package = temporary / "package"
            shutil.copytree(ROOT, package,
                            ignore=shutil.ignore_patterns("__pycache__", "*.pyc", "*.pyo"))
            logs = temporary / "receipts"
            logs.mkdir()

            def execute(name, script, arguments=(), produces_receipt=False):
                receipt = logs / (name + ".json")
                command = python_command + [str(package / script)] + list(arguments)
                if produces_receipt:
                    command += ["--receipt", str(receipt)]
                started = time.monotonic()
                process = subprocess.run(command, cwd=package, env=environment,
                                         text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                elapsed = time.monotonic() - started
                payload = {
                    "script": script, "arguments": list(arguments),
                    "returncode": process.returncode,
                    "elapsed_seconds": round(elapsed, 3),
                    "stdout": process.stdout, "stderr": process.stderr,
                }
                if receipt.exists():
                    payload["receipt"] = json.loads(receipt.read_text())
                if mode_directory:
                    (mode_directory / (name + ".json")).write_text(
                        json.dumps(payload, indent=2, sort_keys=True) + "\n")
                require(process.returncode == 0,
                        name + " failed:\n" + process.stderr + process.stdout)
                record(name, payload)

            def byte_identical(name, relative_paths):
                bindings = []
                for relative in relative_paths:
                    actual = (package / relative).read_bytes()
                    frozen = (ROOT / relative).read_bytes()
                    require(actual == frozen, "Reconstruction changed released bytes: " + relative)
                    bindings.append({"path": relative, "sha256": digest(actual), "bytes": len(actual)})
                record(name, {"byte_identical_files": bindings})

            # Authenticate cross-component bindings before running constructors.
            compact_parent = package / "compact/equations/square_transport85.json"
            whole_parent = package / "whole_product/parent85.json"
            require(compact_parent.read_bytes() == whole_parent.read_bytes(),
                    "Whole-product parent is not byte-identical to the compact square-transport85 equation")
            parent = json.loads(compact_parent.read_text())
            whole = json.loads((package / "whole_product/equation.json").read_text())
            require(parent["coefficient_binding"] == whole["coefficient_binding"],
                    "Whole fixed tuple binding differs across components")
            bindings = []
            for port, specification in sorted(parent["coefficient_binding"]["ports"].items()):
                filename = specification["file"]
                compact_bytes = (package / "compact/coefficients" / filename).read_bytes()
                whole_bytes = (package / "whole_product/coefficients" / filename).read_bytes()
                require(compact_bytes == whole_bytes, "Compressed coefficient differs across components: " + port)
                require(digest(compact_bytes) == specification["gzip_sha256"],
                        "Compressed coefficient hash differs: " + port)
                bindings.append({"port": port, "filename": filename, "gzip_sha256": digest(compact_bytes)})
            record("cross_component_bindings", {
                "parent85_sha256": digest(compact_parent.read_bytes()),
                "compressed_coefficients": bindings,
            })

            execute("compact_reconstruction", "compact/build.py", ["--check"])
            execute("compact_mathematics", "compact/verify.py", produces_receipt=True)
            execute("coefficient_recipe", "compact/rebuild_coefficients.py")

            execute("whole_product_reconstruction", "whole_product/build.py")
            byte_identical("whole_product_reconstruction_bytes", ["whole_product/equation.json"])
            if (package / "whole_product/build_algebra.py").is_file():
                execute("whole_product_algebra_reconstruction", "whole_product/build_algebra.py", ["--check"])
            elif not args.skip_report:
                raise ValueError("The release is missing whole_product/build_algebra.py for the explicit coefficient-array binding.")
            execute("whole_product_exact_check", "whole_product/check.py", produces_receipt=True)
            execute("whole_product_independent_review", "whole_product/review_graph.py", produces_receipt=True)

            execute("direct_reconstruction", "direct/build_natural.py")
            byte_identical("direct_reconstruction_bytes", [
                "direct/" + endpoint + "/" + filename
                for endpoint in ("natural204", "natural203")
                for filename in ("equation.json", "metrics.json", "projection_certificate.json", "expanded_polynomial.json")
            ])
            execute("direct_exact_check", "direct/verify_direct.py", produces_receipt=True)

            if not args.skip_report:
                require((package / "report/generate_inputs.py").is_file(),
                        "report/generate_inputs.py is not present; a complete release check must be rerun after report input generation.")
                execute("report_input_bindings", "report/generate_inputs.py", ["--check"])
                require((package / "report/assemble.py").is_file(),
                        "report/assemble.py is not present; complete verification requires the standalone TeX assembly binding.")
                execute("report_standalone_assembly", "report/assemble.py", ["--check"])
            else:
                result["checks"].append({"name": "report_input_bindings", "status": "SKIPPED_DEVELOPMENT"})

        after = snapshot(ROOT)
        require(before == after, "Released component files changed during verification")
        record("released_files_unchanged", {"files": len(before)})
        result["status"] = "PASS" if not args.skip_report else "PASS_DEVELOPMENT"
    except Exception as error:
        result["status"] = "FAIL"
        result["error"] = str(error)
        print("FAIL: " + str(error), file=sys.stderr)
    finally:
        if receipt_directory:
            (receipt_directory / ("FINAL_CHECK_" + mode + ".json")).write_text(
                json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": result["status"], "mode": mode.lower(),
                      "checks": len(result["checks"]),
                      "scope": result["verification_scope"]}, indent=2))
    return 0 if result["status"] in ("PASS", "PASS_DEVELOPMENT") else 1


if __name__ == "__main__":
    raise SystemExit(main())
