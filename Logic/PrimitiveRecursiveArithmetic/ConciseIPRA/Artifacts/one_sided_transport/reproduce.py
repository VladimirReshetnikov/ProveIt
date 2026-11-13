"""Read-only verification of the delivered package; test outputs stay temporary."""
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "code"))
from measure import all_measurements


def main():
    manifest = json.loads((ROOT / "MANIFEST.json").read_text())
    for entry in manifest["files"]:
        data = (ROOT / entry["path"]).read_bytes()
        if len(data) != entry["size"] or hashlib.sha256(data).hexdigest() != entry["sha256"]:
            raise ValueError("Manifest mismatch: " + entry["path"])
    expected = json.loads((ROOT / "evidence/measurements.json").read_text())
    observed = all_measurements(ROOT)
    same_runtime = sys.version_info[:2] == (3, 12)
    for want, got in zip(expected["rows"], observed["rows"], strict=True):
        if want["path"] != got["path"] or want["raw_sha256"] != got["raw_sha256"]:
            raise ValueError("Source identity changed")
        if same_runtime and want != got:
            raise ValueError("Measurement changed: " + want["path"])
    with tempfile.TemporaryDirectory(prefix="ipra-one-sided-") as temporary:
        code = Path(temporary) / "code"
        shutil.copytree(ROOT / "code", code)
        for program in ("compare_checkers.py", "test_c7.py", "test_m7_control.py"):
            run = subprocess.run([sys.executable, str(code / program)],
                                 capture_output=True, text=True)
            if run.returncode:
                raise RuntimeError(program + "\n" + run.stdout + run.stderr)
        if (code / "m7_control.py").read_bytes() != (ROOT / "code/m7_control.py").read_bytes():
            raise ValueError("Matched control changed outside its equality branch")
        c7 = json.loads((code / "test_results.json").read_text())
        m7 = json.loads((code / "m7_test_results.json").read_text())
        for name in ("test_results.json", "m7_test_results.json"):
            if json.loads((code / name).read_text()) != json.loads((ROOT / "evidence" / name).read_text()):
                raise ValueError("Test report changed: " + name)
    print(json.dumps({
        "manifest_files_verified": len(manifest["files"]),
        "source_measurements_verified": len(observed["rows"]),
        "measurement_runtime_matches": same_runtime,
        "c7_certificate_cases": c7["certificate_cases"],
        "m7_certificate_cases": m7["certificate_cases"],
        "independent_substitution_checks": c7["independent_substitution_checks"],
        "normal_and_optimized_python": True,
        "lean_extension_compiled": False,
        "result": "PASS",
    }, indent=2))


if __name__ == "__main__":
    main()
