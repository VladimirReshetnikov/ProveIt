"""Reproduce the delivered comparisons without rewriting frozen evidence."""
import argparse
import ast
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import tokenize

ROOT = Path(__file__).resolve().parent
IGNORED = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
           tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def verify_manifest():
    path = ROOT / "MANIFEST.sha256"
    require(path.is_file(), "MANIFEST.sha256 is missing.")
    for line in path.read_text().splitlines():
        expected, relative = line.split("  ", 1)
        actual = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
        require(actual == expected, "Manifest mismatch: " + relative)


def measure(path):
    tree = ast.parse(path.read_bytes())
    normalized = (ast.unparse(tree) + "\n").encode()
    return [sum(t.type not in IGNORED for t in tokenize.generate_tokens(
        io.StringIO(normalized.decode()).readline)),
        sum(1 for _ in ast.walk(tree)), len(normalized)]


def load_verifier(directory):
    spec = importlib.util.spec_from_file_location("ipra_local_verify", directory / "verify.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--skip-manifest", action="store_true")
    args = parser.parse_args()
    if not args.skip_manifest:
        verify_manifest()
        print("Distribution manifest verified.")
    audit = json.loads((ROOT / "evidence/frontier_audit.json").read_text())
    for label, row in audit["programs"].items():
        path = ROOT / row["archive_path"]
        require(measure(path) == row["metrics"], "Incumbent measurement mismatch: " + label)
        require(hashlib.sha256(path.read_bytes()).hexdigest() == row["raw_sha256"],
                "Incumbent source hash mismatch: " + label)
    print("Nine frozen incumbent modules match their hashes and measurements.")
    with tempfile.TemporaryDirectory(prefix="ipra47-reproduction-") as temporary:
        temporary = Path(temporary)
        shutil.copytree(ROOT / "checkers", temporary / "checkers")
        shutil.copytree(ROOT / "mathematics", temporary / "mathematics")
        subprocess.run([sys.executable, str(temporary / "mathematics/predecessor47.py")],
                       check=True, stdout=subprocess.DEVNULL)
        for name in ["predecessor47_ast.json", "predecessor47_expanded.txt"]:
            require((temporary / "mathematics" / name).read_bytes() ==
                    (ROOT / "mathematics" / name).read_bytes(),
                    "Regenerated arithmetic artifact differs: " + name)
        subprocess.run([sys.executable, str(temporary / "mathematics/verify_reference50.py")],
                       check=True, stdout=subprocess.DEVNULL)
        print("Expanded 47-node term, exact current 50-node control and arithmetic checks reproduced.")
        verifier = load_verifier(temporary / "checkers")
        for row in verifier.structural_audit():
            require(row["exact_ast_transform"] and row["recorded_hashes_match"],
                    "Exact checker transformation audit failed.")
        for name, expected in verifier.EXPECTED.items():
            require(measure(temporary / "checkers/code" / (name + ".py")) == expected,
                    "Candidate measurement mismatch: " + name)
        if args.quick:
            tasks = []
            for name in verifier.EXPECTED:
                group = "native" if name.startswith("native") else "strict_proofs"
                cases = json.loads((temporary / "checkers/fixtures" / group /
                                    "cases.json").read_text())
                for wanted in [True, False]:
                    case = next(c for c in cases if c["expected"] == wanted)
                    for folder in ["controls", "code"]:
                        tasks.append({"name": name, "program": folder + "/" + name + ".py",
                            "fixture": "fixtures/" + group + "/" + case["file"],
                            "optimized": False, "expected": wanted})
            for task in tasks:
                require(verifier.run(task)["passed"], "Quick certificate check failed.")
            print(f"Exact checker transformations and {len(tasks)} representative executions passed.")
        else:
            result = subprocess.run([sys.executable, str(temporary / "checkers/verify.py")],
                                    capture_output=True, text=True)
            if result.returncode:
                print(result.stdout, result.stderr)
                raise SystemExit(result.returncode)
            print("Exact checker transformations and all 880 CLI executions passed.")
    print("Reproduction completed; delivered evidence was left unchanged.")


if __name__ == "__main__":
    main()
