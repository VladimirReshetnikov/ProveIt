"""Assemble and validate the reviewable source/PDF release from a Git checkout.

Usage: python3 build_release.py --output-dir /absolute/path/to/output
The current Git index and branch are not changed. The patch is generated in
a temporary index against BASELINE and applied in an isolated verification
directory. All changed bytes are checked after applying the patch.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile
import zipfile


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
PREFIX = Path("Topology/UnknotRecognition")
BASELINE = "1be2abc8cc743c1a3b5cb7fdfeb650697f8e2d5b"
SUBTREE_BASELINE = "38e65c9c2e2bfd42b9f71f1a1a7af15a3f8a3005"
RELEASE = "unknot_research_20261008"
NEW_RESULTS = {"endpoint_ap_20261008.json", "endpoint_ap_lcp_ablation_20261008.json",
               "regular_cover_gluing_20261008.json"}

VERIFY_SCRIPT = '''"""Verify every regular file listed in the release SHA-256 manifest."""
import hashlib
from pathlib import Path
root = Path(__file__).resolve().parent
count = 0
for line in (root / "SHA256SUMS").read_text().splitlines():
    expected, name = line.split("  ", 1)
    relative = Path(name)
    if relative.is_absolute() or ".." in relative.parts:
        raise SystemExit("Unsafe manifest path: " + name)
    path = root / relative
    if not path.is_file() or path.is_symlink():
        raise SystemExit("Missing or nonregular file: " + name)
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit("SHA-256 mismatch: " + name)
    count += 1
print("PASS: verified", count, "release files")
'''


def run(args, *, cwd=REPO, env=None):
    return subprocess.run(args, cwd=cwd, env=env, check=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def atomic_write(path, data):
    temporary = path.with_name(path.name + ".stage")
    with temporary.open("wb") as output:
        output.write(data)
        output.flush()
        os.fsync(output.fileno())
    os.replace(temporary, path)


def selected_files():
    root = REPO / PREFIX
    selected = []
    fast = root / "fast"
    for path in fast.rglob("*"):
        if not path.is_file() or path.is_symlink():
            continue
        relative = path.relative_to(fast)
        if any(part in ("__pycache__", ".pytest_cache") for part in relative.parts):
            continue
        if path.suffix in (".pyc", ".pyo"):
            continue
        if relative.parts[0] == "results" and path.name not in NEW_RESULTS:
            continue
        selected.append(path)
    for relative in ("reports/24/reference/graded_transfer_v1.py",
                     "reports/26/LICENSE", "reports/28/LICENSE"):
        selected.append(root / relative)
    for relative in ("reports/26/detshadow", "reports/28/src/closure_reset"):
        selected.extend(p for p in (root / relative).rglob("*.py")
                        if "__pycache__" not in p.parts)
    for path in HERE.rglob("*"):
        if not path.is_file() or path.is_symlink() or "__pycache__" in path.parts:
            continue
        if path.parent.name == "article" and path.suffix not in (".tex", ".pdf"):
            continue
        if path.suffix not in (".py", ".tex", ".pdf", ".png", ".md", ".json", ".txt", ".log"):
            continue
        selected.append(path)
    result = sorted(set(selected))
    for path in result:
        if not path.is_file():
            raise FileNotFoundError(path)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    article = HERE / "article/unknot_compressed_certificates.pdf"
    if not article.is_file():
        raise SystemExit("Build the article before creating the release")
    verification = HERE / "verification/integrated_final.log"
    if not verification.is_file() or "\nOK\n" not in verification.read_text():
        raise SystemExit("A passing final integrated test log is required")
    files = selected_files()
    with tempfile.TemporaryDirectory(prefix="proveit-release-") as temporary:
        work = Path(temporary)
        stage = work / RELEASE
        stage.mkdir()
        for source in files:
            dest = stage / source.relative_to(REPO)
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, dest)
        shutil.copy2(HERE / "README.md", stage / "README.md")
        shutil.copy2(REPO / "LICENSE", stage / "LICENSE")
        (stage / "verify_release.py").write_text(VERIFY_SCRIPT)

        index_env = dict(os.environ, GIT_INDEX_FILE=str(work / "release.index"))
        run(["git", "read-tree", BASELINE], env=index_env)
        run(["git", "add", "--sparse", "--force", "--"] +
            [str(path.relative_to(REPO)) for path in files], env=index_env)
        patch = run(["git", "diff", "--cached", "--binary", BASELINE, "--", str(PREFIX)],
                    env=index_env).stdout
        (stage / "integration.patch").write_bytes(patch)
        fields = run(["git", "diff", "--cached", "--name-status", "-z", BASELINE,
                      "--", str(PREFIX)], env=index_env).stdout.decode().split("\0")
        records = [(fields[i], fields[i+1]) for i in range(0, len(fields)-1, 2)]
        check_tree = work / "patch_check"
        check_tree.mkdir()
        run(["git", "init", "--quiet"], cwd=check_tree)
        for status, name in records:
            if status not in ("A", "M"):
                raise ValueError("Unexpected patch change: " + status + " " + name)
            if status == "M":
                path = check_tree / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(run(["git", "show", BASELINE + ":" + name]).stdout)
        run(["git", "apply", "--check", str(stage / "integration.patch")], cwd=check_tree)
        run(["git", "apply", str(stage / "integration.patch")], cwd=check_tree)
        for _, name in records:
            if (check_tree / name).read_bytes() != (REPO / name).read_bytes():
                raise AssertionError("Patch output differs: " + name)

        evidence = PREFIX / "research/20261008_compressed_certificates/verify_saved_evidence.py"
        saved_audit = run([sys.executable, str(stage / evidence)], cwd=stage).stdout.decode()
        # Import every test module from the snapshot, without a second timed suite.
        # This checks that the historical oracles and other import dependencies
        # were included in the archive instead of accidentally borrowed locally.
        discovery = run([sys.executable, "-c",
            "import unittest; loader=unittest.TestLoader(); s=loader.discover('tests'); "
            "assert not loader.errors, loader.errors; "
            "print('Discovered',s.countTestCases(),'tests')"],
            cwd=stage / PREFIX / "fast").stdout.decode()
        # Discard generated caches before computing the manifest.
        for cache in list(stage.rglob("__pycache__")):
            shutil.rmtree(cache)
        provenance = {
            "release": RELEASE,
            "created_utc": datetime.now(timezone.utc).isoformat(),
            "baseline_checkout": BASELINE,
            "preceding_subtree_revision": SUBTREE_BASELINE,
            "fast_tree": "e7222244bb0d7f35cf7f34f83228b350240e4d13",
            "python": sys.version,
            "platform": platform.platform(),
            "patch_sha256": digest(stage / "integration.patch"),
            "patch_check": "git apply --check, apply, and byte comparison all passed",
            "patch_changes": [{"status": s, "path": p} for s, p in records],
            "snapshot_test_discovery": discovery.strip(),
            "snapshot_evidence_check": saved_audit.strip(),
        }
        (stage / "PROVENANCE.json").write_text(json.dumps(provenance, indent=2) + "\n")
        members = sorted(p for p in stage.rglob("*") if p.is_file())
        (stage / "SHA256SUMS").write_text("".join(
            digest(p) + "  " + p.relative_to(stage).as_posix() + "\n" for p in members))
        result = run([sys.executable, "verify_release.py"], cwd=stage)
        built_zip = work / (RELEASE + ".zip")
        with zipfile.ZipFile(built_zip, "w", compression=zipfile.ZIP_DEFLATED,
                             compresslevel=9) as archive:
            for path in sorted(stage.rglob("*")):
                if path.is_file():
                    info = zipfile.ZipInfo((Path(RELEASE) / path.relative_to(stage)).as_posix(),
                                          date_time=(2026, 10, 8, 0, 0, 0))
                    info.compress_type = zipfile.ZIP_DEFLATED
                    info.external_attr = 0o100644 << 16
                    archive.writestr(info, path.read_bytes())
        with zipfile.ZipFile(built_zip) as archive:
            if archive.testzip() is not None:
                raise AssertionError("ZIP integrity check failed")
        zip_path = output / built_zip.name
        pdf_path = output / article.name
        atomic_write(zip_path, built_zip.read_bytes())
        atomic_write(pdf_path, article.read_bytes())
        print(result.stdout.decode().strip())
        print(json.dumps({"zip": str(zip_path), "zip_bytes": zip_path.stat().st_size,
                          "pdf": str(pdf_path), "pdf_bytes": pdf_path.stat().st_size,
                          "files": len(members)+1, "changed_paths": len(records),
                          "patch_check": "passed", "snapshot_test_discovery": discovery.strip()},
                         indent=2))


if __name__ == "__main__":
    main()
