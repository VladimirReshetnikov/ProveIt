"""Build and check the additive patch without fetching or modifying any repository."""
from pathlib import Path
from hashlib import sha1, sha256
import difflib
import json
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REPO_PREFIX = Path("Topology/UnknotRecognition")
FAST = ROOT/"fast"


def blob(data):
    return sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()


def main():
    provenance = json.loads((ROOT/"provenance/source_inventory.json").read_text())
    baseline = {row["path"]:row for row in provenance["materialized_baseline_files"]}
    for path,row in baseline.items():
        data=(ROOT/path).read_bytes()
        if blob(data)!=row["git_blob_sha"]:
            raise RuntimeError("A pinned baseline file changed: "+path)
    added = []
    omitted = []
    for source in sorted(FAST.rglob("*")):
        if not source.is_file() or "__pycache__" in source.parts or ".pytest_cache" in source.parts:
            continue
        relative=source.relative_to(ROOT).as_posix()
        if relative in baseline:
            continue
        if source.suffix not in (".py",".md") and source.name!="measurements.json":
            omitted.append(relative)
            continue
        data=source.read_bytes()
        if not data.endswith(b"\n"):
            raise RuntimeError("Added text needs a final newline: "+relative)
        added.append((relative,data))
    pieces=[]
    for relative,data in added:
        target=(REPO_PREFIX/relative).as_posix()
        pieces.append(f"diff --git a/{target} b/{target}\nnew file mode 100644\n")
        pieces.extend(difflib.unified_diff([],data.decode().splitlines(keepends=True),
                                           fromfile="/dev/null",tofile="b/"+target))
    patch=ROOT/"integration.patch"
    patch.write_text("".join(pieces))
    with tempfile.TemporaryDirectory(prefix="proveit_patch_check_") as scratch:
        testroot=Path(scratch)
        subprocess.run(["git","init","-q",str(testroot)],check=True)
        for relative in baseline:
            destination=testroot/REPO_PREFIX/relative
            destination.parent.mkdir(parents=True,exist_ok=True)
            shutil.copy2(ROOT/relative,destination)
        subprocess.run(["git","apply","--check","--whitespace=error-all",str(patch)],
                       cwd=testroot,check=True)
        subprocess.run(["git","apply","--whitespace=error-all",str(patch)],
                       cwd=testroot,check=True)
        for relative,data in added:
            if (testroot/REPO_PREFIX/relative).read_bytes()!=data:
                raise RuntimeError("Applied file mismatch: "+relative)
        for relative,row in baseline.items():
            if blob((testroot/REPO_PREFIX/relative).read_bytes())!=row["git_blob_sha"]:
                raise RuntimeError("Patch changed a baseline file: "+relative)
    entries=[{"package_path":p,"repository_path":(REPO_PREFIX/p).as_posix(),
              "operation":"add","bytes":len(data),"git_blob_sha":blob(data),
              "sha256":sha256(data).hexdigest(),
              "role":"production module" if p.startswith("fast/fastunknot/") else
                     "regression test" if p.startswith("fast/tests/") else "research support"}
             for p,data in added]
    manifest={"schema":"additive-integration-manifest-v1",
              "baseline_commit":provenance["baseline_commit"],
              "patch":"integration.patch","patch_bytes":patch.stat().st_size,
              "baseline_files_checked":len(baseline),
              "validation":{"applies":True,"added_files_match_snapshot":True,
                            "baseline_files_unchanged":True},
              "added_files":entries,"retained_artifacts_not_in_patch":omitted,
              "scope":"Code, tests and research support; retained large records and historical source ZIP remain in the report package. Default recognition schedule is unchanged."}
    (ROOT/"integration_manifest.json").write_text(json.dumps(manifest,indent=2)+"\n")
    (ROOT/"validation/integration_check.json").write_text(json.dumps(
        {"status":"PASS","added_files":len(added),"baseline_files":len(baseline),
         "patch_bytes":patch.stat().st_size,"builder_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
         "checks":["Git apply --check with whitespace errors rejected",
                   "Applied additions compared byte for byte with snapshot",
                   "Every pinned baseline file remained unchanged"]},indent=2)+"\n")
    print("Patch verified:",len(added),"additions;",len(baseline),"unchanged baseline files.")


if __name__=="__main__":
    main()
