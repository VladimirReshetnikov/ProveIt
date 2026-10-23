"""Owned static audit. Current bytes are verified; baseline bytes are not bundled."""
from pathlib import Path
import hashlib,json,re
if not __debug__:
    raise RuntimeError("Run without Python optimization.")
ROOT=Path(__file__).resolve().parent
PREFIXES=("BusyBeaver.","FirstOrder.","ZF.","BoundedZFCConsistency.")
manifest=json.loads((ROOT/"source_manifest.json").read_text())
results={}
for label,snapshot in manifest["snapshots"].items():
    rows={r["module"]:r for r in snapshot["rows"]}
    if label=="current":
        base=ROOT/"snapshots"/label
        actual={p.relative_to(base).as_posix() for p in base.rglob("*") if p.is_file()}
        assert actual=={r["path"] for r in rows.values()},("membership",label)
        for mod,row in rows.items():
            b=(base/row["path"]).read_bytes()
            assert hashlib.sha256(b).hexdigest()==row["sha256"],row["path"]
            assert len(b)==row["bytes"] and len(b.splitlines())==row["lines"],row["path"]
            assert hashlib.sha1(b"blob "+str(len(b)).encode()+b"\0"+b).hexdigest()==row["git_blob_sha"],row["path"]
            imports=[x for line in re.findall(r"^import\s+([^\n]+)",b.decode(),re.M) for x in line.split()]
            assert imports==row["imports"],row["path"]
    else:
        assert label=="baseline"
        assert not (ROOT/"snapshots"/"baseline").exists()
    seen=set()
    def visit(mod):
        if mod in seen:return
        assert mod in rows,("unresolved import",label,mod)
        seen.add(mod)
        for nxt in rows[mod]["imports"]:
            if nxt.startswith(PREFIXES):visit(nxt)
    visit("BusyBeaver.ZFC.KEndpoint215")
    assert seen==set(rows),("closure",label)
    metrics={"modules":len(seen),"bytes":sum(r["bytes"] for r in rows.values()),"lines":sum(r["lines"] for r in rows.values())}
    assert all(metrics[k]==snapshot[k] for k in metrics)
    results[label]=metrics
results["delta"]={k:results["current"][k]-results["baseline"][k] for k in results["current"]}
results["scope"]="Current pinned source integrity and static closure; baseline recorded ledger graph and metric sums only. No Lean, Rocq, generator or received program executed."
rocq=json.loads((ROOT/"rocq_source_manifest.json").read_text())
for row in rocq["rows"]:
    b=(ROOT/row["saved_path"]).read_bytes()
    assert hashlib.sha256(b).hexdigest()==row["sha256"]
    assert hashlib.sha1(b"blob "+str(len(b)).encode()+b"\0"+b).hexdigest()==row["git_blob_sha"]
    assert len(b)==row["bytes"]
results["selected_rocq_sources_verified"]=len(rocq["rows"])
print(json.dumps(results,indent=2))
