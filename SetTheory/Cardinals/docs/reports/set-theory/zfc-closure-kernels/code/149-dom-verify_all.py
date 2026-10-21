#!/usr/bin/env python3
"""Reproduce all finite checks; --runtime reruns the quantified physical proof.

Python standard library only. Run with assertions enabled. Outputs are written
to a temporary directory, leaving the authenticated package unchanged.
"""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,sys,tempfile

ROOT=Path(__file__).resolve().parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def run(script,*args):
    command=[sys.executable,"-B",str(ROOT/script),*map(str,args)]
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE="1")
    result=subprocess.run(command,cwd=ROOT,env=env,check=True,capture_output=True,text=True)
    print(result.stdout.rstrip(),flush=True)
    if result.stderr.strip():print(result.stderr.rstrip(),file=sys.stderr,flush=True)
    return result.stdout

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--runtime",action="store_true",help="Recompute all 6,176 quantified runtime derivations.")
    ap.add_argument("--skip-manifest",action="store_true",help="For authoring before the final manifest exists.")
    a=ap.parse_args()
    assert __debug__,"Assertions must be enabled; do not use python -O."
    if not a.skip_manifest:
        m=json.loads((ROOT/"manifest.json").read_text())
        for row in m["files"]:
            p=ROOT/row["path"]
            assert p.is_file() and p.stat().st_size==row["bytes"],row["path"]
            assert digest(p)==row["sha256"],row["path"]
        print("AUTHENTICATED_FILE_MANIFEST_PASS",len(m["files"]),"files",flush=True)

    proof=ROOT/"theory/dominated_rho8_full_certificate.json"
    first=json.loads(run("theory/check_classical_compact.py",proof))
    second=json.loads(run("audits/audit_classical_independent.py",proof))
    assert first["verified"] and second["verified"]
    assert second["proof_nodes"]==3728 and second["roots"]["rho8"]==3727
    run("source/verify_release.py")
    run("audits/verify_source_schedule.py",ROOT/"source/baseline_sites219.json",
        ROOT/"source/sites218.json","--common")

    native=ROOT/"binary/machine/k218.native.tm"
    compact=ROOT/"binary/machine/k218.compact.tm"
    recipe=ROOT/"binary/machine/transition_recipe.json"
    sites=ROOT/"binary/machine/sites218.json"
    assert sites.read_bytes()==(ROOT/"source/sites218.json").read_bytes()
    run("audits/audit_compact.py",native,compact,recipe)
    with tempfile.TemporaryDirectory(prefix="proveit_k218_verify_") as tmp:
        tmp=Path(tmp)
        rebuilt=tmp/"rebuilt.native.tm"
        run("binary/code/rebuild_table.py",ROOT/"binary/machine/k219.baseline.native.tm",recipe,rebuilt)
        assert rebuilt.read_bytes()==native.read_bytes()
        # This independent replay compares every blank-start transition with
        # the exact reference and verifies all final one-cells and zero exterior.
        boot=json.loads(run("audits/audit_blank_independent.py",native,
             ROOT/"binary/provenance/unfolded221.reference.tm"))
        assert boot==json.loads((ROOT/"audits/blank218_independent_receipt.json").read_text())

        stored=json.loads((ROOT/"binary/validation/runtime.json").read_text())
        cases=json.loads((ROOT/"binary/validation/runtime_cases.json").read_text())
        source=json.loads(sites.read_text())
        wanted=[(i,pos)for i,(_,op,arg)in enumerate(source)
                for pos in ((False,True)if op=="CD"else(False,))]
        assert [(x["site_index"],x["positive"])for x in cases]==wanted
        assert len(cases)==6176
        assert stored["status"]=="UNIVERSAL_MATHEMATICAL_PASS"
        assert stored["expected_cases"]==stored["proved_cases"]==6176
        assert stored["failures"]==[]
        assert stored["table_sha256"]==digest(native)
        assert stored["sites_sha256"]==digest(sites)
        assert stored["checker_sha256"]==digest(ROOT/"binary/code/runtime/symbolic_runtime.py")
        assert stored["helper_sha256"]==digest(ROOT/"binary/code/runtime/independent_runtime.py")
        assert all(x["duration"][0]>0 and all(v>=0 for v in x["duration"])for x in cases)
        print("STORED_CASE_INVENTORY_PASS",len(cases),
              "cases; use --runtime to regenerate every derivation",flush=True)
        if a.runtime:
            output=tmp/"runtime"
            run("binary/code/validate_native.py",native,sites,output)
            fresh=json.loads((output/"runtime.json").read_text())
            assert fresh["status"]=="UNIVERSAL_MATHEMATICAL_PASS" and fresh["proved_cases"]==6176
            assert (output/"runtime_cases.json").read_bytes()==(ROOT/"binary/validation/runtime_cases.json").read_bytes()
            assert (output/"startup.json").read_bytes()==(ROOT/"binary/validation/startup.json").read_bytes()
            print("FULL_RUNTIME_REPLAY_AND_EXACT_RECEIPTS_PASS",flush=True)
    print(json.dumps({"status":"ALL_REQUESTED_CHECKS_PASS","working_states":218,
                      "quantified_runtime_recomputed":a.runtime,
                      "proof_assistant_endpoint":"Not newly compiled; see report."},indent=2),flush=True)

if __name__=="__main__":main()

