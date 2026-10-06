"""Run checks in an isolated new directory and create SHA-256 receipts.

The source package is read-only. The output directory must not exist and must
lie outside the companion source directory. Failures exit nonzero; existing
outputs are never overwritten. No network or package installation is performed.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_write(path, value):
    with path.open("x",encoding="utf-8",newline="\n") as stream:
        stream.write(json.dumps(value,sort_keys=True,indent=2)+"\n")


def input_files():
    return sorted(path for path in ROOT.rglob("*") if path.is_file()
                  and "__pycache__" not in path.parts and path.suffix != ".pyc")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",required=True,type=Path,help="New directory outside the companion; its parent must exist")
    parser.add_argument("--extended",action="store_true")
    parser.add_argument("--symbolic",action="store_true",help="Also run optional SymPy generic order-3 engine")
    parser.add_argument("--residuals",action="store_true",help="Also evaluate 80-digit Decimal diagnostics")
    args = parser.parse_args()
    output = args.output.resolve()
    if output == ROOT or ROOT in output.parents:
        parser.error("Output must lie outside the companion source directory")
    if os.path.lexists(args.output):
        parser.error("Output already exists; select a fresh directory (no files were overwritten)")
    inputs = {str(path.relative_to(ROOT)):digest(path) for path in input_files()}
    output.mkdir(exist_ok=False)
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1",PYTHONHASHSEED="0")
    flags = ["-I","-B"] + (["-O"] if sys.flags.optimize else [])
    # -I omits the script directory from sys.path; insert the verified package
    # location explicitly while retaining isolation from PYTHONPATH/user site.
    def run(script, arguments):
        bootstrap = ("import runpy,sys;script=sys.argv.pop(1);root=sys.argv.pop(1);"
                     "sys.path.insert(0,root);sys.argv[0]=root+'/'+script;"
                     "runpy.run_path(sys.argv[0],run_name='__main__')")
        command = [sys.executable,*flags,"-c",bootstrap,script,str(ROOT),*arguments]
        process = subprocess.run(command,cwd=output,env=env,check=False,capture_output=True,text=True)
        if process.stderr:
            sys.stderr.write(process.stderr)
        process.check_returncode()
        return json.loads(process.stdout)
    results = {"checks.json":run("run_checks.py",["--extended"] if args.extended else [])}
    if args.symbolic:
        results["symbolic.json"] = run("symbolic_all_orders.py",["--order","3"])
    if args.residuals:
        results["residuals.json"] = run("residuals.py",["--precision","80"])
    for name,value in sorted(results.items()):
        canonical_write(output/name,value)
    canonical_write(output/"manifest.json",{
        "schema":"cylindrical-kings-companion-build-v1",
        "inputs_sha256":inputs,
        "outputs_sha256":{name:digest(output/name) for name in sorted(results)},
        "options":{"extended":args.extended,"symbolic":args.symbolic,"residuals":args.residuals},
        "status":"PASS"})
    print("PASS: isolated checks and manifest written to "+str(output))


if __name__ == "__main__":
    main()
