#!/usr/bin/env python3
"""Run every exact verification in normal and optimized Python.

No timing benchmarks run by default. Uses only the Python standard library.
Example from the extracted package root:
    python3 code/run_checks.py --output results/recheck
The output folder keeps normal and optimized results separately.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time


def main():
    package_root=Path(__file__).resolve().parents[1]
    code=package_root/"code"
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,default=package_root/"results/recheck")
    parser.add_argument("--modes",nargs="+",choices=("normal","optimized"),
                        default=["normal","optimized"])
    args=parser.parse_args()
    destination=args.output.resolve()
    destination.mkdir(parents=True,exist_ok=True)
    runs=[]
    failed=False
    for mode in args.modes:
        mode_dir=destination/mode
        mode_dir.mkdir(parents=True,exist_ok=True)
        commands=[
           ("verify_and_benchmark.py",["--validation-only","--output",str(mode_dir)],"verification.json"),
           ("verify_projective.py",["--output",str(mode_dir/"projective_verification.json")],"projective_verification.json"),
           ("check_independent_review.py",["--output",str(mode_dir/"independent_review.json")],"independent_review.json"),
           ("check_adaptive_modes.py",["--output",str(mode_dir/"adaptive_mode_results.json")],"adaptive_mode_results.json"),
           ("check_independent_fixture.py",["--output",str(mode_dir/"independent_fixture_result.json")],"independent_fixture_result.json"),
        ]
        for script,options,expected_file in commands:
            command=[sys.executable,"-B"]+(["-O"] if mode=="optimized" else [])+[str(code/script)]+options
            start=time.perf_counter()
            process=subprocess.run(command,cwd=package_root,text=True,capture_output=True)
            seconds=time.perf_counter()-start
            record={"mode":mode,"script":script,"seconds":seconds,
                    "exit_code":process.returncode,"result":str(Path(mode)/expected_file)}
            result_path=mode_dir/expected_file
            success=process.returncode==0 and result_path.is_file()
            if success:
                try: json.loads(result_path.read_text())
                except (ValueError,OSError): success=False
            record["status"]="passed" if success else "failed"
            if not success:
                failed=True
                (mode_dir/(Path(script).stem+".failure.log")).write_text(process.stdout+process.stderr)
            runs.append(record)
            print(json.dumps(record),flush=True)
    result={"status":"failed" if failed else "passed","benchmarks_run":False,
            "python":sys.version,"runs":runs}
    (destination/"release_checks.json").write_text(json.dumps(result,indent=2)+"\n")
    if failed: raise SystemExit(1)


if __name__=="__main__":main()
