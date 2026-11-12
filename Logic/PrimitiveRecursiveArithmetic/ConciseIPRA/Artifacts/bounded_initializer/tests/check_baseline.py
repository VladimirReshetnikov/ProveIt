"""Replay the original upstream fixtures against the two frozen minimum attainers."""
from pathlib import Path
import json
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
cases=json.loads((ROOT/"tests/baseline_cases.json").read_text())["cases"]
rows=[]
for checker in ("reference/current_bytes.py","reference/current_ast.py"):
    for case in cases:
        for optimized in (False,True):
            command=[sys.executable]+(["-O"] if optimized else [])+[str(ROOT/checker)]
            run=subprocess.run(command,input=json.dumps(case["packet"]),text=True,
                               capture_output=True,timeout=15)
            accepted=run.returncode==0 and run.stdout=="ACCEPT\n"
            rows.append(dict(checker=checker,case=case["name"],optimized=optimized,
                             expected=case["accept"],accepted=accepted))
failures=[row for row in rows if row["expected"]!=row["accepted"]]
result=dict(cases=len(cases),executions=len(rows),failures=failures,rows=rows)
(ROOT/"evidence/baseline_validation.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(dict(baseline_executions=len(rows),failures=failures)))
raise SystemExit(bool(failures))
