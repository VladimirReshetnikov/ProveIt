"""Positive/negative proof replay across normal and optimized Python."""
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]

def run():
    cases=json.loads((ROOT/"tests/composition_cases.json").read_text())
    checkers=["code/checker.py","code/checker_compact.py","code/checker_ast.py",
              "code/readable_checker.py"]
    rows=[]
    for name in checkers:
        for case in cases:
            for optimized in (False, True):
                command=[sys.executable]+(["-O"] if optimized else [])+[str(ROOT/name)]
                p=subprocess.run(command,input=json.dumps(case["packet"]),text=True,
                                 capture_output=True,timeout=15)
                accepted=p.returncode == 0 and p.stdout == "ACCEPT\n"
                row=dict(checker=name,case=case["name"],optimized=optimized,
                         expected=case["accept"],accepted=accepted)
                if accepted != case["accept"]:
                    row["stderr"]=p.stderr[-1000:]
                rows.append(row)
        for payload in ("", "{", "null", "true", "3", '"bad"', "{}"):
            p=subprocess.run([sys.executable,str(ROOT/name)],input=payload,text=True,
                             capture_output=True,timeout=15)
            rows.append(dict(checker=name,case="malformed_top_level:"+payload,
                             optimized=False,expected=False,
                             accepted=p.returncode==0 and p.stdout=="ACCEPT\n"))
    return dict(executions=len(rows),failures=[r for r in rows if r["accepted"]!=r["expected"]],rows=rows)

if __name__ == "__main__":
    result=run()
    (ROOT/"evidence/checker_validation.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k!="rows"},indent=2))
    raise SystemExit(bool(result["failures"]))
