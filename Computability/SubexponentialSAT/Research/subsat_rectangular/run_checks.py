#!/usr/bin/env python3
"""Recompute all exact certificates using Python's standard library."""
from pathlib import Path
import json
import subprocess
import sys
ROOT=Path(__file__).resolve().parent
CASES=[("schedule","check_schedule.py"),("streamed","check_streamed.py"),
       ("hermite","check_hermite.py"),("inventory","check_inventory.py")]
def main():
    (ROOT/"results").mkdir(exist_ok=True)
    ledger=[]
    for stem,script in CASES:
        outputs=[]
        for optimized in [False,True]:
            command=[sys.executable]+(["-O"] if optimized else [])+[str(ROOT/"code"/script)]
            proc=subprocess.run(command,cwd=ROOT,text=True,capture_output=True,check=True)
            outputs.append(json.loads(proc.stdout))
        if outputs[0]!=outputs[1]:
            raise RuntimeError("Normal and optimized outputs differ: "+script)
        (ROOT/"results"/(stem+".json")).write_text(json.dumps(outputs[0],indent=2)+"\n")
        ledger.append({"script":script,"normal":"passed","optimized":"passed","outputs_equal":True})
    (ROOT/"results"/"replay.json").write_text(json.dumps({"status":"passed","checks":ledger},indent=2)+"\n")
    print(json.dumps({"status":"passed","checks":ledger},indent=2))
if __name__=="__main__":main()
