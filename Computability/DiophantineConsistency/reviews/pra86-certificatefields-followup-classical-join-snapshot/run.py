#!/usr/bin/env python3
"""Execute exactly the driver bytes whose hash is recorded by the replay."""
from pathlib import Path
import hashlib,os,subprocess,sys
here=Path(__file__).resolve().parent;driver=here/'replay.py';payload=driver.read_bytes();digest=hashlib.sha256(payload).hexdigest();launcher=hashlib.sha256(Path(__file__).read_bytes()).hexdigest();env=dict(os.environ,PRA14_JOIN_EXEC_SHA256=digest,PRA14_JOIN_LAUNCHER_SHA256=launcher)
loader='import hashlib,os,sys; p=sys.argv[1]; sys.argv=[p,*sys.argv[2:]]; data=sys.stdin.buffer.read(); assert hashlib.sha256(data).hexdigest()==os.environ["PRA14_JOIN_EXEC_SHA256"]; globals()["__file__"]=p; exec(compile(data,p,"exec"))'
result=subprocess.run([sys.executable,'-c',loader,str(driver),*sys.argv[1:]],input=payload,env=env)
raise SystemExit(result.returncode)
