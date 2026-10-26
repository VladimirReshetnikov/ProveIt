#!/usr/bin/env python3
import pathlib,subprocess,sys,tempfile,json
R=pathlib.Path(__file__).resolve().parent
p=subprocess.run([sys.executable,'-B',str(R/'audit/check_literal_appendix.py'),str(R)],check=True,capture_output=True,text=True)
print(json.dumps({'status':'PASS','independent_literal_parse':json.loads(p.stdout)},indent=2))
