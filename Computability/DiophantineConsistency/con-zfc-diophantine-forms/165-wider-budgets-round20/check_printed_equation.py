#!/usr/bin/env python3
import pathlib,subprocess,sys,tempfile,json
R=pathlib.Path(__file__).resolve().parent
with tempfile.TemporaryDirectory() as td:
 out=pathlib.Path(td)/'residuals.tex'
 cp=subprocess.run([sys.executable,'-B',str(R/'report/render_residuals.py'),'--equation',str(R/'signed/balanced238/equation.json'),'--out',str(out)],check=True,text=True,capture_output=True)
 if out.read_bytes()!=(R/'report/residuals.tex').read_bytes():raise ValueError('Printed residuals differ from literal principal')
 j=json.loads(cp.stdout);j['status']='PASS'
 parsed=subprocess.run([sys.executable,'-B',str(R/'audit/check_literal_appendix.py'),str(R)],check=True,capture_output=True,text=True)
 j['independent_literal_parse']=json.loads(parsed.stdout);print(json.dumps(j,indent=2))
