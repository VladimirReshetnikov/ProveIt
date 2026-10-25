#!/usr/bin/env python3
import pathlib,subprocess,sys,tempfile,json
ROOT=pathlib.Path(__file__).resolve().parent
with tempfile.TemporaryDirectory() as td:
 out=pathlib.Path(td)/'residuals.tex'
 p=subprocess.run([sys.executable,'-B',str(ROOT/'report/render_residuals.py'),'--equation',str(ROOT/'signed/balanced244/equation.json'),'--out',str(out)],check=True,text=True,capture_output=True)
 if out.read_bytes()!=(ROOT/'report/residuals.tex').read_bytes():raise ValueError('Printed equation differs from literal residuals')
 report=json.loads(p.stdout);report['status']='PASS';print(json.dumps(report,indent=2))
