#!/usr/bin/env python3
import pathlib,subprocess,sys,tempfile,json
R=pathlib.Path(__file__).resolve().parent
with tempfile.TemporaryDirectory()as td:
 out=pathlib.Path(td)/'residuals.tex'
 p=subprocess.run([sys.executable,'-B',str(R/'report/render_residuals.py'),'--equation',str(R/'signed/principal217/equation.json'),'--out',str(out)],check=True,capture_output=True,text=True)
 if out.read_bytes()!=(R/'report/residuals.tex').read_bytes():raise ValueError('Printed equation differs')
 parsed=subprocess.run([sys.executable,'-B',str(R/'audit/check_literal_appendix.py'),str(R)],check=True,capture_output=True,text=True)
 print(json.dumps({'status':'PASS','regenerated':json.loads(p.stdout),'independently_parsed':json.loads(parsed.stdout)},indent=2))
