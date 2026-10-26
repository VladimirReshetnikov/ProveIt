#!/usr/bin/env python3
import pathlib,json,hashlib,subprocess,sys
R=pathlib.Path(__file__).resolve().parent
bindings=json.loads((R/'height_one/SOURCE_BINDINGS.json').read_text());checked=[]
for b in bindings:
 a=R/'height_one'/b['local'];p=R/b['enclosing_source']
 if a.read_bytes()!=p.read_bytes()or hashlib.sha256(a.read_bytes()).hexdigest()!=b['sha256']:raise ValueError('Source binding mismatch: '+b['local'])
 checked.append(b['enclosing_source'])
audits={}
for script,path in [('recollect_polynomials.py',R),('check_positive_payloads.py',R/'scalar/positive10')]:
 p=subprocess.run([sys.executable,'-B',str(R/'audit'/script),str(path)],check=True,text=True,capture_output=True);audits[script]=json.loads(p.stdout)
print(json.dumps({'status':'PASS','height_source_bindings':checked,'independent_audits':audits},indent=2))
