#!/usr/bin/env python3
import pathlib,json,hashlib,subprocess,sys
R=pathlib.Path(__file__).resolve().parent
bindings=json.loads((R/'height_one/SOURCE_BINDINGS.json').read_text());checked=[]
for b in bindings:
 a=R/'height_one'/b['local'];p=R/b['enclosing_source']
 if a.read_bytes()!=p.read_bytes() or hashlib.sha256(a.read_bytes()).hexdigest()!=b['sha256']:raise ValueError('Source mismatch: '+b['local'])
 checked.append(b['enclosing_source'])
cp=subprocess.run([sys.executable,'-B',str(R/'audit/check_component_bindings.py'),str(R)],check=True,text=True,capture_output=True)
audit={'strict_source_bindings':json.loads(cp.stdout)}
for name,path in [('recollect_polynomials.py',R),('check_scalar_payloads.py',R/'scalar/integer11'),('check_positive_payloads.py',R/'scalar/positive10')]:
 p=subprocess.run([sys.executable,'-B',str(R/'audit'/name),str(path)],check=True,text=True,capture_output=True)
 audit[name]=json.loads(p.stdout)
print(json.dumps({'status':'PASS','source_bindings':checked,'independent_audits':audit},indent=2))
