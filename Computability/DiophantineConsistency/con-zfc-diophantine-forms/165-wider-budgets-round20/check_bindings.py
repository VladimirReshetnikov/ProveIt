#!/usr/bin/env python3
import pathlib,json,hashlib,subprocess,sys
R=pathlib.Path(__file__).resolve().parent
bindings=json.loads((R/'height_one/SOURCE_BINDINGS.json').read_text());checked=[]
if len(bindings)!=5:raise ValueError('Expected five height sources')
for b in bindings:
 a=R/'height_one'/b['local'];s=R/b['enclosing_source']
 if a.read_bytes()!=s.read_bytes() or hashlib.sha256(a.read_bytes()).hexdigest()!=b['sha256']:raise ValueError('Source binding mismatch: '+b['local'])
 checked.append({'local':b['local'],'enclosing_source':b['enclosing_source'],'sha256':b['sha256']})
cp=subprocess.run([sys.executable,'-B',str(R/'audit/check_scalar_payloads.py'),str(R/'scalar')],check=True,capture_output=True,text=True)
print(json.dumps({'status':'PASS','bindings':checked,'independent_scalar_numerals':json.loads(cp.stdout)},indent=2))
