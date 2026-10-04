#!/usr/bin/env python3
"""Supplemental release-only flags and output-hardlink boundary checks."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
ROOT=Path(sys.argv[1]); OUT=Path(sys.argv[2]); DOSSIER=Path(sys.argv[3]); OUT.mkdir()
accepted=json.loads((DOSSIER/'ACCEPTED_BINDINGS.json').read_bytes())
for n,h in accepted['sha256'].items():
    assert hashlib.sha256((ROOT/n).read_bytes()).hexdigest()==h,(n,'hash mismatch')
results=[]
for name,flags in [('not-isolated',['-S','-B']),('site-enabled',['-I','-B']),('bytecode-enabled',['-I','-S']),('optimized',['-I','-S','-B','-O'])]:
    for helper in ('release64.py','build_report64.py','selftest64.py'):
        r=subprocess.run([sys.executable,*flags,str(ROOT/'tools'/helper),'check-inputs'],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        assert r.returncode!=0 and b'Use python3 -I -S -B without optimization' in r.stdout,(name,helper,r.stdout)
        results.append({'name':name+'-'+helper,'status':'PASS','exit_status':r.returncode})
(OUT/'sentinel').write_bytes(b'External expendable output sentinel.\n'); os.link(OUT/'sentinel',OUT/'existing-hardlink')
r=subprocess.run([sys.executable,'-I','-S','-B',str(ROOT/'tools/release64.py'),'prepare','--output-dir',str(OUT/'existing-hardlink')],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
assert r.returncode==2 and b'Output must be fresh' in r.stdout
assert (OUT/'sentinel').read_bytes()==(OUT/'existing-hardlink').read_bytes()==b'External expendable output sentinel.\n'
results.append({'name':'reject-existing-hardlink-output','status':'PASS','sentinel_preserved':True})
receipt={'status':'PASS','tests':results,'test_count':len(results),'accepted_tool_sha256':{n:h for n,h in accepted['sha256'].items() if n.endswith('.py')}}
(DOSSIER/'SUPPLEMENTAL_BOUNDARIES_RECEIPT.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
print(json.dumps({'status':'PASS','test_count':len(results)}))
