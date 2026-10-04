#!/usr/bin/env python3
"""Negative tests of this audit's own checker; original packet remains read-only."""
import copy,json,pathlib,subprocess,sys,tempfile
OUT=pathlib.Path(__file__).resolve().parent
DAG=pathlib.Path('/workspace/shared/sandpile-unrestricted-stabilization-20261004/evidence/polynomial-dag.json')
original=json.loads(DAG.read_text());tests=[]
def changed(name,fn):
 d=copy.deepcopy(original);fn(d);tests.append((name,d))
def eq(d,name):return next(x for x in d['equalities'] if x[2]==name)
def mac(d,name):return next(x for x in d['macros'] if x['name']==name)
changed('remove exact-sixteenth equality',lambda d:d['equalities'].remove(eq(d,'radix.sixteenthEquation')))
changed('binary support instead of full cap',lambda d:d['gates'].__setitem__(int(mac(d,'supersolution.support')['mask'][5:]),['*','constant:1',d['ports']['interior_mask']]))
changed('drop one neighbor stream',lambda d:d['gates'].__setitem__(int(d['ports']['balance_left'][5:]),['+',d['gates'][int(d['ports']['balance_left'][5:])][1],'constant:0']))
changed('misreport precision port',lambda d:d['ports'].__setitem__('precision','constant:2'))
changed('allow endpoint heights six and seven',lambda d:d['equalities'].remove(eq(d,'endpoint.exclude67.extract')))
changed('omit raw patch conversion',lambda d:d['gates'].__setitem__(int(mac(d,'patch.rows')['value'][5:]),['+','constant:0',d['ports']['patch']]))
changed('weaken shell to full-box mask',lambda d:d['gates'].__setitem__(int(d['ports']['interior_mask'][5:]),['+','constant:0',d['ports']['all_slots']]))
changed('change POWER congruence coefficient',lambda d:d['gates'].__setitem__(int(eq(d,'patch.shift.eq8')[0][5:]),['+','witness:patch.shift.t','constant:0']))
changed('wrong final output',lambda d:d.__setitem__('output','gate:0'))
changed('remove one positive witness',lambda d:d['witnesses'].pop())
records=[]
with tempfile.TemporaryDirectory(prefix='sandpile-own-negative-tests-') as td:
 td=pathlib.Path(td)
 for name,d in tests:
  path=td/'mutated.json';path.write_text(json.dumps(d));receipt=td/'must-not-exist.json'
  for opt in [False,True]:
   cmd=[sys.executable]+(['-O'] if opt else [])+[str(OUT/'check_exact.py'),'--dag',str(path),'--allow-unsealed-test-data','--receipt',str(receipt)]
   p=subprocess.run(cmd,capture_output=True,text=True)
   if p.returncode==0 or receipt.exists():raise ValueError('Mutation escaped: '+name)
   records.append({'mutation':name,'optimized':opt,'rejected':True,'error':p.stderr.strip().splitlines()[-1]})
r={'status':'PASS','mutations':len(tests),'expected_rejections':len(records),'hash_guard_explicitly_disabled_for_temporary_test_data_only':True,'results':records}
(OUT/'mutation-receipt.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(json.dumps(r,indent=2,sort_keys=True))
