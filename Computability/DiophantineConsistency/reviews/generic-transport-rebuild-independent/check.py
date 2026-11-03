#!/usr/bin/env python3
"""Audit frozen generic transport rebuild without invoking Lean."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/generic-transport-rebuild';o=P/'observations/attempt01';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['root'])
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['status']=='PASS' and sha(P/'run.py')==t['runner_sha256'],'result/runner')
for p,h in t['pins'].items():need(sha(p)==h,'pin '+p)
old={'TransportOrder':('/tmp/tenpositive-transport-order-wpjgqf72/TransportOrder.lean','a72bc5ad47a0188de95ea12713ea6d273375c6c81233d6f8720d5099579d9723'),'CarrierTransport':('/tmp/tenpositive-carrier-transport-r9_49vrn/CarrierTransport.lean','15b76092ae7172e11b07735a918fec18051df29ba54e68f36939a8a47883e990'),'OffsetBound':('/tmp/tenpositive-offset-bound-v3g8qedt/OffsetBound.lean','696900c026b495235e88def39125f56b774341f1ed6ddd5aaccc5a9d0080525b')}
for _,(p,h) in old.items():need(sha(p)==h,'old pin '+p)
z=pathlib.Path(old['TransportOrder'][0]).read_bytes();need(z.startswith(b'import Direct80RankEquality\n') and (P/'TransportOrder.lean').read_bytes()==z.removeprefix(b'import Direct80RankEquality\n'),'first delta')
z=pathlib.Path(old['CarrierTransport'][0]).read_bytes();oldline=b'import TransportOrder\n';newlines=oldline+b'import DiophantineConsistency.ArithmeticGcdNormalization\nimport DiophantineConsistency.ModelDifferenceRing\n';need(z.startswith(oldline) and (P/'CarrierTransport.lean').read_bytes()==z.replace(oldline,newlines,1),'second delta')
need((P/'OffsetBound.lean').read_bytes()==pathlib.Path(old['OffsetBound'][0]).read_bytes(),'third delta')
expected={'TransportOrder':'6696792c784a1f6dc56e06076350015ca235a8973caf3ecda2a9328128056da2','CarrierTransport':'05b15e987fa4eeb289936785ac2aaf7d4d2b0916fe29fd44ad9d52402c9da53d','OffsetBound':'1702af9273f8d0211bc57a013b97fe58c7e58a0791bb4b217f1207c6a27923a4'}
need([x['name'] for x in t['stages']]==list(expected),'stage order');selected=[]
for st in t['stages']:
 n=st['name'];s=P/(n+'.lean');out=o/(n+'.stdout');err=o/(n+'.stderr')
 need(st['exit']==0 and st['reason'] is None and st['object_sha256']==sha(root/(n+'.olean'))==expected[n],'stage '+n)
 need(sha(s)==sha(o/(n+'.source.txt'))==sha(root/(n+'.lean')),'source '+n)
 need(sha(out)==st['stdout_sha256'] and sha(err)==st['stderr_sha256'],'logs '+n)
 reports=re.findall(r'^#print axioms ([\w.]+)$',s.read_text(),re.M)
 need(out.read_text()==''.join(f"'{x}' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for x in reports) and err.read_text()=='','reports '+n)
 for m in re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M):
  rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None);need(p is not None,'selected '+m)
  if m in expected:need(sha(p)==expected[m],'stage object '+m)
  else:need(str(p) in t['pins'] and t['pins'][str(p)]==sha(p),'external pin '+m)
  selected.append({'stage':n,'module':m,'path':str(p),'sha256':sha(p)})
print(json.dumps({'status':'PASS','objects':expected,'selected':selected,'lean_replayed':False},indent=2,sort_keys=True))
