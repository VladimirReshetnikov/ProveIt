#!/usr/bin/env python3
"""Independently check the frozen candidate rows and accepted receipt; no Lean replay."""
import collections, hashlib, json, pathlib, re

D = pathlib.Path(__file__).resolve().parents[2]
P = D/'research/ten-positive-79-ring-probe'
C = D/'research/ten-positive-79-mask-coordinate-probe/candidate.json'
OLD = D/'research/ten-positive-80-original-kernel-variant/equation.json'
def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def need(b, m):
    if not b: raise ValueError(m)
need(sha(C)=='5389bb9386371ca71790c5bbac3e5307f4b15ee278e560c13089d65f3ea25d00','candidate')
need(sha(OLD)=='90bb24c77fab7a19cd4d021e7cd73eda527f71fc361b0aaba6a5f8eaeb1f7be2','parent')
j=json.loads(C.read_text()); old=json.loads(OLD.read_text()); s=(P/'MaskCoordinate79.lean').read_text()
seg=s.split('def output79 ',1)[1].split('\nvariable {R',1)[0]
lines=seg.splitlines(); variables=[]; ports=[]; rows=[]
for line in lines:
    if m:=re.fullmatch(r'  let (\w+) : Expr \(Fin 10\) := \.var (\d+)',line): variables.append((m[1],int(m[2])))
    if m:=re.fullmatch(r'  let (port\d) : Expr \(Fin 10\) := \.constant \(p (\d+)\)',line): ports.append((m[1],int(m[2])))
    if m:=re.fullmatch(r'  let (r\d\d) := (\w+) ([+*\-]) (\w+)',line): rows.append(m.groups())
need(variables==list(zip(j['witnesses'],range(10))),'variable mapping')
need(ports==[(f'port{k}',k) for k in range(4)],'port mapping')
need(j['fixed_numerals']==old['fixed_numerals']==['beta','K0','MC','MF'],'port names')
need(len(rows)==len(j['source'])==j['operations']==79,'row count')
ref={name:name for name in j['witnesses']}; ref.update({name:f'port{k}' for k,name in enumerate(j['fixed_numerals'])})
for k,(candidate,actual) in enumerate(zip(j['source'],rows),1):
    name,op,a,b=candidate
    def cv(x): return str(x) if type(x)==int else ref[x]
    need(actual==(f'r{k:02}',cv(a),op,cv(b)),f'row {k}')
    need(name not in ref,'duplicate');ref[name]=f'r{k:02}'
need(ref[j['output']]=='r79' and lines[-1].strip()=='r79','output')
need(collections.Counter(row[1] for row in j['source'])=={'*':48,'+':17,'-':14},'operations')
need(j['source_parent_sha256']==sha(OLD),'parent pin')
newby={r[0]:r for r in j['source']}; oldby={r[0]:r for r in old['source']}
need([r[0] for r in j['source']]==[r[0] for r in old['source'] if r[0]!='C'],'old order')
need(oldby['C']==['C','-','qmF','alpha'] and oldby['G1']==['G1','*','bJ','qmF'] and oldby['G']==['G','+','G1','alpha'],'old rows')
need(newby['G1']==['G1','*','q','qmF'] and newby['G']==['G','-','G1','C'],'new rows')
need(all(newby[n]==r for n,r in oldby.items() if n not in {'C','G1','G'}),'remaining old rows')
need([r[0] for r in old['source'] if 'alpha' in r[2:]]==['C','G'] and [r[0] for r in old['source'] if 'G1' in r[2:]]==['G'],'changed dependencies')
t=json.loads((P/'observations/attempt02/terminal.json').read_text()); o=P/'observations/attempt02'
need(t['exit']==0 and t['reason'] is None,'inner exit')
need(t['source_sha256']==sha(P/'MaskCoordinate79.lean')==sha(o/'source.txt')==sha(pathlib.Path(t['output_root'])/'MaskCoordinate79.lean'),'source')
need(t['runner_sha256']==sha(P/'run.py'),'runner')
need(t['object_sha256']==sha(pathlib.Path(t['output_root'])/'MaskCoordinate79.olean')=='7fac254b7efc456af7f4aa03ac2d1fa80c23c18faac88ccfd46914b3d07184f6','object')
need(t['stdout_sha256']==sha(o/'stdout') and t['stderr_sha256']==sha(o/'stderr'),'logs')
need((o/'stdout').read_text()=="'TenPositive79Mask.coordinate_identity' depends on axioms: [propext, Quot.sound]\n" and (o/'stderr').read_text()=='','axioms or diagnostics')
need(re.findall(r'^import (\S+)',s,re.M)==['Direct80Graph'],'imports')
found=next((pathlib.Path(x)/'Direct80Graph.olean' for x in t['lean_path'].split(':') if (pathlib.Path(x)/'Direct80Graph.olean').is_file()),None)
need(found and str(found)==t['graph']['path'] and sha(found)==t['graph']['sha256']=='95eb93d8d48d28df810997b666e061ff20aab90e0adbf357e7590c511d2465d4','selected graph')
need(sha(found)==sha('/tmp/direct80-coherent-rebuild-2fbk3sj_/lib/Direct80Graph.olean'),'fresh union graph')
need(not re.search(r'\b(sorry|admit)\b',s),'source placeholder')
print(json.dumps({'status':'PASS','candidate_rows':len(rows),'variable_slots':len(variables),'ports':len(ports),'object_sha256':t['object_sha256'],'graph_path':str(found),'graph_sha256':sha(found),'lean_replayed':False},sort_keys=True))
