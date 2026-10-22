import pathlib,json,hashlib,urllib.request,concurrent.futures,tarfile
D=pathlib.Path('research215_round13_review');pin=json.loads((D/'PINS.json').read_text())['pin'];base=D/'current';v=base/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase14';j=json.loads((v/'integration/current-review.json').read_text());out=[]
def f(kv):
 k,r=kv;p=r['current'].split('/Proofs/')[1];q=base/p
 if not q.exists():q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(urllib.request.urlopen('https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/'+pin+'/'+p).read())
 h=hashlib.sha256(q.read_bytes()).hexdigest();return {'module':k,'path':p,'sha256':h,'recorded_sha256':r['sha256'],'matches':h==r['sha256']}
with concurrent.futures.ThreadPoolExecutor(max_workers=16) as e:out=list(e.map(f,j['sources'].items()))
res={'pin':pin,'current_source_rows':out,'current_matches':sum(r['matches'] for r in out),'current_mismatches':[r for r in out if not r['matches']],'archives':[],'scope':'Owned data-only byte check. No Lean or received script execution.'}
for ph in ['phase13','phase14']:
 v=base/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification'/ph;t=tarfile.open(v/'lean/execution.tar.gz');ix=json.loads((v/'lean/index.json').read_text());rows=[]
 for n,r in ix.items():
  b=t.extractfile(n).read();rows.append({'path':n,'matches':hashlib.sha256(b).hexdigest()==r['sha256'] and len(b)==r['bytes']})
 res['archives'].append({'phase':ph,'archive_sha256':hashlib.sha256((v/'lean/execution.tar.gz').read_bytes()).hexdigest(),'archive_rows':len(rows),'archive_matches':sum(r['matches'] for r in rows),'archive_mismatches':[r for r in rows if not r['matches']]})
(D/'CURRENT_BINDING.json').write_text(json.dumps(res,indent=2));print({k:v for k,v in res.items() if k!='current_source_rows'},flush=True)
# Source status delta with prior exact inspection.
prev=pathlib.Path('research215_round12_review/current'); groups={}
for group,names in {'lean':['KSim','KRuntimeCore','KDecoderPrefix215','KSeed222','KSeedModel222','KDenseBridge','DominatedImplication','Lukasiewicz'], 'rocq':['Source215','EnumPerm','DomRho8']}.items():
 rows=[]
 for n in names:
  if group=='lean':p='Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'+n+'.lean'
  else:
   ps=list(prev.rglob(n+'.v'))
   if not ps:print('NOT FOUND',n);continue
   p=str(ps[0].relative_to(prev));q=base/p
   if not q.exists():q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(urllib.request.urlopen('https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/'+pin+'/'+p).read())
  before=(prev/p).read_bytes() if (prev/p).exists() else None;after=(base/p).read_bytes();rows.append({'path':p,'old_sha256':hashlib.sha256(before).hexdigest() if before else None,'current_sha256':hashlib.sha256(after).hexdigest(),'same':before==after,'bytes':len(after),'lines':after.count(b'\n')})
 groups[group]=rows
(D/'SOURCE_DELTA.json').write_text(json.dumps(groups,indent=2));print(json.dumps(groups,indent=2))
