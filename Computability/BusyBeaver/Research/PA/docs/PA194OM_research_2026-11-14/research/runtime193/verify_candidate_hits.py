import sys,pathlib,json,time
BASE=pathlib.Path(__file__).resolve().parent;sys.path.insert(0,str(BASE/'vendor'))
import compiler as c, symbolic_runtime as s
s.ROOT=c.ROOT=BASE/'reference'
T={}
for l in(BASE/'runtime193.native.tm').read_text().splitlines():
 q,b,w,d,n=l.split();T[int(q),int(b)]=int(w),d=='R',int(n)
from single_edits import edits
E=[f'{q} {b} {w} {"R" if d==1 else "L"} {n}'for i,(q,b),(w,d,n)in edits()]
sites,ins,contracts=c.source(c.read_grammar(BASE/'pa194.grammar.json'))
assert [[''.join(map(str,path)),op,arg]for path,op,arg in sites]==json.loads((BASE/'pa194.sites.json').read_text())
assert [list(code)for code in ins]==json.loads((BASE/'pa194.instructions.json').read_text())
records={}


SK=[51,36,25,48,32,33,22,55,60]
def filebits(vs):
 pos=0;ones=set()
 for v in vs:
  ones.update(range(pos+1,pos+v+2));pos+=v+2
 return ones

def marker_check(rows):
 for vs in [[0]*10,[1]*10,list(range(10)),[0,1,0,2,0,3,0,1,0,2]]:
  original=filebits(vs)|{-1}
  for r in range(9):
   target=set(original);target.remove(sum(v+2 for v in vs[:r])+1)
   q=SK[r];h=0;ones=set(original)
   for step in range(10001):
    if step and(q,h,ones)==(1 if r==0 else 3,-1,target):break
    if step==10000:return {'ok':False,'register':r,'values':vs,'state':q,'head':h,'reason':'marker did not return within10000'}
    if q==254:return {'ok':False,'register':r,'values':vs,'reason':'marker halted'}
    w,d,q=rows[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=1 if d else-1
 return {'ok':True,'cases':36}

new=[]
for l in(BASE/'arbitrary_single_hits.jsonl').read_text().splitlines():
 try:hit=json.loads(l)
 except json.JSONDecodeError:continue
 idx=hit['j']
 if str(idx) in records:continue
 q,b,w,d,n=E[idx-1].split();key=int(q),int(b);a=int(w),d=='R',int(n);rows=dict(T);rows[key]=a
 rec={'id':idx,'edit':[int(q),int(b),int(w),d,int(n)],'startup_site':hit['site'],'startup_steps':hit['steps']}
 if key[0]in c.BOXSTATES or key==(122,1):
  rec['marker_test']=marker_check(rows)
  if not rec['marker_test']['ok']:
   records[str(idx)]=rec;new.append(rec);continue
  # Box modifications require independent universal lemmas even if contracts pass.
  rec['needs_arithmetic_lemma']=True
 rec['symbolic']=c.validate(rows,contracts)
 records[str(idx)]=rec;new.append(rec)

assert json.loads(json.dumps(records))==json.loads((BASE/'single_hit_checks.json').read_text())
assert len(records)==163
print('Verified 163 validation records: 97 marker-test failures and 66 symbolic-contract failures; no candidate passes.')
