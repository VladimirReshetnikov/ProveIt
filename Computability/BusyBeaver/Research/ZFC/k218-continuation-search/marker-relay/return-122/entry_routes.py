"""Narrow existing-entry reuse diagnostic for the six literal122 decoder roles.
No broad transition synthesis. Unknown exterior cells are never read.
"""
from pathlib import Path
import hashlib,json,argparse
ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--census',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
assert not args.output.exists(), 'output must be fresh'
R=args.repo.resolve();B=R/'Computability/BusyBeaver/Research/ZFC/candidate-k218'
def table(path):
 t={}
 for l in path.read_text().splitlines():
  if l and not l.startswith('#'):
   q,b,w,d,z=l.split();t[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
 return t
old=table(B/'k218.native.tm');new=table(R/'Computability/BusyBeaver/Research/ZFC/k218-continuation-search/marker-relay/relay217.native.tm')
new[122,0]=(1,-1,1);new[10,0]=(0,-1,122)
census=json.loads(args.census.read_text()); paths=census['paths']['122']; groups={'CD5_CC1':[p for p in paths if p[-1]=='0'],'CD1_CC1':[p for p in paths if p[-1]=='1']}
assert list(map(len,groups.values()))==[4,2]

def goal(p,b):
 before={-1:1,**{i:int(x)for i,x in enumerate(p+str(b))}};after=before.copy();h=len(p)
 if b:after[h]=0;return before,(1,h-1,after)
 return before,(45 if p[-1]=='0' else 41,h+1,after)

def step(t,q,h,bits):
 rd=bits[h];w,d,z=t[q,rd];bits[h]=w;return z,h+d,[q,h,rd,w,d,z]

def run(t,q,p,b,limit=97):
 before,g=goal(p,b);bits=before.copy();h=len(p);trace=[];seen=set()
 for tick in range(limit+1):
  if tick and (q,h,bits)==g:return {'status':'EXACT_JOIN','steps':tick,'trace':trace}
  if h not in bits:return {'status':'UNKNOWN_CELL','steps':tick,'state':q,'head':h,'trace':trace}
  if(q,bits[h])not in t:return {'status':'NO_ACTION','steps':tick,'state':q,'head':h,'trace':trace}
  # Future chosen caller substitutions are not silently assumed here.
  if t is new and (q,bits[h]) in ((51,0),(196,1)):
   return {'status':'UNRESOLVED_CALLER','steps':tick,'state':q,'head':h,'trace':trace}
  key=q,h,tuple(bits.items())
  if key in seen:return {'status':'EXACT_CYCLE','steps':tick,'state':q,'head':h,'trace':trace}
  seen.add(key)
  if tick==limit:return {'status':'BOUND','steps':tick,'state':q,'head':h,'trace':trace}
  q,h,a=step(t,q,h,bits);trace.append(a)

controls=[]
for p in paths:
 for b in (0,1):
  rec=run(old,122,p,b);assert rec['status']=='EXACT_JOIN';controls.append({'prefix':p,'read':b,**rec})
results={}
for name,ps in groups.items():
 rows=[];survivors=[]
 for q in sorted({s for s,b in new}):
  checked=[]
  for p in ps:
   for b in (0,1):
    a=run(new,q,p,b);checked.append({'prefix':p,'read':b,**a})
    if a['status']!='EXACT_JOIN':break
   if checked[-1]['status']!='EXACT_JOIN':break
  good=all(a['status']=='EXACT_JOIN'for a in checked)and len(checked)==2*len(ps)
  row={'entry':q,'matched_cases':sum(a['status']=='EXACT_JOIN'for a in checked),'first_rejection':None if good else checked[-1]}
  rows.append(row)
  if good:survivors.append({'entry':q,'cases':checked})
 results[name]={'prefixes':ps,'entry_states':len(rows),'survivors':survivors,'records':rows}
out={'status':'EXISTING_ENTRY_DIAGNOSTIC_COMPLETE','scope':'Only existing entry states at unchanged head/prefix; speculative122 full-flip and10 reroute present. Exact endpoints for all six source-prefix cases; exterior never read. Caller row51/0 or196/1 encountered during a helper is unresolved, not a negative equivalence theorem. No transition synthesis, no whole runtime or boot claim.','bound':97,'controls':controls,'groups':results,'pins':{str(p):hashlib.sha256(p.read_bytes()).hexdigest()for p in(B/'k218.native.tm',B/'sites218.json',R/'Computability/BusyBeaver/Research/ZFC/k218-continuation-search/marker-relay/relay217.native.tm',args.census,Path(__file__))}}
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:{'entries':v['entry_states'],'survivors':[x['entry']for x in v['survivors']]}for k,v in results.items()}))
