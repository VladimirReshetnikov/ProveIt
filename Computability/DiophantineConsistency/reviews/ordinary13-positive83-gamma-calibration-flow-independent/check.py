from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path;p=P('research/ordinary13-positive83-gamma-calibration-model-draft')
files=[p/'Positive83GammaCalibration.lean.src',p/'README.md',p/'check.py',p/'receipt.json',P('research/ordinary13-positive83-to84-model-draft/Positive83To84Transport.lean.src'),P('research/ordinary13-positive83-to84-model-draft/Positive83To84Bridge.lean.src'),P('research/ordinary13-positive83-reverse-root-model-draft/Positive83CrossRoot.lean.src'),P('research/ordinary13-positive83-reverse-root-model-draft/Positive83ReverseRoot.lean.src'),P('research/ordinary13-positive81-exact-main-model-draft/Positive81ExactMain.lean.src'),P('research/ordinary13-positive81-to83-model-draft/Positive81To83Transport.lean.src'),P('research/ordinary13-positive81-carrier-data-model-draft/Positive81ForwardCompact.lean.src'),P('research/ordinary13-positive81-carrier-data-model-draft/Positive81ForwardCarrier.lean.src'),P('research/ordinary13-eta-natural-graph-early-index-model-draft/EtaNaturalGraphEarlyIndex.lean.src'),P('research/ordinary13-positive81-calibration-model-draft/Positive81Calibration.lean.src'),P('research/ordinary13-qcube-main83/candidate.json'),P('research/ordinary13-residue-first81/candidate.json'),P('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json')]
s=[f.read_text() for f in files];g83,g81,g85=map(json.loads,s[14:17]);assert [len(g['source']) for g in (g83,g81,g85)]==[83,81,85]
assert g83['witnesses']==g81['witnesses'] and g85['witnesses']==['n_'+x for x in g83['witnesses']]
# Source-backed acyclic local path, bounded to these selected files; this is
# deliberately not a complete import resolution or object-provider audit.
assert s[5].splitlines()[0]=='import Positive83To84Transport'
assert s[7].splitlines()[0]=='import Positive81ForwardCarrier'
assert 'import Positive83To84Bridge' not in s[7] and 'import Positive83GammaCalibration' not in s[7]
body=s[0].split('theorem calibration_of_root',1)[1].split('/-- Proposed compact',1)[0]
for n in ['Positive81To83TransportDraft.zero83_to81','Positive81To83TransportDraft.prototype_zero_of81',
 'EtaNaturalGraphEarlyIndexDraft.compact_early_index K e hz85',
 'Positive81ExactMainDraft.exact_and_main K e hz85 heta n w hn hny hks hnmod',
 'let W : V := 4*(X p v)*(q p v)*(v 7)*w','have hkW : k v=R+1+U p v*W',
 'have hx : main=xcoord R (a p v)','have hy : c p v=ycoord R (a p v)',
 '⟨R,W,main,hR3,hy,hx,hkW,hb⟩']:assert n in body,n
assert 'zero83_to84' not in body and 'gamma_of_calibration' not in body
assert 'Positive83CrossRootDraft.reverse K V v hv hz' in s[0]
assert 'Positive83ReverseRootDraft.reverse_root (ports K) v hv hz hbeta' in s[6]
assert 'def GammaCalibration' in s[4] and '∃ R W d : V, 3≤R' in s[4]
assert 'def CalibrationCut' in s[5] and 'GammaCalibration (ports K) v' in s[5]
assert '⟨m,_,hmx,hmy⟩ := ArithmeticPellClassification.solution_index a main (c p v)' in s[8] and 'simpa only [hmR,ha] using hmx' in s[8] and 'simpa only [hmR,ha] using hmy' in s[8]
# Normalize additive expressions while treating products as opaque interned
# commutative factors. Compare actual 83 and prototype fields after putR
# followed by image85; r may differ and is intentionally not identified.
vec=[];vmap={};amap={}
def v(d):
 z=tuple(sorted((a,c) for a,c in d.items() if c))
 if z not in vmap:vmap[z]=len(vec);vec.append(z)
 return vmap[z]
def atom(k):
 if k not in amap:amap[k]=len(amap)+1
 return amap[k]
def var(n):return v({atom(('v',n)):1})
def num(n):return v({0:n})
def add(x,y,sign=1):
 z=dict(vec[x])
 for a,c in vec[y]:z[a]=z.get(a,0)+sign*c
 return v(z)
def mul(x,y):
 if not vec[x] or not vec[y]:return num(0)
 if len(vec[x])==1 and vec[x][0][0]==0:return v({a:vec[x][0][1]*c for a,c in vec[y]})
 if len(vec[y])==1 and vec[y][0][0]==0:return mul(y,x)
 return v({atom(('m',*sorted((x,y)))):1})
def evaluate(g,env):
 env=env.copy()
 for n,op,l,r in g['source']:
  x=num(l) if isinstance(l,int) else env[l];y=num(r) if isinstance(r,int) else env[r]
  env[n]={'+':lambda:add(x,y),'-':lambda:add(x,y,-1),'*':lambda:mul(x,y)}[op]()
 return env
values={w:var(w) for w in g83['witnesses']};ports={w:var(w) for w in g83['fixed_numerals']}
e83=evaluate(g83,{**values,**ports});down={1,2,4,5,7,10}
einputs={'n_'+w:(var('r_replacement') if i==8 else add(values[w],num(1),-1) if i in down else values[w]) for i,w in enumerate(g83['witnesses'])}
e85=evaluate(g85,{**einputs,**ports})
for name in ('q','X','Y','U','R','k','c','Delta','A1','Fa','g72'):assert e83[name]==e85[name],name
# Sparse full polynomial W identity in Q,X,s,w.
def plus(x,y):
 z=x.copy()
 for k,n in y.items():z[k]=z.get(k,0)+n
 return {k:n for k,n in z.items() if n}
def times(x,y):
 z={}
 for a,b in x.items():
  for c,d in y.items():
   k=tuple(i+j for i,j in zip(a,c));z[k]=z.get(k,0)+b*d
 return {k:n for k,n in z.items() if n}
four={(0,0,0,0):4};q={(1,0,0,0):1};x={(0,1,0,0):1};s0={(0,0,1,0):1};w={(0,0,0,1):1}
y=times(times(times(q,q),q),s0);U=times(y,times(q,q));W=times(times(times(times(four,x),q),s0),w)
assert times(times(times(four,x),times(y,y)),w)==times(U,W)
res=subprocess.run([sys.executable,'-I','-S','-B',str(files[2])],check=True,stdout=subprocess.PIPE);assert res.stdout==files[3].read_bytes()
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'same_nonfirst_graph_fields_exact_symbolic':True,'same_early_n_w_and_oriented_main_source_flow_checked':True,'W_factor_exact_polynomial_identity':True,'visible_reverse_root_path_does_not_use_83_to84_map':True,'author_receipt_reproduced':True,'lean_executed':False,'status':'Bounded source-flow audit, not full import resolution or Lean proof; DivCut, parent bridge and providers remain open.'},sort_keys=True,indent=2))
