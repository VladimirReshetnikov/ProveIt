#!/usr/bin/env python3
"""PA194DHS: Gamma(D) emitter with no-push MP and symmetric cached Shift.
All mutations are local output creation; all inputs are pinned packet data.
"""
from pathlib import Path
import sys,json,hashlib
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'construction'))
import compiler as c
BASE_NODES=c.raw_nodes;BASE_MACHINE=c.machine
I=('leaf','inc',1);BREAK=('leaf','breakTo',1)
c.MACROS[(I,I)]=99;c.MACROS[((I,I),(I,I))]=190;c.MACROS[('leaf','dec',4)]=144

def parse(p):
 ans={}
 for ln in p.read_text().splitlines():
  q,b,w,d,t=ln.split();ans[int(q),int(b)]=int(w),d=='R',int(t)
 return ans

def text(rows):return ''.join(f'{q} {b} {w} {"R"if d else"L"} {t}\n'for(q,b),(w,d,t)in sorted(rows.items()))
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def normal(t):
 if t=='node60':return I,I
 if t=='node61':return(I,I),(I,I)
 return tuple(normal(z)for z in t)if c.isnode(t)else t

def nodes(special=True):
 ns=BASE_NODES();ns['node163']=('node6','node54')
 ns['node170']=(('node36',('node167','node145')),'node56')
 ns['node171']=('node170',(('leaf','inc',5),('leaf','continueTo',3)))
 if special:ns['node22']=(('leaf','dec',8),('leaf','dec',6))
 return ns

def fixed():
 r,l=BASE_MACHINE()
 r.update({(38,0):(0,True,11),(38,1):(1,True,122),(164,1):(1,True,114),
  (214,0):(0,True,312),(214,1):(1,True,30),(312,0):(0,True,188),
  (310,1):(1,True,331),(331,0):(0,True,63),(331,1):(1,False,73),(27,1):(1,True,21)})
 return r,l

def fold(raw,fs):
 alias={a:b for a,b,_ in fs};actions={b:v for a,b,v in fs}
 assert len({q for a,b,_ in fs for q in(a,b)})==2*len(fs)
 ans={}
 for(q,bit),v in raw.items():
  if q in alias:continue
  w,d,t=actions[q][bit]if q in actions else v
  ans[q,bit]=w,bool(d),alias.get(t,t)
 return ans,alias

def local_checks(raw,child,alias,fs):
 incoming={}
 for(q,b),(w,d,t)in raw.items():incoming.setdefault(t,set()).add((w,d))
 out=[]
 for a,b,_ in fs:
  assert incoming[a]=={(0,True)}and incoming[b]=={(1,True)}and 74 not in(a,b)
  for old,hist in((a,0),(b,1)):
   for bit in(0,1):
    w,d,t=raw[old,bit];want=alias.get(t,t),1 if d else-1,{-1:hist,0:w}
    q,h,tape=b,0,{-1:hist,0:bit};trace=[]
    for k in range(1,31):
     assert h in(-1,0)
     w,d,q2=child[q,tape[h]];trace.append([q,h,tape[h],w,d,q2]);q=q2;tape[h]=w;h+=1 if d else-1
     if(q,h,tape)==want:break
    else:raise AssertionError((old,bit))
    out.append({'old':old,'history':hist,'bit':bit,'steps':k,'trace':trace})
 return out

def successor(code,pc,m):
 row=code[pc]
 if row[0]=='jump':return[(row[1],m)]
 if row[0]=='inc':return[(row[2],m|(1<<row[1]))]
 if row[0]=='dec':
  k=1<<row[1]
  return[(row[3],m&~k),(row[3],m)]if m&k else[(row[2],m)]
 return[]

def closure(code):
 seen={(25,1)};todo=list(seen)
 for pc,m in todo:
  for s in successor(code,pc,m):
   if s not in seen:seen.add(s);todo.append(s)
 return seen

def build():
 if not __debug__:raise RuntimeError('Run verification without Python -O')
 M=ROOT/'machine';E=ROOT/'evidence';M.mkdir(exist_ok=True);E.mkdir(exist_ok=True)
 tree=normal(c.read_grammar(ROOT/'inputs/grammar.json'))
 c.machine=fixed;c.raw_nodes=lambda:nodes(True)
 raw,ix,shape=c.build(tree);sites,code,contracts=c.source(tree)
 assert len(shape)==69 and len(raw)==408 and len(sites)==3650
 folds=json.loads((ROOT/'inputs/nine_folds.json').read_text())+[[41,331,[[0,False,31],[1,False,46]]]]
 child,alias=fold(raw,folds);local=local_checks(raw,child,alias,folds)
 assert len(child)==388 and len(local)==40
 valid=c.validate(child,contracts);assert valid['ok'],valid
 def oldbreak(t):return BREAK if t==('leaf','dec',4)else(tuple(oldbreak(z)for z in t)if c.isnode(t)else t)
 c.raw_nodes=lambda:nodes(False)
 ordinary_sites,ordinary,_=c.source(oldbreak(tree));c.raw_nodes=lambda:nodes(True)
 changes=[i for i in range(len(code))if code[i]!=ordinary[i]]
 assert changes==[26,3553]
 R0=closure(ordinary);R1=closure(code)
 assert R0==R1 and all(successor(code,p,m)==successor(ordinary,p,m)for p,m in R0)
 assert all(not(m>>code[p][1]&1)for p,m in R0 if p in changes)
 # Exact entire blank tape, with no earlier halt.
 path=sites[25][0];want={-3,46}|{-2+i for i,z in enumerate(path)if z};pos=47
 physical=[0,0,0,0,0,0,2,0,0]+[1]*26
 for v in physical:pos+=1;want.update(range(pos,pos+v+1));pos+=v+1
 q,h,ones=74,0,set()
 for steps in range(1,1000001):
  w,d,q=child[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=1 if d else-1
  assert q!=254
  if(q,h,ones)==(84,-2,want):break
 else:raise AssertionError('startup')
 states={q for q,_ in child};order=[74];label={74:0}
 for q in order:
  for bit in(0,1):
   t=child[q,bit][2]
   if t!=254 and t not in label:label[t]=len(order);order.append(t)
 assert set(order)==states and len(states)==194
 label[254]=194;dense={(label[q],b):(w,d,label[t])for(q,b),(w,d,t)in child.items()}
 for name,rows in[('machine.native.tm',child),('machine.tm',dense),('raw.native.tm',raw)]:(M/name).write_text(text(rows))
 for name,data in[('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),('instructions.json',code),('labels.json',order+[254]),('ordinary.instructions.json',ordinary),('folds.json',folds)]:dump(M/name,data)
 for name,data in[('local_cases.json',local),('zero_invariant.json',{'pairs':len(R0),'changes':changes,'same_closed_set':True,'all_successors_equal':True,'closure_sha256':hashlib.sha256(json.dumps(sorted(R0),separators=(',',':')).encode()).hexdigest(),'masks':{i:sorted(m for p,m in R0 if p==i)for i in changes}})]:dump(E/name,data)
 seed={'steps':steps,'native_state':84,'head':-2,'site':25,'path':''.join(map(str,path)),'logical_registers':[2]+[0]*8,'physical_registers':physical[:9],'spares':physical[9:],'one_cells':sorted(want),'complete_tape_equal':True};dump(E/'seed.json',seed)
 receipt={'family':'PA194DHS','working_states':194,'raw_states':204,'fixed_states':135,'AX_readers':69,'folds':10,'local_cases':len(local),'sites':len(sites),'outcomes':len(contracts),'construction_validation':valid,'zero_invariant_pairs':len(R0),'startup_steps':steps,'native_sha256':hashlib.sha256(text(child).encode()).hexdigest(),'dense_sha256':hashlib.sha256(text(dense).encode()).hexdigest(),'kernel_checked':False}
 dump(E/'build.json',receipt);print(json.dumps(receipt,indent=2),flush=True)
 return receipt
if __name__=='__main__':build()
