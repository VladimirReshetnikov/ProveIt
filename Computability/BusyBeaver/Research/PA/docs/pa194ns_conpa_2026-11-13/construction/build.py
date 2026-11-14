#!/usr/bin/env python3
"""Rebuild PA194NS: no-push MP-to-top with cache-only symmetric Shift.

The source and arithmetic compiler are inherited from the pinned PA194R
packet. The new contribution is their crossed controller composition and
its command calibration. Run with assertions enabled, Python 3.10+.
"""
from pathlib import Path
import argparse,hashlib,json
import compiler as c
ROOT=Path(__file__).resolve().parents[1]
BASE_MACHINE,BASE_NODES=c.machine,c.raw_nodes
START,HALT=74,254
EXPECTED_DENSE='19935635f2c5722f5a72977d20a7019764a28573e12d1d0bce398245576c33b1'

def text_table(rows):
 return ''.join(f'{q} {bit} {w} {"R" if d else "L"} {t}\n' for (q,bit),(w,d,t) in sorted(rows.items()))

def read_table(path):
 result={}
 for line in path.read_text().splitlines():
  q,bit,w,d,t=line.split();q,bit,w,t=map(int,(q,bit,w,t));assert (q,bit) not in result and bit in (0,1) and w in (0,1) and d in ('L','R');result[q,bit]=w,d=='R',t
 return result

def fixed():
 rows,labels=BASE_MACHINE()
 rows.update({(38,0):(0,True,11),(38,1):(1,True,122),(164,1):(1,True,114),
  (214,0):(0,True,312),(214,1):(1,True,30),(312,0):(0,True,188),
  (310,1):(1,True,330),(330,0):(0,True,63),(330,1):(1,False,73)})
 return rows,labels

def nodes():
 ns=BASE_NODES()
 ns['node163']=('node6','node54')
 ns['node170']=(('node36',('node167','node145')),'node56')
 ns['node171']=('node170',(('leaf','inc',5),('leaf','continueTo',3)))
 return ns

def fold(raw,folds):
 aliases={a:b for a,b,acts in folds};actions={b:acts for a,b,acts in folds}
 assert len({q for a,b,_ in folds for q in (a,b)})==2*len(folds)
 result={}
 for (q,bit),act in raw.items():
  if q in aliases:continue
  w,d,t=actions[q][bit] if q in actions else act
  result[q,bit]=w,bool(d),aliases.get(t,t)
 return result,aliases

def local_checks(raw,child,aliases,folds):
 incoming={}
 for (q,bit),(w,d,t) in raw.items():incoming.setdefault(t,[]).append((q,bit,w,d))
 cases=[]
 for a,b,_ in folds:
  assert START not in (a,b)
  assert {(w,d) for _,_,w,d in incoming[a]}=={(0,True)}
  assert {(w,d) for _,_,w,d in incoming[b]}=={(1,True)}
  for old,history in ((a,0),(b,1)):
   for bit in (0,1):
    w,d,t=raw[old,bit];expected=aliases.get(t,t),1 if d else -1,{-1:history,0:w}
    state,head,tape=b,0,{-1:history,0:bit};trace=[]
    for ticks in range(1,31):
     assert head in (-1,0)
     w,d,t=child[state,tape[head]];trace.append([state,head,tape[head],w,int(d),t]);tape[head]=w;head+=1 if d else -1;state=t
     if (state,head,tape)==expected:break
    else:raise AssertionError(('local failure',old,bit))
    cases.append({'old':old,'history':history,'read':bit,'duration':ticks,'trace':trace})
 return cases

def densify(rows):
 states={q for q,b in rows};assert len(states)==194 and len(rows)==388
 assert set(rows)=={(q,b) for q in states for b in (0,1)} and HALT not in states
 assert {t for w,d,t in rows.values()}-states=={HALT}
 order=[START];index={START:0}
 for q in order:
  for bit in (0,1):
   t=rows[q,bit][2]
   if t!=HALT and t not in index:index[t]=len(order);order.append(t)
 assert set(order)==states
 return {(index[q],bit):(w,d,194 if t==HALT else index[t]) for (q,bit),(w,d,t) in rows.items()},order+[HALT]

def startup(rows,path):
 head=-2;expected={head-1,head+48};expected.update(head+i for i,b in enumerate(path) if b)
 physical=[0,0,0,0,0,0,2,0,0]+[1]*26;pos=head+49
 for v in physical:pos+=1;expected.update(range(pos,pos+v+1));pos+=v+1
 q,h,ones=START,0,set()
 for ticks in range(1,1000001):
  w,d,q=rows[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=1 if d else -1
  assert q!=HALT
  if (q,h,ones)==(84,head,expected):
   assert ticks==57768
   return {'steps':ticks,'state':q,'head':h,'source_site':25,'logical_registers':[2]+[0]*8,'spare_values':[1]*26,'one_cells':sorted(ones),'complete_tape_equality':True}
 raise AssertionError('No exact complete startup frame')

def build(out,full=True):
 assert __debug__,'Run without -O'
 c.machine=fixed;c.raw_nodes=nodes
 inc=('leaf','inc',1);c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
 grammar=c.read_grammar(ROOT/'inputs/pa194.grammar.json')
 sites,instructions,contracts=c.source(grammar);raw,_,shape=c.build(grammar)
 assert len(sites)==3650 and len(contracts)==4750 and len(shape)==67 and len(raw)==404
 folds=json.loads((ROOT/'inputs/pa194.folds.json').read_text())+[[41,330,[[0,False,31],[1,False,46]]]]
 child,aliases=fold(raw,folds);local=local_checks(raw,child,aliases,folds)
 parent=read_table(ROOT/'inputs/pa194CS.native.tm')
 assert [(key,parent[key],child[key]) for key in child if parent[key]!=child[key]]==[((164,1),(1,True,130),(1,True,114))]
 original,_=BASE_MACHINE();assert all(child[q,b]==original[q,b] for q in c.BOXSTATES for b in (0,1))
 valid=c.validate(child,contracts) if full else {'performed':False}
 if full:assert valid['ok']
 seed=startup(child,sites[25][0]);dense,labels=densify(child)
 native_text,dense_text=text_table(child),text_table(dense)
 assert hashlib.sha256(dense_text.encode()).hexdigest()==EXPECTED_DENSE
 out.mkdir(parents=True,exist_ok=True)
 for name,rows in [('machine.native.tm',child),('machine.tm',dense),('raw.native.tm',raw)]: (out/name).write_text(text_table(rows))
 receipt={'family':'PA194NS','working_states':194,'transition_rows':388,'raw_states':202,'fixed_states_before_fold':135,'AX_readers':67,'folds':8,'local_cases':len(local),'source_sites':3650,'source_outcomes':4750,'symbolic_runtime':valid,'startup_steps':seed['steps'],'native_sha256':hashlib.sha256(native_text.encode()).hexdigest(),'dense_sha256':EXPECTED_DENSE,'kernel_checked':False}
 for name,obj in [('sites.json',[[''.join(map(str,p)),op,a] for p,op,a in sites]),('instructions.json',instructions),('folds.json',folds),('local_cases.json',local),('labels.json',labels),('seed.json',seed),('receipt.json',receipt)]: (out/name).write_text(json.dumps(obj,indent=2)+'\n')
 print(json.dumps(receipt,indent=2),flush=True)
 return receipt

if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--quick',action='store_true');args=ap.parse_args();build(args.output,not args.quick)
