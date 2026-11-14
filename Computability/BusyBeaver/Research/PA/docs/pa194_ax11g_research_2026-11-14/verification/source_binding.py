#!/usr/bin/env python3
"""Independent source/CFG binding for the AX11G terminal push.

Reads frozen source trees only; imports no construction or tape simulator.
"""
from pathlib import Path
import json,hashlib,argparse
ROOT=Path(__file__).resolve().parent.parent/'machine'
INPUT=ROOT.parent/'construction'/'inputs'

def require(p,msg):
 if not p:raise AssertionError(msg)
def grammar(path):
 a=json.loads(path.read_text())
 if isinstance(a,list):return a
 def rec(t):return [rec(x)for x in a['rules'][t]]if isinstance(t,str)and t in a['rules']else t
 return rec(a['root'])
def flatten(ax,ns):
 ss=[]
 def walk(t,p):
  if isinstance(t,str):return walk(ax if t=='x67'else ns[t],p)
  if t[0]=='leaf':ss.append([p,t[1],t[2]]);return
  require(len(t)==2,'source pair arity')
  walk(t[0],p+'0');walk(t[1],p+'1')
 walk('node172','');return ss

def resolve(ss):
 loc={p:i for i,(p,op,a)in enumerate(ss)}
 def find(p):
  if p in loc:return loc[p]
  for i,(q,_,_)in enumerate(ss):
   if q.startswith(p)or(p.startswith(q)and'1'not in p[len(q):]):return i
  raise AssertionError(('unresolved',p))
 def after(p):
  k=p.rfind('0');require(k>=0,'source escapes root')
  return find(p[:k]+'1')
 def cut(p,b,n):
  for i in range(len(p)-1,-1,-1):
   if p[i]==b:
    n-=1
    if n==0:return p[:i]
  raise AssertionError('structured branch exceeds source context')
 out=[]
 for p,op,a in ss:
  if op=='inc':row=['inc',a,after(p)]
  elif op=='dec':row=['dec',a,after(cut(p,'0',1)),after(p)]
  elif op=='breakTo':row=['jump',after(cut(p,'0',a))]
  elif op=='continueTo':row=['jump',find(cut(p,'1',a))]
  elif op=='halt':row=['halt']
  else:raise AssertionError(op)
  out.append(row)
 return out

def run(machine=ROOT,output=None):
 ns=json.loads((machine/'nodes.json').read_text())
 raw_nodes=(machine/'nodes.json').read_bytes()
 require(hashlib.sha1(b'blob '+str(len(raw_nodes)).encode()+b'\0'+raw_nodes).hexdigest()=='a089f8a2dde6cde33036b3b9e0e48265c845014e','node map equals pinned PA194G Git blob')
 new=grammar(machine/'grammar.tree.json')
 changes=[]
 # The original G tree is independently pinned, not inferred by deleting an
 # arbitrary push that happens to make the new graph convenient.
 old=grammar(INPUT/'parent_grammar.tree.json')
 original=(INPUT/'parent.grammar.json').read_bytes()
 require(hashlib.sha1(b'blob '+str(len(original)).encode()+b'\0'+original).hexdigest()=='a30963aca7f8f4194591aead83a4a05848d357b8','parent grammar equals pinned PA194G Git blob')
 inc=['leaf','inc',1]
 def normalize(t):
  if t=='node60':return[inc,inc]
  if t=='node61':return[[inc,inc],[inc,inc]]
  if isinstance(t,list)and len(t)==2:return[normalize(t[0]),normalize(t[1])]
  return t
 require(old==normalize(grammar(INPUT/'parent.grammar.json')),'normalized parent tree exactly recovers the pinned grammar')
 def compare(a,b,p=''):
  if a==b:return
  if a==['leaf','breakTo',1]and b=='node49':changes.append(p);return
  require(isinstance(a,list)and isinstance(b,list)and len(a)==len(b)==2,'unexpected macro-source change')
  compare(a[0],b[0],p+'0');compare(a[1],b[1],p+'1')
 compare(old,new);require(len(changes)==1,'exactly one terminal source edit')
 os=flatten(old,ns);nsites=flatten(new,ns)
 oi=resolve(os);ni=resolve(nsites)
 require(nsites==json.loads((machine/'sites.json').read_text()),'exact sites bound')
 require(ni==json.loads((machine/'instructions.json').read_text()),'exact full CFG bound')
 oldpaths={p:i for i,(p,op,a)in enumerate(os)}
 newpaths={p:i for i,(p,op,a)in enumerate(nsites)}
 erased=[i for i,(p,op,a)in enumerate(os)if p not in newpaths]
 require(len(erased)==1,'one erased primitive jump')
 j=erased[0];p,op,a=os[j];require((op,a)==('breakTo',1),'erased closing jump')
 added=[i for i,(q,op,a)in enumerate(nsites)if q.startswith(p)]
 require(len(added)==19 and added==list(range(added[0],added[0]+19)),'19-site push macro')
 relocation={i:newpaths[p]for p,i in oldpaths.items()if p in newpaths}
 relocation[j]=added[0]
 for i,row in enumerate(oi):
  if i==j:continue
  k=2 if row[0]in('inc','dec') else 1 if row[0]=='jump'else len(row)
  mapped=row[:k]+[relocation[t]for t in row[k:]]
  require(mapped==ni[relocation[i]],'outside CFG changed at '+str(i))
 # New routine exit falls through to old MP entry. Its literal source effects
 # and four-field consumption are independently bound in check_commands.py.
 old_next=j+1
 exits=set()
 for jnew in added:
  row=ni[jnew]
  k=2 if row[0]in('inc','dec') else 1 if row[0]=='jump' else len(row)
  exits.update(t for t in row[k:] if t not in added)
 require(exits=={relocation[old_next]},'every push exit goes to full MP input reader')
 result={'status':'PASS','old_sites':len(os),'new_sites':len(nsites),
   'source_macro_changes':[{'local_AX_path':changes[0],'old':['leaf','breakTo',1],'new':'node49'}],
   'old_erased_jump_index':j,'old_erased_jump_path':p,'old_erased_jump_target':oi[j][1],
   'new_push_interval':[added[0],added[-1]+1],'new_push_exit_to_MP':relocation[old_next],
   'all_retained_primitive_operations_and_successors_equal_under_relocation':True,
   'source_complete_CFG_matches_delivered':True,
   'inputs':{n:hashlib.sha256(((INPUT if n=='parent_grammar.tree.json'else machine)/n).read_bytes()).hexdigest()for n in('parent_grammar.tree.json','grammar.tree.json','nodes.json','sites.json','instructions.json')}}
 destination=output or ROOT.parent/'verification'/'source_binding.json'
 destination.parent.mkdir(parents=True,exist_ok=True)
 destination.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2));return result
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--machine',type=Path,default=ROOT)
 p.add_argument('--output',type=Path)
 a=p.parse_args();run(a.machine,a.output)
