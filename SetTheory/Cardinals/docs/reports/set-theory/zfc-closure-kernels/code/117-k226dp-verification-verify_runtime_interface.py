#!/usr/bin/env python3
"""Finite audit of K228 source and exact initialized runtime frame."""
from pathlib import Path
import json, hashlib, sys, re, argparse
assert __debug__ and not sys.flags.optimize, 'Run with assertions enabled'
ap=argparse.ArgumentParser(description=__doc__)
for flag in ('original-sites','rocq-program','baseline-sites','new-sites','startup','output'):
 ap.add_argument('--'+flag,type=Path,required=True)
a=ap.parse_args()
old=json.loads(a.baseline_sites.read_text());new=json.loads(a.new_sites.read_text())
raw_path=a.original_sites; raw=json.loads(raw_path.read_text())
opmap={'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC','EHalt':'CH'}
converted=[]
for pc,edge in raw:
 parts=edge.split(); converted.append([pc,opmap[parts[0]],int(parts[1]) if len(parts)>1 else None])
assert converted==old
# Independently extract the actual frozen Rocq p230_tab definition.
prog_path=a.rocq_program; prog_text=prog_path.read_text()
body=prog_text.split('Definition p230_tab : list (cedge * cedge) := [',1)[1].split('].',1)[0]
rx=r'\(\s*(CN|CI|CD|CB|CC|CH)(?:\s+(\d+))?\s*,\s*(CN|CI|CD|CB|CC|CH)(?:\s+(\d+))?\s*\)'
pairs=[((a,int(b) if b else None),(c,int(d) if d else None)) for a,b,c,d in re.findall(rx,body)]
assert len(pairs)==5124
remaining=re.sub(rx,'',body);assert not remaining.replace(';','').strip()
extracted=[];active=set()
def walk(edge,pc):
 op,arg=edge
 if op!='CN':extracted.append([pc,op,arg]);return
 assert 0<=arg<len(pairs) and arg not in active;active.add(arg)
 for bit,e in enumerate(pairs[arg]):walk(e,pc+str(bit))
 active.remove(arg)
walk(('CN',0),'');assert extracted==old
assert hashlib.sha256(raw_path.read_bytes()).hexdigest()=='400fad2b1c5f99ed8490f6346ff63088ba94fc39ada376962cee2f68c092e487'
assert hashlib.sha256(prog_path.read_bytes()).hexdigest()=='b795e411095048db7849efe621d6b9fef4da3523167c7848ade26e3c715b83cc'
# Independent nested trie; no compiler/builder imports.
def trie(rows):
 root={}
 for pc,op,arg in rows:
  n=root
  for bit in pc:
   assert 'leaf' not in n;n=n.setdefault(bit,{})
  assert not n;n['leaf']=(op,arg)
 def freeze(n):
  if 'leaf' in n:assert set(n)=={'leaf'};return n['leaf']
  assert set(n)=={'0','1'};return freeze(n['0']),freeze(n['1'])
 return freeze(root)
def leaf(t):return isinstance(t[0],str)
def sites(t,p=''):
 return [[p,*t]] if leaf(t) else sites(t[0],p+'0')+sites(t[1],p+'1')
H=((('CD',6),(('CI',5),('CC',2))),('CI',5));H1=(('CI',5),(('CD',6),('CC',2)))
paths=[]
def replace(t,p=''):
 if t==H:paths.append(p);return H1
 return t if leaf(t) else(replace(t[0],p+'0'),replace(t[1],p+'1'))
assert sites(replace(trie(old)))==new and len(paths)==4
# Every leaf successor canonicalizes by adding/removing only zeros.
def inc(p):return format((int(p,2)+1)%(1<<len(p)),'0'+str(len(p))+'b') if p else ''
def cut(p,c,k):
 if k==0:return p
 for i in range(len(p)-1,-1,-1):
  if p[i]==c:
   k-=1
   if k==0:return p[:i]
 return ''
leaves={p for p,o,r in new};maxdepth=max(map(len,leaves));count=0;initial=None
for p,o,r in [('', 'INITIAL',None)]+new:
 targets=[p] if o=='INITIAL' else [inc(p)] if o=='CI' else [inc(p),inc(cut(p,'0',1))] if o=='CD' else [inc(cut(p,'0',r))] if o=='CB' else [cut(p,'1',r)] if o=='CC' else []
 for z in targets:
  word=z+'0'*maxdepth
  found=[word[:i] for i in range(1,maxdepth+1) if word[:i] in leaves];assert len(found)==1
  q=found[0];assert all(c=='0' for c in z[len(q):]);count+=1
  if o=='INITIAL':initial=q
# Reconstruct the complete boot support independently from frame definition.
boot=json.loads(a.startup.read_text())
h=boot['endpoint_head'];logical=[3,0,0,0,3,0,0,0,0];phy=(6,2,0,4,3,7,8,5,1)
physical=[None]*9
for i,j in enumerate(phy):physical[j]=logical[i]
assert physical==[0,0,0,3,0,0,3,0,0]
g=117;spare=[1]*167;ones={h-1,h+64+g};ones.update(h+i for i,c in enumerate(initial) if c=='1');pos=h+64+g+1
for v in physical+spare:
 pos+=1;ones.update(range(pos,pos+v+1));pos+=v+1
assert sorted(ones)==boot['one_cells']
res={'status':'EXACT_SOURCE_REWRITE_AND_FRAME_INTERFACE_PASS','raw_k230_source_sha256':hashlib.sha256(raw_path.read_bytes()).hexdigest(),'rocq_program_sha256':hashlib.sha256(prog_path.read_bytes()).hexdigest(),'rocq_node_count':len(pairs),'rocq_program_leaves_match_source':True,'old_source_leaves':len(old),'new_source_leaves':len(new),'new_source_maximum_depth':maxdepth,'h_rewrite_paths':paths,'h_parameters':{'consumed_register':6,'incremented_register':5,'closed_form':'R6 becomes 0; R5 becomes R5+R6+1; others unchanged','source_steps':'3*old_R6+2'},'normalized_successor_checks':count,'initial_leaf':initial,'boot_gap_extra':g,'header_distance':64+g,'logical_registers':logical,'physical_registers':physical,'spare_values':[1,167],'exact_boot_support_cells':len(ones),'new_source_sha256':hashlib.sha256(a.new_sites.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
