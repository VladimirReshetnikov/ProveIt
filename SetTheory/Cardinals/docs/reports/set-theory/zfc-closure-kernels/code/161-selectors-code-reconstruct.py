#!/usr/bin/env python3
"""Reconstruct K215 from the pinned K216 partial-selector packet; stdlib only.

This reproduces the exact source, native table, and canonical table without
MILP, source search, simulated examples, or assumptions about a runtime proof.
The independent source audit and universal runtime remain separate obligations.
"""
from pathlib import Path
from functools import cache
import argparse,hashlib,json,sys
ROOT=Path(__file__).resolve().parent

def need(ok,why):
 if not ok:raise ValueError(why)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def leaf(t):return isinstance(t[0],str)
def sites(t,p=''):
 return [[p,*t]]if leaf(t)else sites(t[0],p+'0')+sites(t[1],p+'1')
def parse_source(rows):
 root={}
 for p,op,a in rows:
  need(p and set(p)<={'0','1'},'Binary nonempty source path')
  need(op in ('CI','CD','CB','CC','CH'),'Opcode')
  need(a is None if op=='CH'else type(a)is int and a>=0,'Operand')
  at=root
  for c in p:
   need('leaf'not in at,'Prefix-free source');at=at.setdefault(c,{})
  need(not at,'Duplicate leaf');at['leaf']=(op,a)
 def finish(x):
  if'leaf'in x:need(set(x)=={'leaf'},'Leaf structure');return x['leaf']
  need(set(x)=={'0','1'},'Full binary source');return finish(x['0']),finish(x['1'])
 t=finish(root);need(sites(t)==rows,'Ordinal order');return t
@cache
def width(t):return 1 if leaf(t)else width(t[0])+width(t[1])
@cache
def boundary(t):
 if leaf(t):
  op,a=t
  return(1,0)if op=='CD'else(a,0)if op=='CB'else(0,a)if op=='CC'else(0,0)
 a,b=boundary(t[0]),boundary(t[1]);return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0)
def seq(xs):
 need(bool(xs),'Nonempty sequence');return xs[0]if len(xs)==1 else(xs[0],seq(xs[1:]))
def extract(t,lo,hi):
 chunks=[]
 def go(n,i=0):
  j=i+width(n)
  if j<=lo or hi<=i:return
  if lo<=i and j<=hi:
   need(boundary(n)==(0,0),'Extract closed subtree');chunks.append(n);return
  need(not leaf(n),'Extract endpoint');go(n[0],i);go(n[1],i+width(n[0]))
 go(t);need(sum(map(width,chunks))==hi-lo,'Extract coverage');return seq(chunks)
def splice(t,edits):
 used={}
 def go(n,i=0):
  j=i+width(n);touch=[(rg,v)for rg,v in edits.items()if not(j<=rg[0]or rg[1]<=i)]
  if not touch:return n
  for(lo,hi),v in touch:
   if lo<=i and j<=hi:
    need(boundary(n)==(0,0),'Splice closed fragment')
    if i==lo:used[lo,hi]=used.get((lo,hi),0)+1;return v
    return None
  need(not leaf(n),'Splice endpoint');a,b=go(n[0],i),go(n[1],i+width(n[0]))
  if a is None:
   if b is not None:need(boundary(b)==(0,0),'Closed surviving right')
   return b
  if b is None:need(boundary(a)==(0,0),'Closed surviving left');return a
  return a,b
 ans=go(t);need(used=={rg:1 for rg in edits},'Exactly one splice for each interval');return ans

def source215(parent_rows):
 t=parse_source(parent_rows);read=extract(t,23,37);load=extract(t,40,66)
 walk,transfer=read
 need([width(x)for x in(walk,transfer,load)]==[11,3,26],'Read/load factor lengths')
 need(all(boundary(x)==(0,0)for x in(walk,transfer,load)),'Closed reassociation factors')
 local=walk,(transfer,load)
 t=splice(t,{(23,37):None,(187,201):None,(228,254):local,(4659,4685):local})
 paths=('111','110101','110100101')
 def at(n,p):
  for c in p:need(not leaf(n),'Body path');n=n[int(c)]
  return n
 bodies=[at(t,p)for p in paths]
 need(all(boundary(n)==(0,0)for n in bodies),'Closed command bodies')
 def move(n,p=''):
  if p in paths:return bodies[(2,1,0)[paths.index(p)]]
  return n if leaf(n)else(move(n[0],p+'0'),move(n[1],p+'1'))
 return move(t)
def parse_table(raw):
 T={}
 for line in raw.decode('ascii').splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));need((q,b)not in T and b in(0,1)and w in(0,1)and d in('L','R'),'Table row');T[q,b]=(w,d,z)
 return T
def serialize(T,halt=None):
 return ('#! start 0\n'+(''if halt is None else f'#! halt {halt}\n')+''.join(f'{q} {b} {w} {d} {z}\n'for(q,b),(w,d,z)in sorted(T.items()))).encode('ascii')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--parent',required=True,type=Path);ap.add_argument('--output',required=True,type=Path);ap.add_argument('--recipe',type=Path,default=ROOT.parent/'source/transition_recipe215.json');a=ap.parse_args()
 need(__debug__ and not sys.flags.optimize,'Assertions enabled')
 recipe=json.loads(a.recipe.read_text());native=(a.parent/'machine/k216.native.tm').read_bytes();sr=(a.parent/'source/sites216.json').read_bytes()
 need(sha(native)==recipe['parent_native_sha256'],'Pinned native input');need(sha(sr)==recipe['parent_source_sha256'],'Pinned source input')
 new=source215(json.loads(sr));newrows=sites(new);src=(json.dumps(newrows,separators=(',',':'))+'\n').encode('ascii');need(sha(src)==recipe['source215_sha256'],'Source byte identity')
 T=parse_table(native);seen=set()
 for row in recipe['rows']:
  key=tuple(row['key']);need(key not in seen,'Unique row delta');seen.add(key)
  need(T.get(key)==tuple(row['old']),'Row precondition')
  if row['new']is None:del T[key]
  else:T[key]=tuple(row['new'])
 Q={q for q,b in T};need(len(Q)==215 and len(T)==430,'215 states and430 rows')
 need(all((q,b)in T for q in Q for b in(0,1)),'Total working table');need(0 in Q and 254 not in Q,'Start/halt');need({z for w,d,z in T.values()}-Q=={254},'Unique external halt')
 raw=serialize(T);need(sha(raw)==recipe['native215_sha256'],'Native byte identity')
 m={q:i for i,q in enumerate(sorted(Q))};m[254]=215;C={(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in T.items()};canonical=serialize(C,215);need(sha(canonical)==recipe['canonical215_sha256'],'Canonical byte identity')
 inverse={v:k for k,v in m.items()};need({(inverse[q],b):(w,d,inverse[z])for(q,b),(w,d,z)in parse_table(canonical).items()}==T,'Inverse renaming')
 a.output.mkdir(parents=True,exist_ok=True)
 for name,data in[('k215.native.tm',raw),('k215.tm',canonical),('sites215.json',src)]:(a.output/name).write_bytes(data)
 (a.output/'canonicalization.json').write_text(json.dumps({'native_to_canonical':m,'native_halt':254,'canonical_halt':215,'native_dispatcher':84,'canonical_dispatcher':m[84]},indent=2)+'\n')
 receipt={'status':'PASS_EXACT_K215_RECONSTRUCTION','working_states':215,'rows':430,'source_leaves':len(newrows),'changed_retained_rows':sum(r['new']is not None for r in recipe['rows']),'deleted_states':sorted({q for q,b in parse_table(native)}-Q),'native_sha256':sha(raw),'canonical_sha256':sha(canonical),'source_sha256':sha(src),'scope':'Literal finite construction and renaming only; semantic calibration and universal runtime are separate proofs.'}
 (a.output/'reconstruction.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
