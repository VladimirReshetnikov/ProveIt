#!/usr/bin/env python3
"""Expand three declared Gamma grammars and cross-check ordinal control flow.
No physical runtime claim is made. Uses only this directory's pinned inputs.
"""
from pathlib import Path
import argparse,json,re,hashlib
P=Path(__file__).resolve().parent
SYMBOLS=['node58','node55','node65',('leaf','inc',1),'node72','node75','node70','node49','node142','node150',('leaf','breakTo',1)]
def need(c,m):
 if not c:raise ValueError(m)
def read_nodes():
 nodes={}
 for line in(P/'OriginalProgram.lean').read_text().splitlines():
  m=re.match(r'def (\w+) : Tree := \.node (.*)',line)
  if m:
   ts=re.findall(r'\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b',m[2])
   items=[name if name else('leaf',op,int(arg)if arg else None)for op,arg,name in ts]
   need(len(items)==2,'source node arity');nodes[m[1]]=tuple(items)
 return nodes

def expand_grammar(g):
 trees=[];words=[]
 for i,(l,r)in enumerate(g['rules']):
  need(l<i and r<i,'non-topological grammar')
  def leaf(x):
   if x>=0:return trees[x],words[x]
   need(0<=-1-x<len(SYMBOLS),'terminal range')
   return SYMBOLS[-1-x],[-1-x]
  a,x=leaf(l);b,y=leaf(r);trees.append((a,b));words.append(x+y)
 return trees[g['root']],words[g['root']]
def leaves(nodes,ax):
 out=[]
 def walk(t,p):
  if isinstance(t,str):walk(ax if t=='x67'else nodes[t],p)
  elif len(t)==3 and t[0]=='leaf':out.append((p,t[1],t[2]))
  else:walk(t[0],p+(0,));walk(t[1],p+(1,))
 walk('node172',());return out

def path_cfg(xs):
 trie={}
 for i,(path,_,_)in enumerate(xs):
  cursor=trie
  for bit in path:cursor=cursor.setdefault(bit,{})
  cursor['leaf']=i
 def locate(p):
  cursor=trie
  for k,bit in enumerate(p):
   if 'leaf'in cursor:
    need(not any(p[k:]),'nonzero suffix after leaf');return cursor['leaf']
   need(bit in cursor,'bad trie path');cursor=cursor[bit]
  while 'leaf'not in cursor:cursor=cursor[0]if 0 in cursor else cursor[1]
  return cursor['leaf']
 def after(p):
  for i in range(len(p)-1,-1,-1):
   if p[i]==0:return locate(p[:i]+(1,))
  raise ValueError('path escaped trie')
 def cut(p,bit,n):
  for i in range(len(p)-1,-1,-1):
   if p[i]==bit:
    n-=1
    if n==0:return p[:i]
  raise ValueError('not enough enclosing branches')
 out=[]
 for p,op,n in xs:
  if op=='inc':out.append(('inc',n,after(p)))
  elif op=='dec':out.append(('dec',n,after(cut(p,0,1)),after(p)))
  elif op=='breakTo':out.append(('jump',after(cut(p,0,n))))
  elif op=='continueTo':out.append(('jump',locate(cut(p,1,n))))
  elif op=='halt':out.append(('halt',))
  else:raise ValueError(op)
 return out

def interval_cfg(xs):
 spans={}
 for i,(p,_,_)in enumerate(xs):
  for n in range(len(p)+1):
   key=p[:n]
   if key not in spans:spans[key]=[i,i+1]
   else:spans[key][1]=i+1
 out=[]
 for i,(p,op,n)in enumerate(xs):
  if op=='halt':ins=('halt',)
  elif op=='inc':ins=('inc',n,i+1)
  elif op in('dec','breakTo','continueTo'):
   positions=[j for j,b in enumerate(p)if b==(1 if op=='continueTo'else 0)]
   k=1 if op=='dec'else n;need(len(positions)>=k,'interval cut depth')
   interval=spans[p[:positions[-k]]]
   target=interval[0]if op=='continueTo'else interval[1]
   need(target<len(xs),'interval target beyond program')
   ins=('dec',n,target,i+1)if op=='dec'else('jump',target)
  else:raise ValueError(op)
  out.append(ins)
 return out

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path);args=ap.parse_args()
 cfg=json.loads((P/'source_inputs.json').read_text());probes=json.loads((P/'source_probes.json').read_text());nodes=read_nodes();rows=[]
 for i,g in enumerate(probes):
  tree,word=expand_grammar(g)
  want=cfg['prefix']+sum((h[0]for h in cfg['head_words']),[])+cfg['gate_words'][[0,16,32][i]]+cfg['suffix']
  need(word==want,'declared word mismatch')
  xs=leaves(nodes,tree);a=path_cfg(xs);b=interval_cfg(xs);need(a==b,'independent CFG resolver mismatch')
  need(len(xs)==3700,'source-site count');cases=sum(2 if row[0]=='dec'else 1 for row in a)
  need(cases==4815,'primitive case count')
  rows.append({'gamma':['c','a','b'][i],'macro_tokens':len(word),'source_sites':len(xs),'primitive_cases':cases,'independent_cfg_resolvers_agree':True,'cfg_sha256':hashlib.sha256(json.dumps(a,separators=(',',':')).encode()).hexdigest()})
 receipt={'ok':True,'variants':rows,'original_program_sha256':hashlib.sha256((P/'OriginalProgram.lean').read_bytes()).hexdigest(),'scope':'Exact macro-word bindings and ordinal source CFG identities; no scanner/runtime or small-table certification.'}
 if args.out:args.out.write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
