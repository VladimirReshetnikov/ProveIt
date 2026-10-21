#!/usr/bin/env python3
"""Exact symbolic/source certificate for rowwise B/C swaps on accepted K215.
No binary runtime claim. Standard library only; pass repository ZFC directory.
"""
from __future__ import annotations
import argparse,hashlib,importlib.util,itertools,json,sys
from pathlib import Path
PARENT_SOURCE='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
PARENT_TABLE='9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
SPANS={'rho4':(1467,1766),'rho2':(2062,2412),'rho6':(888,1171)}
EXPECTED_WORDS={'rho4':'abcQQbacQQI','rho2':'abcIQabQacQII','rho6':'aacQFIQFIcI'}
def sha(b):return hashlib.sha256(b).hexdigest()
def need(c,m):
 if not c:raise ValueError(m)
def rename_tree(s,n,mp):
 if s.leaf(n):
  op,r=n;return(op,mp.get(r,r))if op in ('CI','CD')else n
 return(rename_tree(s,n[0],mp),rename_tree(s,n[1],mp))
def symbolic(w):
 st=[]
 for x in w:
  if x in 'abc':st.append(x)
  elif x=='F':st.append(1)
  else:
   right=st.pop();left=st.pop();st.append((x,left,right))
 need(len(st)==1,('bad postfix',w,st));return st[0]
def parameters(e):
 if isinstance(e,tuple):return set.union(*(parameters(x)for x in e[1:]))
 return {e}if e in ('a','b','c')else set()
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--zfc',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 p=a.zfc/'candidate-k215';sys.path.insert(0,str(p));sys.path.insert(0,str(p/'code'))
 import source_language as s
 import build221 as b
 raw=(p/'sites215.json').read_bytes();traw=(p/'k215.native.tm').read_bytes()
 need(sha(raw)==PARENT_SOURCE,'parent source hash');need(sha(traw)==PARENT_TABLE,'parent table hash')
 rows=json.loads(raw);old=s.tree(rows);T=b.read_table(traw);groups,_=b.decoder_map(T,old)
 flat=lambda x:[tuple(r[1:])for r in s.sites(x)]
 macros={'a':b.sole(groups,98),'b':b.sole(groups,12),'c':b.sole(groups,166),'I':b.sole(groups,90)}
 inc=('CI',1);macros.update(R=(macros['I'],inc),Q=(macros['I'],(inc,inc)),E=(macros['I'],((inc,inc),inc)),F=(macros['a'][0],inc))
 need(all(s.boundary(v)==(0,0,False)for v in macros.values()),'all formula macros closed')
 # Independent arithmetic/ancestor source resolvers agree.
 oldgraph=s.graph_intervals(rows);need(oldgraph==s.graph_arithmetic(rows)[0],'parent CFG')
 macro_results=[]
 for name,(lo,hi)in SPANS.items():
  word=EXPECTED_WORDS[name]
  got=[v for t in word for v in flat(macros[t])]
  need(got==[tuple(r[1:])for r in rows[lo:hi]],('literal row word',name))
  swapped=word.translate(str.maketrans('bc','cb'))
  changed=[(op,{3:5,5:3}.get(r,r))if op in ('CI','CD')else(op,r)for op,r in got]
  want=[v for t in swapped for v in flat(macros[t])]
  need(changed==want,('renamed macro word',name))
  for t in ('a','b','c'):
   target={'a':'a','b':'c','c':'b'}[t]
   need(rename_tree(s,macros[t],{3:5,5:3})==macros[target],('copy macro renaming',t))
  macro_results.append({'row':name,'span':[lo,hi],'old_word':word,'new_word':swapped,'old_expression':symbolic(word),'new_expression':symbolic(swapped),'all_macro_blocks_closed':True,'literal_parameter_renaming':True})
 a.output.mkdir(parents=True,exist_ok=False);variants=[]
 for name,changed_names in [('rho6',('rho6',)),('joint24',('rho4','rho2')),('joint246',('rho4','rho2','rho6'))]:
  rr=[r[:]for r in rows]
  for item in changed_names:
   lo,hi=SPANS[item]
   for i in range(lo,hi):
    if rr[i][1]in ('CI','CD'):rr[i][2]={3:5,5:3}.get(rr[i][2],rr[i][2])
  new=s.tree(rr);graph=s.graph_intervals(rr);need(graph==s.graph_arithmetic(rr)[0],'variant CFG')
  need([x[1]for x in graph]==[x[1]for x in oldgraph],'unchanged every guarded target')
  changed=[i for i in range(len(rows))if rr[i]!=rows[i]]
  need(len(changed)=={'rho6':4,'joint24':16,'joint246':20}[name],'changed ordinal census')
  need(all(rows[i][1]==rr[i][1]and set((rows[i][2],rr[i][2]))=={3,5}for i in changed),'only B/C changed')
  encoded=s.compact(rr);(a.output/(name+'.sites.json')).write_bytes(encoded)
  variants.append({'name':name,'source_sha256':sha(encoded),'metrics':s.metrics(new),'changed_ordinals':changed,'guarded_edges':sum(len(x[1]) for x in graph),'runtime_cases':sum(2 if x[1]=='CD' else 1 for x in rr),'same_guarded_targets':True,'source_patches':[{'span':SPANS[x],'register_permutation':{'3':5,'5':3}}for x in changed_names]})
 result={'status':'PASS_EXACT_SYMBOLIC_SOURCE_CERTIFICATE','baseline_source_sha256':PARENT_SOURCE,'baseline_table_sha256':PARENT_TABLE,'baseline_metrics':s.metrics(old),'macros':macro_results,'variants':variants,'scope':'Exact row formulas, all macro trees, literal parameter involution, full source reconstruction and guarded-target identity. All-natural inherited macro contracts and command compiler theorem are proved in joint_swaps_proof.md. No binary runtime/startup or machine state count claimed here.'}
 (a.output/'source-certificate.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
