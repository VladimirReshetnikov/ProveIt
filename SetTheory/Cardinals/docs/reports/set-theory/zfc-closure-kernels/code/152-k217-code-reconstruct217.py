#!/usr/bin/env python3
"""Deterministic construction; no search. Full runtime is verified separately."""
from pathlib import Path
import argparse,hashlib,json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
import source_language as s
import build221 as b
PARENT_TABLE='9c8505bf3731212192b83ee61dbc569085b4675ae9e0539843ae57d43ad9e886'
PARENT_SOURCE='264fba90229974a53c2c5c943cf5fe8924327b6bbc31bd47e64d7f5c670b7495'
NATIVE='b235f7d0403460ff00d274d7d030fec6ba3562127035165e3ead555237c83088'
CANONICAL='522a71c067afe8862c9aab98e0f7f93eac747f5ef91d26bd3568760e1c1c478f'
SOURCE='9eac900e83742470893ea433cb0868e9ff6296f905cd6f3359b7a2c0e3114655'
def sha(x):return hashlib.sha256(x).hexdigest()
def need(ok,message):
 if not ok:raise ValueError(message)
def replace(t,old,new):
 if t==old:return new
 if s.leaf(t):return t
 return replace(t[0],old,new),replace(t[1],old,new)
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--base',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 need(__debug__ and not sys.flags.optimize,'Run Python with assertions enabled')
 raw=(a.base/'binary/machine/k218.native.tm').read_bytes();sr=(a.base/'source/sites218.json').read_bytes()
 need(sha(raw)==PARENT_TABLE and sha(sr)==PARENT_SOURCE,'Pinned parent identity')
 old=b.read_table(raw);T=dict(old);src=json.loads(sr);tree=s.tree(src);graph=s.graph_arithmetic(src)[0];word=[x[1:]for x in src];steps=[]
 for q,r,edge in [(210,188,0),(213,210,0),(201,213,1)]:
  groups,paths=b.decoder_map(T,tree);need(len(groups[q])==len(groups[r])==1,'Unique logical roles')
  node=next(iter(groups[q]));need(not s.leaf(node[edge])and groups[r]=={node[edge]},'Exact child role')
  need([k for k,v in T.items()if v[2]==r]==[(q,edge)],'Unique physical child entry')
  need(all(T[z,bit][:2]==(bit,1)for z in(q,r)for bit in(0,1)),'Pure decoder rows')
  if edge==0:
   (A,B),C=node;newnode=A,(B,C)
   patch={(q,0):(0,1,T[r,0][2]),(q,1):(1,1,r),(r,0):(0,1,T[r,1][2]),(r,1):(1,1,T[q,1][2])}
  else:
   A,(B,C)=node;newnode=(A,B),C
   patch={(q,0):(0,1,r),(q,1):(1,1,T[r,1][2]),(r,0):(0,1,T[q,0][2]),(r,1):(1,1,T[r,0][2])}
  need(all(s.boundary(x)==(0,0,False)for x in(A,B,C)),'Closed halt-free factors')
  tree=replace(tree,node,newnode);T.update(patch);rows=s.sites(tree)
  need([x[1:]for x in rows]==word,'Primitive word equality')
  need(s.graph_arithmetic(rows)[0]==graph==s.graph_intervals(rows),'Both guarded CFG resolvers')
  actual,_=b.decoder_map(T,tree);expected={z:{replace(n,node,newnode)for n in ns}for z,ns in groups.items()};expected[r]={newnode[1-edge]}
  need(dict(actual)==expected,'Complete expected decoder binding')
  steps.append({'parent_state':q,'child_state':r,'edge':edge,'paths':paths[q],'factor_lengths':[len(s.sites(x))for x in(A,B,C)],'patch':[[*k,*v]for k,v in patch.items()]})
 need(T[69,1]==T[400,1]==(1,1,31),'Common read-one branch')
 need(T[69,0]==(0,1,105)and T[400,0]==(0,1,104),'Read-zero endpoints')
 need(T[213,0]==(0,1,92)and T[213,1]==(1,1,90),'Exposed selector')
 need(T[92,0]==(0,1,104)and T[90,0]==(0,1,105),'Selector continuations')
 need([(k,v)for k,v in T.items()if v[2]==69]==[((53,1),(1,1,69))],'One marker')
 need([(k,v)for k,v in T.items()if v[2]==400]==[((224,0),(0,1,400))],'Zero marker')
 U={(q,bit):(w,d,69 if z==400 else z)for(q,bit),(w,d,z)in T.items()if q!=400};U[69,0]=(0,-1,213)
 folded,_=b.decoder_map(U,tree);unfolded,_=b.decoder_map(T,tree);expected={}
 for q,ns in unfolded.items():expected.setdefault(69 if q==400 else q,set()).update(ns)
 need(dict(folded)==expected,'Merged complete role relation')
 Q=sorted({q for q,bit in U});need(len(Q)==217 and len(U)==434,'State census')
 mapping={q:i for i,q in enumerate(Q)};mapping[254]=217;need(mapping[0]==0,'Start')
 canonical={(mapping[q],bit):(w,d,mapping[z])for(q,bit),(w,d,z)in U.items()}
 native=b.table_bytes(U);can=b.table_bytes(canonical);source=s.compact(s.sites(tree))
 need((sha(native),sha(can),sha(source))==(NATIVE,CANONICAL,SOURCE),'Exact output byte identities')
 a.output.mkdir(parents=True,exist_ok=True)
 for name,data in [('k217.native.tm',native),('k217.tm',can),('sites217.json',source),('unfolded218.native.tm',b.table_bytes(T))]:(a.output/name).write_bytes(data)
 receipt={'status':'DETERMINISTIC_K217_RECONSTRUCTION_PASS','working_states':217,'rows':434,'removed_states':[400],'added_states':[],'rotations':steps,'changed_retained_rows':[{'state':q,'read':bit,'old':old[q,bit],'new':v}for(q,bit),v in sorted(U.items())if old[q,bit]!=v],'metrics':s.metrics(tree),'changed_source_addresses':sum(x[0]!=y[0]for x,y in zip(src,s.sites(tree))),'native_sha256':NATIVE,'canonical_sha256':CANONICAL,'source_sha256':SOURCE,'scope':'Exact source and table construction; runtime, startup, and theory are separate obligations.'}
 need(len(receipt['changed_retained_rows'])==9,'Nine-row delta')
 (a.output/'construction.json').write_text(json.dumps(receipt,indent=2)+'\n')
 (a.output/'canonicalization.json').write_text(json.dumps({'native_to_canonical':mapping,'start':0,'halt':217,'working_states':217,'rows':434,'native_sha256':NATIVE,'canonical_sha256':CANONICAL},indent=2)+'\n')
 print(receipt['status'], '217 states, 434 rows, 94 changed source addresses')
if __name__=='__main__':main()
