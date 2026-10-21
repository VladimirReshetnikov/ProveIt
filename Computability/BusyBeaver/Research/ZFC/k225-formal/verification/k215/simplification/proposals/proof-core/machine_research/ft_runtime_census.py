#!/usr/bin/env python3
"""Fresh all-natural whole-tape primitive proof and exact engine-role census.
Uses the inherited symbolic engine, explicitly bundled with attribution.
A case starts from a valid dispatcher frame for arbitrary natural values.
Decoder prefix consumption is replayed literally before classifying engine rows.
"""
from pathlib import Path
from collections import defaultdict,Counter
import argparse,json,hashlib,sys,time
HERE=Path(__file__).resolve().parent;sys.path.insert(0,str(HERE/'vendor'))
import symbolic_runtime as sy, independent_runtime as ir
import source_language as sl,build221 as bb

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--table',type=Path,default=HERE/'ft-frontier/machine.native.tm');ap.add_argument('--output',type=Path,default=HERE/'ft-frontier/runtime.json');a=ap.parse_args()
 assert __debug__;T=ir.table(a.table);ss=json.loads((HERE/'ft-source.sites.json').read_text());tree=sl.tree(ss)
 M={int(k):int(v)for k,v in json.loads((HERE/'native-to-legacy.json').read_text()).items()}
 for q in sorted({q for q,b in T}|{z for w,d,z in T.values()}):
  if q not in M:M[q]=max(M.values())+1
 assert len(set(M.values()))==len(M) and M[84]==96 and M[254]==254
 inv={v:k for k,v in M.items()};U={(M[q],b):(w,d,M[z])for(q,b),(w,d,z)in T.items()};lemmas,blocks=sy.prove_blocks(U)
 groups,ps=bb.decoder_map(T,tree);G={p:q for q,paths in ps.items()for p in paths};engine=set();allrows=set();examples={};counts=Counter();rules=0;cases=0;tic=time.monotonic()
 for i,site in enumerate(ss):
  pc,op,arg=site;prefix=pc[:-1];tape={-1:1,**{j:int(v)for j,v in enumerate(prefix)}};before=tape.copy();q,h=84,0;pre=[]
  for tick in range(10000):
   if h==len(prefix):break
   k=(q,tape[h]);w,d,q=T[k];tape[h]=w;h+=d;pre.append(k)
  else:raise AssertionError('Decoder prefix bound')
  assert h==len(prefix)and tape==before and q==G[prefix]
  leaf=(q,int(pc[-1]));pre.append(leaf)
  for positive in((False,True)if op=='CD'else(False,)):
   ans=sy.case(U,lemmas,site,positive,append=0,keep_trace=True);native=[]
   for ev in ans['trace']:
    if ev[0]=='list':native.append(None)
    elif ev[0]=='literal':native.append((inv[ev[1][0]],ev[1][1]))
    else:
     assert ev[0]=='unary'
     n=ev[2]
     # Before engine entry the run is a concrete finite prefix; expand it.
     if all(x==0 for x in n[1:]):native.extend([(inv[ev[1][0]],ev[1][1])]*n[0])
     else:native.append((inv[ev[1][0]],ev[1][1]))
   assert native[:len(pre)]==pre,('Prefix/engine partition mismatch',i,positive,native[:len(pre)],pre)
   excluded=set();decoder_passes=0
   for j,k in enumerate(native):
    if k is not None and k[0]==84:
     assert native[j:j+len(pre)]==pre,('Repeated decoder mismatch',i,positive,j,native[j:j+len(pre)],pre)
     excluded.update(range(j,j+len(pre)));decoder_passes+=1
   used={k for j,k in enumerate(native)if k is not None and j not in excluded}
   for k in used:
    engine.add(k);counts[k]+=1
    if k not in examples:examples[k]={'index':i,'site':site,'positive':positive,'prefix_literal_steps':len(pre),'decoder_passes':decoder_passes,'engine_trace_prefix':[list(x)if x else None for x in native[len(pre):len(pre)+80]]}
   allrows.update((inv[q],b)for q,b in ans['rows']);rules+=ans['symbolic_steps'];cases+=1
  if i%500==0:print('proved',cases,'cases',round(time.monotonic()-tic,2),flush=True)
 # Include every row used by the four independently reproved list schemas.
 for block in blocks:
  for ev in block['trace']:
   if ev[0]!='list':engine.add((inv[ev[1][0]],ev[1][1]))
 special={str(q):{'engine_rows':[b for b in(0,1)if(q,b)in engine],'incoming':[[p,b,*act]for(p,b),act in sorted(T.items())if act[2]==q],'decoder_paths':ps.get(q,[]),'case_counts':{str(b):counts[q,b]for b in(0,1)},'examples':{str(b):examples[q,b]for b in(0,1)if(q,b)in examples}}for q in(26,38,134)}
 report={'status':'ALL_NATURAL_RUNTIME_PASS','table_sha256':hashlib.sha256(a.table.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256((HERE/'ft-source.sites.json').read_bytes()).hexdigest(),'working_states':len(T)//2,'cases':cases,'symbolic_rules':rules,'row_coverage':len(allrows),'engine_rows':[list(x)for x in sorted(engine)],'engine_row_count':len(engine),'engine_state_count':len({q for q,b in engine}),'special':special,'blocks':blocks,'seconds':time.monotonic()-tic,'scope':'Inherited symbolic all-natural proof rules, with fresh actual-table block proofs and every FT215 primitive case. Ordinary executable mathematical evidence; not a proof-assistant kernel theorem. Engine census excludes every exactly matched repetition of the literal decoder prefix through its leaf-selection row; it includes all other rows and all list-schema rows.'}
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k not in('special','engine_rows','blocks')},indent=2))
if __name__=='__main__':main()
