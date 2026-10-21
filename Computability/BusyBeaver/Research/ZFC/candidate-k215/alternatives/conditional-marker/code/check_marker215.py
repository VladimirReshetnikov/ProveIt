#!/usr/bin/env python3
"""Literal, independent checks for the marker215 all-tape simulation lemma.

No candidate programs are imported. The global theorem uses the induction
written in marker215-proof.tex; this checks its finite hypotheses and blocks.
Stored symbolic summaries are audited for order/identity, not re-proved here.
"""
from pathlib import Path
from collections import Counter
import argparse,gzip,hashlib,json

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(path):return json.loads(gzip.decompress(path.read_bytes()) if path.suffix=='.gz' else path.read_text())
def parse(path):
 t={};start=None
 for line in path.read_text().splitlines():
  if line.startswith('#! start '):start=int(line[9:]);continue
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();key=int(q),int(b)
  assert key not in t and b in('0','1')and w in('0','1')and d in('L','R')
  t[key]=int(w),1 if d=='R'else-1,int(z)
 return start,t

def block(t,q,head,cells,n):
 before=dict(cells)
 for step in range(n):
  assert head in cells
  bit=cells[head];w,d,q=t[q,bit];cells[head]=w;head+=d
 return q,head,cells,before

def phi(q):return 52 if q==176 else q

def check(base,dest):
 oldstart,T=parse(base/'k215.native.tm');start,N=parse(dest/'marker215.native.tm')
 assert oldstart==start==0
 assert sha(base/'k215.native.tm')=='9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
 assert sha(dest/'marker215.native.tm')=='e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252'
 assert set(T)==set(N)and len(N)==430
 assert {z for w,d,z in N.values()}-{q for q,b in N}=={254}
 incoming=lambda t,q:{key:act for key,act in t.items()if act[2]==q}
 assert incoming(T,52)=={(190,1):(1,1,52),(193,1):(1,1,52)}
 assert incoming(T,176)=={(156,1):(1,1,176),(165,0):(0,1,176),(193,0):(0,1,176)}
 assert incoming(T,156)=={(189,1):(1,-1,156)}
 assert incoming(N,176)=={(52,0):(0,-1,176)}
 # Literal outer-step transfer. The two exceptional source states are handled below.
 for(q,b),(w,d,z)in T.items():
  if q not in(52,176):assert N[q,b]==(w,d,phi(z))
 assert T[52,1]==T[176,1]==N[52,1]==(1,1,150)
 assert T[52,0]==(0,1,154)and T[176,0]==(0,1,168)
 local=[]
 for oldq,m,target in[(52,1,154),(176,0,168)]:
  for bit in(0,1):
   count=3 if bit==0 else 1
   q,h,cells,before=block(N,52,0,{-1:m,0:bit},count)
   assert (q,h,cells)==(target if bit==0 else 150,1,before)
   local.append({'old_state':oldq,'current':bit,'left_marker':m,'new_steps':count,'target':q,'head_delta':h,'tape_unchanged':True})
 # Both symbols at156: if its one branch is taken, the next current symbol is1.
 # It is established by the unique189/1 incoming edge, on arbitrary outside tape.
 for neighbour in(0,1):
  q,h,cells,before=block(T,189,0,{-1:neighbour,0:1},2)
  if neighbour==1:assert(q,h,cells[h])==(176,0,1)
 dstart,D=parse(dest/'marker215.tm');mapping={int(k):v for k,v in load(dest/'canonicalization.json')['native_to_dense'].items()}
 assert dstart==0 and mapping[0]==0 and mapping[254]==215
 assert len(set(mapping.values()))==216
 assert D=={(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in N.items()}
 assert sum(d==-1 for w,d,z in N.values())==sum(d==-1 for w,d,z in T.values())+1
 # Whole-frame blank replay, on both exact presentations, independent of startup parser.
 expected={-9,57};pos=58
 values=[0]*9;values[6]=4
 for value in values+[1]*40:
  pos+=1;expected.update(range(pos,pos+value+1));pos+=value+1
 assert len(expected)==95
 stored=load(dest/'runtime/startup.json.gz')
 assert stored['steps']==95714 and len(stored['trace'])==95714
 for t,qstart,qend,dense in[(N,0,84,False),(D,0,mapping[84],True)]:
  q=qstart;h=0;ones=set()
  for k in range(95714):
   bit=int(h in ones);w,d,z=t[q,bit]
   ref=stored['trace'][k]
   if dense:ref=[mapping[ref[0]],ref[1],ref[2],ref[3],ref[4],mapping[ref[5]]]
   assert[q,h,bit,w,d,z]==ref
   if w:ones.add(h)
   else:ones.discard(h)
   q=z;h+=d
  assert(q,h,ones)==(qend,-8,expected)
 assert stored['one_cells']==sorted(expected)
 source=load(dest/'sites.json');assert(dest/'sites.json').read_bytes()==(base/'sites215.json').read_bytes()
 leaves={p for p,op,arg in source};prefixes={p[:i]for p in leaves for i in range(len(p))}
 assert len(leaves)==4751 and len(prefixes)==4750 and not leaves&prefixes
 assert all(p+b in leaves|prefixes for p in prefixes for b in('0','1'))
 for p in sorted(prefixes):
  reached=[]
  for t in(T,N):
   cells={-1:1,**{i:int(v)for i,v in enumerate(p)}};before=dict(cells);q=84;h=0
   for tick in range(10000):
    if h==len(p):break
    assert h in cells
    w,d,q=t[q,cells[h]];cells[h]=w;h+=d
   assert h==len(p)and cells==before
   reached.append(q)
  assert reached[1]==phi(reached[0]),(p,reached)

 cases=load(dest/'runtime/runtime_cases.json.gz');wanted=[(i,pos)for i,x in enumerate(source)for pos in((False,True)if x[1]=='CD'else(False,))]
 assert[(c['site_index'],c['positive'])for c in cases]==wanted and len(cases)==6176
 legacy={int(k):int(v)for k,v in load(base/'code/runtime-inputs/inputs/legacy_mapping.json').items()}
 for q in{q for q,b in N}|{254}:
  if q not in legacy:legacy[q]=q+1000
 assert len({legacy[q]for q in{q for q,b in N}|{254}})==216
 assert set((q,b)for c in cases for q,b in c['rows'])=={(legacy[q],b)for q,b in N}
 for c in cases:assert len(c['duration'])==13 and c['duration'][0]>0 and all(x>=0 for x in c['duration'][1:])
 output={'status':'LITERAL_MARKER_THEOREM_HYPOTHESES_AND_RECORDS_PASS','table_sha256':sha(dest/'marker215.native.tm'),'source_sha256':sha(dest/'sites.json'),'working_states':215,'rows':430,'changed_rows':sum(T[key]!=N[key]for key in T),'scope':'All initial tapes and head positions, starting control0; not arbitrary control states. Global induction is in marker215-proof.tex. Stored universal case records audited, not independently rederived by this script.','local_blocks':local,'exceptional_predecessor':'189/1 writes1 L156; hence156/1 returns to current1 and uses common branch','blank_steps':95714,'blank_head':-8,'blank_ones':95,'cases':len(cases),'symbolic_rules':sum(c['symbolic_steps']for c in cases),'minimum_positive_duration':min(c['duration'][0]for c in cases),'row_coverage':430,'internal_decoder_prefixes':len(prefixes),'dense_bijection_pass':True,'direction_count_distinguishes_baseline':True}
 (dest/'literal-check.json').write_text(json.dumps(output,indent=2)+'\n');print(json.dumps(output,indent=2))

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[1]/'reference/primary215');ap.add_argument('--candidate',type=Path,default=Path(__file__).resolve().parents[1]/'machine');a=ap.parse_args();check(a.base,a.candidate)
