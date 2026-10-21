#!/usr/bin/env python3
"""Deterministically reconstruct the two 215-state intermediates."""
from pathlib import Path
import argparse,hashlib,json,sys
HERE=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--baseline',type=Path,default=HERE.parent/'baseline/k215')
 p.add_argument('--out',type=Path,default=HERE/'rebuilt');a=p.parse_args()
 K=a.baseline.resolve();sys.path.insert(0,str(K/'code'))
 import build221 as b, source_language as sl
 assert sha(K/'k215.native.tm')=='9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
 assert sha(K/'sites215.json')=='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
 T=b.read_table((K/'k215.native.tm').read_bytes());R=sl.tree(json.loads((K/'sites215.json').read_text()))
 ((G,(F,(ci0,H))),B)=R
 assert G==(('CD',8),('CB',1)) and H==(('CD',6),('CC',2)) and ci0==('CI',0)
 Rnew=((G,(F,(ci0,(H,('CB',1))))),B)
 new_sites=sl.sites(Rnew)
 assert sl.graph_intervals(new_sites)==sl.graph_arithmetic(new_sites)[0]
 source=sl.compact(new_sites);assert source==(HERE/'accepted/cb1_sites.json').read_bytes()
 assert T[8,1]==(1,1,13)
 T[8,1]=(1,1,103)
 cb=b.table_bytes(T);assert cb==(HERE/'accepted/cb1_215.native.tm').read_bytes()
 assert sorted((q,b) for (q,b),(_,_,z) in T.items() if z==13)==[(38,0),(42,0)]
 assert T[38,0]==T[42,0]==(0,1,13)
 # The two exact three-step microtraces use only cells h and h-1.
 expected=[[(13,0,0,-1,91),(91,0,0,1,82),(82,0,0,1,49)],
           [(13,1,1,-1,31),(31,0,0,1,21),(21,1,0,1,60)]]
 for bit,steps in enumerate(expected):
  tape={0:bit,-1:0};q,h=13,0;trace=[]
  for _ in range(3):
   read=tape[h];w,d,z=T[q,read];trace.append((q,read,w,d,z));tape[h]=w;h+=d;q=z
  assert trace==steps and h==1 and q==[49,60][bit] and tape=={0:0,-1:0}
 T[13,0]=(0,1,49);T[13,1]=(0,1,60)
 norm=b.table_bytes(T);assert norm==(HERE/'accepted/normalized215.native.tm').read_bytes()
 assert len({q for q,_ in T})==215
 # Source decoding also traverses helper paths; check it after each construction.
 b.decoder_map(b.read_table(cb),Rnew);b.decoder_map(T,Rnew)
 a.out.mkdir(parents=True,exist_ok=True)
 (a.out/'cb1_sites.json').write_bytes(source);(a.out/'cb1_215.native.tm').write_bytes(cb);(a.out/'normalized215.native.tm').write_bytes(norm)
 result={'status':'RECONSTRUCTED','working_states':215,'source_metrics':sl.metrics(Rnew),
         'cb1_table_sha256':hashlib.sha256(cb).hexdigest(),'normalized_table_sha256':hashlib.sha256(norm).hexdigest(),
         'source_sha256':hashlib.sha256(source).hexdigest(),'normalization_microtraces':expected}
 (a.out/'construction.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
