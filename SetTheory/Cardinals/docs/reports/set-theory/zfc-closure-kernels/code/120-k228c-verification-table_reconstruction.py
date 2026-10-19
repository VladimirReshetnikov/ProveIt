#!/usr/bin/env python3
"""Reconstruct K228 from the exact released K230 and H-loop intermediate.

Python standard library only. Paths default relative to this file.
The H-loop source-equivalence proof is supplied by the accompanying H builder.
"""
from pathlib import Path
import argparse, hashlib, json

ROOT=Path(__file__).resolve().parent
PINS={
 'original':'e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8',
 'h':'a4d7614b7bfc61f0c9934013f7bec6897aacc53978bc100613037b150f7a5645',
 'sites':'61450579877bc79cc4bc323ff0b8ae506064c79644107f4d818401dcfbce941b',
 'canonical':'06726bd731f3a42e3ccd1c4189d80af74ba2d486e333045097480fcaa3313001',
 'oldlabels':'2b791ed22523b9610d43d7440631b27063089d2d1a24cf3bfbe5ace6cf416ea2',
 'normalized':'0466c10a478b573d98ca91ea68a4159a83b15247aecd525388172f473cfe522c',
}
def require(ok,msg):
 if not ok:raise ValueError(msg)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def parse(raw):
 table={};starts=[]
 for line in raw.decode('ascii').splitlines():
  if line.startswith('#! start '):starts.append(int(line[9:]))
  elif line and not line.startswith('#'):
   fields=line.split();require(len(fields)==5,'Malformed row');q,b,w,d,z=fields;q,b,w,z=map(int,(q,b,w,z))
   require(q>=0 and z>=0 and b in(0,1) and w in(0,1) and d in('L','R') and(q,b) not in table,'Malformed or duplicate transition')
   table[q,b]=(w,1 if d=='R' else -1,z)
 require(len(starts)==1,'Exactly one start declaration is required')
 return table,starts[0]
def validate(table,start,halt,count):
 states={q for q,b in table}
 require(len(states)==count and len(table)==2*count,'Wrong working-state count')
 require(set(table)=={(q,b) for q in states for b in(0,1)},'Partial transition table')
 require(start in states and halt not in states,'Invalid start or halt')
 require({z for w,d,z in table.values()}-states=={halt},'Unexpected undefined successor')
def encode(table,start):
 return(f'#! start {start}\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for(q,b),(w,d,z) in sorted(table.items()))).encode('ascii')
def normalize(q):return {0:95,95:0,84:96,96:84,230:254}.get(q,q)
def build(original_path,h_path,sites_path,out):
 raw=Path(original_path).read_bytes();hraw=Path(h_path).read_bytes();sraw=Path(sites_path).read_bytes()
 for key,value in(('original',raw),('h',hraw),('sites',sraw)):require(sha(value)==PINS[key],f'Wrong pinned {key} input')
 old,start=parse(raw);h,hs=parse(hraw);require(start==hs==0,'Released labels must start in0');validate(old,0,230,230);validate(h,0,230,229)
 require({q for q,b in old}==set(range(230)),'Wrong released working labels')
 # Independently verify all H-stage literal changes, including every redirected target.
 expected={(q,b):(w,d,63 if z==79 else z) for(q,b),(w,d,z) in old.items() if q!=79}
 expected[63,0]=(0,-1,123);expected[63,1]=(1,-1,30);expected[121,0]=(0,1,63);expected[121,1]=(1,1,13)
 require(h==expected,'H intermediate has unexpected literal changes')
 require(h[71,0]==(0,1,21) and h[80,1]==(0,-1,42),'Unexpected retained delayed-erasure rows')
 require(h[126,0]==(0,1,140) and h[140,0]==(0,1,49) and h[140,1]==(0,1,48),'Unexpected deleted-state interface')
 new={(q,b):(w,d,71 if z==140 else z) for(q,b),(w,d,z) in h.items() if q!=140}
 new[71,0]=(0,-1,91);new[80,1]=(1,-1,138);validate(new,0,230,228)
 require({q for q,b in new}==set(range(230))-{79,140},'Wrong deleted states')
 order=sorted({q for q,b in new});number={q:i for i,q in enumerate(order)}|{230:228}
 canonical={(number[q],b):(w,d,number[z]) for(q,b),(w,d,z) in new.items()};validate(canonical,0,228,228)
 require({q for q,b in canonical}==set(range(228)),'Noncanonical final labels')
 normalized={(normalize(q),b):(w,d,normalize(z)) for(q,b),(w,d,z) in new.items()};validate(normalized,95,254,228)
 for(q,b),(w,d,z) in new.items():
  require(canonical[number[q],b]==(w,d,number[z]),'Canonical relabel does not commute')
  require(normalized[normalize(q),b]==(w,d,normalize(z)),'Normalized relabel does not commute')
 raws={'canonical':encode(canonical,0),'oldlabels':encode(new,0),'normalized':encode(normalized,95)}
 for key,value in raws.items():require(sha(value)==PINS[key],f'Wrong reconstructed {key} bytes')
 out=Path(out);out.mkdir(parents=True,exist_ok=True)
 for key,value in raws.items():(out/('k228.tm' if key=='canonical' else f'k228_{key}.tm')).write_bytes(value)
 receipt={'status':'EXACT_K228_CONSTRUCTION_AND_RELABELING_PASS','states':228,'transition_rows':456,'binary_symbols':[0,1],'directions':['L','R'],'start':0,'halt':228,'dispatcher':number[84],'deleted_released_labels':[79,140],'old_to_canonical':number,'canonical_to_old':order+[230],'normalization_nonidentity':{q:normalize(q) for q in set(range(230))|{230} if normalize(q)!=q},'input_sha256':{k:PINS[k] for k in('original','h','sites')},'output_sha256':{k:sha(v) for k,v in raws.items()},'source_obligation':'The separate H-loop theorem calibrates the supplied5121-leaf source to released K230.'}
 (out/'construction.json').write_text(json.dumps(receipt,indent=2)+'\n')
 return old,canonical,normalized,json.loads(sraw),receipt

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--original',type=Path,default=ROOT/'inputs/k230.tm');p.add_argument('--h-table',type=Path,default=ROOT/'inputs/k229_h_oldlabels.tm');p.add_argument('--sites',type=Path,default=ROOT/'inputs/sites_h.json');p.add_argument('--output-dir',type=Path,default=ROOT/'reproduced/machines');a=p.parse_args()
 *_,receipt=build(a.original,a.h_table,a.sites,a.output_dir);print(json.dumps({k:v for k,v in receipt.items() if k not in('old_to_canonical','canonical_to_old')},indent=2))
if __name__=='__main__':main()
