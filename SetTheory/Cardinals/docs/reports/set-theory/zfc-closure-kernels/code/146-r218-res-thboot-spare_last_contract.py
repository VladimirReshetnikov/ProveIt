#!/usr/bin/env python3
"""Explore CI last-spare growth using the pinned symbolic rules.

The frame is reparameterized as an arbitrary spare prefix followed by one
arbitrary final spare.  This is the same family of nonempty finite lists.
"""
from pathlib import Path
import json,sys,time
ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'k220_replay/baseline/K221_Construction_2026-10-20'
sys.path.insert(0,str(BASE/'portable'))
import build221 as b
sys.path.insert(0,str(BASE/'portable/runtime/vendor'))
import symbolic_runtime as rt
T=b.read_table((ROOT/'root218/candidate218/candidate.tm').read_bytes())
S=json.loads((ROOT/'root218/candidate218/sites.json').read_text())
mp={int(q):int(z)for q,z in json.loads((BASE/'portable/runtime/reference_results/legacy_mapping.json').read_text()).items()}
for q in {q for q,bit in T}|{254}:
 if q not in mp:mp[q]=q+1000

def file_bits(values,append=None):
 atoms=[]
 for v in values:atoms+=rt.block(v)
 atoms += [rt.tail()] + rt.block(rt.add(rt.var(11),rt.num(0 if append is None else append)))
 return atoms+[rt.BLANK]

def main():
 rt.file_bits=file_bits
 U=T.copy();U[94,0]=(1,1,66)
 L={(mp[q],bit):(w,d,mp[z])for(q,bit),(w,d,z)in U.items()}
 lemmas,blocks=rt.prove_blocks(L)
 seen=set();records=[]
 for i,site in enumerate(S):
  if site[1]=='CI' and site[2]not in seen:
   seen.add(site[2])
   try:
    ans=rt.case(L,lemmas,site,False,append=3)
    record={'index':i,'site':site,'status':'PASS','symbolic_steps':ans['symbolic_steps']}
   except Exception as e:
    record={'index':i,'site':site,'status':'FAIL','error':str(e)}
   records.append(record);print(json.dumps(record),flush=True)
 (Path(__file__).parent/'spare_last_contract.json').write_text(json.dumps(records,indent=2)+'\n')

if __name__=='__main__':main()
