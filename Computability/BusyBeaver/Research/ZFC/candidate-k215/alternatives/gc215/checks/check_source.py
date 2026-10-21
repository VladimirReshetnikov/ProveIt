#!/usr/bin/env python3
"""Exact two-site GEN_C source construction and independent CFG audit.
The all-natural macro fact is copy: (C,T,X)=(c,0,0)->(c,c,0).
This checker binds that seven-leaf loop to the literal source. It does not
claim that finite examples prove the copy theorem or the whole machine.
"""
from pathlib import Path
import argparse,hashlib,json,sys
sys.path.insert(0,str(Path(__file__).parent))
import source_splice as s
OLD='212cf0ffde43c1cc22c183dd8bf0b3a699396f96c9942ee92a7cc372cd273ca9'
NEW='3b4e8203227f4be6d868ffdfb8d1a6311f5ac9a647dadf8386eb8f0de509ce57'
def sha(b):return hashlib.sha256(b).hexdigest()
def compact(x):return (json.dumps(x,separators=(',',':'))+'\n').encode()
def run(baseline,source,output):
 raw=baseline.read_bytes();assert sha(raw)==OLD
 old=json.loads(raw);rows=[x.copy()for x in old]
 changes=[(44,'0011001000100','CD'),(49,'00110010001110','CI')]
 for i,p,op in changes:
  assert rows[i]==[p,op,4];rows[i]=[p,op,3]
 built=compact(rows);assert built==source.read_bytes()and sha(built)==NEW
 before=s.parse(old);after=s.parse(rows)
 assert s.metrics(before)==dict(dag_nodes=201,leaf_occurrences=4732,maximum_depth=44,maximum_zero_run=6)
 assert s.metrics(after)==dict(dag_nodes=202,leaf_occurrences=4732,maximum_depth=44,maximum_zero_run=6)
 oldcfg=s.cfg_intervals(old);newcfg=s.cfg_intervals(rows)
 assert oldcfg==s.cfg_arithmetic(old)and newcfg==s.cfg_arithmetic(rows)
 assert all(x[0]==y[0]and x[2]==y[2]for x,y in zip(oldcfg,newcfg))
 assert [i for i,(x,y)in enumerate(zip(oldcfg,newcfg))if x!=y]==[44,49]
 copy=s.serial(s.closed_forest(after,44,51))
 assert copy==((('CD',3),(('CI',1),(('CI',6),('CC',3)))),(('CD',6),(('CI',3),('CC',2))))
 assert s.boundary(copy)==(0,0,False)
 receipt={'status':'EXACT_SOURCE_AND_TWO_INDEPENDENT_CFGS_PASS','baseline_sha256':OLD,'source_sha256':NEW,'changed_sites':[{'ordinal':i,'address':p,'opcode':op,'old_register':4,'new_register':3}for i,p,op in changes],'metrics':s.metrics(after),'source_control_flow_targets_unchanged':True,'copy_macro_interval':[44,51],'copy_macro':copy,'copy_macro_boundary':s.boundary(copy),'copy_theorem':'For all natural c, with logical T=X=0, the seven-leaf macro preserves C=c, sets T=c, and restores X=0. All other registers are unchanged. The two loops terminate by the descending measures C and X.','scope':'Literal source and guarded-CFG audit; universal runtime, startup and logical calibration are separate obligations.'}
 output.mkdir(exist_ok=True);(output/'source.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('baseline',type=Path);a.add_argument('source',type=Path);a.add_argument('output',type=Path);z=a.parse_args();run(z.baseline,z.source,z.output)
