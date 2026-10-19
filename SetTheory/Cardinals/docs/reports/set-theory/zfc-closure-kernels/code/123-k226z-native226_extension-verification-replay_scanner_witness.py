#!/usr/bin/env python3
"""Exact scanner counterexample to the unrepaired226 instruction layout."""
from pathlib import Path
import argparse,hashlib,json,sys
H=Path(__file__).resolve().parent.parent

def prove(base):
 sys.path.insert(0,str(base/'engine'))
 import independent_runtime as r
 table=H/'rejected/unrepaired226_native.tm';sites=H/'rejected/sites.json'
 site=json.loads(sites.read_text())[650];assert site==['1110100100111000010000000','CD',1]
 regs=[0]*9;spares=[0];gap=0
 actual,steps,trace=r.run(r.table(table),site[0],regs,spares,gap,limit=1000000,trace=True)
 expected,_=r.expected(site,regs,spares,gap)
 assert actual[:2]==expected[:2]==(96,0) and actual[2]!=expected[2]
 diff=[[q,int(q in actual[2]),int(q in expected[2])]for q in sorted(actual[2]^expected[2])]
 assert diff==[[20,1,0],[23,0,1]]
 return {'status':'EXACT_UNREPAIRED226_RUNTIME_COUNTEREXAMPLE','site_index':650,'site':site,'logical_registers':regs,'first_spare_and_tail':spares,'gap':gap,
 'table_sha256':hashlib.sha256(table.read_bytes()).hexdigest(),'sites_sha256':hashlib.sha256(sites.read_bytes()).hexdigest(),
 'helper_sha256':hashlib.sha256(Path(r.__file__).read_bytes()).hexdigest(),'steps_to_clean_redispatch':steps,
 'initial_one_positions':sorted(r.frame(site[0],regs,spares,gap)),'actual':r.describe(actual),'expected':r.describe(expected),
 'difference_position_actual_expected':diff,'literal_trace':trace,'scope':'A complete finite counterexample to a claimed instruction-frame protocol; no claim about the rejected table blank run.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--base',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();j=prove(a.base);a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(j,indent=2)+'\n');print(j['status'],j['steps_to_clean_redispatch'],'steps')
