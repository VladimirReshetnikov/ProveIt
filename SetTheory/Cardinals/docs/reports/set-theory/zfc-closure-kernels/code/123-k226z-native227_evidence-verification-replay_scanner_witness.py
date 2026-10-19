#!/usr/bin/env python3
"""Pin the exact rejected seven-zero source address and its wrong tape result."""
from pathlib import Path
import argparse,hashlib,json,sys
H=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(H/'engine'))
import independent_runtime as r

def prove():
 table=H/'rejected/seven_zero227_native.tm';sites=H/'rejected/sites.json'
 site=json.loads(sites.read_text())[1042]
 assert site==['11101001001110010000000','CD',2]
 regs=[0]*9;spares=[0];gap=0;T=r.table(table)
 actual,steps,trace=r.run(T,site[0],regs,spares,gap,limit=1000000,trace=True)
 want,_=r.expected(site,regs,spares,gap)
 assert actual[:2]==want[:2]==(96,0) and actual[2]!=want[2]
 diff=[[p,int(p in actual[2]),int(p in want[2])] for p in sorted(actual[2]^want[2])]
 assert diff==[[16,1,0],[19,1,0],[21,0,1],[23,1,0]]
 return {'status':'EXACT_REJECTED_RUNTIME_COUNTEREXAMPLE','table_sha256':hashlib.sha256(table.read_bytes()).hexdigest(),
 'sites_sha256':hashlib.sha256(sites.read_bytes()).hexdigest(),'site_index':1042,'site':site,'logical_registers':regs,'spares':spares,'gap':gap,
 'steps_to_clean_redispatch':steps,'initial_tape':sorted(r.frame(site[0],regs,spares,gap)),
 'actual':r.describe(actual),'expected':r.describe(want),'difference_position_actual_expected':diff,'literal_trace':trace,
 'scope':'A valid clean instruction frame; this disproves the rejected table/source protocol, without making a claim about its blank run.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();j=prove();a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(j,indent=2)+'\n');print(j['status'],j['steps_to_clean_redispatch'],'steps')
