#!/usr/bin/env python3
"""Replay every arbitrary-natural primitive contract of the 198-state experiment."""
from pathlib import Path
import argparse,hashlib,json,sys,time
import native_symbolic as s
HERE=Path(__file__).resolve().parent

def require(ok,message):
    if not ok:raise ValueError(message)

def verify_inputs():
    manifest=json.loads((HERE/'manifest.json').read_text())
    for name,digest in manifest['files_sha256'].items():
        require(hashlib.sha256((HERE/name).read_bytes()).hexdigest()==digest,'Hash mismatch: '+name)
    return manifest

def load_table(path):
    table={}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        require(q>=0 and z>=0 and b in(0,1) and w in(0,1) and d in('L','R'),'Invalid transition')
        require((q,b)not in table,'Duplicate row')
        table[q,b]=(w,1 if d=='R' else -1,z)
    states={q for q,b in table}
    require(all((q,b)in table for q in states for b in(0,1)),'Incomplete table')
    require({z for w,d,z in table.values()}-states=={254},'Unexpected terminal')
    require(74 in states and 84 in states,'Missing start or runtime root')
    return table

def load_sites(path):
    sites=json.loads(path.read_text());leaves=set();prefixes=set()
    for p,op,arg in sites:
        require(isinstance(p,str) and p and set(p)<={'0','1'},'Bad source address')
        require(p not in leaves,'Repeated source address')
        leaves.add(p);prefixes.update(p[:j]for j in range(len(p)))
        require(op in('CI','CD','CB','CC','CH'),'Bad source operation')
        require((op=='CH'and arg is None)or(type(arg)is int and ((op in('CI','CD')and 0<=arg<9)or(op in('CB','CC')and arg>=1))),'Bad source operand')
    require(not leaves&prefixes,'Overlapping source addresses')
    require(all(p+b in leaves|prefixes for p in prefixes for b in('0','1')),'Non-full source tree')
    require([row[0]for row in sites]==sorted(leaves),'Noncanonical source order')
    return sites

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=HERE/'runtime_receipt.json')
    args=parser.parse_args();verify_inputs()
    table=load_table(HERE/'data/runtime_198.native.tm');sites=load_sites(HERE/'data/runtime_198.sites.json')
    require(len(table)==396 and len(sites)==3810,'Unexpected experiment census')
    lemmas,blocks=s.prove_blocks(table);start=time.monotonic();count=0;used=set();maximum=0
    for i,site in enumerate(sites):
        for positive in([False,True]if site[1]=='CD'else[False]):
            result=s.case(table,lemmas,site,positive)
            count+=1;used.update(result['rows']);maximum=max(maximum,result['symbolic_steps'])
        if i%500==0:print(f'Checked {i+1}/{len(sites)} sites, {count} branch contracts',flush=True)
    require(count==4956,'Wrong branch count')
    result={'status':'ARBITRARY_NATURAL_PRIMITIVE_CONTRACTS_PASS','working_states':198,'transition_rows':396,'source_occurrences':3810,'branch_contracts':count,'rows_used_by_contracts':len(used),'checked_list_block_schemas':len(blocks),'maximum_symbolic_steps':maximum,'elapsed_seconds':time.monotonic()-start,'minimum_frame_gap':56,'blank_startup_calibrated':False,'accepted_blank_tape_con_pa_machine':False,'scope':'Universal primitive-frame replay by the inherited unary/list symbolic engine, with arbitrary natural gap, nine registers and nonempty spare list. Not a Lean kernel proof, a blank-startup proof, or a sub-196 result.'}
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
