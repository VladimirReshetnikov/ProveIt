#!/usr/bin/env python3
"""Audit integrity and coverage of a retained runtime receipt; standard library.

This is a quick stored-evidence audit. It does not rederive the unbounded
symbolic proofs. Run check_literal_runtime.py for a fresh mathematical replay.
"""
from pathlib import Path
import argparse
import hashlib
import json

def require(condition,message):
    if not condition:raise ValueError(message)

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def strip(pc,bit,count):
    for index in range(len(pc)-1,-1,-1):
        if pc[index]==bit:
            count-=1
            if count==0:return pc[:index]
    return ''

def verify(table_path,sites_path,receipt_path,checker_dir):
    receipt=json.loads(receipt_path.read_text())
    require(receipt.get('status')=='UNIVERSAL_MATHEMATICAL_PASS','Receipt is not a completed runtime pass')
    require(digest(table_path)==receipt['table_sha256'],'Table hash differs')
    require(digest(sites_path)==receipt['sites_sha256'],'Source hash differs')
    for key,filename in [('checker_sha256','check_literal_runtime.py'),('engine_sha256','symbolic_runtime.py'),('helper_sha256','independent_runtime.py')]:
        require(digest(checker_dir/filename)==receipt[key],f'Checker code hash differs: {filename}')
    filename=receipt['cases_file']
    require(isinstance(filename,str) and Path(filename).name==filename,'Case filename must be a basename')
    cases_path=receipt_path.parent/filename
    require(digest(cases_path)==receipt['cases_sha256'],'Companion case hash differs')
    cases=json.loads(cases_path.read_text())
    table={};start=None
    for line in table_path.read_text().splitlines():
        if line.startswith('#! start '):
            require(start is None,'Duplicate start declaration');start=int(line.split()[-1]);continue
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        require((q,b)not in table and b in(0,1) and w in(0,1) and d in('L','R'),'Malformed literal table')
        table[q,b]=w,d,z
    states={q for q,b in table}
    require(start==95 and 254 not in states,'Expected legacy start95 and halt254')
    require(set(table)=={(q,b)for q in states for b in(0,1)},'Partial literal table')
    require({z for w,d,z in table.values()}-states=={254},'Unexpected halt or missing target')
    reachable={95};pending=[95]
    for q in pending:
        for b in(0,1):
            z=table[q,b][2]
            if z!=254 and z not in reachable:reachable.add(z);pending.append(z)
    require(reachable==states,'Declared graph contains unreachable states')
    require(len(states)==receipt['working_states']==receipt['graph_reachable_states'],'State census differs')
    require(len(table)==receipt['transition_rows'],'Transition census differs')
    recorded_rows=[tuple(row)for row in receipt['directly_used_rows']]
    require(len(recorded_rows)==len(set(recorded_rows)) and set(recorded_rows)==set(table),'Transition coverage differs')
    require(receipt['all_transition_rows_exercised'] is True,'Missing full-coverage assertion')
    sites=json.loads(sites_path.read_text());trie={};addresses=[]
    require(isinstance(sites,list)and bool(sites),'Empty or malformed source')
    for site in sites:
        require(isinstance(site,list)and len(site)==3,'Malformed source row')
        pc,op,arg=site
        require(isinstance(pc,str)and 0<len(pc)<=64 and set(pc)<={'0','1'},'Invalid source address')
        require(op in('CI','CD','CB','CC','CH'),'Invalid primitive')
        require((type(arg)is int and 0<=arg<9)if op in('CI','CD')else(type(arg)is int and arg>=1)if op in('CB','CC')else arg is None,'Invalid argument')
        node=trie
        for bit in pc:
            require('leaf'not in node,'Source leaf prefixes another source leaf')
            node=node.setdefault(bit,{})
        require(not node,'Duplicate source leaf or conflicting prefix')
        node['leaf']=True;addresses.append(pc)
    def complete(node):
        if 'leaf'in node:return len(node)==1
        return set(node)=={'0','1'}and complete(node['0'])and complete(node['1'])
    require(complete(trie)and addresses==sorted(addresses),'Incomplete or unordered source tree')
    require(receipt['complete_source_prefix_tree'] is True,'Missing source completeness assertion')
    expected=[(index,positive)for index,(_,op,_)in enumerate(sites)
              for positive in((False,True)if op=='CD'else(False,))]
    require(isinstance(cases,list)and len(cases)==len(expected)==receipt['cases'],'Guarded case count differs')
    for case,(index,positive)in zip(cases,expected):
        require(type(case['site_index'])is int and case['site_index']==index and type(case['positive'])is bool and case['positive']==positive,'Case/source pairing differs')
        duration=case['duration'];motion=case['motion'];steps=case['symbolic_steps'];kinds=case['kinds']
        require(isinstance(duration,list)and len(duration)==13 and all(type(x)is int and x>=0 for x in duration)and duration[0]>0,'Invalid positive affine duration')
        require(isinstance(motion,list)and len(motion)==13 and all(type(x)is int for x in motion),'Invalid affine head displacement')
        require(type(steps)is int and 0<steps<4000,'Invalid symbolic proof length')
        require(isinstance(kinds,dict)and set(kinds)<={'literal','unary','list'}and all(type(x)is int and x>=0 for x in kinds.values())and sum(kinds.values())==steps,'Rule-type census differs')
        pc,op,arg=sites[index]
        if op!='CH':
            if op=='CC':overflow=0
            else:
                before=strip(pc,'0',arg if op=='CB'else 1)if op=='CB'or(op=='CD'and not positive)else pc
                overflow=int(not before or set(before)=={'1'})
            require(motion==[-overflow]+[0]*12,'Wrong source-prescribed head displacement')
    require(sum(c['symbolic_steps']for c in cases)==receipt['symbolic_steps'],'Symbolic-step total differs')
    require(min(c['duration'][0]for c in cases)==receipt['minimum_actual_steps'],'Minimum duration differs')
    return {'status':'RETAINED_RUNTIME_RECEIPT_INTEGRITY_PASS','states':len(states),'rows':len(table),
            'guarded_cases':len(cases),'symbolic_steps':receipt['symbolic_steps'],
            'source_sha256':receipt['sites_sha256'],'table_sha256':receipt['table_sha256'],
            'scope':'Hashes, complete syntax, case alignment, affine metadata and full row coverage. Symbolic proofs are not rederived in this quick audit.'}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table',type=Path,required=True);ap.add_argument('--sites',type=Path,required=True)
    ap.add_argument('--receipt',type=Path,required=True)
    ap.add_argument('--checker-dir',type=Path,default=Path(__file__).resolve().parent)
    args=ap.parse_args();print(json.dumps(verify(args.table,args.sites,args.receipt,args.checker_dir),indent=2))

if __name__=='__main__':main()
