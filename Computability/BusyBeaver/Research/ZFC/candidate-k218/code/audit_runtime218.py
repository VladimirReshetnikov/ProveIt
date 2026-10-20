#!/usr/bin/env python3
"""Independent integrity/coverage and one-block audit for the K218 proof.

This does not replace rederiving all symbolic cases. The default replay does
both. Four block schemas below are independently checked from literal rows.
Adapted from the pinned K220 audit; inherited MIT No Attribution license.
"""
from pathlib import Path
import argparse,json,sys,hashlib
from common import *
CASES_SHA='8180a18a947ea8d4a2990f32c41a4dfcfdf1e2898cfbc40ca5b8e1b5e2dd1866'
ENGINE_SHA='c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145'
HELPER_SHA='0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346'

def normalize(word):
    out=[]
    for bit,constant,variable in word:
        if out and out[-1][0]==bit:
            b,c,v=out.pop();out.append((b,c+constant,v+variable))
        else:out.append((bit,constant,variable))
    return out

def exact_blocks(table,stored):
    """Prove the four schemas by literal rows and one explicitly checked self-loop.

    Each token (bit,c,v) has length c+v*n for arbitrary natural n.  The sole
    variable token is traversed by a self-loop, including its n=0 case.
    Remaining tokens are one cell each.  Only represented cells are touched.
    """
    B=[(0,1,0),(1,1,1)];C=[(1,1,0),(0,1,0),(1,0,1)]
    specs=[(73,1,'B','B',[(0,1,0),(1,1,0),(1,0,1)]),
           (95,1,'B','C',[(0,1,0),(1,1,0),(1,0,1)]),
           (48,-1,'B','B',[(1,1,0),(1,0,1),(0,1,0)]),
           (112,-1,'C','B',[(1,0,1),(0,1,0),(1,1,0)])]
    require([(x['entry'],x['direction'],x['before'],x['after'])for x in stored]
         ==[(q,d,a,b)for q,d,a,b,t in specs],'Four block signatures')
    reports=[]
    for rec,(entry,direction,before,after,tokens)in zip(stored,specs):
        target=B if after=='B'else C
        input_word=B if before=='B'else C
        if direction==-1:target=list(reversed(target));input_word=list(reversed(input_word))
        require(normalize(tokens)==normalize(input_word),'Block input word identity')
        q=entry;written=[];trace=[];c=v=0
        for bit,constant,variable in tokens:
            write,move,nxt=table[q,bit]
            require(move==direction,'Block scan direction')
            row=[q,bit,write,move,nxt]
            if variable:
                require((constant,variable)==(0,1)and nxt==q,'Unbounded token is not a self-loop')
                trace.append(['unary',row,[0,0,1]+[0]*10])
            else:
                require(constant==1,'Literal token is not one cell')
                trace.append(['literal',row])
            written.append((write,constant,variable));c+=constant;v+=variable;q=nxt
        require(q==entry and(c,v)==(2,1),'Block state or duration formula')
        require(normalize(written)==normalize(target),'Block output word identity')
        require(rec['steps']=='v+2'and rec['arbitrary_contexts']is True and rec['trace']==trace,
             'Stored block differs from independent exact-row derivation')
        reports.append({'entry':entry,'direction':direction,'before':before,'after':after,
                        'duration':[2,1],'trace':trace,'arbitrary_exterior_untouched':True})
    return reports

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for name in('baseline','table','sites','runtime','driver','canonical','output'):ap.add_argument('--'+name,type=Path,required=True)
    a=ap.parse_args();T=parse_table(a.table.read_bytes());S=json.loads(a.sites.read_text());Q={q for q,bit in T}
    require(sha_file(a.table)==TABLE_SHA and sha_file(a.sites)==SOURCE_SHA,'Pinned final inputs')
    require(len(Q)==218 and len(T)==436,'Exact state count')
    rec=json.loads((a.runtime/'runtime.json').read_text());cases=json.loads((a.runtime/'cases.json').read_text())
    require(sha_file(a.runtime/'cases.json')==CASES_SHA,'Pinned guarded-case certificate')
    require(rec['status']=='ALL_PRIMITIVE_INTERFACES_PROVED'and rec['debug_enabled']is True,'Incomplete proof')
    require(rec['table_sha256']==TABLE_SHA and rec['sites_sha256']==SOURCE_SHA and rec['driver_sha256']==sha_file(a.driver),'Runtime input/driver provenance')
    for path,digest in rec['dependencies'].items():require(sha_file(a.baseline/path)==digest,'Runtime dependency bytes: '+path)
    require(rec['dependencies']['portable/runtime/vendor/symbolic_runtime.py']==ENGINE_SHA and rec['dependencies']['portable/runtime/vendor/independent_runtime.py']==HELPER_SHA,'Pinned engine and helper')
    expected=[(i,p)for i,(_,op,arg)in enumerate(S)for p in((False,True)if op=='CD'else(False,))]
    require(len(expected)==len(cases)==rec['cases']==rec['expected_cases']==6167,'Guard census')
    require([(x['index'],x['positive'])for x in cases]==expected,'Exact ordered guard coverage')
    for x in cases:
        require(type(x['index'])is int and type(x['positive'])is bool,'Case identifier types')
        require(type(x['symbolic_steps'])is int and 0<x['symbolic_steps']<4000,'Proof construction bound')
        require(len(x['duration'])==13 and all(type(v)is int and v>=0 for v in x['duration'])and x['duration'][0]>0,'Positive affine duration')
        require(len(x['motion'])==13 and all(type(v)is int for v in x['motion']),'Head displacement type')
        require(set(x['kinds'])<={'literal','unary','list'}and all(type(v)is int and v>0 for v in x['kinds'].values())and sum(x['kinds'].values())==x['symbolic_steps'],'Proof rule census')
    require(sum(x['symbolic_steps']for x in cases)==rec['symbolic_steps']==1515158,'Symbolic step count')
    require(min(x['duration'][0]for x in cases)==rec['minimum_actual_steps']==12,'Minimum positive duration')
    require(rec['working_states']==218 and rec['transition_rows']==436,'Runtime state count')
    require(rec['directly_used_native_rows']==[list(key)for key in sorted(T)],'All436 literal rows covered')
    mp={int(q):int(z)for q,z in json.loads((a.baseline/'portable/runtime/reference_results/legacy_mapping.json').read_text()).items()}
    for q in Q|{254}:
        if q not in mp:mp[q]=q+1000
    require(len(set(mp.values()))==len(mp)and(mp[0],mp[84],mp[254])==(95,96,254),'Runtime mapping')
    legacy={(mp[q],bit):(w,d,mp[z])for(q,bit),(w,d,z)in T.items()}
    blocks=exact_blocks(legacy,rec['block_schemas'])
    can=json.loads(a.canonical.read_text());boot=can['startup']
    require(can['status']=='EXACT_K218_CANONICALIZATION_AND_BLANK_STARTUP_PASS'and can['table_sha256']==TABLE_SHA and can['canonical_sha256']==CANONICAL_SHA,'Independent startup certificate')
    require((boot['steps'],boot['native_state'],boot['head'],boot['header'],boot['extra_gap'])==(312909,84,-5,139,80),'Exact blank endpoint')
    require(boot['logical_registers']==[3,0,0,0,3,0,0,0,0]and boot['spares']==[1]*130 and len(boot['one_cells'])==277 and boot['all_other_cells']==0,'Complete initialized frame')
    # Independent bottom-up syntax census, not the source constructor.
    ids={};paths={};internal=set()
    def intern(node):
        if node not in ids:ids[node]=len(ids)
        return ids[node]
    for p,op,arg in S:
        require(p not in paths and p and set(p)<={'0','1'},'Source path')
        paths[p]=intern(('L',op,arg));internal.update(p[:i]for i in range(len(p)))
    require(not internal.intersection(paths),'Prefix-free source leaves')
    for p in sorted(internal,key=len,reverse=True):paths[p]=intern(('N',paths[p+'0'],paths[p+'1']))
    require((len(ids),len(S),len(internal),max(len(p)for p,_,_ in S))==(205,4744,4743,38),'Independent syntax census')
    receipt=dict(status='INDEPENDENT_K218_RUNTIME_INTEGRITY_AND_COVERAGE_PASS',working_states=218,transition_rows=436,guarded_cases=6167,symbolic_steps=1515158,
        minimum_duration_constant=12,source_dag_nodes=205,block_schemas_independently_rederived=blocks,
        table_sha256=TABLE_SHA,source_sha256=SOURCE_SHA,cases_sha256=CASES_SHA,runtime_receipt_sha256=sha_file(a.runtime/'runtime.json'),
        auditor_sha256=sha_file(Path(__file__)),scope='Stored proof integrity, complete case/row coverage and independent four-block proofs. Fresh full symbolic induction, ordinal source-control equivalence and startup replay remain separate obligations.')
    dump(a.output,receipt);print(receipt['status'])
if __name__=='__main__':main()
