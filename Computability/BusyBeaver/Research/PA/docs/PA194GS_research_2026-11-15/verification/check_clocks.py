#!/usr/bin/env python3
"""Audit complete frame closure and positive affine clocks for both machines.

The finite arithmetic checks below bind the written simulation argument.
They do not run or check the inherited PA proof compiler.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('inspection',ROOT/'vendor/relative_inspection.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

def main(output, candidate):
    old_sites,old_ins,old=m.inspect(ROOT/'reference/AX11H',ROOT/'vendor/literal')
    new_sites,new_ins,new=m.inspect(candidate,ROOT/'vendor/literal')
    assert old_ins==new_ins
    assert all(a[1:]==b[1:] for a,b in zip(old_sites,new_sites))
    assert old_sites[25]==new_sites[25]==['1000000','dec',8]
    ot=m.table(ROOT/'reference/AX11H/machine.native.tm')
    nt=m.table(candidate/'machine.native.tm')
    changes=[{'row':list(k),'parent':ot.get(k),'child':nt.get(k)}
             for k in sorted(ot.keys()|nt.keys()) if ot.get(k)!=nt.get(k)]
    assert {tuple(v['row']) for v in changes}=={(221,0),(221,1),(2066,0),(2066,1),(2067,0),(2067,1)}
    local=[]
    for table,words in [(ot,[('00',196),('01',217),('1',19)]),
                        (nt,[('0',196),('10',217),('11',19)])]:
        for word,target in words:
            q=2066;trace=[]
            for bit in map(int,word):
                w,d,z=table[q,bit]
                assert (w,d)==(bit,'R')
                trace.append([q,bit,z]);q=z
            assert q==target
            local.append({'word':word,'exit':target,'trace':trace})
    delta=[{'site':i,'old':a[0],'new':b[0],'length_change':len(b[0])-len(a[0])}
           for i,(a,b) in enumerate(zip(old_sites,new_sites)) if a[0]!=b[0]]
    assert len(delta)==49
    result={'status':'PASS','scope':'Finite bindings for the separately written relative iPRA theorem',
            'parent':old,'candidate':new,'same_source':True,'changed_source_addresses':49,
            'shorter':sum(x['length_change']<0 for x in delta),
            'longer':sum(x['length_change']>0 for x in delta),
            'same_length_changed_bits':sum(x['length_change']==0 for x in delta),
            'literal_changes':changes,'prefix_code_checks':local,
            'witness_maps':{'parent_to_child':'B_child(t+1)','child_to_parent':'B_parent(t+1)',
                            'B_j(k)':'startup_j + alpha_j*k + beta_j*k*(k-1)/2'}}
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['status','same_source','changed_source_addresses','shorter','longer','same_length_changed_bits']}))
    print('parent',old['physical_time_bound'])
    print('child',new['physical_time_bound'])

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,default=ROOT/'verification/clock_closure.json')
    p.add_argument('--candidate',type=Path,default=ROOT/'machine')
    args=p.parse_args()
    main(args.output,args.candidate)
