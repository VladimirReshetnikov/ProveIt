#!/usr/bin/env python3
"""Independent finite source-frame closure check; imports no source compiler."""
from pathlib import Path
import argparse,hashlib,json

def inc(pc):
    n=len(pc);v=(int(pc,2)if pc else 0)+1
    return(format(v%2**n,'0'+str(n)+'b')if n else ''),int(v==2**n)
def strip(pc,bit,count):
    for i in range(len(pc)-1,-1,-1):
        if pc[i]==bit:
            count-=1
            if count==0:return pc[:i]
    raise AssertionError(('invalid tag',pc,bit,count))
def check(name,directory):
    sites=json.loads((directory/'sites.json').read_text())
    ins=json.loads((directory/'instructions.json').read_text())
    assert len(sites)==len(ins)==3671
    outcomes=0
    for i,(pc,op,a)in enumerate(sites):
        assert isinstance(pc,str)and len(pc)<=48
        if op=='halt':assert ins[i]==['halt'];continue
        for positive in([False,True]if op=='dec'else[False]):
            if op=='inc':assert ins[i][:2]==['inc',a];target=ins[i][2];successor,overflow=inc(pc)
            elif op=='dec':
                assert ins[i][:2]==['dec',a];target=ins[i][3 if positive else 2]
                successor,overflow=inc(pc if positive else strip(pc,'0',1))
            elif op=='breakTo':assert ins[i][0]=='jump';target=ins[i][1];successor,overflow=inc(strip(pc,'0',a))
            else:
                assert op=='continueTo'and ins[i][0]=='jump'
                target=ins[i][1];successor=strip(pc,'1',a);overflow=0
            assert overflow==0,(i,positive)
            assert successor.ljust(48,'0')==sites[target][0].ljust(48,'0'),(i,positive,target)
            outcomes+=1
    assert outcomes==4777
    return {'name':name,'source_sites':3671,'nonhalting_outcomes':outcomes,
      'all_overflow_flags_zero':True,'all_padded_successors_equal':True,
      'sites_sha256':hashlib.sha256((directory/'sites.json').read_bytes()).hexdigest(),
      'instructions_sha256':hashlib.sha256((directory/'instructions.json').read_bytes()).hexdigest()},sites
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--parent',type=Path,required=True);p.add_argument('--child',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    assert(a.parent/'instructions.json').read_bytes()==(a.child/'instructions.json').read_bytes()
    pa,ss=check('parent',a.parent);ch,tt=check('child',a.child)
    assert pa['instructions_sha256']==ch['instructions_sha256']=='43a4ba0d62f95fe766d5369940b0aa8b7a4da04824feb8836905e289640f59f7'
    assert [s[1:]for s in ss]==[t[1:]for t in tt]
    changed=[i for i,(s,t)in enumerate(zip(ss,tt))if s!=t];assert changed==list(range(3572,3659))
    result={'status':'PASS','results':[pa,ch],'instructions_identical':True,'source_opcodes_and_arguments_identical':True,'changed_address_sites':changed,'changed_address_count':len(changed),
      'consequence':'Together with the verified physical template: common extended source; gap increases by one only for positive decrements; unit spare appended only for increments; boundary head fixed.',
      'scope':'Finite source/address premises, not an independent proof of uniform physical-rule soundness or arithmetic calibration.'}
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='changed_address_sites'},indent=2))
if __name__=='__main__':main()
