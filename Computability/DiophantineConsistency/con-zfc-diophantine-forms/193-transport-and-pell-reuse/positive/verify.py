#!/usr/bin/env python3
"""Read-only finite release replay; this does not search for a Diophantine zero."""
from pathlib import Path
import argparse,collections,copy,hashlib,json,sys
import build
import check_independent as independent
import check_companion as companion
from reconstruct_coefficients import check as reconstruct

ROOT=Path(__file__).resolve().parent

def verify():
    ledger=json.loads((ROOT/'SOURCE_LEDGER.json').read_text())
    for item in ledger['retained_files']:
        path=ROOT/item['local_path']
        independent.require(hashlib.sha256(path.read_bytes()).hexdigest()==item['sha256'],'Changed retained source: '+item['local_path'])
    parent=json.loads((ROOT/'parent87.json').read_text())
    independent.require(hashlib.sha256((ROOT/'parent87.json').read_bytes()).hexdigest()==independent.PARENT_SHA,'Changed frozen parent')
    result={'python_optimized':not __debug__,'source_snapshot':ledger['repository_commit'],'source_files_checked':len(ledger['retained_files'])}
    result['coefficients']=reconstruct()
    for kind,checker in [('whole190',independent.verify_graph),('quotient202',companion.check)]:
        data=(ROOT/(kind+'.json')).read_bytes()
        graph=json.loads(data)
        built=(json.dumps(build.build(parent,kind),indent=2)+'\n').encode()
        independent.require(built==data,'Producer reconstruction differs: '+kind)
        checked=checker(graph,parent)
        checked['actual_input_dependence']=independent.dependence_certificate(graph,independent.load_coefficients(graph))
        checked['sha256']=hashlib.sha256(data).hexdigest()
        checked['byte_exact_reconstruction']=True
        mutations=[('new_ScShift','+'),('new_S','+'),('RG','+')] if kind=='whole190' else [('new_gcenter','+'),('new_S','+'),('RG','+')]
        rejected=[]
        for name,op in mutations:
            corrupt=copy.deepcopy(graph)
            for row in corrupt['source']:
                if row[0]==name:row[1]=op
            corrupt['operation_breakdown']=dict(collections.Counter(r[1] for r in corrupt['source']))
            try:checker(corrupt,parent)
            except (ValueError,KeyError):rejected.append(name)
            else:raise ValueError('Accepted deliberately corrupted graph '+kind+': '+name)
        checked['deliberate_corruptions_rejected']=rejected
        result[kind]=checked
    result['scope']='Exact finite sources, coefficient reconstruction, polynomial graph identities, degrees, input dependence and producer replay; unbounded arithmetic and logical proofs are separate.'
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--receipt',type=Path)
    args=p.parse_args()
    result=verify()
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.receipt:args.receipt.write_text(text)
    print(text,end='')
