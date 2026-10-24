#!/usr/bin/env python3
"""Targeted controls for the projection, fixed bounds, and sign orbits."""
import argparse
import copy
import json
from pathlib import Path
from check_projected import ProjectedAudit
from check_normalized import inspect_integer

def main():
    p=argparse.ArgumentParser();p.add_argument('natural',type=Path);p.add_argument('core',type=Path);p.add_argument('integer',type=Path);p.add_argument('--output',type=Path);args=p.parse_args();cases=[]
    def reject(name,change,check):
        a=ProjectedAudit(args.natural);change(a)
        try:check(a)
        except (ValueError,KeyError,StopIteration) as e:
            cases.append({'name':name,'rejected':True,'reason':str(e)});return
        raise ValueError('missed corruption: '+name)
    reject('swapped modus ponens labels',lambda a:a.binding['encoded_source']['rules'][-2]['labels'].reverse(),lambda a:a.check_source())
    reject('deleted bundled side condition',lambda a:a.binding['encoded_source']['rules'][-3].__setitem__('guard',None),lambda a:a.check_source())
    reject('wrong schema bound',lambda a:a.binding['upper'].__setitem__('a',a.binding['parameters']['x']),lambda a:a.check_bindings())
    reject('wrong quotient bound',lambda a:a.binding['range_lower_arguments'].__setitem__('u',a.binding['range_lower_arguments']['a']),lambda a:a.check_bindings())
    reject('halved label exponent',lambda a:a.binding['label_bound_certificate'].__setitem__('exponent',2**21),lambda a:a.check_majorants())
    reject('halved source exponent',lambda a:a.binding['radius_majorant'].__setitem__('exponent',2**22),lambda a:a.check_majorants())
    reject('changed projected polynomial coefficient',lambda a:a.p['terms'][0].__setitem__(0,2*a.p['terms'][0][0]),lambda a:a.check_expansion())
    core=ProjectedAudit(args.core);core.run();original=json.loads((args.integer/'normalization_certificate.json').read_text())
    def reject_sign(name,change):
        cert=copy.deepcopy(original);change(cert)
        try:inspect_integer(core,args.integer,cert)
        except (ValueError,KeyError,StopIteration) as e:
            cases.append({'name':name,'rejected':True,'reason':str(e)});return
        raise ValueError('missed normalization corruption: '+name)
    def remove_paired_quotient(c):
        action=next(x for x in c['actions'] if x['name'].endswith('.U'))
        q=core.names[action['name'][:-2]+'.B_mod_U.quotient'];action['raw_flips'].remove(q)
    reject_sign('U flip without quotient flip',remove_paired_quotient)
    reject_sign('sign action touches retained guard',lambda c:c['actions'][0]['raw_flips'].append(c['raw_seed_indices'][0]))
    reject_sign('missing normalized pivot',lambda c:c['normalized_pivots'].pop())
    reject_sign('reversed sign closure proof',lambda c:c['application_order'].reverse())
    result={'status':'PASS','rejected_corruptions':cases,'scope':'adversarial finite checks, not a consistency decision or kernel proof'}
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
