#!/usr/bin/env python3
"""Independently replay K/B/Peirce -> S certificate, using exact trees."""
from pathlib import Path
import argparse
import copy
import hashlib
import json
from verify_basis import formula, subst, expected_targets, fail

BASE=Path(__file__).resolve().parent

def replay(data):
    if data.get('format')!='kbp-closed-basis-v1':fail('wrong format')
    expected=expected_targets()
    expected['W']=[['v0',['v0','v1']],['v0','v1']]
    roots={'K','B','Peirce'}
    if set(data.get('axiom_kinds',[]))!=roots:fail('unapproved basis')
    checked=[]
    def app(a,arity):
        if not isinstance(a,dict) or set(a)!={'lemma','args'}:fail('malformed application')
        n=a['lemma']
        if not isinstance(n,int) or n<0 or n>=len(checked):fail('reference is not earlier')
        args=a['args']
        if not isinstance(args,list) or len(args)!=checked[n]['arity']:fail('wrong arity')
        for x in args:formula(x,arity)
        return subst(checked[n]['statement'],args)
    for n,row in enumerate(data['rows']):
        if row.get('id')!=n:fail('wrong id')
        arity=row['arity']
        if not isinstance(arity,int) or arity<0:fail('invalid arity')
        formula(row['statement'],arity)
        p=row['proof']
        if p['kind'] in roots:
            if row['statement']!=expected[p['kind']]:fail('false basis root')
        elif p['kind']=='mp':
            if app(p['major'],arity)!=[app(p['minor'],arity),row['statement']]:fail('invalid modus ponens')
        else:fail('unapproved rule')
        checked.append(row)
    if set(data['targets'])!=set(expected):fail('wrong target set')
    for name,n in data['targets'].items():
        if not isinstance(n,int) or n<0 or n>=len(checked):fail('invalid target index')
        if checked[n]['statement']!=expected[name]:fail('wrong target '+name)
    return {'rows':len(checked),'basis_roots':sum(r['proof']['kind'] in roots for r in checked),
             'mp_rows':sum(r['proof']['kind']=='mp' for r in checked),'targets':data['targets']}

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path)
    args=p.parse_args()
    raw=(BASE/'kbp_closed_certificate.json').read_bytes();data=json.loads(raw)
    result=replay(data)
    result['certificate_sha256']=hashlib.sha256(raw).hexdigest()
    bad=copy.deepcopy(data);bad['rows'][-1]['proof']['minor']['lemma']=len(data['rows'])-1
    try:replay(bad)
    except ValueError:result['self_reference_mutation_rejected']=True
    else:fail('accepted cyclic proof')
    bad=copy.deepcopy(data);bad['rows'][0]['statement']=['v0','v1']
    try:replay(bad)
    except ValueError:result['false_K_mutation_rejected']=True
    else:fail('accepted false root')
    text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
