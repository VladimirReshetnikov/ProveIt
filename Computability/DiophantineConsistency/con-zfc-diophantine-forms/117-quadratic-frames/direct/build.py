#!/usr/bin/env python3
"""Build literal quadratic integer sources with signed-output Pell frames."""
from copy import deepcopy
from pathlib import Path
import argparse
import importlib.util
import json

HERE = Path(__file__).resolve().parent
QUOTIENTS = [575, 584, 592, 600, 609, 618, 627, 636]
OUTPUTS = [573, 583, 591, 599, 607, 617, 625, 635]

def need(test, message):
    if not test:
        raise ValueError(message)

def read(path):
    return json.loads(path.read_text())

def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True, separators=(',', ':'))+'\n')

def source(variant=67):
    parent = read(HERE/'source/parent75.json')
    domain = read(HERE/'source/domain75.json')
    n = domain['baseline_body_variables']
    r = domain['baseline_body_rows']
    need((n, r, len(domain['guards'])) == (1259, 1177, 75), 'source75 dimensions')
    removed = QUOTIENTS + ([104] if variant <= 66 else []) + ([6,106] if variant <= 64 else []) + ([825] if variant == 63 else [])
    outputs = OUTPUTS + ([6,106] if variant <= 64 else [])
    child = dict(schema='quadratic_sum_squares_v1', domain='unrestricted integers',
                 variant=f'squared_output_frame_{variant}_predicates',
                 variables=deepcopy(parent['variables'][:n]),
                 residuals=deepcopy(parent['residuals'][:r]))
    row = child['residuals'][1176]
    need(row == dict(label='shared.frame_definition', terms=[[1,[643]],[-1,[1258]]]),
         'exact old frame row')
    row['label'] = 'shared.signed_output_frame_definition'
    row['terms'] += [[a, monomial] for m in outputs for a, monomial in [(1,[m]),(-1,[m,m])]]
    retained = []
    for j, old in enumerate(domain['guards']):
        p = old['predicate']
        if p['kind'] == 'retained_scalar' and p['raw_variables'][0] in removed:
            continue
        new_aux = list(range(len(child['variables']), len(child['variables'])+3))
        mp = dict(zip(old['auxiliary'],new_aux))
        child['variables'].extend(deepcopy(parent['variables'][k]) for k in old['auxiliary'])
        oldrow = deepcopy(parent['residuals'][r+j])
        oldrow['terms'] = [[c,[mp.get(k,k) for k in mon]] for c,mon in oldrow['terms']]
        child['residuals'].append(oldrow)
        retained.append(dict(predicate=deepcopy(p), auxiliary=new_aux, old_position=j))
    need(len(retained)==variant, 'exact specified predicates removed')
    return child, dict(body_variables=n, body_rows=r, guards=retained,
                       removed_quotients=QUOTIENTS, removed_guard_indices=removed,
                       signed_outputs=outputs,
                       modified_body_row=1176)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--variant',type=int,choices=[67,66,64,63],default=63)
    parser.add_argument('--profiles', nargs='*', default=['support32','support16_affine2'])
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('pinned_terminal_elimination',HERE/'source/terminal_elimination.py')
    engine = importlib.util.module_from_spec(spec);spec.loader.exec_module(engine)
    parent, domain=source(args.variant)
    files={'parent.json':parent,'domain.json':domain}
    census={}
    for name in args.profiles:
        cap=int(name.split('_')[0].replace('support',''))
        affine=int(name.split('_affine')[1]) if '_affine' in name else None
        eq, cert, metrics=engine.optimize(parent,max_support=cap,affine_support=affine)
        need(cert['unconstrained_removed']==[],'no unconstrained coordinate removal')
        engine.verify(parent,eq,cert)
        files[name+'/equation.json']=eq
        files[name+'/projection.json']=cert
        files[name+'/polynomial.json']=engine.expand(eq)
        census[name]=eq['metrics']
        print(name,json.dumps(eq['metrics']),flush=True)
    files['CENSUS.json']=census
    for path,value in files.items():
        out=HERE/'variants'/str(args.variant)/path
        if args.check:
            need(out.read_text()==json.dumps(value,sort_keys=True,separators=(',', ':'))+'\n',
                 'deterministic reconstruction '+path)
        else:write(out,value)

if __name__=='__main__':main()
