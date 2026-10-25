#!/usr/bin/env python3
"""Independent literal audit of the nearest-factorial source modification.

Reads JSON only; imports and executes no producing program.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OLD = ROOT / 'direct_parent'
NEW = ROOT.parent / 'direct/data'

def require(p, msg):
    if not p:
        raise ValueError(msg)

def named(row, names, rename=None):
    rename = rename or {}
    out = {}
    for c, monomial in row['terms']:
        key = tuple(sorted(rename.get(names[i], names[i]) for i in monomial))
        out[key] = out.get(key, 0) + c
    return {k:v for k,v in out.items() if v}

def doc(path):
    x = json.loads(path.read_text())
    return x, [v['name'] for v in x['variables']]

def check(old, old_names, new, new_names, oldg, oldgn, newg, newgn):
    removed = {'fact0.ceiling', 'fact0.remainder_bound'}
    expected = [r for r in old['residuals'] if r['label'] not in removed]
    require(len(expected) == len(new['residuals']) - 3, 'Unexpected row count')
    for a, b in zip(expected, new['residuals']):
        require(a['label'] == b['label'], 'An inherited row label changed')
        require(named(a, old_names) == named(b, new_names), 'An inherited polynomial changed')
    ext = {r['label']: named(r, new_names) for r in new['residuals'][-3:]}
    require(ext['remainder_budget.ceiling_ratio'] == {
        ('choose0.output', 'remainder_budget.ceiling_ratio'):-1,
        ('pow14.output',):1}, 'Incorrect B vB = M equation')
    require(ext['remainder_budget.ceiling_scaled'] == {
        ('fact0.output', 'pow14.output'):-1,
        ('pow0.output', 'remainder_budget.ceiling_ratio'):1,
        ('remainder_budget.ceiling_residue',):1}, 'Incorrect scaled ceiling equation')
    require(ext['remainder_budget.odd_radix_square'] == {
        ():-1, ('pow2.output',):1, ('remainder_budget.odd_radix_root',):-4,
        ('remainder_budget.odd_radix_root','remainder_budget.odd_radix_root'):-4},
        'Incorrect odd-square radix')
    require(len(oldg['residuals']) == len(old['residuals'])+5, 'Old guard count')
    require(len(newg['residuals']) == len(new['residuals'])+2, 'New guard count')
    require(newg['residuals'][:len(new['residuals'])] == new['residuals'], 'Guarded source mismatch')
    for j, name in enumerate(['fact0.remainder', 'fact0.slack', 'choose0.oslack']):
        row = named(oldg['residuals'][len(old['residuals'])+j], oldgn)
        require(row == {(name,):1, (f'new_guard{j}.a',f'new_guard{j}.a'):-1,
                        (f'new_guard{j}.b',f'new_guard{j}.b'):-1,
                        (f'new_guard{j}.c',):-1,
                        (f'new_guard{j}.c',f'new_guard{j}.c'):-1},
                'An allegedly deleted guard is different')
    rename = {f'new_guard{j}.{c}':f'new_guard{j-3}.{c}' for j in [3,4] for c in ['a','b','c']}
    cap = named(oldg['residuals'][-2], oldgn, rename)
    require(cap == named(newg['residuals'][-2], newgn), 'Anchor cap changed')
    norm = named(oldg['residuals'][-1], oldgn, rename)
    norm[('remainder_budget.ceiling_residue','remainder_budget.ceiling_residue')] = -4
    require(norm == named(newg['residuals'][-1], newgn), 'Norm pool changed beyond the declared S square')
    return True

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    old,on = doc(OLD/'source.json'); new,nn = doc(NEW/'source.json')
    oldg,ogn = doc(OLD/'guarded.json'); newg,ngn = doc(NEW/'guarded.json')
    check(old,on,new,nn,oldg,ogn,newg,ngn)
    rejected = []
    for mode in ['drop_ceiling_square', 'wrong_radix_sign', 'wrong_ceiling_scale']:
        n, g = copy.deepcopy(new), copy.deepcopy(newg)
        if mode == 'drop_ceiling_square':
            idx = ngn.index('remainder_budget.ceiling_residue')
            g['residuals'][-1]['terms'] = [r for r in g['residuals'][-1]['terms'] if r[1] != [idx,idx]]
        elif mode == 'wrong_radix_sign':
            n['residuals'][-1]['terms'][-1][0] *= -1
            g['residuals'][:len(n['residuals'])] = n['residuals']
        else:
            n['residuals'][-2]['terms'][0][0] *= -1
            g['residuals'][:len(n['residuals'])] = n['residuals']
        try:
            check(old,on,n,nn,oldg,ogn,g,ngn)
        except ValueError:
            rejected.append(mode)
        else:
            raise ValueError('Mutation accepted: '+mode)
    files = [OLD/'source.json', OLD/'guarded.json', NEW/'source.json', NEW/'guarded.json']
    receipt = {'status':'pass', 'inherited_rows_preserved':381,
               'old_rows_deleted':['fact0.ceiling','fact0.remainder_bound'],
               'new_rows_checked':3, 'initial_scalar_guards_deleted':3,
               'anchor_cap_preserved':True, 'norm_changes':'one additional -4 S^2 term only',
               'mutations_rejected':rejected,
               'sha256':{str(p.relative_to(ROOT.parent)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
               'scope':'Raw source and guard modification only; final coordinate projections and logical calibration are separate proofs.'}
    if args.receipt:
        args.receipt.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
