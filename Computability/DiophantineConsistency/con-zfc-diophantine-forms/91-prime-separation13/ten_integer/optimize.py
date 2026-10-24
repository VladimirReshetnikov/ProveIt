"""Exact shared-power, discriminant, and norm circuit rewrites.

This program does not alter the polynomial, its integer zero set, or its
coefficients. All source data are supplied in ./upstream. Python standard
library only; explicit verification checks remain active under python -O.
"""
import collections
import copy
import hashlib
import json
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parent

def finish(nodes, output, names, parent):
    live = set()
    todo = [output]
    while todo:
        i = todo.pop()
        if i in live:
            continue
        live.add(i)
        if 'left' in nodes[i]:
            todo.extend((nodes[i]['left'], nodes[i]['right']))
    mapping = {old: new for new, old in enumerate(sorted(live))}
    newnodes = []
    for old in sorted(live):
        node = dict(nodes[old])
        if 'left' in node:
            node['left'] = mapping[node['left']]
            node['right'] = mapping[node['right']]
        newnodes.append(node)
    counts = dict(collections.Counter(n['kind'] for n in newnodes if 'left' in n))
    degree = []
    for node in newnodes:
        degree.append(1 if node['kind'] == 'variable' else 0 if 'left' not in node else degree[node['left']] + degree[node['right']] if node['kind'] == 'mul' else max(degree[node['left']], degree[node['right']]))
    result = copy.deepcopy(parent)
    result.update(nodes=newnodes, output=mapping[output], named_nodes={k: mapping[v] for k, v in names.items() if v in mapping}, operation_counts=counts, total_operations=sum(counts.values()), degree_upper_bound=degree[mapping[output]], schema='identical-polynomial-shared-power-and-norm-v1')
    result['named_degree_bounds'] = {k: degree[v] for k,v in result['named_nodes'].items()}
    return result

def transform(parent, rewrite_delta=False):
    oldnodes = parent['nodes']
    oldnames = parent['named_nodes']
    nodes = []
    mapping = {}
    intern = {}
    def emit(node):
        if node['kind'] in ('add','mul') and node['left'] > node['right']:
            node = dict(node, left=node['right'], right=node['left'])
        key = tuple(sorted(node.items()))
        if key not in intern:
            intern[key] = len(nodes)
            nodes.append(node)
        return intern[key]
    def op(kind, a, b):
        return emit(dict(kind=kind, left=a, right=b))
    s = oldnames['S']
    s2 = next(i for i,n in enumerate(oldnodes) if n == dict(kind='mul',left=s,right=s))
    s4 = next(i for i,n in enumerate(oldnodes) if n == dict(kind='mul',left=s2,right=s2))
    s5 = next(i for i,n in enumerate(oldnodes) if n['kind']=='mul' and {n.get('left'),n.get('right')}=={s,s4})
    s3 = next(i for i,n in enumerate(oldnodes) if n['kind']=='mul' and {n.get('left'),n.get('right')}=={s,s2})
    for i, node in enumerate(oldnodes):
        if rewrite_delta and i == oldnames['Delta']:
            g = mapping[oldnames['g']]
            cap = mapping[oldnames['cap']]
            k = mapping[oldnames['K']]
            ckl = mapping[oldnames['CKL']]
            four = emit(dict(kind='literal',value=4))
            eight = emit(dict(kind='literal',value=8))
            g2 = op('mul',g,g)
            k2 = op('mul',k,k)
            cap3 = op('mul',cap,op('mul',cap,cap))
            g4paid = op('mul',four,g)
            bracket = op('sub',k2,op('mul',g4paid,op('mul',ckl,ckl)))
            coefficient = op('mul',g,op('mul',eight,cap3))
            mapping[i] = op('sub',op('mul',coefficient,bracket),op('mul',k2,op('mul',g2,g2)))
        elif i == s4:
            # The former S^4 node becomes S^3. It is used by the S^5 node
            # below, and the old later S^3 node is replaced by this shared one.
            mapping[i] = op('mul',mapping[s],mapping[s2])
        elif i == s5:
            mapping[i] = op('mul',mapping[s2],mapping[s4])
        elif i == s3:
            mapping[i] = mapping[s4]
        else:
            n = dict(node)
            if 'left' in n:
                n.update(left=mapping[n['left']],right=mapping[n['right']])
            mapping[i] = emit(n)
    names = {k: mapping[v] for k,v in oldnames.items()}
    center_name = 'center' if 'center' in names else 'shifted_center'
    a0, a1, z, sigma = [names[k] for k in ('guard','lucas',center_name,'Sigma')]
    z2 = op('mul',z,z)
    sigma2 = op('mul',sigma,sigma)
    inner = op('add',z2,op('mul',sigma2,op('sub',a0,a1)))
    four = emit(dict(kind='literal',value=4))
    tail = op('mul',four,op('mul',a0,op('mul',z2,sigma2)))
    out = op('sub',op('mul',inner,inner),tail)
    names.update(inner=inner,F10=out)
    return finish(nodes,out,names,parent)

def evaluate(d, variables, fixed, modulus):
    vals=[]
    for n in d['nodes']:
        k=n['kind']
        if k=='variable': v=variables[n['name']]
        elif k=='literal': v=n['value']
        elif k=='fixed': v=fixed[n['name']]
        elif k=='add': v=vals[n['left']]+vals[n['right']]
        elif k=='sub': v=vals[n['left']]-vals[n['right']]
        elif k=='mul': v=vals[n['left']]*vals[n['right']]
        else: raise ValueError(k)
        vals.append(v % modulus)
    return vals[d['output']]

def verify(parent,new, saving=2):
    if parent['total_operations'] - new['total_operations'] != saving: raise ValueError('wrong gate count')
    if new['degree_upper_bound'] != parent['degree_upper_bound']: raise ValueError('degree bound changed')
    if new['variables'] != parent['variables']: raise ValueError('variables changed')
    if new['fixed_recipes'] != parent['fixed_recipes']: raise ValueError('coefficients changed')
    rng=random.Random(20261023)
    fixednames={n['name'] for n in parent['nodes'] if n['kind']=='fixed'}
    tested=0
    for modulus in (2,3,5,7,101,1009,1000003,2**61-1):
        for _ in range(128):
            variables={v:rng.randrange(modulus) for v in parent['variables']}
            fixed={v:rng.randrange(modulus) for v in fixednames}
            if evaluate(parent,variables,fixed,modulus)!=evaluate(new,variables,fixed,modulus):
                raise ValueError('modular mismatch')
            tested+=1
    return dict(parent_operations=parent['total_operations'],new_operations=new['total_operations'],parent_split=parent['operation_counts'],new_split=new['operation_counts'],exact_degree_inherited_by_polynomial_identity=parent.get('exact_degree',parent['degree_upper_bound']),domain='Z^10',modular_checks=tested,modular_scope='Independent arbitrary residues for every fixed leaf and every variable; transcription check, not the semantic proof.',identities=['S^5 = (S^2)(S^3)','(Z^2-Sigma^2*(a0+a1))^2-4*Sigma^4*a0*a1 = (Z^2+Sigma^2*(a0-a1))^2-4*Z^2*Sigma^2*a0']+(['8*cap^3*g*K^2-g^2*(32*(C-K*L)^2*cap^3+g^2*K^2)=8*g*cap^3*(K^2-4*g*(C-K*L)^2)-g^4*K^2'] if saving==3 else []))

if __name__=='__main__':
    import runpy
    runner = runpy.run_path(str(ROOT/'optimize_shears.py'))
    print(json.dumps(runner['build_all'](), indent=2))
