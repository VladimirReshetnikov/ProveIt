#!/usr/bin/env python3
"""Fresh data-only counted-suffix lift of the context-absorbed matrix source."""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path

PINS = {
 'matrix193_context_absorption.py': '1304ea242ca6a5faafdb527ac3e56c6cd06b0276dca6441fc3477c7065054485',
 'matrix193_context_absorption.json': '73f8cae212c6c1917e73cc76c7bf3c43b8c587748bbf4327eddf4c82e726a436',
 'matrix193_context_absorption.md': 'd7492809ba00a011c8280172bb016f96f3f6c240de6a823ed717d82bda5e4f4b',
 'group_directed_semigroup193.md': '75f7e527b62717f21394750842a5569adc56231f1f6d6fab5e359e63b71ce56e',
 'u15_unary_block_interface.md': 'cdc686700af3545609796034e0a2c906bd0438b6bcabc0c0b267954cc9d20452',
}

def need(ok, label):
    if not ok: raise ValueError(label)

def sha(raw): return hashlib.sha256(raw).hexdigest()

def pairs(items):
    out = {}
    for key, value in items:
        need(key not in out, 'duplicate JSON key')
        out[key] = value
    return out

def loads(raw):
    def bad(value): raise ValueError('nonfinite JSON: '+value)
    return json.loads(raw, object_pairs_hook=pairs, parse_constant=bad)

def exact(a, b):
    if type(a) is not type(b): return False
    if isinstance(a, dict): return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if isinstance(a, list): return len(a) == len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a == b

def eye(n): return [[int(i == j) for j in range(n)] for i in range(n)]
def zero(n): return [[0]*n for _ in range(n)]
def mul(a,b):
    n=len(a)
    return [[sum(a[i][k]*b[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def block(a,b):
    n=len(a);m=len(b)
    return [r+[0]*m for r in a]+[[0]*n+r for r in b]
def flat(a): return [v for row in a for v in row]
def power(a,n):
    out=eye(len(a))
    for _ in range(n): out=mul(out,a)
    return out

def product_matrices(names, table, n):
    out=eye(n)
    for name in names: out=mul(out,table[name])
    return out

O=[[1,0,0],[0,0,0],[0,0,0]]
F=[[0,1,0],[0,0,0],[0,0,0]]
D=[[0,0,0],[0,1,1],[0,0,1]]
P=[[1,2],[0,1]]

def control_target(x): return [[0,1,x],[0,0,0],[0,0,0]]
def target(x): return block(block(eye(2),P),control_target(x))

def parse_control(word):
    """Independent language oracle: O* F D*. Returns the suffix length."""
    if word.count('F') != 1: return None
    j=word.index('F')
    if any(c!='O' for c in word[:j]) or any(c!='D' for c in word[j+1:]): return None
    return len(word)-j-1

def build_acceptance(packet,x):
    """Fresh literal rewrite simulation; no predecessor executable is used."""
    text=packet['U']+'01010111'*(2*x)+packet['V']
    initial=text; trace=[]; tileword=[]
    copies={t['letter']:t['id'] for t in packet['tiles'] if t['kind']=='copy'}
    ruletiles={(t['h'],t['g']):t['id'] for t in packet['tiles'] if t['kind']=='rewrite'}
    while text!='[J1]':
        need(len(trace)<500,'bounded accepting fixture')
        hits=[]
        for r in packet['rules']:
            j=text.find(r['lhs'])
            if j>=0: hits.append((r,j))
        need(hits,'enabled rewrite')
        transitions=[h for h in hits if h[0]['kind']=='transition']
        if transitions:
            need(len(transitions)==len(hits)==1,'unique live machine rewrite')
        r,j=min(hits,key=lambda h:h[0]['id'])
        left=text[:j];right=text[j+len(r['lhs']):]
        after=left+r['rhs']+right
        tileblock=[copies[c] for c in left]+[ruletiles[(r['rhs'],r['lhs'])]]+[copies[c] for c in right]+[114]
        trace.append(dict(before=text,after=after,rule_id=r['id'],offset=j,tiles=tileblock))
        tileword.extend(tileblock);text=after
    tiles={t['id']:t for t in packet['tiles']}
    h=''.join(tiles[i]['h'] for i in tileword)
    g=''.join(tiles[i]['g'] for i in tileword)
    need(initial+'#'+h==g+'[J1]#','literal correspondence equation')
    names=['A'+str(i) for i in tileword]+['C']+['B'+str(i) for i in reversed(tileword)]
    return dict(x=x,input_word=initial,rewrites=trace,tileword=tileword,parent_word=names,
                word=names+['END']+['COUNT']*x)

def verify(root):
    raw={}
    for name,pin in PINS.items():
        raw[name]=(root/name).read_bytes();need(sha(raw[name])==pin,'pin '+name)
    old=loads(raw['matrix193_context_absorption.json']);packet=old['packet']
    need(old['status']=='PASS','parent receipt')
    source=packet['generators'];need(len(source)==193,'parent array size')
    b=old['block']['B'];B=[b[:2],b[2:]]
    records=[dict(name=g['name'],matrix=block(g['matrix'],O)) for g in source]
    records += [dict(name='END',matrix=block(eye(4),F)),
                dict(name='COUNT',matrix=block(block(B,eye(2)),D))]
    table={g['name']:g['matrix'] for g in records}
    need(len(table)==195,'all names distinct')
    need(len({tuple(flat(g['matrix'])) for g in records})==195,'all matrices distinct')
    for g in records:
        need(len(g['matrix'])==7 and all(len(r)==7 for r in g['matrix']),'full dimension')
        need(all(type(v) is int for v in flat(g['matrix'])),'integer matrix')
    controls={'O':O,'F':F,'D':D};control_counts=Counter();control_checks=0
    for n in range(10):
        for chars in product('OFD',repeat=n):
            word=''.join(chars);value=product_matrices(chars,controls,3);k=parse_control(word)
            need((value[0][1]==1)==(k is not None),'unrestricted grammar sample')
            if k is not None:
                need(value==control_target(k),'literal counted control');control_counts[k]+=1
            control_checks+=1
    # General block identity sampled on many old words, including ones which
    # fail the lower target. The unrestricted proof is in the companion note.
    names=list(table)[:193];oldtable={g['name']:g['matrix'] for g in source}
    block_checks=0
    for j in range(96):
        prefix=[names[(j*17+3*t)%193] for t in range(j%7)]
        m=product_matrices(prefix,oldtable,4)
        for k in (0,1,2,5):
            actual=product_matrices(prefix+['END']+['COUNT']*k,table,7)
            expected=block(mul(m,block(power(B,k),eye(2))),control_target(k))
            need(actual==expected,'entire lifted block identity');block_checks+=1
    # Repeat the pinned historical accepted product and reconstruct new positive
    # input examples by literal rules, then evaluate every full 7x7 product.
    saved=old['accepting_witness']['generator_word']+['END']
    need(product_matrices(saved,table,7)==target(0),'inherited full accepted product')
    accepted=[];mutation_checks=0
    for x in range(4):
        case=build_acceptance(packet,x)
        value=product_matrices(case['word'],table,7)
        need(value==target(x),'new full positive-input accepted product')
        for wrong in (x+1,x+2):
            need(value!=target(wrong),'wrong input target');mutation_checks+=1
        # Moving a counted letter before the bridge necessarily destroys its
        # control; changing its number also changes the literal target count.
        for changed in (case['parent_word']+['COUNT','END'],
                        case['parent_word']+['END','END'],
                        ['COUNT']+case['parent_word']+['END']):
            need(product_matrices(changed,table,7)!=target(x),'invalid phase mutation');mutation_checks+=1
        case['product']=value;case['target']=target(x);case['factor_count']=len(case['word'])
        accepted.append(case)
    # The target template uses only literal 0,1,2 and a direct copy of x.
    template=target('x')
    need(Counter(flat(template))['x']==1,'exactly one varying entry')
    for x in (-7,0,1,13,10**50):
        instantiated=[[x if v=='x' else v for v in row] for row in template]
        need(instantiated==target(x),'zero-gate input template')
    entries=[v for g in records for v in flat(g['matrix'])]
    return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,
        packet=dict(schema='counted-suffix-195-dimension-7',generators=records,
                    contexts=dict(U=packet['U'],V=packet['V']),B=B,
                    target_template=template,target_source=[],target_operations=0,
                    input_port='x',witness_alphabet_size=195,
                    domain='ordinary positive integer x; theorem also holds for x=0',
                    matrices_are_singular=True),
        statistics=dict(generators=195,dimension=7,entry_slots=len(entries),
                        nonzero_entries=sum(v!=0 for v in entries),
                        maximum_absolute_entry=max(map(abs,entries)),
                        maximum_magnitude_bits=max(abs(v).bit_length() for v in entries),
                        sum_magnitude_bits=sum(abs(v).bit_length() for v in entries)),
        checks=dict(control_words=control_checks,accepted_control_counts={str(k):v for k,v in sorted(control_counts.items())},
                    full_block_identities=block_checks,historical_accepting_factors=len(saved),
                    reconstructed_accepting_inputs=4,mutations_rejected=mutation_checks,
                    new_complete_entries=len(entries)),
        accepting_witnesses=accepted,
        projection=dict(positions_zero_based=[[0,0],[0,1],[2,2],[2,3],[3,2],[4,5],[4,6]],
                        targets=[1,0,1,2,0,1,'x'],
                        clarification='Position (4,5) has fixed target 1; (4,6) is x.'),
        exact_index_enforced_by_word=True,unbounded_product_certificate_paid=False,
        new_universal_Diophantine_bound=False,predecessor_code_executed=False,
        scope='Exact program-specific directed integer-matrix membership; counted suffix replaces the external Pell-index relation. Zero target gates are not a complete Diophantine operation count.')

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,required=True)
    group=p.add_mutually_exclusive_group(required=True)
    group.add_argument('--output',type=Path);group.add_argument('--expect',type=Path)
    a=p.parse_args();result=verify(a.root)
    if a.expect: need(exact(result,loads(a.expect.read_bytes())),'type-exact saved receipt')
    else: a.output.write_text(json.dumps(result,sort_keys=True,indent=2,allow_nan=False)+'\n')
    print('PASS: 195 complete 7x7 matrices; exact counted suffix and direct ordinary-input target')
if __name__=='__main__':main()
