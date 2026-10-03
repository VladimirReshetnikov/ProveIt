#!/usr/bin/env python3
"""Independent JSON-only polynomial and certificate reconstruction; no packet imports."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PIN = '506144b361b2bea634d468a94921644d91868dc089a257fe289a0bf51b74cec9'


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def load(path):
    def pairs(items):
        out = {}
        for k,v in items:
            need(k not in out,'duplicate JSON key');out[k] = v
        return out
    return json.loads(path.read_bytes(),object_pairs_hook=pairs)


def same(a,b):
    need(type(a) is type(b),'exact JSON type mismatch')
    if type(b) is dict:
        need(set(a) == set(b),'exact JSON keys mismatch')
        for k in b:same(a[k],b[k])
    elif type(b) is list:
        need(len(a) == len(b),'exact JSON length mismatch')
        for x,y in zip(a,b):same(x,y)
    else:need(a == b,'exact JSON value mismatch')


# Ordinary commutative sparse-polynomial algebra, independent of either compiler.
def plus(a,b):
    out = dict(a)
    for mon,c in b.items():
        out[mon] = out.get(mon,0)+c
        if out[mon] == 0:del out[mon]
    return out


def scale(a,c):
    return {m:v*c for m,v in a.items() if v*c}


def times(a,b):
    out = {}
    for u,c in a.items():
        for v,d in b.items():out = plus(out,{tuple(sorted(u+v)):c*d})
    return out


def number(c):
    return {():c} if c else {}


def var(name):
    return {(name,):1}


def mm(a,b):
    out = []
    for row in a:
        line = []
        for j in range(len(b[0])):
            value = {}
            for k in range(len(b)):value = plus(value,times(row[k],b[k][j]))
            line.append(value)
        out.append(line)
    return out


def numeric_mm(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]


def inv(a):
    need(a[0][0]*a[1][1]-a[0][1]*a[1][0] == 1,'SL2 determinant')
    return [[a[1][1],-a[0][1]],[-a[1][0],a[0][0]]]


def pair(z,s,i,j,sign):
    return z+'_'+str(s)+'_'+str(i)+str(j)+'_'+sign


def state(z,s):
    if s == 0:return [[number(int(i==j)) for j in range(2)] for i in range(2)]
    return [[plus(var(pair(z,s,i,j,'p')),scale(var(pair(z,s,i,j,'n')),-1)) for j in range(2)] for i in range(2)]


def terminal(mode):
    if mode == 'signed':return [[var('T_'+str(i)+str(j)) for j in range(2)] for i in range(2)]
    return [[plus(var('T_'+str(i)+str(j)+'_p'),scale(var('T_'+str(i)+str(j)+'_n'),-1)) for j in range(2)] for i in range(2)]


def expected_polys(u,v,c,r,mode):
    out = []
    def append_matrix(prefix,a,b):
        for i in range(2):
            for j in range(2):out.append((prefix+str(i)+str(j),plus(a[i][j],scale(b[i][j],-1))))
    for s in range(1,r+1):
        selectors = [var('e_'+str(s)+'_'+str(k)) for k in range(1,115)]
        q = number(-1)
        for e in selectors:q = plus(q,e)
        out.append(('select_'+str(s),q))
        for z,data in [('H',u),('G',v)]:
            selected = [[{} for _ in range(2)] for _ in range(2)]
            for e,m in zip(selectors,data):
                for i in range(2):
                    for j in range(2):selected[i][j] = plus(selected[i][j],scale(e,m[i][j]))
            append_matrix('update_'+z+'_'+str(s)+'_',state(z,s),mm(state(z,s-1),selected))
        for z in ('H','G'):
            for i in range(2):
                for j in range(2):out.append(('canonical_'+z+'_'+str(s)+'_'+str(i)+str(j),times(var(pair(z,s,i,j,'p')),var(pair(z,s,i,j,'n')))))
    append_matrix('terminal_',mm(state('H',r),[[number(x) for x in row] for row in c]),mm(terminal(mode),state('G',r)))
    if mode == 'natural':
        for i in range(2):
            for j in range(2):out.append(('canonical_T_'+str(i)+str(j),times(var('T_'+str(i)+str(j)+'_p'),var('T_'+str(i)+str(j)+'_n'))))
    return [{'name':name,'polynomial':[{'coefficient':q[m],'variables':list(m)} for m in sorted(q)]} for name,q in out]


def assignment(u,v,c,seq,mode='signed'):
    values = {};h = [[1,0],[0,1]];g = [[1,0],[0,1]]
    for s,index in enumerate(seq,1):
        need(type(index) is int and 1<=index<=114,'valid tile ID')
        for k in range(1,115):values['e_'+str(s)+'_'+str(k)] = int(k==index)
        h = numeric_mm(h,u[index-1]);g = numeric_mm(g,v[index-1])
        for z,m in [('H',h),('G',g)]:
            for i in range(2):
                for j in range(2):
                    values[pair(z,s,i,j,'p')] = max(m[i][j],0)
                    values[pair(z,s,i,j,'n')] = max(-m[i][j],0)
    t = numeric_mm(numeric_mm(h,c),inv(g))
    for i in range(2):
        for j in range(2):
            name = 'T_'+str(i)+str(j)
            if mode == 'signed':values[name] = t[i][j]
            else:values[name+'_p'],values[name+'_n'] = max(t[i][j],0),max(-t[i][j],0)
    return values,t


def main():
    raw = (ROOT/'paired/data/semigroup.json').read_bytes()
    need(hashlib.sha256(raw).hexdigest() == PIN,'common numerical source pin')
    source = load(ROOT/'paired/data/semigroup.json');generators = source['generators']
    u = [[row[:2] for row in item['matrix'][:2]] for item in generators[:114]]
    v = [inv([row[:2] for row in item['matrix'][:2]]) for item in generators[114:228]]
    c = [row[:2] for row in generators[-1]['matrix'][:2]]
    comparisons = monomials = zeros = 0
    for r in range(3):
        for mode in ('signed','natural'):
            obj = load(ROOT/'paired/examples'/('r'+str(r)+'-'+mode+'-sos.json'))
            need(obj['source_sha256'] == PIN and type(obj['r']) is int and obj['r'] == r and obj['mode'] == mode,'export metadata')
            expected = expected_polys(u,v,c,r,mode)
            same(obj['residuals'],expected)
            aux = ['e_'+str(s)+'_'+str(k) for s in range(1,r+1) for k in range(1,115)]
            aux += [pair(z,s,i,j,sign) for s in range(1,r+1) for z in ('H','G') for i in range(2) for j in range(2) for sign in ('p','n')]
            ext = ['T_'+str(i)+str(j)+suffix for i in range(2) for j in range(2) for suffix in (('',) if mode=='signed' else ('_p','_n'))]
            need(type(obj['natural_auxiliary_variables']) is list and len(obj['natural_auxiliary_variables']) == len(set(aux)) and set(obj['natural_auxiliary_variables']) == set(aux),'auxiliary variable domain')
            same(obj['external_variables'],ext)
            terms = [term for row in expected for term in row['polynomial']]
            hist = [sum(len(t['variables']) == degree for t in terms) for degree in range(3)]
            l = obj['ledger']
            for key,value in {'natural_auxiliary_count':130*r,'external_input_count':len(ext),'residual_count':17*r+(4 if mode=='signed' else 8),'literal_residual_monomials_by_degree':hist,'literal_residual_monomials_total':len(terms),'generic_sparse_evaluator_multiplications':sum((degree+1)*hist[degree] for degree in range(3))+len(expected),'generic_sparse_evaluator_additions':len(terms)+len(expected),'sos_total_degree':2 if r==0 and mode=='signed' else 4}.items():same(l[key],value)
            for seq in ([[]] if r==0 else ([[1],[57],[114]] if r==1 else [[20,109],[110,20],[1,114]])):
                vals,t = assignment(u,v,c,seq,mode)
                need(all(type(x) is int for x in vals.values()),'integer assignment')
                for residual in expected:
                    result = 0
                    for term in residual['polynomial']:
                        x = term['coefficient']
                        for name in term['variables']:x *= vals[name]
                        result += x
                    need(result == 0,'independently constructed root')
                zeros += 1
            comparisons += 1;monomials += len(terms)
    cert = load(ROOT/'paired/examples/accepting-94-certificate.json')
    witness = load(ROOT/'paired/data/accepting-witness.json')
    same(cert['sequence'],witness['inner_tile_sequence'])
    values,target = assignment(u,v,c,cert['sequence'])
    same(cert['values'],values);same(cert['target'],target)
    same(cert['r'],94);same(cert['mode'],'signed')
    need(len(values) == 12224,'full witness assignment count')
    same(target,[row[:2] for row in witness['input']['target'][:2]])
    collision = load(ROOT/'paired/examples/target-collision.json')
    a,ta = assignment(u,v,c,collision['distinct_sequences'][0]);b,tb = assignment(u,v,c,collision['distinct_sequences'][1])
    same(ta,tb);same(ta,collision['target']);need(a != b,'distinct sequence roots')
    print(json.dumps({'status':'PASS','source_sha256':PIN,'method':'Independent JSON-only sparse matrix-polynomial reconstruction; no compiler imports or execution','literal_exports_reconstructed':comparisons,'literal_monomials_reconstructed':monomials,'independent_small_roots_evaluated':zeros,'accepting_r':94,'accepting_auxiliaries_reconstructed':12220,'accepting_external_values_reconstructed':4,'collision_distinct_roots_reconstructed':2},indent=2,sort_keys=True))

if __name__ == '__main__':main()
