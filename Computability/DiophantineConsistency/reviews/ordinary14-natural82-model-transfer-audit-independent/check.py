#!/usr/bin/env python3
"""Check selected interfaces and exact external DAG cuts, without Lean."""
import hashlib, json, re, sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):
    raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2]
A=D/'research/ordinary14-natural82-model-transfer-audit'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'check.py') == '35fbe397517a0d4aea4d8a941915d12cbe85f477420a0bd6afdffe609ad5abff'
assert sha(A/'result.json') == 'a8977322658d2c7df5ca4ddccd45f0c146b09a7736fd2b14122ff2f69e69fda4'
receipt=json.loads((A/'result.json').read_text())
for path, expected in receipt['files'].items(): assert sha(D/path) == expected, path

def source(path): return (D/path).read_text()
def signature(s,name):
    m=re.search(r'\b(?:def|theorem)\s+'+re.escape(name)+r'\b(.*?)(?=\s*:=)',s,re.S)
    assert m,name
    return re.sub(r'\s+',' ',m.group(1)).strip()
def decl_block(s,name):
    m=re.search(r'\b(?:def|theorem)\s+'+re.escape(name)+r'\b(.*?)(?=\n\s*\n)',s,re.S)
    assert m,name
    return re.sub(r'\s+',' ',m.group(1)).strip()
unit=source('research/ordinary14-root74-slim-overlay/source/OwnZeroProduct74.lean.src')
u=signature(unit,'factor_units_of_zero')
for token in ['(hbeta : (p 0 : DiffRing V)=ι beta)', '(hb : 0<beta)',
              '(hJ : 0<v 0)', '(hw : 0<v 6)', '(hs : 0<v 7)',
              '(hmain :', '(haux :', '(hstrong :',
              'v 8*v 8=(m beta v*k v)*(m beta v*k v+k v)+1',
              '(P74PositiveGuard.graph p).aux', '(P74PositiveGuard.graph p).strong']:
    assert token in u,token
res=signature(source('research/ordinary14-root74-slim-overlay/source/FactorResidues74.lean.src'),'restricted_residues')
assert '(p : Fin 4 → ℤ) (v : Fin 14 → V)' in res
assert all('(P74PositiveGuard.graph p).'+k in res for k in ['main','aux','strong'])
assert '0<v' not in res
mod=source('research/ordinary14-natural-forced82-ring-bridge-draft/Natural82Model.lean')
pred=decl_block(mod,'HasThreePredecessors')
assert all(t in pred for t in ['v 3 = f + 1','v 8 = r + 1','v 11 = y + 1'])
cond=signature(mod,'exists_zero_iff_of_predecessors')
assert '(predecessors : ∀ v, InternalZero' in cond and 'HasThreePredecessors v' in cond
nz=source('Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean')
nzdef=decl_block(nz,'SameNoZero')
assert '∀ (V : Type)' in nzdef and '𝗜𝚺₁' in nzdef and '∀ v : Fin n → V' in nzdef
assert 'SameNoZero e f' in signature(nz,'bridge') and 'PolynomialBridge f' in signature(nz,'bridge')
assert '(hd : Discrete R)' in signature(source('Lean/DiophantineConsistency/DiscreteOrderedRingFacts.lean'),'eq_one_or_neg_one_of_mul_eq_one')
assert '(hd : ∀ a : V, 0 < a → 1 ≤ a)' in signature(source('Lean/DiophantineConsistency/ModelDifferenceRing.lean'),'one_le_of_pos')

# Exact external graph comparison with the partially shifted 74 valuation.
p74=D/'research/ordinary14-positive-guard74/candidate.json'
p82=D/'research/ordinary14-root74-natural-forced82/candidate.json'
assert sha(p74)=='e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093'
assert sha(p82)=='1532ea5ec5f8dee349353044b9618a2e8a633f618e6f7ef5f1d19630b53b6c8a'
a,b=json.loads(p74.read_text()),json.loads(p82.read_text())
old={n:(op,x,y) for n,op,x,y in a['source']}
new={n:(op,x,y) for n,op,x,y in b['source']}
assert len(old)==74 and len(new)==82
assert a['witnesses']==['J','F','alpha','f','i','T','w','s','r','eta','zeta','y','gamma','h']
assert b['witnesses']==['n_'+s for s in a['witnesses']]
assert a['fixed_numerals']==b['fixed_numerals']
for graph in (a,b):
    known=set(graph['witnesses']+graph['fixed_numerals'])
    for name,op,x,y in graph['source']:
        assert name not in known and op in ('+','-','*')
        assert all(type(z) is int or z in known for z in (x,y))
        known.add(name)
    assert graph['output']=='out' and graph['output'] in known
for x in ['J','alpha','i','T','w','s','eta','gamma']:
    assert new[x]==('+','n_'+x,1)
exceptions={'qF','k','g52','r0','guard_base','bt_quotient','guard'}
rename={'f':'n_f','r':'n_r','y':'n_y'}
for n in set(old)-exceptions:
    op,x,y=old[n]
    assert new[n]==(op,rename.get(x,x),rename.get(y,y)), n
assert old['qF']==('-', 'q','F') and new['qF']==('-', 'qm','n_F')
assert old['k']==('+','eta','zeta') and new['kbase']==('+','eta','n_zeta') and new['k']==('+','kbase',1)
assert old['g52']==('-','k','R') and old['r0']==('-','g52',1) and new['r0']==('-','kbase','R')
assert old['guard_base']==('+','g27','qF') and new['guard_base']==('-','g27','n_F')
assert old['bt_quotient']==('*','qm','h') and new['bt_quotient']==('*','qm','n_h')
assert old['guard']==('-', 'guard_base','bt_quotient') and new['guard']==old['guard']
assert old['q']==('+',1,'qm')
# Sparse formal polynomials justify the qF, k/r0 and combined guard cuts.
def var(x): return {(x,):1}
def const(x): return {():x} if x else {}
def add(a,b):
    out=dict(a)
    for k,v in b.items(): out[k]=out.get(k,0)+v
    return {k:v for k,v in out.items() if v}
def neg(a): return {k:-v for k,v in a.items()}
def sub(a,b): return add(a,neg(b))
def mul(a,b):
    out={}
    for x,u in a.items():
        for y,v in b.items():
            k=tuple(sorted(x+y));out[k]=out.get(k,0)+u*v
    return {k:v for k,v in out.items() if v}
one=const(1)
q,f,eta,z,r,g,h=map(var,['q','f','eta','z','r','g','h'])
qfold=sub(add(one,q),add(f,one));qfnew=sub(q,f)
assert qfold==qfnew
assert sub(sub(add(eta,add(z,one)),r),one)==sub(add(eta,z),r)
assert sub(add(g,qfold),mul(q,add(h,one)))==sub(sub(g,f),mul(q,h))
print(json.dumps({'scope':'source-signature observations and exact external 82-to-74 graph cuts; no Lean elaboration, model theorem or iPRA proof', 'audit_files_pinned':len(receipt['files']), 'old_operations':len(old),'new_operations':len(new),'shared_gate_rows_checked':len(set(old)-exceptions),'algebraic_cuts_checked':3},sort_keys=True,indent=2))
