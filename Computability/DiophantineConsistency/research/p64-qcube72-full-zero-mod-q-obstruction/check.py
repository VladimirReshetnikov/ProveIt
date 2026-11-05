#!/usr/bin/env python3
"""Finite premises and graph checks for a symbolic 72-gate full zero."""
import hashlib,json,operator,random,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2];p76=root/'research/p64-qcube76-independent-y-candidate/graph.json';p72=root/'research/p64-qcube72-free-main-candidate/graph.json';prior=root/'reviews/p64-free-fsquare75-symbolic-full-zero-independent/check.py'
pins={p76:'196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c',p72:'875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806',prior:'bb32ea64f45d70daf8b93b4aa6eab017366512016487d565813ac1358e64a59f'}
for p,h in pins.items():
    if hashlib.sha256(p.read_bytes()).hexdigest()!=h:raise RuntimeError('pin mismatch '+str(p))
r=subprocess.run([sys.executable,'-I','-S','-B',str(prior)],capture_output=True,text=True,timeout=20,check=True)
a=json.loads(r.stdout)
if a['status']!='PASS_BOUNDED_CHECKS' or a['strict_ratio']!='27 < c/k < 28' or (a['A_mod_U'],a['k_mod_U'])!=(486,428):raise RuntimeError('premise mismatch')
# Independent main Pell coordinate mod 729.
def mul(A,B,n):return tuple(sum(A[2*i+k]*B[2*k+j] for k in range(2))%n for i in range(2) for j in range(2))
def powmat(A,k,n):
    r=(1,0,0,1)
    while k:
        if k&1:r=mul(r,A,n)
        k//=2
        if k:A=mul(A,A,n)
    return r
_,_,c,_=powmat((191,36480,1,191),4020619,729)
h,k,m=486,428,4020619%729
if c!=115 or m!=184 or (h+k-m-1)%729!=0 or (h+k-m-c-1)%729!=614:raise RuntimeError('carrier residue mismatch')
g76=json.loads(p76.read_bytes());g72=json.loads(p72.read_bytes());rows76=g76['source'];rows72=g72['source'];ops={'+':operator.add,'-':operator.sub,'*':operator.mul}
def ev(rows,vals):
    d=vals.copy()
    for n,o,x,y in rows:d[n]=ops[o](d[x] if isinstance(x,str) else x,d[y] if isinstance(y,str) else y)
    return d
rng=random.Random(720072)
for _ in range(100):
    v={n:rng.randrange(1,5) for n in g76['witnesses']};v.update({n:rng.randrange(0,5) for n in g76['fixed_numerals']});v['J']=1
    old=ev(rows76,v);u=v.copy();u.pop('gamma');u['h']=old['main_gap'];u['MC']+=old['c'];u['T']+=1
    free=ev(rows72,u)
    if free['R']!=old['R']+old['c'] or free['V']!=old['V'] or any(free[n]!=old[n] for n in ('A0','M','W','Na','Lt','polynomial')):raise RuntimeError('shifted-port graph identity')
print(json.dumps({'status':'PASS_BOUNDED_PREMISES','ratio':a['strict_ratio'],'A_mod_729':h,'k_mod_729':k,'m_mod_729':m,'c_mod_729':c,'new_carrier_mod_729':614,'shifted_port_graph_cases':100,'scope':'Independent bounded numerical premises and finite graph controls; full symbolic zero is established by the accompanying mathematical argument, not evaluated or Lean-checked.'},sort_keys=True))
