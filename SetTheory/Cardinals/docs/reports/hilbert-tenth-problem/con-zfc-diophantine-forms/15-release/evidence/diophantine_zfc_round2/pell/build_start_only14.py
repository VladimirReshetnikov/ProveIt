import sys
if sys.flags.optimize:
    raise SystemExit("Do not run these evidence checks with -O or PYTHONOPTIMIZE.")
"""New audit code. Read prior circuits as inert JSON, never import source programs."""
import json, hashlib, random
from pathlib import Path
from collections import Counter
from fractions import Fraction
ROOT=Path(__file__).resolve().parents[2]
OUT=Path(__file__).resolve().parent
baseline=ROOT/'diophantine_zfc_review/start_only_polynomial67.json'
p=json.loads(baseline.read_text())
rows=p['source'][:48]
rows += [
['aux_coefficient_root','*','i','Ac2'],
['R16','*','aux_coefficient_root','aux_coefficient_root'],
['ng_ic2','*','i','c2'],
['ng_Dminus1','*','ng_ic2','aux_coefficient_root'],
['ng_D','+','ng_Dminus1',1],
['ng_RD','*','r_lhs','ng_D'],
['ng_b','+','R10a','ng_RD'],
['ng_u','*','R10a','auxiliary_quotient'],
['ng_u2','*','ng_u','ng_u'],
['ng_p','*','ng_D','ng_u2'],
['ng_b2','*','ng_b','ng_b'],
['ng_P4a','*','norm_pair','norm_index'],
['ng_P4','*','ng_P4a','norm_transport'],
['ng_sum','+','ng_p','ng_b2'],
['ng_gap','-','ng_sum','aux_y2'],
['ng_Qgap','*','R16','ng_gap'],
['ng_Aplus1','+','ng_Qgap','aux_y2'],
['ng_A','-','ng_Aplus1',1],
['ng_Qp','*','R16','ng_p'],
['ng_Qb2','*','R16','ng_b2'],
['ng_cross','*','ng_Qp','ng_Qb2'],
['ng_four','*',4,'ng_cross'],
['ng_A2','*','ng_A','ng_A'],
['ng_K','-','ng_A2','ng_four'],
['ng_unit','+','ng_K',1],
['ng_product','*','ng_P4','ng_unit'],
['polynomial','-','ng_product',1],
]
witnesses=[v for v in p['witnesses'] if v!='f']
factors=['norm_first','norm_main','norm_index','norm_transport','ng_unit']

def finish(rows,targets):
    seen=set(witnesses+p['fixed_numerals']); count=Counter(); by={}
    for dst,op,a,b in rows:
        assert dst not in seen, dst
        for v in (a,b):assert isinstance(v,int) or v in seen,(dst,v)
        assert op in '+-*'; seen.add(dst); count[op]+=1; by[dst]=(a,b)
    live=set(); stack=list(targets)
    while stack:
        v=stack.pop()
        if isinstance(v,int) or v in live:continue
        live.add(v)
        if v in by:stack.extend(by[v])
    assert all(x[0] in live for x in rows)
    assert set(witnesses+p['fixed_numerals'])<=live
    return {'total':len(rows),'M':count['*'],'A':count['+']+count['-'],'all_rows_and_ports_live':True}

poly={k:p[k] for k in ['witness_domain','fixed_numerals','compiler_contract','claim_scope']}
poly.update(description='Start-only with the auxiliary f root eliminated by an integer quadratic norm. Signed-root soundness is proved in START_ONLY14_PROOF.md.',witnesses=witnesses,source=rows,output='polynomial',factor_names=factors,factor_exact_degrees=[22,18,7,2,244],exact_total_degree=293)
poly['ledger']=finish(rows,['polynomial'])
remove={'norm_pair','ng_P4a','ng_P4','ng_unit','ng_product','polynomial'}
sysrows=[r for r in rows if r[0] not in remove]
comparisons=[['norm_first',1],['norm_main',1],['norm_index',1],['norm_transport',1],['ng_K',0]]
sys={k:poly[k] for k in ['description','witness_domain','witnesses','fixed_numerals','compiler_contract','claim_scope']}
sys.update(source=sysrows,comparisons=comparisons,residual_exact_degrees=[22,18,7,2,244],ledger=finish(sysrows,[a for a,b in comparisons]))
for name,obj in [('start_only14_polynomial75.json',poly),('start_only14_system69.json',sys)]:
    (OUT/name).write_text(json.dumps(obj,indent=2)+'\n')

def evaluate(rows,inputs,mod=None):
    e=dict(inputs)
    for d,op,a,b in rows:
        a=e[a] if isinstance(a,str) else a;b=e[b] if isinstance(b,str) else b
        v=a+b if op=='+' else a-b if op=='-' else a*b
        e[d]=v%mod if mod else v
    return e

# Exact off-zero local norm algebra, with arbitrary signs, and agreement of
# inherited common fields. None of these trials pretends to be a full zero.
rng=random.Random(22026)
checks=0
for _ in range(200):
    vals={v:rng.randrange(-6,8) for v in witnesses}
    vals.update({v:rng.randrange(2,19) for v in p['fixed_numerals']})
    ev=evaluate(rows,vals)
    D=ev['ng_D']; Q=ev['R16']; b=ev['ng_b']; u=ev['ng_u']; y=vals['y_aux']
    A=Q*(D*u*u+b*b)-(Q-1)*y*y-1;B=2*Q*u*b
    assert ev['ng_A']==A
    assert ev['ng_K']==A*A-D*B*B
    for f in [-3,2]:
        na=Q*(u*f-b)**2-(Q-1)*y*y
        assert na-1==A-B*f+Q*u*u*(f*f-D)
    base=evaluate(p['source'],dict(vals,f=2))
    for r in p['source'][:48]:assert base[r[0]]==ev[r[0]]
    checks+=1

# Dense modular univariate expansion with all positive witnesses replaced
# by independently chosen affine functions. Degrees are corroborated, not
# inferred solely from this finite check; see the homogeneous proof.
def add(a,b,sgn,mod):
    c=[0]*max(len(a),len(b))
    for i,x in enumerate(a):c[i]=(c[i]+x)%mod
    for i,x in enumerate(b):c[i]=(c[i]+sgn*x)%mod
    while len(c)>1 and c[-1]==0:c.pop()
    return c

def mul(a,b,mod):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%mod
    while len(c)>1 and c[-1]==0:c.pop()
    return c

dense=[]
for mod in [1000000007,1000000009,998244353]:
    ev={v:[rng.randrange(1,20),rng.randrange(1,20)] for v in witnesses}
    # Fixtures are arithmetic tests, not claims to instantiate a compiler.
    ev.update({v:[rng.randrange(2,100)] for v in p['fixed_numerals']})
    for d,op,a,b in rows:
        a=ev[a] if isinstance(a,str) else [a%mod];b=ev[b] if isinstance(b,str) else [b%mod]
        ev[d]=mul(a,b,mod) if op=='*' else add(a,b,1 if op=='+' else -1,mod)
    deg=[len(ev[f])-1 for f in factors]
    assert deg==[22,18,7,2,244],deg
    assert len(ev['polynomial'])-1==293
    dense.append({'modulus':mod,'factor_degrees':deg,'degree':293,'leading_coefficient':ev['polynomial'][-1]})

receipt={'baseline_sha256':hashlib.sha256(baseline.read_bytes()).hexdigest(),'polynomial_ledger':poly['ledger'],'system_ledger':sys['ledger'],'exact_signed_local_identity_tests':checks,'dense_modular_checks':dense,'scope':'Newly authored checker. No received program imported or executed. Counts/liveness and local algebra/dense degrees are checked; the quantified theorem is in the accompanying mathematical proof.'}
(OUT/'start_only14_arithmetic_audit.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
