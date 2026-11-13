#!/usr/bin/env python3
"""Independent bounded checks for the symbolic 72-zero obstruction."""
import hashlib,json,operator,random,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')
def need(b,s):
    if not b:raise RuntimeError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
base=Path(__file__).resolve().parents[2];d=base/'research'/'p64-qcube72-full-zero-mod-q-obstruction';p72=base/'research'/'p64-qcube72-free-main-candidate'/'graph.json';prior=base/'research'/'p64-free-fsquare75-symbolic-full-zero'
pins={d/'README.md':'99b0da7530b0f7bbbaed76fd8c452b9791280babba8d8f2f82573552b842a860',
 d/'check.py':'a6e1d4ad04e290865a603c4de1a2ff2a3819f44b27d530fc1bdf8ff005ead435',
 d/'result.json':'cfad29e461980b9e6d3b8fa68d9e5e14855c305c91a707559882bfa912ee0cbb',
 p72:'875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806',
 prior/'check.py':'fe7159ca3efbd0fa922ea46a66157d192f63185691c4599f31fc40b955f2cbf4',
 prior/'result.json':'f34ccd14e96ee665ddac13c7d8c64c65e547064fcb6fe390a4df61713ba9284f'}
for p,h in pins.items():need(sha(p)==h,'pin drift '+str(p))
# Recompute the independently retained bounded Pell interval input; no large witnesses.
r=subprocess.run([sys.executable,'-I','-S','-B',str(prior/'check.py')],capture_output=True,check=True,timeout=20)
need(r.stdout==(prior/'result.json').read_bytes() and not r.stderr,'bounded witness premise')
p=json.loads(r.stdout);need(p['proved_ratio_bounds']=='27 < c/k < 28' and p['first_index']==2446738 and p['main_index']==4020619 and
 (p['A_mod_U'],p['k_mod_U'],p['m_mod_U'],p['c_mod_U'])==(486,428,184,115),'wrong residue premise')
need((486+428-184-115-1)%729==614 and 614%3==2,'carrier congruence')
# Structural proof of the changed-port shift: MC has one direct use, and R
# flows only to cT-R; T has one use, while c does not depend on MC or T.
graph=json.loads(p72.read_bytes());rows=graph['source'];table={r[0]:r for r in rows}
def uses(name):return [r[0] for r in rows if name in r[2:]]
need(uses('MC')==['mask_factor'] and uses('R')==['quotient_gap'] and uses('T')==['cT'] and uses('h')==['H_main_gap'],'graph coordinate uses')
need(table['mask_factor']==['mask_factor','+','MC','qMF'] and table['mask']==['mask','*','mask_factor','J'] and
     table['R']==['R','+','R_product','mask'] and table['cT']==['cT','*','c','T'] and
     table['quotient_gap']==['quotient_gap','-','cT','R'],'shift gate formulas')
def deps(name):
    if name not in table:return {name} if isinstance(name,str) else set()
    return deps(table[name][2])|deps(table[name][3])
need(not ({'MC','T','h'} & deps('c')),'c depends on shifted coordinate')
# Additional integer controls exercise the whole 72 DAG, independently of the
# author's random seed; the algebraic proof follows from the use checks.
ops={'+':operator.add,'-':operator.sub,'*':operator.mul}
def evaluate(v):
    out=v.copy()
    for n,o,x,y in rows:out[n]=ops[o](out[x] if isinstance(x,str) else x,out[y] if isinstance(y,str) else y)
    return out
rng=random.Random(191729)
for _ in range(160):
    v={n:rng.randrange(1,6) for n in graph['witnesses']};v.update({n:rng.randrange(0,6) for n in graph['fixed_numerals']});v['J']=1
    a=evaluate(v);v2=v.copy();v2['MC']+=a['c'];v2['T']+=1;b=evaluate(v2)
    need(b['R']==a['R']+a['c'] and b['V']==a['V'] and
         all(a[n]==b[n] for n in ('A0','M','W','Na','Lt','polynomial')),'DAG shift')
out={'status':'PASS_INDEPENDENT_BOUNDED_AND_GRAPH_REVIEW','script_sha256':sha(__file__),
     'author_readme_sha256':pins[d/'README.md'],'author_check_sha256':pins[d/'check.py'],
     'graph_sha256':pins[p72],'premise_checker_sha256':pins[prior/'check.py'],
     'c_mod_729':115,'changed_gap_mod_729':614,'changed_gap_mod_3':2,'finite_DAG_cases':160,
     'scope':'Symbolic full zero at specified changed natural ports; no Lean, compact44, original no-zero or existence-equivalence claim.'}
print(json.dumps(out,indent=2,sort_keys=True))
