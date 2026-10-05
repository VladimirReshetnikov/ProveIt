"""Independent inert array audit plus newly written finite polynomial algebra."""
from pathlib import Path
import hashlib,json
ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
TMP=Path('/tmp')
def need(c,m):
    if not c:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
pins={
 'complete84_nonlinear_norm_next.md':'270a6ed4bc26fa598763fe518950d48cfa923240ecb7323e4e41d9b8f9c8e6ca',
 'complete84_nonlinear_norm_next_checks.py':'bb46e086ac686cb8862499bd0ad3702c9b190161e2710d78bfb8f4738ac4d889',
 'complete84_nonlinear_norm_next_checks.json':'39d2e0ad0ee227acac368680b9f90667475aa03952d9c6ac93ddf0432963cb2c',
}
for name,pin in pins.items():need(sha((TMP/name).read_bytes())==pin,name)
j=json.loads((TMP/'complete84_nonlinear_norm_next_checks.json').read_text())
for name,pin in j['pins'].items():need(sha((ROOT/name).read_bytes())==pin,name)
parent=json.loads((ROOT/'complete84_scaled_strong_output.json').read_text())['packet']
need(j['parent_packet']==parent,'parent packet data')
old={x[0]:x for x in parent['source']}
need(j['same_free_ports']==parent['free'] and len(parent['free'])==25,'ports')
need(j['same_witnesses']==parent['witnesses'] and len(parent['witnesses'])==18,'witnesses')
need(j['same_input']==parent['ordinary_input'],'input')
for row in j['literal_guards']:need(row==old[row[0]],'guard')
ledger={}
for name,key,expected in [('numerator','new_source',(98,56,42)),('factored','factored_source',(87,49,38))]:
    rows=j[key];names={x[0] for x in rows};seen=set(parent['free'])
    need(len(names)==len(rows),'unique names')
    for out,op,l,r in rows:
        need(op in ['+','-','*'] and out not in seen,'operator/topology')
        need(all(isinstance(x,int) or x in seen for x in [l,r]),'available operands')
        seen.add(out)
    deps={x[0]:{v for v in x[2:] if isinstance(v,str)} for x in rows}
    live={'polynomial'}
    while True:
        updated=live|set().union(*(deps.get(v,set()) for v in live))
        if updated==live:break
        live=updated
    need(live==names|set(parent['free']),'all rows and supplied ports live')
    m=sum(x[1]=='*' for x in rows);a=len(rows)-m
    need((len(rows),m,a)==expected,'ledger')
    ledger[name]={'rows':len(rows),'M':m,'A':a,'live_ports':len(live-names)}
new={x[0]:x for x in j['new_source']}
retained=[x for x in parent['source'] if x[0] not in ['L15','norm_main','polynomial']]
need(len(retained)==81 and all(new[x[0]]==x for x in retained),'81 exact retained rows')
need(set(new)=={x[0] for x in retained}|{x[0] for x in j['replacement_rows']}|{'polynomial'},'row set')
for row in j['replacement_rows']:need(new[row[0]]==row,'replacement row')
need(new['polynomial']==['polynomial','-','seven_units','cayley_target'],'numerator final')
fact=j['factored_source']
need(fact[:83]==parent['source'][:83],'factored old prefix')
need(fact[83:]==[['cayley_old_output','-','seven_units','A'],['cayley_den','-','kappa2','A'],['cayley_den2','*','cayley_den','cayley_den'],['polynomial','*','cayley_den2','cayley_old_output']],'factored suffix')

# Direct expressions below are independently authored from the mathematical
# formulas, not an interpreter for any saved source array or helper.
def plus(*ps):
    out={}
    for p in ps:
        for exp,c in p.items():out[exp]=out.get(exp,0)+c
    return {e:c for e,c in out.items() if c}
def scale(p,c):return {e:c*v for e,v in p.items() if c*v}
def times(p,q):
    terms=[]
    for e,c in p.items():
        for f,d in q.items():terms.append({tuple(x+y for x,y in zip(e,f)):c*d})
    return plus(*terms)
def square(p):return times(p,p)
variables=[]
for i in range(5):
    e=[0]*5;e[i]=1;variables.append({tuple(e):1})
D,c,v,delta,P=variables
den=plus(square(v),scale(delta,-1));p=plus(square(v),delta)
dn=plus(times(p,D),scale(times(times(delta,v),c),2))
cn=plus(times(p,c),scale(times(v,D),2))
norm=plus(square(D),scale(times(delta,square(c)),-1))
numerator=plus(square(dn),scale(times(delta,square(cn)),-1))
need(numerator==times(square(den),norm),'direct norm identity')
whole=plus(times(P,numerator),scale(times(delta,square(den)),-1))
need(whole==times(square(den),plus(times(P,norm),scale(delta,-1))),'direct whole identity')
for key,p in [('formal_norm_numerator',numerator),('formal_denominator_square',square(den)),('formal_whole_output',whole)]:
    saved={tuple(e):c for e,c in j[key]}
    need(len(saved)==len(j[key]) and saved==p,'saved formal coefficients')
out={'schema':'nonlinear-norm-root-audit-v1','author_pins':pins,'parent_pins':j['pins'],'ledger':ledger,'retained_numerator_rows':81,'formal_coefficient_counts':{'norm':len(numerator),'denominator_square':len(square(den)),'whole':len(whole)},'scope':'Inert source graph and byte audit; direct newly authored polynomial identities. No saved source or helper execution; proof classification reviewed separately.'}
(TMP/'review_nonlinear_norm_root.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print('PASS',ledger,'81 retained rows, direct norm and whole polynomial coefficient identities')
