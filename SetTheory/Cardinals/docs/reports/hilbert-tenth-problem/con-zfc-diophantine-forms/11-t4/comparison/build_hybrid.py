"""Own static arithmetic construction and verifier. Never imports vendor code.

Input JSON is treated only as data. Degree diagnostics use exact polynomial
arithmetic over F_p under a line substitution; the uniform degree proof is in
HYBRID_PROOF.md. No K215 coefficient enumeration is executed.
"""
from pathlib import Path
import json, collections, hashlib

HERE=Path(__file__).resolve().parent
BASE=HERE/'sources/06-blank67/data/fixed_blank_67.json'
old=json.loads(BASE.read_text())['packet']
new=[]
for row in old['source']:
    name=row[0]
    if name=='aux_coefficient_root':
        new += [
            ['f2_minus_one','-','L16',1],
            ['R16','*','A','f2_minus_one'],
            ['ordinary_ic2','*','i','c2'],
            ['ordinary_ic2_square','*','ordinary_ic2','ordinary_ic2'],
            ['ordinary_strong_sum','+','ordinary_ic2_square',1],
            ['norm_strong','-','ordinary_strong_sum','R16']]
    elif name in ('R16','scaled_f_square','norm_strong'):
        continue
    elif name=='polynomial':
        new.append(['polynomial','-','seven_units',1])
    else:
        new.append(row)

comparisons=[['norm_first',1],['norm_main',1],['norm_aux',1],
             ['norm_index',1],['norm_transport',1],['ordinary_ic2_square','R16']]
def prune(source,outputs):
    needed={x for x in outputs if isinstance(x,str)}
    out=[]
    for row in reversed(source):
        if row[0] in needed:
            out.append(row)
            needed.update(x for x in row[2:] if isinstance(x,str))
    return out[::-1]
sys=prune(new,[x for eq in comparisons for x in eq])
sos=sys.copy()
for j,(left,right) in enumerate(comparisons):
    sos.extend([[f'residual{j}','-',left,right],
                [f'square{j}','*',f'residual{j}',f'residual{j}']])
last='square0'
for j in range(1,len(comparisons)):
    out='sos' if j==len(comparisons)-1 else f'sum{j}'
    sos.append([out,'+',last,f'square{j}']); last=out

def ledger(source):
    return {'multiplication':sum(x[1]=='*' for x in source),
            'addition_subtraction':sum(x[1]!='*' for x in source),
            'total':len(source)}
def schema(source):
    seen=set(old['witnesses']+old['fixed_numerals'])
    for name,op,x,y in source:
        assert op in ('+','-','*') and name not in seen
        assert all(isinstance(t,int) or t in seen for t in (x,y))
        seen.add(name)
    return True

common={'witnesses':old['witnesses'],'witness_domain':'strictly positive integers',
        'fixed_numerals':old['fixed_numerals'],
        'coefficient_binding':{
            'selected_recipe':'../bridge/T4_CONSTANTS.json',
            'fallback_recipe':'sources/06-blank67/data/k215_constants.json',
            'selected_recipe_role':'Primary T4 coefficient tuple proved in ../bridge/BRIDGE_AUDIT.md; authenticated packet06 is a separate fallback, never mix ports.',
            'required_interface':'Four fixed ports Bm1=B-1, Kconstant=DC+B*DR, MC=native low mask, MF=native high mask+B-1; valid blank-input Start/impossible-End finite-window compiler, with full carry/mask/completeness theorem.',
            'arithmetic_is_parametric':True,
            'not_sufficient':'Mask congruences and positivity alone do not establish a compatible compiler.'},
        'source_pin':'3b201cdea32d2c816f5f3d20734051f25fd3ef14',
        'proof':'HYBRID_PROOF.md',
        'scope':'Ordinary mathematical reduction using pinned compiler/Pell lemmas; not an end-to-end kernel-checked proof. Coefficients not materialized.',
        'equivalence':'Existence of positive solutions is equivalent to K215 blank halting. Not a same-tuple equivalence with the normalized-strong source.'}
packets={
 'hybrid_product69.json':dict(common,name='Inputless ordinary-strong product',source=new,
                 output='polynomial',ledger=ledger(new),exact_degree=99,
                 factor_degrees=[22,18,28,7,2,22]),
 'hybrid_system61.json':dict(common,name='Inputless ordinary-strong six-equation system',source=sys,
                 comparisons=comparisons,ledger=ledger(sys),exact_maximum_degree=28,
                 residual_degrees=[22,18,28,7,2,22]),
 'hybrid_sos78.json':dict(common,name='Inputless ordinary-strong sum of squares',source=sos,
                 output='sos',ledger=ledger(sos),exact_degree=56)}

# Polynomial arithmetic, low to high, over a prime field.
P=1_000_000_007
def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a
def add(a,b,sgn=1):
    c=[0]*max(len(a),len(b))
    for j,x in enumerate(a):c[j]+=x
    for j,x in enumerate(b):c[j]+=sgn*x
    return trim([x%P for x in c])
def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for j,x in enumerate(a):
        for k,y in enumerate(b):c[j+k]=(c[j+k]+x*y)%P
    return trim(c)
def eval_source(source,seed=1):
    e={x:[3+seed*j,2+seed+3*j] for j,x in enumerate(old['witnesses'])}
    e.update(dict(zip(old['fixed_numerals'],([31],[97],[6],[35]))))
    for name,op,x,y in source:
        a=[x%P] if isinstance(x,int) else e[x]
        b=[y%P] if isinstance(y,int) else e[y]
        e[name]=mul(a,b) if op=='*' else add(a,b,-1 if op=='-' else 1)
    return e
checks={}
for file,packet in packets.items():
    source=packet['source']; schema(source)
    outs=[packet['output']] if 'output' in packet else [x for eq in comparisons for x in eq]
    assert len(prune(source,outs))==len(source)
    diagnostics=[]
    for seed in (1,2,3):
        values=eval_source(source,seed)
        if 'output' in packet:
            degree=len(values[packet['output']])-1
            assert degree==packet['exact_degree']
            diagnostics.append(degree)
        else:
            degrees=[]
            for x,y in comparisons:
                a=[x] if isinstance(x,int) else values[x]
                b=[y] if isinstance(y,int) else values[y]
                degrees.append(len(add(a,b,-1))-1)
            assert degrees==packet['residual_degrees']
            diagnostics.append(degrees)
    (HERE/file).write_text(json.dumps(packet,indent=2)+'\n')
    checks[file]={'ledger':packet['ledger'],'schema_pass':True,'all_gates_live':True,
                  'finite_field_line_degrees':diagnostics,
                  'sha256':hashlib.sha256((HERE/file).read_bytes()).hexdigest()}
assert ledger(new)=={'multiplication':39,'addition_subtraction':30,'total':69}
assert ledger(sys)=={'multiplication':34,'addition_subtraction':27,'total':61}
assert ledger(sos)=={'multiplication':40,'addition_subtraction':38,'total':78}

# Normalized -> ordinary positive witness map is i_o=Delta*i_n.
# Test exact off-zero relations without claiming reverse tuple equivalence.
def ev(source,e):
    e=dict(e)
    for name,op,x,y in source:
        a=x if isinstance(x,int) else e[x]; b=y if isinstance(y,int) else e[y]
        e[name]=a+b if op=='+' else a-b if op=='-' else a*b
    return e
for seed in range(1,20):
    ports=dict(zip(old['fixed_numerals'],[31,97,6,35]))
    ports.update({x:1+(seed*(j+1))%13 for j,x in enumerate(old['witnesses'])})
    a=ev(old['source'],ports)
    ports['i']*=a['A']
    b=ev(new,ports)
    assert b['norm_strong']==1+a['A']-a['norm_strong']
    assert b['norm_aux']-a['norm_aux']==(a['norm_strong']-a['A'])*a['aux_square_gap']
    for x in ['norm_first','norm_main','norm_index','norm_transport','r_lhs','aux_u_rhs']:
        assert a[x]==b[x]
checks['local_normalized_to_ordinary_identities']={'exact_integer_tests':19,'passed':True,
      'warning':'These are arithmetic source checks with toy constants, not accepting ZFC witnesses.'}
(HERE/'HYBRID_VALIDATION.json').write_text(json.dumps(checks,indent=2)+'\n')
print(json.dumps(checks,indent=2))
