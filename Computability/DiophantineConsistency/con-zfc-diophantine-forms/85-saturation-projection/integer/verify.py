#!/usr/bin/env python3
"""Exact independent verification of the transport-coordinate projections.

Uses the retained independent sparse ring, not the new builder. Verifies
universal identities over Z, topology, degree bounds/certificates, literal
coefficient bytes, provenance, and an operation-preserving corruption.
"""
from pathlib import Path
import copy, gzip, hashlib, importlib.util, json, sys
from collections import Counter

ROOT=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(ROOT/'upstream/circuits'))
from exact_ring import Ring, equal, evaluate, require

FAMILY=[('transport18_degree88','joint19_degree88',88,105),
        ('transport19_degree32','joint20_degree32',32,108),
        ('transport20_degree20','joint21_degree20',20,111),
        ('transport21_degree16','joint22_degree16',16,114)]

def topology(p):
    known=set(p['witnesses']+p['fixed_numerals']); live={p['output']}
    for n,op,x,y in p['source']:
        require(n not in known and op in ('+','-','*'),'Gate declaration')
        require(all(type(v) is int or isinstance(v,str) and v in known for v in (x,y)),'Gate inputs')
        known.add(n)
    for n,op,x,y in reversed(p['source']):
        if n in live:live.update((x,y))
    require(known<=live,'No dead gates, inputs, or coefficient leaves')
    require(len(p['source'])==p['operations'],'Gate count')
    require(dict(Counter(g[1] for g in p['source']))==p['operation_breakdown'],'Gate histogram')
    core=set(p['residuals'])
    for n,op,x,y in reversed(p['source']):
        if n in core:core.update((x,y))
    require(sum(n in core for n,op,x,y in p['source'])==p['system_operations'],'Residual-system count')

def check_packet(p,parent_name,degree,ops):
    topology(p)
    require(p['operations']==ops and p['exact_degree']==degree,'Advertised metrics')
    parent=json.loads((ROOT/'upstream/circuits'/(parent_name+'_dag.json')).read_text())
    src_raw=(ROOT/p['source_polynomial']).read_bytes()
    require(hashlib.sha256(src_raw).hexdigest()==p['source_sha256'],'Actual parent polynomial pin')
    require(p['source_sha256']==parent['source_sha256'],'Same parent source')
    require(p['fixed_numerals']==parent['fixed_numerals'],'Same whole coefficient tuple')
    expected=[v for v in parent['witnesses'] if v not in ('F','alpha')]
    expected.insert(1,'C')
    require(p['witnesses']==expected,'Exact quantified coordinates')
    require(p['source_row_indices']==[i for i in parent['source_row_indices'] if i!=6],'Deleted row and exact residual order')
    require(p['restoration']=={'F':'(K0+W)*C-z*(q-1)','alpha':'q-F-C'},'Restoration declaration')
    expected_binding={**parent['coefficient_binding'],
        'manifest':'upstream/guards/COEFFICIENT_BINDING.json',
        'ports':{k:'upstream/guards/coefficients/'+k+'.bin.gz' for k in p['fixed_numerals']}}
    require(p['coefficient_binding']==expected_binding,'Coefficient paths and conventions')

    # Validate low-degree arithmetic cuts against actual original inputs.
    r=Ring(p['witnesses']+p['fixed_numerals'])
    env={v:r.var(v) for v in r.names}; roots=p['named_registers']
    vals=evaluate(p,[roots[n] for n in ('W','X','Y')],env)
    J=3*env['J3']+1; q=env['beta']*J+1; W=4*(3*env['w3']+1)
    for n,target in [('W',W),('X',q*W),('Y',(2*env['v_scale']+1)*q**3)]:
        equal(vals[roots[n]],target,'Cut definition '+n)

    # At independent W,X,Y cuts, compare EVERY retained row exactly.
    # The only altered source inputs are the displayed polynomial map.
    names=p['witnesses']+p['fixed_numerals']+['W','X','Y']
    weights=[1 if n in p['witnesses'] else 0 for n in names]
    for n,w in [('W',1),('X',2),('Y',4)]:weights[names.index(n)]=w
    r=Ring(names,weights); e={v:r.var(v) for v in names}
    J=3*e['J3']+1; q=e['beta']*J+1
    F=(e['K0']+e['W'])*e['C']-e['z']*(q-1)
    alpha=q-F-e['C']
    oldenv={v:e[v] for v in parent['witnesses']+parent['fixed_numerals'] if v not in ('F','alpha')}
    oldenv.update(F=F,alpha=alpha)
    oldenv.update({parent['named_registers'][n]:e[n] for n in ('W','X','Y')})
    newenv={v:e[v] for v in p['witnesses']+p['fixed_numerals']}
    newenv.update({roots[n]:e[n] for n in ('W','X','Y')})
    old=evaluate(parent,parent['residuals'],oldenv)
    new=evaluate(p,p['residuals'],newenv)
    indexed=dict(zip(parent['source_row_indices'],parent['residuals']))
    equal(old[indexed[6]],r.const(0),'Eliminated transport row is identically zero')
    degrees=[];monomials=[]
    for root,index in zip(p['residuals'],p['source_row_indices']):
        equal(new[root],old[indexed[index]],'Restored parent row '+str(index))
        degrees.append(new[root].degree());monomials.append(len(new[root].d))
    require(2*max(degrees)<=degree,'Exact weighted upper degree bound')

    # The following specializations keep all actual fixed ports symbolic.
    # Each is a linear map of the quantified variables. A nonzero top t
    # coefficient, independent of the other ports, certifies actual degree.
    r=Ring(['t']+p['fixed_numerals'],[1]+[0]*len(p['fixed_numerals']))
    e={n:r.var(n) for n in r.names}; t=e['t']
    active={88:{'h','w3','v_scale','J3'},32:{'eta','h','w3','v_scale','J3'},
            20:{'f','v_scale','J3'},16:{'a','f','o'}}[degree]
    env={v:t if v in active else r.const(0) for v in p['witnesses']}
    env.update({v:e[v] for v in p['fixed_numerals']})
    vals=evaluate(p,p['residuals'],env)
    top=r.const(0)
    for root in p['residuals']:
        v=vals[root]
        require(v.degree()*2<=degree,'Specialization degree bound')
        if v.degree()*2==degree:top+=v.lead()**2
    coefficient={88:2**32*3**64*e['beta']**56,
                 32:2**12*3**20*e['beta']**16,
                 20:2**4*3**12*e['beta']**12,
                 16:r.const(1)}[degree]
    equal(top,coefficient*t**degree,'Nonzero top-degree specialization')

    # The finalizer is the literal sum of exactly the retained squares.
    r=Ring(p['residuals']);e={v:r.var(v) for v in r.names}
    out=evaluate(p,[p['output']],e)[p['output']]
    equal(out,sum((v*v for v in e.values()),r.const(0)),'Exact finalizer')
    return dict(name=p['name'],variables=len(p['witnesses']),degree=degree,
                operations=ops,system_operations=p['system_operations'],
                residual_degrees=degrees,staged_residual_monomials=monomials,
                source_parent=parent_name,exact_restoration=True,
                top_coefficient_positive_for_authentic_beta=True,status='PASS')

def verify_coefficients():
    binding=json.loads((ROOT/'upstream/guards/COEFFICIENT_BINDING.json').read_text())
    names=['beta','K0','MC','MF','cone_A','cone_B']; vals={}
    for n in names:
        d=binding['payloads'][n];packed=(ROOT/'upstream/guards'/d['path']).read_bytes()
        raw=gzip.decompress(packed)
        require(hashlib.sha256(raw).hexdigest()==d['raw_sha256'],'Actual coefficient '+n)
        require(len(raw)==d['raw_bytes'],'Raw byte count '+n)
        v=int.from_bytes(raw,'little')
        require(v.bit_length()==d['bits'] and raw[-1]!=0,'Minimal unsigned numeral '+n)
        vals[n]=v
    require(vals['beta']==2**1064921-1,'Literal beta recipe')
    require(vals['cone_A']==2**1113 and vals['cone_B']==2**666104,'Literal determinant scales')
    require(0<vals['MC']<vals['beta']<vals['MF']<2*vals['beta'],'Literal mask inequalities')
    source=ROOT/'upstream/guards/upstream/source34/source34_builder.py'
    spec=importlib.util.spec_from_file_location('retained_numeral_recipe',source)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    regenerated,audit=mod.construct()
    for new,old in [('beta','beta'),('K0','K'),('MC','MC'),('MF','MF_source')]:
        require(vals[new]==regenerated[old],'Complete numeral reconstruction '+new)
    return {'raw_bytes':sum(binding['payloads'][n]['raw_bytes'] for n in names),
            'complete_native_numeral_recipe_replayed':True,
            'basis_convolution_checks':audit['basis_convolution_checks'],'status':'PASS'}

def main():
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for name,sha in pins['files'].items():
        require(hashlib.sha256((ROOT/'upstream'/name).read_bytes()).hexdigest()==sha,'Immutable retained source '+name)
    # Reuse the upstream INDEPENDENT checker for parent-DAG/source binding.
    spec=importlib.util.spec_from_file_location('parent_checker',ROOT/'upstream/circuits/check.py')
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    parents=[m.check_packet(parent) for name,parent,deg,ops in FAMILY]
    checks=[]
    for name,parent,deg,ops in FAMILY:
        p=json.loads((ROOT/(name+'.json')).read_text())
        checks.append(check_packet(p,parent,deg,ops))
    bad=copy.deepcopy(json.loads((ROOT/'transport18_degree88.json').read_text()))
    gate=next(g for g in bad['source'] if g[0]==bad['named_registers']['G'])
    gate[1]='+'
    bad['operation_breakdown']=dict(Counter(g[1] for g in bad['source']))
    rejected=False
    try:check_packet(bad,'joint19_degree88',88,105)
    except ValueError:rejected=True
    require(rejected,'Operation-preserving identity corruption must be rejected')
    report={'status':'PASS','python_optimization':sys.flags.optimize,
            'upstream_files_authenticated':len(pins['files']),
            'parent_polynomial_bindings':[x['name'] for x in parents],
            'packets':checks,'coefficients':verify_coefficients(),
            'operation_preserving_corruption_rejected':True,
            'scope':'Exact algebra, degree, literal data, and source restoration; not an unbounded compiler or object-ZFC proof.'}
    (ROOT/('VERIFICATION_OPTIMIZED.json' if sys.flags.optimize else 'VERIFICATION.json')).write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
