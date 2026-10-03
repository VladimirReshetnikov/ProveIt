"""Standalone exact total-degree certificates for emitted packed U15 sources.

No parent is edited. A fixed positive linear slice and exact modular highest-
degree coefficients certify the propagated upper bound for the full SOS.
"""
import argparse
from contextlib import contextmanager
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

PINS={
 'u15_packed_composed_truth646.py':'d2ec28b859b43e93396f66395866b3f18098a959da22c1a5559fc4c1be2cdeb7',
 'u15_packed_two_tape_history.py':'ada8106314bffe545cc106ca66b737d48398d6288f3d86cfaf602e58d0e1c318',
 'u15_packed_state_relabel652.py':'cd3904fb083d1a254461ffde87636a6b9014bcdecb1db48cfcf2f30f41493879',
 'u15_packed_computed_truth647.py':'c363ea0679825559d5247608f748d877e75146dbb997b159db42294d9d676eb7',
}
PRIMES=(1000000007,1000000009)


def require(ok,message):
    if not ok:raise ValueError(message)


def authenticate(path):
    path=Path(path).resolve()
    require(path.name in PINS,'Unknown source filename')
    require(hashlib.sha256(path.read_bytes()).hexdigest()==PINS[path.name],'Pinned compiler source changed')
    return path


@contextmanager
def isolated_imports(root,paths):
    root=Path(root).resolve();oldpath=list(sys.path);before=set(sys.modules)
    names={p.stem for p in root.glob('*.py')}|{'_degree_source_'+str(i) for i in range(len(paths))}
    saved={name:sys.modules[name] for name in names if name in sys.modules}
    for name in names:sys.modules.pop(name,None)
    sys.path.insert(0,str(root))
    try:
        modules=[]
        for i,path in enumerate(paths):
            name='_degree_source_'+str(i);spec=importlib.util.spec_from_file_location(name,path)
            mod=importlib.util.module_from_spec(spec);sys.modules[name]=mod;spec.loader.exec_module(mod);modules.append(mod)
        yield modules
    finally:
        sys.path[:]=oldpath
        for name in names:sys.modules.pop(name,None)
        for name in set(sys.modules)-before:
            filename=getattr(sys.modules.get(name),'__file__',None)
            if filename and Path(filename).resolve().is_relative_to(root):sys.modules.pop(name,None)
        sys.modules.update(saved)


def source_contract(packet):
    names=packet['parameters']+packet['auxiliaries'];known=set(names)
    require(len(names)==len(known) and all(type(n) is str for n in names),'Coordinate schema changed')
    require(set(packet['fixed_parameters'])<=set(packet['parameters']),'Fixed parameter schema changed')
    for row in packet['polynomial_source']:
        require(type(row) in (tuple,list) and len(row)==4,'Binary source row required')
        n,op,a,b=row
        require(type(n) is str and n not in known and type(op) is str and op in ('+','-','*'),'Invalid arithmetic row')
        require(all(type(v) is int or type(v) is str and v in known for v in (a,b)),'Unpaid or inexact operand')
        known.add(n)
    # Authenticate the entire SOS finalizer, not only its metadata.
    rows=list(packet['source']);squares=[]
    for i,(a,b) in enumerate(packet['comparisons']):
        residual='poly_res'+str(i);square='poly_sq'+str(i)
        rows.extend(((residual,'-',a,b),(square,'*',residual,residual)));squares.append(square)
    output=squares[0]
    for i,square in enumerate(squares[1:],1):
        name='poly_sum'+str(i);rows.append((name,'+',output,square));output=name
    require(rows==packet['polynomial_source'] and output==packet['output'],'Literal SOS finalizer changed')
    require(packet['comparisons'].count(('native__L9','native__R9'))==1,'Native norm residual changed')
    by={n:(op,a,b) for n,op,a,b in packet['source']}
    expected={
      'native__bs_X_bound':('+','native__bs_packed','native__bound_beta'),
      'native__wn2':('*','native__bs_X_bound','native__q'),
      'native__bs_even':('*',2,'native__odd_half'),
      'native__bs_odd':('+','native__bs_even',1),
      'native__sn2':('*','native__bs_odd','native__q'),
      'native__UM':('*','native__wn2','native__sn2'),
      'native__UM2':('*','native__UM','native__UM'),
      'native__scaled_norm_coefficient':('+','native__UM2','native__wn2'),
      'native__R10b':('+','native__eta','native__zeta'),
      'native__ksn2':('*','native__R10b','native__sn2'),
      'native__ratio_product2':('*','native__ksn2','native__ksn2'),
      'native__L9':('*','native__scaled_norm_coefficient','native__ratio_product2'),
      'native__tauplus1':('+','native__tau',1),
      'native__R9':('*','native__tau','native__tauplus1'),
    }
    require(all(by.get(name)==row for name,row in expected.items()),'Actual leading norm schedule changed')


def coefficient_audit(packet,prime):
    # All moving coordinates are exactly t, all fixed program numerals exactly1.
    # Degree bounds are never lowered after cancellation: each residue below is
    # the coefficient at its independently propagated formal upper degree.
    fixed=set(packet['fixed_parameters'])
    env={n:(0 if n in fixed else 1,1) for n in packet['parameters']+packet['auxiliaries']}
    dependencies={n:({n} if n in fixed else set()) for n in env}
    def deps(v):return dependencies[v] if type(v) is str else set()
    def get(v):return env[v] if type(v) is str else (0,v%prime)
    for n,op,a,b in packet['polynomial_source']:
        da,ca=get(a);db,cb=get(b)
        if op=='*':d,c=da+db,ca*cb
        else:
            d=max(da,db);c=(ca if da==d else 0)+(1 if op=='+' else -1)*(cb if db==d else 0)
        env[n]=(d,c%prime)
        dependencies[n]=(deps(a)|deps(b)) if op=='*' else ((deps(a) if da==d else set())|(deps(b) if db==d else set()))
    require(not dependencies[packet['output']],'Top coefficient may depend on fixed program values')
    output_degree,output_lead=env[packet['output']]
    require(output_degree==packet['ledger']['formal_degree_upper_bound']==1936,'Unexpected output upper degree')
    r=packet['registers']
    aliases={**{n:r[n] for n in ('B','J','P','Zjoin')},
             'q':'native__q','F3':'native__F3','r':'native__bs_packed',
             'X':'native__wn2','Y':'native__sn2','k':'native__R10b'}
    degrees={n:env[name][0] for n,name in aliases.items()}
    require(degrees==dict(B=1,J=1,P=2,Zjoin=67,q=69,F3=67,r=274,X=343,Y=70,k=1),'Principal degree chain changed')
    leading={n:env[name][1] for n,name in aliases.items()}
    require(leading['P']==leading['B']*leading['J']%prime,'P leading identity failed')
    require(leading['q']==16*leading['B']*pow(leading['P'],34,prime)%prime,'q leading identity failed')
    require(leading['F3']==16*pow(leading['P'],33,prime)%prime,'F3 edge28 leading identity failed')
    require(leading['r']==pow(leading['q'],3,prime)*leading['F3']%prime,'r leading identity failed')
    require(leading['X']==leading['q']*leading['r']%prime,'X leading identity failed')
    require(leading['Y']==2*leading['q']%prime and leading['k']==2,'Y/k leading identity failed')
    index=packet['comparisons'].index(('native__L9','native__R9'))
    residuals=[env['poly_res'+str(i)] for i in range(len(packet['comparisons']))]
    norm_degree,norm_lead=residuals[index]
    formula=pow(leading['X'],2,prime)*pow(leading['Y'],4,prime)*pow(leading['k'],2,prime)%prime
    require(norm_degree==968 and norm_lead==formula and norm_lead!=0,'Native top residual coefficient vanished')
    top=[{'comparison':i,'coefficient':c} for i,(d,c) in enumerate(residuals) if d==968]
    require(output_lead==sum(v['coefficient']**2 for v in top)%prime!=0,'Full SOS top coefficient vanished')
    require(max(d for d,c in residuals)==968,'Larger residual appeared')
    return dict(prime=prime,slice='Every nonfixed supplied coordinate=t; fixed program numerals=1',
      principal_degrees=degrees,principal_leading_coefficients=leading,
      norm_comparison_index=index,norm_residual_degree=968,norm_residual_leading_coefficient=norm_lead,
      top_residual_coefficients=top,output_leading_coefficient=output_lead,
      exact_output_degree=1936,fixed_program_dependencies_of_top_coefficient=sorted(dependencies[packet['output']]))


def verify(root,computed647=None,computed646=None):
    require(__debug__,'Author compilers require enabled assertions')
    root=Path(root).resolve()
    paths=[authenticate(root/name) for name in ('u15_packed_two_tape_history.py','u15_packed_state_relabel652.py')]
    if computed647 is not None:paths.append(authenticate(computed647))
    if computed646 is not None:
        require(computed647 is not None,'Include the pinned647 source when auditing646')
        paths.append(authenticate(computed646))
    forms=[]
    with isolated_imports(root,paths) as modules:
        for path,module in zip(paths,modules):
            methods=['build']+(['tagged_parent'] if path.name in ('u15_packed_computed_truth647.py','u15_packed_composed_truth646.py') else [])
            for method in methods:
                for ordinary in (False,True):
                    kwargs={'root':root} if path.name in ('u15_packed_state_relabel652.py','u15_packed_composed_truth646.py') else {}
                    packet=getattr(module,method)(ordinary,**kwargs)
                    source_contract(packet)
                    proofs=[coefficient_audit(packet,prime) for prime in PRIMES]
                    require(packet['ledger']['exact_degree_claimed'] is False,'Parent metadata must remain upper-only')
                    forms.append(dict(compiler=path.name,constructor=method,ordinary=ordinary,
                      operations=packet['ledger']['polynomial']['operations'],
                      polynomial_source_sha256=hashlib.sha256(json.dumps(packet['polynomial_source'],separators=(',',':')).encode()).hexdigest(),
                      declared_upper_degree=1936,independently_certified_exact_degree=1936,
                      inherited_exact_degree_claimed=False,modular_certificates=proofs))
    for path in paths:authenticate(path)
    return dict(status='PASS_EXACT_DEGREE1936',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      compiler_pins={path.name:PINS[path.name] for path in paths},forms=forms,
      scope='Exact total degree in moving supplied coordinates with positive program numerals fixed. Literal full SOS certificate, not a new arithmetic operation bound or an optimization of parent metadata.')


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--computed647',type=Path);ap.add_argument('--computed646',type=Path);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path)
    a=ap.parse_args();result=verify(a.root,a.computed647,a.computed646);wire=json.dumps(result,indent=2)+'\n'
    if a.expect:require(json.loads(a.expect.read_text())==result,'Saved degree receipt differs')
    if a.output:a.output.write_text(wire)
    print(wire)
