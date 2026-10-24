#!/usr/bin/env python3
"""Independent arithmetic verification. Standard library only; no network.
Exact coefficient, generic norm, degree, and liveness checks are distinguished
from finite modular whole-circuit transcription diagnostics.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,random,sys,time
from exact_polynomial import Ring
from audit_support import require,coefficients,Fp,formal_conjugate_norm,evaluate_dag
from formal_radicals import Poly
from five_square_norm import cleared_norm5_compact2
from check_degree import cut,actual_leading
ROOT=Path(__file__).resolve().parent

def generic_norm():
    product=Poly.variable(0)
    for i in range(5):product=product-Poly.radical(i)
    for i in reversed(range(5)):product=product*product.conjugate(i)
    require(all(m[-1]==0 for m in product.terms),'radicals eliminated')
    expected={m[:5]+(m[5],16-m[5]):v for m,v in product.terms.items()}
    names=['x','a','b','c','d','cn','delta'];ring=Ring(names)
    actual=cleared_norm5_compact2(*(ring.var(n) for n in names))
    require(actual.terms==expected,'all generic cleared norm coefficients')
    # The coefficient identity is the exact finite certificate; the following
    # deliberate corruption is required to fail the same equality test.
    corrupt=dict(expected);key=next(iter(corrupt));corrupt[key]+=1
    require(actual.terms!=corrupt,'negative control detects corrupt coefficient')
    from circuit import DAG
    dag=DAG(names);leaves=[dag.leaf('variable',name) for name in names]
    out=cleared_norm5_compact2(*leaves);live=set()
    def visit(i):
        if i in live:return
        live.add(i);n=dag.nodes[i]
        if n[0] in ('add','sub','mul'):visit(n[1]);visit(n[2])
    visit(out.i)
    operations=sum(dag.nodes[i][0] in ('add','sub','mul') for i in live)
    require(operations==83,'83-gate generic cleared norm')
    return {'conjugates':32,'monomials':len(expected),'clearing_exponent':16,
            'generic_live_binary_operations':operations,
            'all_coefficients_equal':True,'corruption_rejected':True}

def front(inputs,ports,prime,centered):
    x={n:Fp(v,prime) for n,v in inputs.items()};p={n:Fp(v,prime) for n,v in ports.items()}
    J=1+6*x['j'];q=1+p['beta']*J;W=4*(3*x['w']+1)
    X=W*q;Y=x['v']*q;a=(X+1)*Y;E=a-Y;H=4*a+3;Delta=(a+1)*(a+3)
    C=x['C'];F=p['K0']*C+W*C-x['z']*q+x['z'];alpha=q-C-F
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(p['MC']+p['MF']*q)*J
    k=R+1+x['h']*E;c=x['c'];eta=c-Y*k
    I=(2*x['r']+1)*c*c;I2=I*I;Bstrong=Delta*I2
    Df=(a+2)**2*I2-I2+1;Q=(Delta*I)**2;delta=Q-1
    V=Df*c*x['T']-Df*R-c;Cy=(delta+1)*V*V-1
    ell0=X*Y*Y;L=ell0*k;Dtau=ell0*(ell0+1)*k*k+1;Dmain=1+Delta*c*c
    b0=a*c+X;coneU=p['cone_A']*F;coneZ=p['cone_B']*C
    Derr=coneU*coneU+coneZ*coneZ-2*q*(coneU+coneZ)+2*q*q
    budget=(q*k)**2-k*k*Derr-(2*q*eta)**2
    Ag=budget-(1+x['p2']**2+x['p3']**2+x['p3'])
    M=2*q*q;Lcrt=1;U=M*H;ML=M
    center=M*(H*(x['n']+V+(L if centered else 0))+Lcrt*b0)+H*(x['v']-q*q)
    return {n:v.value for n,v in locals().copy().items() if isinstance(v,Fp)}

def check_packet(packet,ports,centered):
    nodes=packet['nodes'];used=set();counts=Counter()
    for i,n in enumerate(nodes):
        op=n[0]
        if op in ('add','sub','mul'):
            require(len(n)==3 and all(isinstance(j,int) and 0<=j<i for j in n[1:]),'acyclic DAG')
            counts[op]+=1
        else:
            require(op in ('integer','variable','coefficient') and len(n)==2,'literal leaf')
            if op=='variable':used.add(n[1])
    live=set()
    def visit(i):
        if i in live:return
        live.add(i)
        if nodes[i][0] in ('add','sub','mul'):visit(nodes[i][1]);visit(nodes[i][2])
    visit(packet['output'])
    require(len(live)==len(nodes),'all nodes live')
    require(used==set(packet['variables']) and len(used)==12,'exactly twelve unrestricted inputs')
    require(dict(counts)==packet['operation_counts'] and sum(counts.values())==packet['operations'],'exact binary count')
    require(packet['operations']==(180 if centered else 179),'frozen cost')
    require(packet['exact_degree']==(1000 if centered else 1024),'frozen degree')
    rng=random.Random(1008);primes=(1000000007,1000000009,1000000033);done=0;registers=0
    while done<45:
        prime=primes[done%3];inputs={name:rng.randrange(-30,31) for name in packet['variables']}
        if done==0:inputs['v']=0
        if done==1:inputs['c']=0
        if done==2:inputs['v']=inputs['c']=0
        r=front(inputs,ports,prime,centered)
        if not r['delta']:continue
        values=evaluate_dag(packet,inputs,ports,prime)
        for name,value in r.items():
            if name in packet['named_registers']:
                require(values[packet['named_registers'][name]]==value,'front register '+name);registers+=1
        dy=r['Cy']*pow(r['delta'],prime-2,prime)%prime
        rad=[r['ML']**2*r['Dmain']%prime,r['U']**2*r['Df']%prime,
             r['U']**2*r['Dtau']%prime,r['U']**2*r['Ag']%prime,r['U']**2*dy%prime]
        expected=pow(r['delta'],16,prime)*formal_conjugate_norm(r['center'],rad,prime)%prime
        require(values[packet['output']]==expected,'independent whole conjugate norm')
        done+=1
    degree=cut(centered);degree['actual_coefficient']=actual_leading(centered)
    return {'name':packet['name'],'operations':packet['operations'],'variables':12,'degree':degree,
       'modular_diagnostics':done,'front_register_diagnostics':registers,'primes':list(primes),
       'exceptional_slices':['v=0','c=0','v=c=0']}

def main():
    start=time.monotonic();ports,receipt=coefficients(ROOT)
    results=[]
    for centered,name in ((False,'budget12_aux_centered'),(True,'budget12_tau_centered')):
        results.append(check_packet(json.loads((ROOT/(name+'.json')).read_text()),ports,centered))
    import check_semantic_cuts,check_exact_cuts
    check_semantic_cuts.main()
    cut_receipt=check_exact_cuts.main()
    result={'status':'PASS','fixed_coefficients':receipt,'generic_norm':generic_norm(),'exact_DAG_cuts':cut_receipt,'packets':results,
      'seconds':round(time.monotonic()-start,3),'scope':'Exact finite arithmetic certificates; semantic reduction and inherited calibration stated separately in PROOF.md.'}
    path=ROOT/('CHECK_OPTIMIZED.json' if sys.flags.optimize else 'CHECK_NORMAL.json')
    path.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
