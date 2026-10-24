#!/usr/bin/env python3
"""Exact degree/gate/front/norm audits for the eleven-integer synthesis."""
from pathlib import Path
from collections import Counter
import json,random,sys,time
ROOT=Path(__file__).resolve().parent
sys.path.append(str(ROOT.parent/'guard'))
from exact_polynomial import Ring
from audit_support import require,coefficients,Fp,evaluate_dag,formal_conjugate_norm
from check_exact_cuts import exact_cut
from five_square_norm import cleared_norm5_compact2
from formal_radicals import Poly

FORMULAS={
 'J':'6*j+1','q':'beta*J+1','W0':'4*(3*w+1)','X':'q*W0',
 'Y':'(2*v+1)*q**3','E':'X*Y','a':'E+Y','H':'4*a+3','Delta':'a*a+H',
 'F':'(K0+W0)*C-z*(q-1)',
 'R':'(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J','k':'R+1+h*E',
 'eta':'c-Y*k','U':'cone_A*F','Zc':'cone_B*C',
 'Derr':'(U-q)**2+(Zc-q)**2','Budget':'k*k*(q*q-Derr)-4*q*q*eta*eta',
 'Dg':'4*(3*Budget-4)*s*s+1','I':'2*s*r*c*c','I2':'I*I',
 'Df':'1+Delta*I2','Q':'Delta*Delta*I2','delta':'Q-1',
 'V':'Df*(c-R+4*I*T)-c','Cy':'Q*V*V-1','Da':'delta*Cy',
 'ell':'E*Y','Ltau':'ell*k','Dt':'1+Ltau*(Ltau+k)',
 'Dm':'1+Delta*c*c','b0':'X+a*c','u':'H*T-b0','u2':'u*u',
 'H2':'H*H','H3':'H2*H','Q0':'u2+Dm+31*H2',
 'C0':'u*(u2+3*Dm+H2)+H3','C1':'3*u2+Dm+H2','u_twice':'2*u',
 'A':'Q0*C0+u_twice*Dm*C1','B':'Q0*C1+u_twice*C0',
 'H5':'H3*H2','S':'I*H5','S2':'S*S','A0':'B*B*Dm',
 'c2':'c*c','s2':'s*s','r2':'r*r','T2':'T*T',
 'b_bound':'1+c2+R+c2*(s2+r2)*(T2+1)',
 'ba':'Q*(Df*b_bound+c2+1)','bf':'Delta+I2+3','bt':'2+ell*ell+k*k',
 'bound_K':'T2+c2+1','w1':'512*bound_K*bound_K+1',
 'w2':'w1*(2*ba+1)','w3':'w2*(2*bf+1)','w4':'w3*(2*bt+1)',
 'A1':'4*S2*Da','A2':'S2*Df',
 'A3':'16*S2*Dt','A4':'64*S2*Dg',
 'aux_shift':'(2*Q-1)*V','tau_shift':'4*Ltau','center':'S*n-A'
}

def degree(packet):
    import importlib.util
    spec=importlib.util.spec_from_file_location('eleven_degree_certificate',ROOT/'check_degree.py')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    cut,actual=module.cut,module.actual
    variant=packet['centering_variant']
    result=cut(variant);result['actual_coefficient']=actual(variant)
    require(result['degree']==packet['exact_degree'],'packet exact degree')
    return result

def norm_cut(packet):
    names=['x','a','b','c','d','e'];ring=Ring(names);values=[ring.var(n) for n in names]
    aliases=['center','A2','A3','A0','A4','A1']
    cuts={packet['named_registers'][n]:v for n,v in zip(aliases,values)};memo={}
    def walk(i):
        if i in cuts:return cuts[i]
        if i in memo:return memo[i]
        n=packet['nodes'][i];op=n[0]
        if op=='integer':v=ring.scalar(n[1])
        elif op in ('variable','coefficient'):raise ValueError('uncut norm input')
        else:
            a,b=walk(n[1]),walk(n[2]);v=a+b if op=='add' else a-b if op=='sub' else a*b
        memo[i]=v;return v
    actual=walk(packet['output'])
    product=Poly.variable(0)
    for i in range(5):product=product-Poly.radical(i)
    for i in reversed(range(5)):product=product*product.conjugate(i)
    expected={m[:6]:v for m,v in product.terms.items()}
    require(actual.terms==expected,'complete independent norm coefficient identity')
    return len(actual.terms)

def diagnostics(packet,ports):
    # Independent alternate algebraic front; all values below are field elements.
    trials=36;primes=[1000000007,1000000009,1000000033];rng=random.Random(4512)
    for case in range(trials):
        prime=primes[case%3];inp={n:rng.randrange(-10,11) for n in packet['variables']}
        if case==0:inp['s']=0
        if case==1:inp['r']=0
        if case==2:inp['c']=0
        x={n:Fp(v,prime) for n,v in inp.items()};p={n:Fp(v,prime) for n,v in ports.items()}
        J=1+6*x['j'];q=1+p['beta']*J;W=4*(3*x['w']+1);X=q*W;Y=(1+2*x['v'])*q**3
        E=X*Y;a=(X+1)*Y;H=4*a+3;D=(a+1)*(a+3);c=x['c']
        C=x['C'];F=p['K0']*C+W*C-x['z']*q+x['z'];alpha=q-C-F
        R=((q-1)*(q-F)+alpha)*(q*q-1)+(p['MC']+p['MF']*q)*J
        k=1+R+x['h']*E;eta=c-Y*k;cu=p['cone_A']*F;cz=p['cone_B']*C
        err=cu*cu+cz*cz-2*q*(cu+cz)+2*q*q
        budget=(q*k)**2-k*k*err-(2*q*eta)**2
        dg=1+4*(3*budget-4)*x['s']**2;I=2*x['s']*x['r']*c*c;df=1+D*I*I;Q=(D*I)**2
        delta=Q-1;V=df*c-df*R+4*df*I*x['T']-c;da=delta*(Q*V*V-1)
        ell=X*Y*Y;dt=1+ell*(ell+1)*k*k;dm=1+D*c*c;b0=X+a*c;u=H*x['T']-b0
        AA=u**5+10*u**3*dm+5*u*dm**2+32*H**2*(u**3+3*u*dm)+H**3*(u*u+dm)+31*H**4*u+31*H**5
        BB=5*u**4+10*u*u*dm+dm*dm+32*H**2*(3*u*u+dm)+2*H**3*u+31*H**4
        S=I*H**5
        rad=[BB*BB*dm,4*S*S*da,S*S*df,16*S*S*dt,64*S*S*dg]
        shift=Fp(0,prime)
        if packet['centering_variant']!='direct':shift=shift+(2*Q-1)*V
        if packet['centering_variant']=='both':shift=shift+4*ell*k
        center=S*(x['n']+shift)-AA
        expected=formal_conjugate_norm(center.value,[v.value for v in rad],prime)
        actual=evaluate_dag(packet,inp,ports,prime)[packet['output']]
        require(actual==expected,'whole11 modular transcription')
    return {'cases':trials,'primes':primes,'exceptional_slices':['s=0','r=0','c=0']}

def main():
    start=time.monotonic();ports,coeff=coefficients(ROOT.parent/'guard');results=[]
    import check_semantic_cuts
    check_semantic_cuts.main()
    for variant,deg,cost in (('direct',2912,200),('aux',2272,204),('both',2240,206)):
        packet=json.loads((ROOT/('budget_intersective11_degree'+str(deg)+'.json')).read_text())
        counts=Counter(n[0] for n in packet['nodes'] if n[0] in ('add','sub','mul'));live=set()
        def visit(i):
            if i in live:return
            live.add(i);n=packet['nodes'][i]
            if n[0] in ('add','sub','mul'):
                require(0<=n[1]<i and 0<=n[2]<i,'acyclic gates');visit(n[1]);visit(n[2])
        visit(packet['output'])
        require(len(live)==len(packet['nodes']),'all gates live')
        require(sum(counts.values())==packet['operations']==cost,'operation count')
        require(set(n[1] for n in packet['nodes'] if n[0]=='variable')==set(packet['variables']) and len(packet['variables'])==11,'eleven unrestricted variables')
        formulas=dict(FORMULAS)
        if variant=='aux':formulas['center']='S*(n+aux_shift)-A'
        if variant=='both':formulas['center']='S*(n+aux_shift+tau_shift)-A'
        cuts={name:exact_cut(packet,name,text) for name,text in formulas.items() if name in packet['named_registers']}
        results.append({'name':packet['name'],'variables':11,'operations':cost,'degree':degree(packet),
          'exact_front_register_cuts':len(cuts),'exact_norm_coefficients':norm_cut(packet),
          'diagnostics':diagnostics(packet,ports)})
    result={'status':'PASS','packets':results,'coefficients':coeff,
      'scope':'Finite arithmetic checks; new centered generalized-strong proof and inherited calibration are separate.',
      'seconds':round(time.monotonic()-start,3)}
    (ROOT/('CHECK_OPTIMIZED.json' if sys.flags.optimize else 'CHECK_NORMAL.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
