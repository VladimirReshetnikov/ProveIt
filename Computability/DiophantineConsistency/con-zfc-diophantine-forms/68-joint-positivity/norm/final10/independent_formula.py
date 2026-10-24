"""Independent complete equation evaluator from sparse kernel/weight data.
No circuit, builder, or baseline program is imported. Intended for modular replay.
"""
def evaluate(inputs,p,ports,code,kernels):
    # Explicit interface order t,g0,c0,k0,l,w,x,y,z,m.
    t,g0,c0,k0,l,w,x,y,z,m=inputs
    env={}
    def put(k,v): env[k]=v%p; return env[k]
    b=put('b',6*t+4);g=put('g',b*g0);k=put('k',b*(3*k0+2));kap=2134940
    base=put('base',pow(2,kap,p)*b*b)
    weights=code['weights'];targets=code.get('targets_by_row',code.get('targets'))
    W=max(weights);H=max(term['exponent']+layer['degree']*W for layer in kernels['kernels'] for term in layer['terms'])
    ell=put('ell',sum(pow(base,e,p) for e in weights));word=put('word',ell+g)
    ds=[]
    for layer in kernels['kernels']:
        value=0
        for term in layer['terms']:
            coef=0
            for row in term['coefficient']:
                v=row['coefficient']
                for port,exponent in zip(ports,row['powers']):v=v*pow(port,exponent,p)%p
                coef=(coef+v)%p
            value=(value+coef*pow(base,term['exponent'],p))%p
        ds.append(put('Dcode'+str(layer['degree']),value))
    codeword=put('coded',ds[2]*word*word+ds[1]*word+ds[0])
    AT=put('targets',sum(pow(base,e,p) for e in targets))
    N0=put('n0',pow(base,W+1,p));N=put('nn',pow(base,H+W+2,p))
    mask=put('mask',N0-1-(b-1)*ell);jc=put('jc',2*codeword+AT)
    sc=put('sc',g+N0*jc);tc=put('tc',mask+N0*(base-2)*AT-2)
    X=put('X',N*(sc+tc+1)-sc-1)
    Y=put('Y',pow(2,16*kap-23,p)*b*pow(base,H+2*W+9,p))
    cap=put('cap',b*pow(base,W,p));L=put('L',l*Y);U=put('U',2*L*X)
    V=put('V',4*g*w*Y);Wb=put('W',b*w);A=put('A',U*(V+1));B1=put('B1',2*X+1)
    C=put('C',6*c0-1);Phalf=put('Phalf',(L*X)*U*V);P=put('P',2*Phalf)
    K=put('K',X+1+k*(P-2));S=put('S',2*A-5);T=put('T',3*Wb*C-2*(Wb*Wb-1))
    Q=put('Q',(Phalf*Phalf-1)*K*K+1)
    Delta=put('Delta',8*cap**3*g*K*K-g*g*(32*(C-K*L)**2*cap**3+g*g*K*K))
    xi=put('xi',z*x);D=put('D',(A*A-4)*C*C+4);E=put('E',C*C*D*xi)
    F=put('F',4*(A*A-4)*E*E+1);G=put('G',2*(A+2)*(A-2)**2*E*E-1)
    Omega=put('Omega',16*E);HH=put('H',C+F*(B1-C+Omega*y));I=put('I',(G*G-1)*HH*HH+1)
    rho=put('rho',T+S*y);Sigma=put('Sigma',xi*pow(S,5,p))
    Theta=put('Theta',(rho**3-rho*S*S-S**3)*(rho*rho+23*S*S))
    seed=put('r',b*Q);aa=put('guard',seed+(9*Delta-3)*(seed*z)**2);dd=put('lucas',D*F*I)
    center=put('center',Sigma*m-Theta)
    result=put('F10',(center*center-Sigma*Sigma*(aa+dd))**2-4*Sigma**4*aa*dd)
    return result,env
