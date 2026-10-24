"""One shared slack bounds every rule label; factorial carrier compatible.

The host passes its reviewed build_projected module as bp. No imported
upstream program is executed by importing this file.
"""
LOCAL_NAMES=('a','b','c','d','S','Sp','u','vq','w')
ONE=('c',1)

def label_data(b,bp,source,env):
    data=bp.codes(b,source,env)
    a,z=env['a'],env['b']
    data['label_sum']=b.sum(data['codes']+[a,z,data['I'](a,z),data['A'](a,z),ONE])
    return data

def projected_source(b,bp,source,env,index):
    data=label_data(b,bp,source,env);cs=data['codes'];I,A=data['I'],data['A']
    a,z,c,d=[env[s] for s in ('a','b','c','d')]
    add,mul,sd,sq=b.add,b.mul,b.sqdiff,b.square
    S,Sp,M=env['S'],env['Sp'],env['F']
    SpM=mul(Sp,M)
    ordinary=[sd(Sp,S)]+[sd(add(Sp,mul(SpM,h)),S) for h in cs[:-1]]
    guard=sd(mul(sd(c,a),sd(c,z)),sq(add(d,ONE)))
    bundle=add(sd(add(Sp,mul(SpM,cs[-1])),S),guard)
    def weight(v):return add(ONE,mul(v,M))
    mp=sd(mul(Sp,weight(z)),b.product([S,weight(a),weight(I(a,z))]))
    gen=sd(mul(Sp,weight(A(a,z))),mul(S,weight(z)))
    horn=b.product(ordinary+[bundle,mp,gen])
    den=add(mul(add(index,ONE),env['y']),ONE)
    beta=[sd(env['x'],add(S,mul(den,env['u']))),
          sd(env['x'],add(Sp,mul(add(den,env['y']),env['vq'])))]
    label_bound=sd(env['t'],add(env['w'],data['label_sum']))
    return b.sum([horn]+beta+[label_bound])

def local_majorant(bp,source):
    b=bp.UpperBuilder(True)
    atoms={n:b.new(n) for n in ('t','x','y','F')}
    bounds={n:atoms['t'] if n in ('a','b','c','d','w') else atoms['y'] if n in ('S','Sp') else atoms['x'] for n in LOCAL_NAMES}
    value=projected_source(b,bp,source,atoms|bounds,atoms['t'])
    out=b.sum([value,atoms['t'],atoms['x'],atoms['y'],ONE])
    cert=bp.bound_certificate(b,atoms,out)
    cert['base']='2+t+x+y+F'
    cert['squared_difference_majorization']='(u-v)^2 <= (U+V)^2 for 0<=u<=U,0<=v<=V'
    cert['emitted_exponent']=max(4,1<<(cert['exponent']-1).bit_length())
    cert['new_bound']='sum(nine axiom codes)+a+b+I(a,b)+A(a,b)+1+w=t'
    return cert
