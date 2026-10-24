#!/usr/bin/env python3
"""Literal division-free consistency polynomials. Python standard library only.

The generated DAGs contain only integer numeral/variable leaves and binary
addition, subtraction, multiplication. No proof search is run.
"""
from pathlib import Path
from collections import Counter
import gzip, hashlib, importlib.util, json
from five_square_norm import cleared_norm5

ROOT = Path(__file__).resolve().parent
BASE_PORTS = ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']
VARS13 = ['j', 'C', 'z', 'h', 'r', 'v', 'w', 'T', 'c', 'n', 't', 'p2', 'p3']

def require(ok, message):
    if not ok:
        raise ValueError(message)

class DAG:
    def __init__(self, variables):
        self.nodes = []
        self.index = {}
        self.variables = list(variables)
    def leaf(self, kind, value):
        return self.intern((kind, value))
    def intern(self, key):
        if key not in self.index:
            self.index[key] = len(self.nodes)
            self.nodes.append(list(key))
        return Expr(self, self.index[key])
    def coerce(self, value):
        if isinstance(value, Expr):
            require(value.d is self, 'foreign arithmetic register')
            return value
        require(isinstance(value, int), 'integer literal required')
        return self.leaf('integer', value)
    def op(self, tag, left, right):
        a, b = self.coerce(left), self.coerce(right)
        na, nb = self.nodes[a.i], self.nodes[b.i]
        if na[0] == nb[0] == 'integer':
            x, y = na[1], nb[1]
            return self.coerce(x+y if tag == 'add' else x-y if tag == 'sub' else x*y)
        if tag == 'mul':
            if na == ['integer', 0] or nb == ['integer', 0]: return self.coerce(0)
            if na == ['integer', 1]: return b
            if nb == ['integer', 1]: return a
        if tag == 'add':
            if na == ['integer', 0]: return b
            if nb == ['integer', 0]: return a
        if tag == 'sub':
            if nb == ['integer', 0]: return a
            if a.i == b.i: return self.coerce(0)
        if tag in ('add', 'mul') and a.i > b.i: a, b = b, a
        return self.intern((tag, a.i, b.i))

class Expr:
    def __init__(self, d, i): self.d, self.i = d, i
    def __add__(self, other): return self.d.op('add', self, other)
    def __radd__(self, other): return self.d.op('add', other, self)
    def __sub__(self, other): return self.d.op('sub', self, other)
    def __rsub__(self, other): return self.d.op('sub', other, self)
    def __mul__(self, other): return self.d.op('mul', self, other)
    def __rmul__(self, other): return self.d.op('mul', other, self)
    def __neg__(self): return self.d.op('mul', -1, self)
    def __pow__(self, exponent):
        require(isinstance(exponent, int) and exponent >= 0, 'fixed natural exponent')
        if exponent == 0: return self.d.coerce(1)
        if exponent == 1: return self
        a = self ** (exponent // 2)
        return a*a if exponent % 2 == 0 else (a*a)*self

def front(variables):
    d = DAG(variables)
    x = {name: d.leaf('variable', name) for name in variables}
    p = {name: d.leaf('coefficient', name) for name in BASE_PORTS}
    J = 6*x['j']+1
    q = p['beta']*J+1
    W = 12*x['w']+4
    X = q*W
    Y = (2*x['v']+1)*(q*q*q)
    E = X*Y
    a = E+Y
    H = 4*a+3
    Delta = a*a+H
    C = x['C']
    F = (p['K0']+W)*C-x['z']*(q-1)
    alpha = q-F-C
    R = (q*(q-F)-C)*(q*q-1)+(p['MC']+q*p['MF'])*J
    k = R+1+x['h']*E
    c = x['c']
    eta = c-Y*k
    zeta = k-eta
    c2 = c*c
    I = (2*x['r']+1)*c2
    I2 = I*I
    Bstrong = Delta*I2
    Df = 1+Bstrong
    Q = Delta*Bstrong
    delta = Q-1
    V = Df*(c*x['T']-R)-c
    Cy = Q*V*V-1
    Aaux = delta*Cy
    ell0 = E*Y
    L = ell0*k
    Dtau = ell0*(ell0+1)*(k*k)+1
    Dmain = 1+Delta*c2
    b0 = X+a*c
    U = p['cone_A']*F
    Zc = p['cone_B']*C
    G = U*Zc-(q-U-Zc)**2
    Peta = eta*zeta
    Pair = G*Peta-(x['t']**2-G-Peta+1)**2
    Ag = Pair-1-x['p2']**2-x['p3']*(x['p3']+1)
    F0 = (a+2)*I
    registers = {name: val for name, val in locals().copy().items() if isinstance(val, Expr)}
    return d, x, p, registers

def export(name, d, output, registers, metadata):
    live = set()
    def visit(i):
        if i in live: return
        live.add(i)
        node = d.nodes[i]
        if node[0] in ('add', 'sub', 'mul'):
            visit(node[1]); visit(node[2])
    visit(output.i)
    remap = {old: new for new, old in enumerate(sorted(live))}
    nodes = []
    for old in sorted(live):
        node = d.nodes[old]
        nodes.append([node[0], remap[node[1]], remap[node[2]]]
                     if node[0] in ('add', 'sub', 'mul') else node)
    counts = Counter(node[0] for node in nodes if node[0] in ('add', 'sub', 'mul'))
    used = {node[1] for node in nodes if node[0] == 'variable'}
    require(used == set(d.variables), 'every declared variable is live')
    return dict(schema='integer-polynomial-dag-v1', name=name,
                domain='unrestricted integers', variables=d.variables,
                variable_count=len(d.variables), nodes=nodes, output=remap[output.i],
                named_registers={key: remap[value.i] for key, value in registers.items()
                                 if value.i in remap},
                operation_counts=dict(sorted(counts.items())), operations=sum(counts.values()),
                coefficient_binding='../coefficients/BINDING.json', **metadata)

def make13(sheared=True):
    d, x, p, r = front(VARS13)
    H2 = r['H']*r['H']
    A = H2*r['Df']; B = H2*r['Dtau']; Cn = H2*r['Cy']
    Dm = r['Dmain']; AgH2 = H2*r['Ag']
    center = r['H']*(x['n']+r['V'])+r['b0'] if sheared else r['H']*x['n']+r['b0']
    output = cleared_norm5(center, A, B, Dm, AgH2, Cn, r['delta'])
    r.update(center=center, norm=output, scaled_Df=A, scaled_Dtau=B,
             scaled_Ag=AgH2, scaled_Cy=Cn)
    degree = 1392 if sheared else 1408
    packet = export('norm13_degree'+str(degree), d, output, r,
       dict(exact_degree=degree, norm_degree=32, integral_shear=sheared,
            degree_proof=('Section 8: the biquadratic cleared three-root cut has unique top term of weighted degree348, and two norms give1392.' if sheared else 'The unique highest cleared radicand numerator is H^2*Cy of degree88; its16th power is the unique top part.'),
            semantic_proof='../report/report.pdf'))
    return packet

def make13crt():
    d=DAG(VARS13)
    x={name:d.leaf('variable',name) for name in VARS13}
    p={name:d.leaf('coefficient',name) for name in BASE_PORTS}
    J=6*x['j']+1;q=p['beta']*J+1;W=12*x['w']+4
    X=q*W;Y=q*x['v'];E=X*Y;a=E+Y;H=4*a+3;Delta=a*a+H
    C=x['C'];F=(p['K0']+W)*C-x['z']*(q-1);alpha=q-F-C
    R=(q*(q-F)-C)*(q*q-1)+(p['MC']+q*p['MF'])*J
    k=R+1+x['h']*E;c=x['c'];eta=c-Y*k;zeta=k-eta
    c2=c*c;I=(2*x['r']+1)*c2;I2=I*I;Bstrong=Delta*I2
    Df=1+Bstrong;Q=Delta*Bstrong;delta=Q-1
    V=Df*(c*x['T']-R)-c;Cy=Q*V*V-1
    ell0=E*Y;L=ell0*k;Dtau=ell0*(ell0+1)*(k*k)+1
    Dmain=1+Delta*c2;b0=X+a*c
    coneU=p['cone_A']*F;coneZ=p['cone_B']*C
    G=coneU*coneZ-(q-coneU-coneZ)**2;Peta=eta*zeta
    Pair=G*Peta-(x['t']**2-G-Peta+1)**2
    Ag=x['v']**2*Pair-1-x['p2']**2-x['p3']*(x['p3']+1)
    M=2*(q*q);Lcrt=4*H+1;U=M*H;ML=4*U+M;U2=U*U
    center=U*(x['n']+V)+ML*b0+H*(x['v']-q*q)
    scaled_Df=U2*Df;scaled_Dtau=U2*Dtau;scaled_Dmain=ML*ML*Dmain
    scaled_Ag=U2*Ag;scaled_Cy=U2*Cy
    output=cleared_norm5(center,scaled_Df,scaled_Dtau,scaled_Dmain,
                             scaled_Ag,scaled_Cy,delta)
    registers={name:value for name,value in locals().copy().items() if isinstance(value,Expr)}
    return export('norm13_crt_degree1088',d,output,registers,
      dict(exact_degree=1088,norm_degree=32,crt_carrier=True,
           degree_proof='Independent exact biquadratic cut: degrees [272,258,268,262], then two norms.',
           semantic_proof='../report/report.pdf, section on the coprime carrier'))


def cleared_three_norm(center, A, B, Cn, delta):
    Jn = delta*(center*center-A-B)-Cn
    Tn = delta*delta*A*B
    Rn = delta*Cn
    Kn = Jn*Jn-4*(Tn+Rn*(A+B))
    return Kn*Kn-64*Tn*Rn*center*center

def make15():
    variables = VARS13+['gamma', 'p1']
    d, x, p, r = front(variables)
    # An integral half-centering, not a restriction on the norm coordinate.
    center = x['n']+2*r['V']+2*r['L']+r['k']+2*r['F0']
    N = cleared_three_norm(center, 4*r['Dtau'], 4*r['Df'], 4*r['Cy'], r['delta'])
    main = (r['b0']+x['gamma']*r['H'])**2-r['Dmain']
    guard = r['Ag']-x['p1']**2
    S = main*main+guard*guard
    output = N+S+N*S
    r.update(center=center, norm=N, main_residual=main, guard_residual=guard, S=S)
    return export('norm15_degree344', d, output, r,
                  dict(exact_degree=344, norm_degree=8, norm_exact_degree=256,
                       residual_square_degree=88,
                       semantic_proof='../report/report.pdf'))

def make14(centered=True):
    variables = VARS13+['p1']
    d, x, p, r = front(variables)
    H2 = r['H']*r['H']
    scale2 = 4*H2 if centered else H2
    A = scale2*r['Dtau']; B = scale2*r['Df']; Cn = scale2*r['Cy']
    delta = r['delta']; Dm = 4*r['Dmain'] if centered else r['Dmain']
    if centered:
        center = r['H']*(x['n']+2*r['V']+2*r['L']+r['k']+2*r['F0'])+2*r['b0']
    else:
        center = r['H']*x['n']+r['b0']
    # Cleared F8(center-sqrt(Dm);A,B,Cn/delta), then its conjugate norm.
    q0 = delta*(center*center+Dm-A-B)-Cn
    q1 = -2*delta*center
    Tn = delta*delta*A*B
    Rn = delta*Cn
    t0 = q0*q0+Dm*q1*q1-4*(Tn+Rn*(A+B))
    t1 = 2*q0*q1
    z64 = 64*Tn*Rn
    f0 = t0*t0+Dm*t1*t1-z64*(center*center+Dm)
    f1 = 2*t0*t1+2*z64*center
    N = f0*f0-Dm*f1*f1
    guard = r['Ag']-x['p1']**2
    S = guard*guard
    output = N+S+N*S
    r.update(center=center, norm=N, guard_residual=guard, S=S)
    degree = 696 if centered else 792
    return export('norm14_degree'+str(degree), d, output, r,
                  dict(exact_degree=degree, norm_degree=16,
                       norm_exact_degree=608 if centered else 704, centered=centered,
                       residual_square_degree=88,
                       semantic_proof='../report/report.pdf'))

def load_base_coefficients():
    binding = json.loads((ROOT/'coefficients/BINDING.json').read_text())
    result = {}
    for name in BASE_PORTS:
        rec = binding['payloads'][name]
        raw = gzip.decompress((ROOT/'coefficients'/rec['file']).read_bytes())
        require(hashlib.sha256(raw).hexdigest() == rec['raw_sha256'], 'coefficient '+name)
        result[name] = int.from_bytes(raw, 'little')
        require(result[name].bit_length() == rec['bits'], 'coefficient bits '+name)
    return result

def main():
    (ROOT/'equations').mkdir(exist_ok=True)
    packets = []
    load_base_coefficients()
    for packet in (make13crt(), make13(), make13(False), make14(), make14(False), make15()):
        (ROOT/'equations'/(packet['name']+'.json')).write_text(json.dumps(packet,indent=2)+'\n')
        packets.append({k:packet[k] for k in ('name','variable_count','exact_degree','operations','operation_counts')})
    (ROOT/'equations/METRICS.json').write_text(json.dumps(packets,indent=2)+'\n')
    print(json.dumps(packets,indent=2))

if __name__ == '__main__': main()
