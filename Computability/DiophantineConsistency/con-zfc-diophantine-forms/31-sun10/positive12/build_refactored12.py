"""Exact refactor of ProveIt package 30, with literal binary-operation accounting.

No root extraction, division, or resultant is a primitive operation.
Run with Python 3.10+; only the standard library is needed.
"""
import gzip
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PIN = '8c6eec9d19ef80538c8e61ff6e0180040583446a'
WITNESSES = ['J', 'F', 'alpha', 'z', 'h', 'i', 'T', 's', 'w', 'eta', 'zeta', 't']
PORTS = ['beta', 'K0', 'MC', 'MF']

class Circuit:
    def __init__(self):
        self.rows, self.cache = [], {}

    def op(self, op, x, y, name=None):
        key = (op, *sorted((x, y), key=str)) if op in ('+', '*') else (op, x, y)
        if key in self.cache:
            return self.cache[key]
        name = name or 'g' + str(len(self.rows) + 1)
        self.rows.append([name, op, x, y])
        self.cache[key] = name
        return name

    def add(self, x, y, name=None): return self.op('+', x, y, name)
    def sub(self, x, y, name=None): return self.op('-', x, y, name)
    def mul(self, x, y, name=None): return self.op('*', x, y, name)
    def sq(self, x, name=None): return self.mul(x, x, name)

def make(kind):
    if kind not in ('product108', 'system103', 'shifted_system102'):
        raise ValueError(kind)
    shifted = kind == 'shifted_system102'
    c = Circuit()
    a, s, m, q = c.add, c.sub, c.mul, c.sq
    qm1=m('beta','J','qm1'); qq=a(qm1,1,'q'); q2=q(qq,'q2'); q3=m(q2,qq,'q3')
    X=m('w',qq,'X'); Y=m('s',q3,'Y'); E=m(X,Y,'E'); k=a('eta','zeta','k')
    kY=m(k,Y,'kY'); ell=m(E,kY,'ell'); A=a(m(ell,a(ell,k)),1,'A')
    cc=a(kY,'eta','c'); av=a(E,Y,'a'); H=a(m(4,av),3,'H')
    Delta=a(q(av),H,'Delta'); c2=q(cc,'c2'); G=a(m(Delta,c2),1,'G')
    b0=a(X,m(av,cc),'b0'); qF=s(qq,'F','qF'); Cw=s(qF,'alpha','Cw')
    R=a(m(a(m(qm1,qF),'alpha'),s(q2,1)),m(a('MC',m(qq,'MF')),'J'),'R')
    Nk=s(s(k,m('h',E)),R,'Nk')
    transport_left=m(a('K0','w'),Cw,'transport_left')
    zterm=m('z',qm1,'zterm')
    if shifted:
        transport_right=a('F',zterm,'transport_right')
    else:
        Nt=s(a(transport_left,qF),zterm,'Nt')
    I=m('i',c2,'I'); I2=q(I,'I2'); Dm1=m(Delta,I2,'Dm1'); D=a(Dm1,1,'D')
    Q=m(Delta,Dm1,'Q'); d=s(Q,1,'d'); T2=q('T','T2'); v2=m(c2,T2,'v2')
    b=a(cc,m(R,D),'b'); M=m(k,a(I2,T2),'M'); HM=m(H,M,'HM')
    L=a(HM,1,'L'); W=a(b0,m(H,'t'),'W'); H2=q(H,'H2')
    # Share H^2 Q before forming both auxiliary terms.
    H2Q=m(H2,Q,'H2Q'); HP=m(H2Q,m(D,v2),'HP'); HU=m(H2Q,q(b),'HU')
    n=m(q(HM),A,'n'); dn=m(d,n,'dn'); He=s(a(HP,HU),H2,'He')
    j=m(4,m(HP,HU),'j'); W2=q(W,'W2'); L2G=m(q(L),G,'L2G')
    Trace=m(2,m(d,a(W2,L2G)),'Trace')
    # d^2 (W^2-L^2 G)^2 = [d(W^2-L^2 G)]^2.
    rootK=m(d,s(W2,L2G),'rootK'); Knorm=q(rootK,'Knorm')
    AA=m(2,a(dn,He),'AA'); constant=s(q(s(dn,He)),j,'constant')
    at=s(Trace,AA,'at'); bt=s(constant,Knorm,'bt'); coef=m(16,m(dn,j),'coef')
    vr=s(m(at,a(m(at,Trace),m(2,bt))),coef,'vr')
    # u is the negative of package 30's ur.
    u=s(m(q(at),Knorm),q(bt),'u')
    left=m(u,s(m(Trace,vr),u),'norm_left'); right=m(Knorm,q(vr),'norm_right')
    packet=dict(name=kind,witnesses=WITNESSES,fixed_numerals=PORTS,
                domain='strictly positive integers',source_commit=PIN,
                coefficient_binding_file='../COEFFICIENT_BINDING.json',
                coefficient_binding_path_base='directory containing this generated JSON',
                active_instance='wang943-mixed-121x8801',
                proof='../REFACTORED12_PROOF.md')
    if kind == 'product108':
        N=s(right,left,'N')
        out=s(m(m(Nk,Nt),a(N,1)),1,'polynomial')
        packet.update(output=out, exact_degree=1081,
                      relation_to_source='Identical four-port polynomial template to package 30 positive12_product; all four fixed coefficients are rebound by the complete new adapter.')
    else:
        transport=[transport_left,transport_right] if shifted else [Nt,1]
        packet.update(comparisons=[[Nk,1],transport,[right,left]],
                      exact_residual_degrees=[7,2,1072],
                      transport_coordinate='z_old=z+1' if shifted else 'unchanged')
    packet['source']=c.rows
    packet['ledger']=dict(operations=len(c.rows),
                         multiplications=sum(r[1]=='*' for r in c.rows),
                         additions_subtractions=sum(r[1]!='*' for r in c.rows))
    expected={'product108':108,'system103':103,'shifted_system102':102}[kind]
    if len(c.rows)!=expected:
        raise RuntimeError((kind,len(c.rows),expected))
    return packet

def main():
    output=HERE/'generated'
    output.mkdir(exist_ok=True)
    for kind in ('product108','system103','shifted_system102'):
        packet=make(kind)
        (output/(kind+'.json')).write_text(json.dumps(packet,indent=2)+'\n')
        print(kind,packet['ledger'])
    canonical=HERE.parent/'coefficients/COEFFICIENT_BINDING.json'
    binding=json.loads(canonical.read_text())
    if binding['instance']!='wang943-mixed-121x8801':
        raise RuntimeError('Unexpected active coefficient instance')
    aliases={'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'}
    files={}
    for port,payload in aliases.items():
        record=next(r for r in binding['files'] if r['port']==payload)
        path=HERE.parent/'coefficients'/record['file']
        raw=gzip.decompress(path.read_bytes())
        if hashlib.sha256(raw).hexdigest()!=record['sha256']:
            raise RuntimeError('Bad active coefficient bytes: '+port)
        files[port]=dict(record,path='../coefficients/'+record['file'])
    active=dict(schema='complete-fixed-instance-binding-v1',instance=binding['instance'],
                canonical_binding='../coefficients/COEFFICIENT_BINDING.json',
                path_base='directory containing this binding JSON',
                coefficient_files=files,port_aliases=aliases,
                adapter_proof='../coefficients/COEFFICIENT_PROOF.md',
                fixed_coefficient_scope='The complete 121x8801 tuple is active. The historical source tuple inside upstream/ remains evidence only.',
                mask_convention='MF is MF_source, already shifted by B-1.')
    (HERE/'COEFFICIENT_BINDING.json').write_text(json.dumps(active,indent=2)+'\n')

if __name__=='__main__':
    main()
