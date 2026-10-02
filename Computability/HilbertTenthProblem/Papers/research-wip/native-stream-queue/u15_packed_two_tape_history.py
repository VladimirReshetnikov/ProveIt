"""Complete fixed-arity U15 halting certificates with paid packed tape typing.

The raw interface takes natural half tapes. The ordinary interface adds the
complete paid binary recoder and four fixed positive program numerals.
All witnesses are strictly positive. Bitwise operations occur only in proof
fixtures; every emitted arithmetic instruction is binary +, - or *.
"""
import argparse
from collections import Counter, defaultdict
from copy import deepcopy
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import native_binary_computed_fields as native
import u15_raw_half_tape_loader as loader

TABLE = '0RB1RA_1RC1RA_0LG0LE_0LF1LE_1RA1LD_1LD1LD_0LH1LG_1LI1LG_0RA1LJ_1LK---_0RL1RN_0RM1RL_0LB1RL_0LC0RO_0RN1RN'
RULES = tuple((q,s,ord(t[2])-65,int(t[1]=='L'),int(t[0]))
    for q,row in enumerate(TABLE.split('_')) for s in (0,1)
    if (t:=row[3*s:3*s+3]) != '---')
assert len(RULES) == 29
HERE = Path(__file__).resolve().parent
NATIVE_DESCRIPTOR_SHA256 = 'd8bc3b92ac1a6715f9afc6df8957b9ef69bcfc2025848be824bae3724c637f49'


def exact(a,b):
    if type(a) is not type(b): return False
    if type(a) is dict:
        return a.keys()==b.keys() and all(type(k) is str and exact(a[k],b[k]) for k in a)
    if type(a) in (tuple,list):
        return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b


def flag(ordinary):
    if type(ordinary) is not bool: raise ValueError('ordinary must be Boolean')
    return ordinary


class DAG:
    def __init__(self): self.rows=[]; self.cache={}; self.powers={0:1,1:'P'}
    def g(self,op,a,b):
        if type(a) is int and type(b) is int:
            return a*b if op=='*' else a+b if op=='+' else a-b
        if op=='*':
            if a==0 or b==0:return 0
            if a==1:return b
            if b==1:return a
        if op=='+' and a==0:return b
        if op in ('+','-') and b==0:return a
        if op=='-' and a==b:return 0
        if op in ('+','*') and repr(b)<repr(a):a,b=b,a
        key=op,a,b
        if key not in self.cache:
            n=f'v{len(self.rows)}';self.rows.append((n,op,a,b));self.cache[key]=n
        return self.cache[key]
    def add(self,*terms):
        out=0
        for t in terms:out=self.g('+',out,t)
        return out
    def mul(self,a,b):return self.g('*',a,b)
    def sub(self,a,b):return self.g('-',a,b)
    def power(self,n):
        if n not in self.powers:
            h=n//2;v=self.mul(self.power(h),self.power(h))
            self.powers[n]=self.mul(v,self.powers[1]) if n%2 else v
        return self.powers[n]
    @lru_cache(None)
    def repunit(self,n):
        if n==1:return 1
        if n%2:return self.add(self.repunit(n-1),self.power(n-1))
        h=n//2;return self.mul(self.repunit(h),self.add(1,self.power(h)))
    def linear(self,weights):
        groups=defaultdict(list)
        for i,c in enumerate(weights):
            if c:groups[c].append(f'edge{i}')
        value=self.add(*(self.mul(c,self.add(*vs)) for c,vs in sorted(groups.items())))
        return self.sub(value,sum(weights))


def execute(source,values):
    env=dict(values)
    for n,op,a,b in source:
        x=env[a] if type(a) is str else a;y=env[b] if type(b) is str else b
        env[n]=x*y if op=='*' else x+y if op=='+' else x-y
    return env


def get(env,v):return env[v] if type(v) is str else v


def raw_build():
    d=DAG();r={};keep=lambda n,v:r.setdefault(n,v)
    J=keep('J',d.sub(d.add(*(f'edge{i}' for i in range(29))),29))
    D=keep('D',d.add('L0','R0','height'))
    B=keep('B',d.mul(64,D));Bm1=keep('Bm1',d.sub(B,1))
    P=keep('P',d.add(d.mul(Bm1,J),1));d.powers[1]=P
    for name,column in (('Q',0),('S',1),('N',2),('Dir',3),('W',4)):
        keep(name,d.linear([t[column] for t in RULES]))
    WD=keep('WD',d.linear([t[3]*t[4] for t in RULES]))
    Lf=keep('Lf',d.sub('Lfhat',1));keep('Rf','Rf')
    T=d.add(d.mul(2,WD),'ZU')
    left=(d.mul(2,d.add(d.sub('H','L0'),d.mul(P,Lf))),
          d.mul(B,d.sub(d.add(d.sub(d.mul(4,'H'),d.mul(3,'ZL')),d.mul(2,r['W'])),T)))
    right=(d.mul(2,d.add(d.sub('G','R0'),d.mul(P,'Rf'))),
           d.mul(B,d.sub(d.add('G',d.mul(3,'ZR'),T),'U')))
    pairs=[left,right,(d.mul(B,r['N']),d.add(r['Q'],d.mul(9,P))),
           (d.mul(B,'U'),d.add(r['S'],P)),
           (d.add('H','G','ZL','ZR','ZU','bound'),P)]
    # Low three regions: two full-cell selections and one Boolean intersection.
    HP=keep('HP',d.add('H',d.mul(P,'G')))
    mask=keep('direction_mask',d.mul(Bm1,r['Dir']))
    range_mask=keep('range_mask',d.mul(d.sub(D,1),J))
    oneP=d.add(1,P)
    Hlow=d.add(HP,d.mul(d.power(2),'U'))
    Mlow=d.add(d.mul(oneP,mask),d.mul(d.power(2),r['Dir']))
    Zlow=d.add('ZL',d.mul(P,'ZR'),d.mul(d.power(2),'ZU'))
    # Next two regions bound both tapes digitwise. The last29 type rule fields.
    K=keep('K29',d.repunit(29))
    packed='edge28'
    for i in range(27,-1,-1):packed=d.add(f'edge{i}',d.mul(P,packed))
    Ec=keep('Ec',d.sub(packed,K));Mc=keep('Mc',d.mul(J,K))
    common=d.add(d.mul(d.power(3),HP),d.mul(d.power(5),Ec))
    Hj=keep('Hjoin',d.add(Hlow,common))
    Mj=keep('Mjoin',d.add(Mlow,d.mul(d.power(3),d.mul(range_mask,oneP)),d.mul(d.power(5),Mc)))
    Zj=keep('Zjoin',d.add(Zlow,common))
    scale=keep('scale',d.mul(B,d.power(34)))
    core=native.build('and',scaled=True,fields=native.VARIANTS['six'])
    descriptor={k:core[k] for k in ('parameters','auxiliaries','source','comparisons')}
    if hashlib.sha256(json.dumps(descriptor,sort_keys=True).encode()).hexdigest()!=NATIVE_DESCRIPTOR_SHA256:
        raise ValueError('Native AND descriptor changed')
    for scaled,padded in (('scaled_A','padded_A'),('scaled_B','padded_B'),('scaled_Z','F3')):
        if [n for n,op,a,b in core['source'] if scaled in (a,b)]!=[padded]:
            raise ValueError('Padded native port no longer private')
    aliases={'P':scale,'Hhat':Hj,'Mhat':Mj,'Zhat':Zj}
    rename=lambda v:aliases.get(v,'native__'+v) if type(v) is str else v
    rows=list(d.rows)
    for n,op,a,b in core['source']:
        # Evaluate the virtual positive arguments Hjoin+1,Mjoin+1,Zjoin+1.
        # Each scaled register has one private consumer, its padded register.
        if n in ('padded_A','padded_B','F3'):
            op='+';b={'padded_A':12,'padded_B':10,'F3':8}[n]
        rows.append(('native__'+n,op,rename(a),rename(b)))
    pairs += [(rename(a),rename(b)) for a,b in core['comparisons']]
    aux=([f'edge{i}' for i in range(29)]
         +['height','H','G','U','ZL','ZR','ZU','Lfhat','Rf','bound']
         +['native__'+n for n in core['auxiliaries']])
    return dict(source=rows,comparisons=pairs,parameters=['L0','R0'],auxiliaries=aux,
        registers=r,ordinary=False,fixed_parameters=[],outer_comparison_count=5,
        native_descriptor_sha256=NATIVE_DESCRIPTOR_SHA256,
        native_packet_sha256=hashlib.sha256(json.dumps(core['source']).encode()).hexdigest(),
        table=TABLE,rules=RULES,scope='Complete first-halt predicate on natural raw half tapes; unbounded duration, fixed arity.')


@lru_cache(None)
def _build(ordinary):
    flag(ordinary);p=raw_build()
    if ordinary:
        load=loader.build(False)
        aliases={'x':'x','L0':'program_L','R0':'input_R0',
                 **{n:n for n in ('program_L','program_A','program_B','program_D')}}
        renamed=lambda v:aliases.get(v,'input__'+v) if type(v) is str else v
        rows=[(renamed(n),op,renamed(a),renamed(b)) for n,op,a,b in load['source']]
        pairs=[(renamed(a),renamed(b)) for a,b in load['comparisons'] if (a,b)!=('L0','program_L')]
        rawalias=lambda v:{'L0':'program_L','R0':'input_R0'}.get(v,v)
        rows += [(n,op,rawalias(a),rawalias(b)) for n,op,a,b in p['source']]
        pairs += [(rawalias(a),rawalias(b)) for a,b in p['comparisons']]
        p.update(source=rows,comparisons=pairs,
            parameters=['x','program_L','program_A','program_B','program_D'],
            auxiliaries=['input_R0']+[renamed(n) for n in load['auxiliaries']]+p['auxiliaries'],
            ordinary=True,fixed_parameters=['program_L','program_A','program_B','program_D'],
            loader_comparison_count=len(load['comparisons'])-1,
            scope='Complete fixed-arity halting polynomial with ordinary positive integer input on the proved four-numeral U15 program slices; arbitrary positive parameter slices are not asserted valid programs.')
    return finish(p)


def finish(p):
    known=set(p['parameters']+p['auxiliaries'])
    assert len(known)==len(p['parameters'])+len(p['auxiliaries'])
    for n,op,a,b in p['source']:
        assert n not in known and op in ('+','-','*')
        assert all(type(v) is int or type(v) is str and v in known for v in (a,b))
        known.add(n)
    assert all(type(v) is int or v in known for pair in p['comparisons'] for v in pair)
    source=list(p['source']);squares=[]
    for i,(a,b) in enumerate(p['comparisons']):
        n=f'poly_res{i}';s=f'poly_sq{i}'
        source += [(n,'-',a,b),(s,'*',n,n)];squares.append(s)
    out=squares[0]
    for i,s in enumerate(squares[1:],1):
        n=f'poly_sum{i}';source.append((n,'+',out,s));out=n
    needed={out}
    for n,op,a,b in reversed(source):
        if n in needed:needed.update(v for v in (a,b) if type(v) is str)
    assert all(n in needed for n,op,a,b in source),'dead emitted arithmetic'
    degrees={n:0 if n in p['fixed_parameters'] else 1 for n in p['parameters']+p['auxiliaries']}
    for n,op,a,b in source:
        da=degrees[a] if type(a) is str else 0;db=degrees[b] if type(b) is str else 0
        degrees[n]=da+db if op=='*' else max(da,db)
    count=lambda rows:dict(operations=len(rows),M=sum(op=='*' for n,op,a,b in rows),
        A=sum(op!='*' for n,op,a,b in rows))
    return dict(p,polynomial_source=source,output=out,ledger=dict(certificate=count(p['source']),
        polynomial=count(source),equations=len(p['comparisons']),positive_witnesses=len(p['auxiliaries']),
        formal_degree_upper_bound=degrees[out],exact_degree_claimed=False))


def build(ordinary=False):return deepcopy(_build(flag(ordinary)))


def checked(packet):
    if type(packet) is not dict:raise ValueError('Complete canonical packet required')
    ordinary=flag(packet.get('ordinary'))
    if not exact(packet,_build(ordinary)):raise ValueError('Noncanonical compiler packet')
    return packet


def assignment(packet,values,signed=False):
    if type(signed) is not bool:raise ValueError('signed must be Boolean')
    names=packet['parameters']+packet['auxiliaries']
    if type(values) is not dict or set(values)!=set(names):raise ValueError('Wrong coordinate set')
    for n,v in values.items():
        if type(n) is not str or type(v) is not int:raise ValueError('Exact integer coordinates required')
        lower=0 if not packet['ordinary'] and n in ('L0','R0') else 1
        if not signed and v<lower:raise ValueError('Coordinate outside declared domain')
    return dict(values)


def evaluate(packet,values,*,signed=False):
    p=checked(packet);v=assignment(p,values,signed)
    return execute(p['polynomial_source'],v)[p['output']]


def trace(L,R,limit=128):
    if any(type(x) is not int or x<0 for x in (L,R,limit)):raise ValueError('Natural tapes and cap required')
    q=s=0;out=[]
    for _ in range(limit+1):
        match=[(i,r) for i,r in enumerate(RULES) if r[:2]==(q,s)]
        if not match:return out,(q,s,L,R)
        if len(out)==limit:return None
        i,(_,_,qn,d,w)=match[0]
        quotient,rem=divmod(L if d else R,2)
        out.append((i,q,s,L,R,d,w,rem,qn))
        L,R=(quotient,2*R+w) if d else (2*L+w,quotient)
        q,s=qn,rem


def outer_fixture(L,R,limit=128):
    result=trace(L,R,limit)
    if result is None:raise ValueError('No halt within fixture cap')
    rows,end=result;t=len(rows);assert t>=4 and end[:2]==(9,1)
    largest=max([L+R]+[v for row in rows for v in row[3:5]]+list(end[2:]))
    D=1<<largest.bit_length();B=64*D;P=B**t
    pack=lambda f:sum(f(row)*B**j for j,row in enumerate(rows))
    p=build();values={n:1 for n in p['parameters']+p['auxiliaries']}
    values.update(L0=L,R0=R,height=D-L-R,H=pack(lambda z:z[3]),G=pack(lambda z:z[4]),
        U=pack(lambda z:z[7]),ZL=pack(lambda z:z[5]*z[3]),ZR=pack(lambda z:z[5]*z[4]),
        ZU=pack(lambda z:z[5]*z[7]),Lfhat=end[2]+1,Rf=end[3])
    values.update({f'edge{i}':1+pack(lambda z:int(z[0]==i)) for i in range(29)})
    values['bound']=P-sum(values[n] for n in ('H','G','ZL','ZR','ZU'))
    assignment(p,values)
    prefix=[row for row in p['source'] if not row[0].startswith('native__')]
    env=execute(prefix,values);reg={n:get(env,v) for n,v in p['registers'].items()}
    assert (reg['B'],reg['P'],reg['D'])==(B,P,D)
    assert reg['Hjoin']&reg['Mjoin']==reg['Zjoin']
    assert max(reg[n] for n in ('Hjoin','Mjoin','Zjoin'))<reg['scale']
    assert all(get(env,a)==get(env,b) for a,b in p['comparisons'][:5])
    return values,dict(t=t,final=end,registers=reg,
        scope='Genuine full outer history and exact joined AND; native Pell coordinates are positive placeholders, not a claimed full zero.')


def verify():
    if not __debug__:raise RuntimeError('Assertions required for research replay')
    rng=random.Random(150229);records=[];counts=Counter()
    primary=loader.nw.transition_table('15,2')
    expected={(int(q[1:])-1,int(s=='b')):(int(n[1:])-1,int(move=='L'),int(w=='b'))
              for (q,s),(n,w,move) in primary.items()}
    assert {(q,s):(n,d,w) for q,s,n,d,w in RULES}==expected
    counts['fixed_primary_table_instructions']=len(expected)
    for ordinary in (False,True):
        p=build(ordinary)
        for i in range(36):
            v={n:rng.randrange(-3,5) if i>=18 else rng.randrange(1,7)
               for n in p['parameters']+p['auxiliaries']}
            env=execute(p['polynomial_source'],v)
            rr=[get(env,a)-get(env,b) for a,b in p['comparisons']]
            assert evaluate(p,v,signed=True)==env[p['output']]==sum(x*x for x in rr)
            counts['complete_literal_SOS_replays']+=1
        bad=deepcopy(p);bad['ledger']['equations']=float(bad['ledger']['equations'])
        try:checked(bad)
        except ValueError:counts['malformed_packets_rejected']+=1
        else:raise AssertionError('Float metadata accepted')
        records.append(dict(ordinary=ordinary,ledger=p['ledger']))
    examples=[]
    for L in range(16):
        for R in range(12):
            t=trace(L,R,40)
            if t is not None:
                v,meta=outer_fixture(L,R,40);counts['genuine_outer_histories']+=1
                p=build();prefix=[r for r in p['source'] if not r[0].startswith('native__')]
                for field in ('H','G','ZL','ZR','ZU','U','Lfhat','Rf'):
                    bad=dict(v);bad[field]+=1;e=execute(prefix,bad)
                    regs={n:get(e,a) for n,a in p['registers'].items()}
                    assert any(get(e,a)!=get(e,b) for a,b in p['comparisons'][:5]) or regs['Hjoin']&regs['Mjoin']!=regs['Zjoin']
                    counts['outer_coordinate_corruptions_rejected']+=1
                if len(examples)<6:examples.append(dict(L=L,R=R,t=meta['t'],final=meta['final']))
    # The failed canonical-only argument has a concrete one-left-move alias.
    B=64;H=B//2;Lf=B//4-1
    assert 2*(H+B*Lf)==B*(H-1) and H>=B//64
    counts['half_radix_alias_excluded_by_range']=1
    for ordinary in (False,True):
        p=build(ordinary);v={n:1 for n in p['parameters']+p['auxiliaries']}
        for n in v:
            for badvalue in (True,1.0,0 if n in p['auxiliaries'] else -1):
                bad=dict(v);bad[n]=badvalue
                try:evaluate(p,bad)
                except ValueError:counts['malformed_assignments_rejected']+=1
                else:raise AssertionError('Bad scalar accepted')
    return dict(status='PASS',counts=dict(counts),ledgers=records,examples=examples,
        complete_raw_compiler=build(),complete_ordinary_compiler=build(True),
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope='Full arithmetic sources and paid mathematical composition; finite outer/AND fixtures do not materialize astronomical native Pell witnesses.')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==json.loads(json.dumps(result))
    print(json.dumps({k:result[k] for k in ('status','counts','ledgers','examples')},indent=2))
