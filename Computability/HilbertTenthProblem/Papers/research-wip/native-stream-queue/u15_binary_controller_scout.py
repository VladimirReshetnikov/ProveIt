"""Complete scalar U15 controller scout; no packed multiplication claim.

verify(wip_root) reads one hash-pinned table module as AST data and returns a
portable deterministic receipt. No author module is executed. By default the
CLI compares its sibling JSON; --write is the only receipt-writing mode.
"""
from __future__ import annotations
import argparse
import ast
from collections import Counter
from copy import deepcopy
from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path

PARENT = 'neary_woods_explicit_universal_tm.py'
PARENT_SHA256 = '0a0f970df8dcf4dca5f8d105908b06f82fefb3e1948198ca2692fcb97b5da0e5'
ENCODING = (0,15,14,1,4,12,9,13,6,5,2,11,8,10,3)
ORDER = (0,1,2,3,4)
LITERAL = ('0RB1RA','1RC1RA','0LG0LE','0LF1LE','1RA1LD',
           '1LD1LD','0LH1LG','1LI1LG','0RA1LJ','1LK---',
           '0RL1RN','0RM1RL','0LB1RL','0LC0RO','0RN1RN')
if not __debug__:
    raise RuntimeError('The research verifier requires assertions enabled.')

VARIABLES = ('b0','b1','b2','b3','b4','state','next_state','write','left')


def rules():
    out = {}
    for q, row in enumerate(LITERAL):
        for s in (0,1):
            tok = row[3*s:3*s+3]
            if tok != '---':
                out[q,s] = (ord(tok[2])-65, int(tok[0]), int(tok[1]=='L'))
    return out


class DAG:
    def __init__(self):
        self.ops = []
        self.memo = {}

    def op(self, op, a, b):
        if op in ('+','*') and repr(a)>repr(b):
            a,b = b,a
        if type(a) is int and type(b) is int:
            return {'+':lambda:a+b, '-':lambda:a-b, '*':lambda:a*b}[op]()
        if op=='*':
            if a==0 or b==0:return 0
            if a==1:return b
            if b==1:return a
        if op=='+':
            if a==0:return b
            if b==0:return a
        if op=='-':
            if b==0:return a
            if a==b:return 0
        key = op,a,b
        if key not in self.memo:
            name = 'v'+str(len(self.ops))
            self.memo[key]=name
            self.ops.append((name,op,a,b))
        return self.memo[key]

    def mux(self,x,lo,hi):
        if lo==hi:return lo
        if lo==0:return self.op('*',x,hi)
        if hi==0:return self.op('*',self.op('-',1,x),lo)
        if lo==1:return self.op('-',1,self.op('*',x,self.op('-',1,hi)))
        if hi==1:return self.op('+',lo,self.op('*',x,self.op('-',1,lo)))
        return self.op('+',lo,self.op('*',x,self.op('-',hi,lo)))

    def sum(self,xs):
        out=0
        for x in xs:out=self.op('+',out,x)
        return out

    def prod(self,xs):
        out=1
        for x in xs:out=self.op('*',out,x)
        return out


def _lookup(d, encoding=ENCODING, order=ORDER):
    values = [None]*32
    for (q,s),(r,w,left) in rules().items():
        values[encoding[q]+16*s] = (encoding[r],w,left)
    idx = [sum(((i>>j)&1)<<v for j,v in enumerate(order)) for i in range(32)]
    memo={}
    def rec(seq,level):
        seq=tuple(seq)
        present=[v for v in seq if v is not None]
        if not present:return 0
        if len(set(present))==1:return present[0]
        key=level,seq
        if key in memo:return memo[key]
        lo,hi=seq[::2],seq[1::2]
        if all(v is None for v in lo):out=rec(hi,level+1)
        elif all(v is None for v in hi):out=rec(lo,level+1)
        else:out=d.mux('b'+str(order[level]),rec(lo,level+1),rec(hi,level+1))
        memo[key]=out
        return out
    return [rec([None if values[i] is None else values[i][j] for i in idx],0)
            for j in range(3)]


def _scalar(positive=False):
    d=DAG()
    lookup=_lookup(d)
    lookup_gates=len(d.ops)
    comp=[d.op('-',1,'b'+str(i)) for i in range(5)]
    typing=[d.op('*','b'+str(i),comp[i]) for i in range(5)]
    # Unused code7 and halt code5 share b0=1,b2=1,b3=0.
    # Thus the guard is b0*b2*(1-b3)*(b1+(1-b1)*read).
    unused=next(c for c in range(16) if c not in ENCODING)
    halt=ENCODING[9]
    common=[]; u=[]; h=[]
    for i in range(4):
        ub=(unused>>i)&1; hb=(halt>>i)&1
        ul='b'+str(i) if ub else comp[i]
        hl='b'+str(i) if hb else comp[i]
        (common if ub==hb else u).append(ul)
        if ub!=hb:h.append(hl)
    bad=d.op('*',d.prod(common),d.op('+',d.prod(u),d.op('*',d.prod(h),'b4')))
    code='b3'
    for i in (2,1,0):code=d.op('+',d.op('*',2,code),'b'+str(i))
    residuals=[d.op('-',code,'state'),d.op('-',lookup[0],'next_state'),
               d.op('-',lookup[1],'write'),d.op('-',lookup[2],'left'),bad]
    out=d.sum([d.op('*',r,r) for r in residuals])
    for t in typing:out=d.op('-',out,t)
    ops=list(d.ops)
    if positive:
        ops=[(v,'-',v+'_hat',1) for v in VARIABLES]+ops
    return dict(kind='scalar_positive' if positive else 'scalar_integer',
                inputs=[v+'_hat' for v in VARIABLES] if positive else list(VARIABLES),
                witnesses=[('b'+str(i))+('_hat' if positive else '') for i in range(4)],
                encoding=list(ENCODING), order=list(ORDER), source=ops, output=out,
                lookup=lookup, lookup_gates=lookup_gates, guard=bad,
                bit_terms=typing, residuals=residuals,
                relations='five squared residuals plus five consecutive-integer products')


def _onehot(positive=False):
    d=DAG(); rs=list(sorted(rules().items())); names=['e'+str(i) for i in range(29)]
    state_groups=[]
    for q in range(15):state_groups.append(d.sum([names[i] for i,((a,s),o) in enumerate(rs) if a==q]))
    # Factor the source-state projection and the checksum through the same groups.
    source=d.sum([d.op('*',ENCODING[q],state_groups[q]) for q in range(15)])
    checksum=d.sum(state_groups)
    target_groups=[]
    for q in range(15):target_groups.append(d.sum([names[i] for i,((a,s),(r,w,left)) in enumerate(rs) if r==q]))
    target=d.sum([d.op('*',ENCODING[q],target_groups[q]) for q in range(15)])
    def boolean_column(index):
        chunks=[]
        for q in range(15):
            indices=[i for i,((a,s),o) in enumerate(rs) if a==q]
            chosen=[i for i in indices if ((rs[i][0][1] if index==0 else rs[i][1][index])==1)]
            chunks.append(state_groups[q] if chosen==indices else d.sum([names[i] for i in chosen]))
        return d.sum(chunks)
    read=boolean_column(0);write=boolean_column(1);left=boolean_column(2)
    forms=[source,read,target,write,left]
    params=['state','b4','next_state','write','left']
    if positive:
        weights=[sum(ENCODING[q] for (q,s),o in rs),sum(s for (q,s),o in rs),
                 sum(ENCODING[r] for k,(r,w,l) in rs),sum(w for k,(r,w,l) in rs),sum(l for k,(r,w,l) in rs)]
        residuals=[d.op('-',checksum,30)]
        residuals += [d.op('-',d.op('+',f,1-c),p+'_hat') for f,c,p in zip(forms,weights,params)]
    else:
        residuals=[d.op('-',checksum,1)] + [d.op('-',f,p) for f,p in zip(forms,params)]
    out=d.sum([d.op('*',r,r) for r in residuals])
    # In positive mode e_i itself denotes e_i^hat: the affine constants above
    # implement the exact substitution without paying 29 separate subtractions.
    used={out}
    for name,op,a,b in reversed(d.ops):
        if name in used:used.update(x for x in (a,b) if type(x) is str)
    live=[row for row in d.ops if row[0] in used]
    return dict(kind='onehot_positive' if positive else 'onehot_natural',
                inputs=names+[p+'_hat' if positive else p for p in params],
                witnesses=names, encoding=list(ENCODING), source=live, output=out,
                residuals=residuals, relations='six squared residuals')


def exact_same(a,b):
    if type(a) is not type(b):return False
    if isinstance(a,dict):return a.keys()==b.keys() and all(exact_same(a[k],b[k]) for k in a)
    if isinstance(a,(tuple,list)):return len(a)==len(b) and all(exact_same(x,y) for x,y in zip(a,b))
    return a==b


@lru_cache(None)
def _canonical(kind):
    if kind=='scalar_integer':return _scalar(False)
    if kind=='scalar_positive':return _scalar(True)
    if kind=='onehot_natural':return _onehot(False)
    if kind=='onehot_positive':return _onehot(True)
    raise ValueError('unknown form')


def build(kind='scalar_integer'):
    if type(kind) is not str:raise TypeError('kind must be exact str')
    return deepcopy(_canonical(kind))


def checked(packet):
    if type(packet) is not dict or type(packet.get('kind')) is not str:
        raise TypeError('canonical packet required')
    if not exact_same(packet,_canonical(packet['kind'])):
        raise ValueError('noncanonical packet')
    return packet


def _execute(packet,values):
    env=dict(values)
    def value(x):return x if type(x) is int else env[x]
    for name,op,a,b in packet['source']:
        x,y=value(a),value(b)
        env[name] = x+y if op=='+' else x-y if op=='-' else x*y
    return env


def execute(packet,values):
    checked(packet)
    if type(values) is not dict or values.keys()!=set(packet['inputs']):
        raise ValueError('exact input dictionary required')
    if any(type(x) is not int for x in values.values()):
        raise TypeError('exact integer coordinates required')
    if packet['kind'].endswith('positive') and any(x<=0 for x in values.values()):
        raise ValueError('strictly positive coordinates required')
    if packet['kind']=='onehot_natural' and any(x<0 for x in values.values()):
        raise ValueError('natural coordinates required')
    return _execute(packet,values)


def ledger(packet):
    checked(packet)
    counts=Counter(r[1] for r in packet['source'])
    seen=set(packet['inputs']);used={packet['output']}
    for name,op,a,b in packet['source']:
        assert name not in seen
        assert all(type(x) is int or x in seen for x in (a,b))
        seen.add(name)
    for name,op,a,b in reversed(packet['source']):
        if name in used:used.update(x for x in (a,b) if type(x) is str)
    assert all(r[0] in used for r in packet['source'])
    return dict(operations=len(packet['source']),multiplications=counts['*'],
                additions_subtractions=counts['+']+counts['-'],
                witnesses=len(packet['witnesses']),full_source_live=True)


def symbolic_degree(packet):
    # Exact sparse expansion over Q; no estimated degree propagation.
    import sympy as sp
    symbols=dict(zip(packet['inputs'],sp.symbols(' '.join(packet['inputs']))))
    env=_execute(packet,symbols)
    poly=sp.Poly(env[packet['output']],*symbols.values())
    degree=poly.total_degree()
    leading=[(mon,int(coef)) for mon,coef in poly.terms() if sum(mon)==degree]
    return dict(exact_degree=degree,terms=len(poly.terms()),
                leading_term_count=len(leading),leading_example=leading[0],
                expanded_terms_sha256=hashlib.sha256(repr(poly.terms()).encode()).hexdigest())


def verify(wip_root):
    data=(Path(wip_root)/PARENT).read_bytes()
    assert hashlib.sha256(data).hexdigest()==PARENT_SHA256
    tree=ast.parse(data)
    tables=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign)
                and any(isinstance(t,ast.Name) and t.id=='TABLES' for t in n.targets))
    imported={}
    for read,row in tables['15,2'].items():
        for q,tok in enumerate(row.split()):
            if tok!='-':imported[q,int(read=='b')]=(int(tok[2:])-1,int(tok[0]=='b'),int(tok[1]=='L'))
    assert imported==rules() and len(imported)==29
    kinds=('scalar_integer','scalar_positive','onehot_natural','onehot_positive')
    packets={kind:build(kind) for kind in kinds}
    p=packets['scalar_integer']; pp=packets['scalar_positive']
    table_cases=0; zeros=0; wrong_states=0; mutations=0
    # Every five-bit input against every physically typed output tuple.
    for code in range(16):
        bits={f'b{i}':(code>>i)&1 for i in range(4)}
        for read in (0,1):
            key=(ENCODING.index(code),read) if code in ENCODING else None
            expected=imported.get(key)
            for r,w,left in itertools.product(range(16),range(2),range(2)):
                v=dict(bits,b4=read,state=code,next_state=r,write=w,left=left)
                out=execute(p,v)[p['output']]
                good=expected is not None and (r,w,left)==(ENCODING[expected[0]],expected[1],expected[2])
                assert (out==0)==good and out>=0
                vp={k+'_hat':x+1 for k,x in v.items()}
                assert execute(pp,vp)[pp['output']]==out
                table_cases+=1;zeros+=good
                if good:
                    for param in ('state','next_state','write','left'):
                        for delta in (-1,1):
                            bad=dict(v);bad[param]+=delta
                            assert execute(p,bad)[p['output']]>0
                            wrong_states+=1
    assert zeros==29
    # All untyped signed bit assignments in a box, with outputs set to the
    # actual emitted lookup. This gives a particularly strong adversary because
    # the four interface residuals vanish by construction.
    signed=0;signed_zeros=0
    for bs in itertools.product(range(-2,4),repeat=5):
        v=dict(zip(('b0','b1','b2','b3','b4'),bs));v.update(state=0,next_state=0,write=0,left=0)
        env=_execute(p,v)
        v.update(state=sum((1<<i)*bs[i] for i in range(4)),
                 next_state=env[p['lookup'][0]],write=env[p['lookup'][1]],left=env[p['lookup'][2]])
        out=execute(p,v)[p['output']]
        assert out>=sum(b*(b-1) for b in bs)>=0
        if out==0:
            assert all(b in (0,1) for b in bs)
            signed_zeros+=1
        signed+=1
    assert signed_zeros==29
    # Actual one-hot zero graph and the compressed positive substitution.
    hotcases=0
    for j,((q,s),(r,w,left)) in enumerate(sorted(imported.items())):
        v={f'e{i}':int(i==j) for i in range(29)}
        v.update(state=ENCODING[q],b4=s,next_state=ENCODING[r],write=w,left=left)
        assert execute(packets['onehot_natural'],v)[packets['onehot_natural']['output']]==0
        pv={k:(x+1) for k,x in v.items() if k.startswith('e')}
        pv.update({k+'_hat':v[k]+1 for k in ('state','b4','next_state','write','left')})
        assert execute(packets['onehot_positive'],pv)[packets['onehot_positive']['output']]==0
        hotcases+=1
    # Strict type and canonical-source rejection, including Python's int==float.
    def rejects(f):
        try:f()
        except (ValueError,TypeError,KeyError):return
        raise AssertionError('malformed object accepted')
    for kind in kinds:
        base=packets[kind]
        for idx,row in enumerate(base['source']):
            for j in (2,3):
                if type(row[j]) is int:
                    bad=deepcopy(base); rr=list(bad['source'][idx]);rr[j]=float(rr[j]);bad['source'][idx]=tuple(rr)
                    rejects(lambda bad=bad:checked(bad));mutations+=1
        bad=deepcopy(base);bad['encoding'][0]=float(bad['encoding'][0]);rejects(lambda:checked(bad));mutations+=1
        bad=deepcopy(base);bad['source']=tuple(bad['source']);rejects(lambda:checked(bad));mutations+=1
        fresh=build(kind);fresh['encoding'][0]=99
        assert build(kind)['encoding'][0]==0
        good={v:1 for v in base['inputs']}
        for key in good:
            for value in (True,1.0):
                bad=dict(good);bad[key]=value
                rejects(lambda bad=bad,base=base:execute(base,bad));mutations+=1
    # Signed positive-shift identity as literal polynomials; validation is
    # intentionally bypassed only for this exact symbolic internal audit.
    import sympy as sp
    syms=dict(zip(VARIABLES,sp.symbols(' '.join(VARIABLES))))
    a=_execute(p,syms)[p['output']]
    b=_execute(pp,{k+'_hat':x+1 for k,x in syms.items()})[pp['output']]
    assert sp.expand(a-b)==0
    degrees={kind:symbolic_degree(packet) for kind,packet in packets.items()}
    assert degrees['scalar_integer']['exact_degree']==10
    assert degrees['scalar_positive']['exact_degree']==10
    assert degrees['onehot_natural']['exact_degree']==degrees['onehot_positive']['exact_degree']==2
    return dict(status='PASS',parent=dict(path=PARENT,sha256=PARENT_SHA256),
                state_order='ABCDEFGHIJKLMNO',encoding=list(ENCODING),halt=['J',1],unused=7,
                counts=dict(imported_rules=29,typed_table_output_cases=table_cases,exact_zeros=zeros,
                            wrong_endpoint_adversaries=wrong_states,signed_bit_adversaries=signed,
                            signed_zeros=signed_zeros,onehot_true_rows=hotcases,rejected_guards=mutations),
                ledgers={kind:ledger(packet) for kind,packet in packets.items()},
                degrees=degrees,packets=packets,
                scope='Complete scalar one-step graph only; runtime unrolling grows. No packed or universal total count; onehot counts describe this grouped literal baseline, not a minimum.')


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--write',action='store_true')
    args=ap.parse_args();result=verify(args.root)
    path=Path(__file__).with_suffix('.json')
    wire=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if args.write:path.write_text(wire)
    else:assert exact_same(json.loads(path.read_text()),json.loads(wire))
    print(json.dumps(dict(status=result['status'],counts=result['counts'],ledgers=result['ledgers']),sort_keys=True))


if __name__=='__main__':main()
