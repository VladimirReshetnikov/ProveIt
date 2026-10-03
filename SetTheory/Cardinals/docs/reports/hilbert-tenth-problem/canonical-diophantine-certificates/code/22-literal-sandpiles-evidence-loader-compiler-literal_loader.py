#!/usr/bin/env python3
"""Literal finite generator of the fixed U15 sandpile background and loader.

Newly authored. No geometric routing oracle. An emitted edge comprises seven
axis-parallel segments; periodic_router provides the exact integer coordinates.
The dense table is enormous: generation is streaming and no complete dense
materialization is claimed. Every gate/edge is nonetheless numbered explicitly.
"""
from __future__ import annotations
from collections import Counter
from dataclasses import asdict
from pathlib import Path
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'ca'));sys.path.insert(0,str(ROOT/'geometry'))
import lazy_u15 as ca
from periodic_router import Edge,corners,primitive,port

def require(condition, detail="verification failed"):
    if not condition:
        raise AssertionError(detail)

class Circuit:
    def __init__(self):
        self.ms=[0]*34; self.fs=[0]*34; self.R=0;self.F=0
        for r in ca.iter_rules():
            self.R+=1; self.ms[r.output]+=1
            for _,s in r.inputs:self.fs[s]+=1;self.F+=1
        self.A=self.F-self.R
        self.or_base=[];n=34+self.A
        for m in self.ms:self.or_base.append(n);n+=max(m-1,0)
        self.O=n-(34+self.A)
        self.fork_base=[]
        for f in self.fs:self.fork_base.append(n);n+=max(f-1,0)
        self.K=n-(34+self.A+self.O);self.N=n
        self.M=(self.F-2*self.R)+self.R+self.O+self.K+self.F
        self.B=48*(self.N+1)
        self.P=(7*self.B,4*self.B,336*self.M+84)
    def gates(self):
        yield from ('WIRE' for _ in range(34))
        yield from ('AND' for _ in range(self.A))
        yield from ('OR' for _ in range(self.O))
        yield from ('FORK' for _ in range(self.K))
    def occurrence_source(self,s,j):
        f=self.fs[s]
        if f==1:return s,'R'
        if j<f-1:return self.fork_base[s]+j,'R'
        return self.fork_base[s]+f-2,'B'
    def producer_target(self,s,j):
        m=self.ms[s]
        if m==1:return s,'L'
        if j==0:return self.or_base[s],'L'
        return self.or_base[s]+j-1,'R'
    def edges(self):
        """Edge indices are precisely enumeration order; no adjacency search."""
        ap=34; in_seen=[0]*34; out_seen=[0]*34
        for rule in ca.iter_rules():
            inputs=rule.inputs; k=len(inputs)
            # Temporal incoming edges, in ordered condition order.
            for j,(offset,s) in enumerate(inputs):
                a,pa=self.occurrence_source(s,in_seen[s]);in_seen[s]+=1
                target=ap if j<2 else ap+j-1
                targetport='L' if j==0 else 'R'
                yield Edge(a,pa,target,targetport,-offset,1)
            # Chain the conjunction gates.
            for j in range(k-2):yield Edge(ap+j,'B',ap+j+1,'L')
            b,pb=self.producer_target(rule.output,out_seen[rule.output]);out_seen[rule.output]+=1
            yield Edge(ap+k-2,'B',b,pb)
            ap+=k-1
        require(ap == 34 + self.A and in_seen == self.fs and (out_seen == self.ms), 'literal_loader.py: invariant at original line 66')
        # OR producer chains and state roots.
        for s,m in enumerate(self.ms):
            if m>=2:
                base=self.or_base[s]
                for j in range(m-2):yield Edge(base+j,'B',base+j+1,'L')
                yield Edge(base+m-2,'B',s,'L')
        # All ports of each FORK are one undirected state signal.
        for s,f in enumerate(self.fs):
            if f>=2:
                base=self.fork_base[s]
                yield Edge(s,'R',base,'L')
                for j in range(f-2):yield Edge(base+j,'B',base+j+1,'L')
    def manifest(self):
        Hmax=336*self.M+52
        # Every route has <= 2Hmax+4B+32 edges. This is an upper bound,
        # uniform in all edge labels and all source residues.
        Rmax=2*Hmax+4*self.B+32
        primitive_sites=25*34+41*(self.A+self.O)+37*self.K
        primitive_chips=125*34+202*self.A+203*self.O+185*self.K
        return dict(active_states=34,rules=self.R,input_occurrences=self.F,
                    gate_counts=dict(WIRE=34,AND=self.A,OR=self.O,FORK=self.K),
                    gates=self.N,edges=self.M,macrocell_side=self.B,
                    periods=self.P,max_wire_height=Hmax,
                    max_route_edges=Rmax,
                    primitive_sites_per_macrocell=primitive_sites,
                    primitive_chips_per_macrocell=primitive_chips,
                    support_sites_per_period_upper=28*(primitive_sites+self.M*(Rmax-1)),
                    dense_period_table_sites=self.P[0]*self.P[1]*self.P[2],
                    m_s=self.ms,f_s=self.fs)

def kind_at(c, i):
    if not 0 <= i < c.N:
        raise ValueError("primitive index out of range")
    if i < 34: return 'WIRE'
    if i < 34+c.A: return 'AND'
    if i < 34+c.A+c.O: return 'OR'
    return 'FORK'

def edge_at(c, index):
    """Explicit bounded enumeration, not a routing or graph oracle."""
    if not 0 <= index < c.M:
        raise ValueError("edge index out of range")
    for e, edge in enumerate(c.edges()):
        if e == index: return edge
    raise RuntimeError("edge count mismatch")

def modular_segment_contains(point, a, b, periods):
    """Exact integer membership even for a segment crossing a period seam."""
    for x, lo, hi, period in zip(point, a, b, periods):
        lo,hi=min(lo,hi),max(lo,hi)
        # Some x+k*period lies in the closed integer interval [lo,hi].
        if -((x-lo)//period) > (hi-x)//period:
            return False
    return True

def background_height(point, circuit=None):
    """Literal periodic coefficient evaluator on all integer Z^3.

    At most two complete edge-generator scans (2M records), 7 segment tests,
    and one <=41-site primitive lookup. The expensive fixed scan is charged,
    not an unspecified background oracle. No dense table is materialized.
    """
    c=circuit or Circuit()
    if len(point)!=3 or any(type(v) is not int for v in point):
        raise ValueError("expected three integer coordinates")
    x,y,z=(point[i]%c.P[i] for i in range(3))
    xl,yl=x%c.B,y%c.B;j=xl//48
    if z==0:
        if j>=c.N:return 0
        return primitive(kind_at(c,j)).get((xl-24-48*j,yl-24,0),0)
    if z>336*c.M+52:return 0
    # The only vertical supports are unique shafts at the primitive ports.
    tag=None
    if j<c.N:
        if xl%48==12 and yl==24:tag='L'
        elif xl%48==36 and yl==24:tag='R'
        elif xl%48==24 and yl==12 and kind_at(c,j)!='WIRE':tag='B'
    if tag is not None:
        for e,edge in enumerate(c.edges()):
            source=None
            if (edge.a,edge.ap)==(j,tag):source=(x//c.B,y//c.B)
            elif (edge.b,edge.bp)==(j,tag):source=(x//c.B-edge.dx,y//c.B-edge.dt)
            if source is not None:
                H=64+12*(e+c.M*((source[0]%7)+7*(source[1]%4)))
                if z<=H:return 5
                break
    # A routing plane identifies its exact edge label and source residues.
    if z>=64 and (z-64)%12==0:
        number=(z-64)//12;e=number%c.M;residue=number//c.M
        if residue<28:
            edge=edge_at(c,e)
            cs=corners(c.N,c.M,e,edge,residue%7,residue//7)
            for a,b in zip(cs,cs[1:]):
                if modular_segment_contains((x,y,z),a,b,c.P):return 5
    return 0

def loader_height(point,ell,r,circuit=None):
    return int(tuple(point) in set(tape_pair_loader(ell,r,circuit)))


def tape_pair_loader(ell:str,r:str,circuit=None):
    """Both tape halves nearest-head-first; head A scanning blank0 at0.

    A fully binary input format is 1^len(ell) 0 ell r. Decoding is separate
    in decode_binary_input and does not require a program-to-U15 compiler.
    """
    if any(x not in '01' for x in ell+r):raise ValueError('nonbinary tape')
    c=circuit or Circuit();a=-len(ell);b=len(r)
    L=min(-3,a-1);R=max(3,b+1)
    tape={-i-1:int(v) for i,v in enumerate(ell)}
    tape.update({i+1:int(v) for i,v in enumerate(r)})
    seeds=[]
    for x in range(L,R+1):
        s=ca.FL if x==L else ca.FR if x==R else ca.head('A',0) if x==0 else tape.get(x,0)
        # Midpoint of one state WIRE, not an attached port or gate center.
        seeds.append((x*c.B+24+48*s,24,0))
    return seeds

def decode_binary_input(word:str):
    if any(x not in '01' for x in word):raise ValueError('nonbinary input')
    j=word.find('0')
    if j<0 or len(word)<2*j+1:raise ValueError('expected 1^k 0 ell[k] r')
    return word[j+1:2*j+1],word[2*j+1:]

def load_binary_input(word:str,circuit=None):
    return tape_pair_loader(*decode_binary_input(word),circuit=circuit)

def audit(c):
    """Exhaustively checks all six million edge incidences in bit storage."""
    used=bytearray(c.N); counts=Counter();digest=hashlib.sha256()
    def mask(kind,p):
        if kind=='WIRE':require(p in ('L', 'R'), 'literal_loader.py: invariant at original line 128')
        else:require(p in ('L', 'R', 'B'), 'literal_loader.py: invariant at original line 129')
        return {'L':1,'R':2,'B':4}[p]
    def kind(i):
        if i<34:return 'WIRE'
        if i<34+c.A:return 'AND'
        if i<34+c.A+c.O:return 'OR'
        return 'FORK'
    count=0
    for e in c.edges():
        require(e.dt in (0, 1) and (e.dx == 0 if e.dt == 0 else -2 <= e.dx <= 2), 'literal_loader.py: invariant at original line 138')
        for i,p in ((e.a,e.ap),(e.b,e.bp)):
            require(0 <= i < c.N, 'literal_loader.py: invariant at original line 140')
            bit=mask(kind(i),p);require(not used[i] & bit, (i, p))
            used[i]|=bit
        counts['temporal' if e.dt else 'internal']+=1
        digest.update(f'{e.a},{e.ap},{e.b},{e.bp},{e.dx},{e.dt}\n'.encode())
        count+=1
    require(count == c.M, 'literal_loader.py: invariant at original line 146')
    for i,m in enumerate(used):require(m == (1 if i == ca.HALT else 3 if i < 34 else 7), (i, m))
    return dict(edge_count=count,edge_types=dict(counts),one_incidence_per_port=True,
                all_required_ports_filled=True,unused_port='final state WIRE.R only',
                canonical_edges_sha256=digest.hexdigest())

if __name__=='__main__':
    c=Circuit();out=c.manifest()
    if '--audit' in sys.argv:out['exhaustive_port_audit']=audit(c)
    (ROOT/'compiler'/'circuit_manifest.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('m_s','f_s')},indent=2))
