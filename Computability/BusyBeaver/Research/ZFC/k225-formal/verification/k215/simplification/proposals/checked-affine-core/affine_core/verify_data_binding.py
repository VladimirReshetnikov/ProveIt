#!/usr/bin/env python3
"""Independent parser checks the actual printed Coq literals against inputs.

This parser does not import either generator.  Logical source/graph adequacy is
proved in SourceGraphBridge and checked concretely by K215GraphBinding.
"""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parent

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

class Literal:
    def __init__(self,text,name):
        m=re.search(r'Definition\s+'+re.escape(name)+r'\b[^=]*:=\s*(.*?)\.\s',text,re.S)
        if not m:
            raise ValueError(f'Missing definition {name}')
        body=m.group(1)
        token=re.compile(r'%positive|%N|[0-9]+|[A-Za-z_]+|[()\[\];,]')
        self.ts=token.findall(body)
        if re.sub(r'\s+','',token.sub('',body)):
            raise ValueError('Unrecognized Coq literal text')
        self.i=0
    def pop(self,want=None):
        got=self.ts[self.i];self.i+=1
        if want is not None and got!=want:
            raise ValueError((want,got,self.i))
        return got
    def integer(self,scope=None):
        n=int(self.pop())
        if scope:self.pop(scope)
        return n
    def arc(self):
        self.pop('(');self.pop('Arc');v=self.integer('%N');self.pop('[')
        inc=[]
        while self.ts[self.i]!=']':
            if inc:self.pop(';')
            self.pop('(');r=self.integer();self.pop(',');k=self.integer();self.pop(')')
            inc.append([r,k])
        self.pop(']');self.pop(')')
        return [v,inc]
    def node(self):
        if self.ts[self.i]=='Halt':
            self.pop();return {'op':['halt'],'successors':[]}
        self.pop('(');self.pop('Test');r=self.integer();a=self.arc();b=self.arc();self.pop(')')
        return {'op':['decnz',r],'successors':[a,b]}
    def tree(self,kind):
        if self.ts[self.i]=='Empty':
            self.pop();return {}
        self.pop('(');self.pop('Branch');left=self.tree(kind);k=self.integer('%N')
        value=self.node() if kind=='node' else self.integer('%positive' if kind=='positive' else None)
        right=self.tree(kind);self.pop(')')
        if k in left or k in right or left.keys() & right.keys():
            raise ValueError('Duplicate tree key')
        if any(v>=k for v in left) or any(v<=k for v in right):
            raise ValueError('Unsorted binary search tree')
        return left | {k:value} | right
    def done(self):
        if self.i!=len(self.ts):raise ValueError('Unparsed tokens')

graph_text=(ROOT/'K215DrainData.v').read_text()
binding_text=(ROOT/'K215GraphBinding.v').read_text()
rawG={int(k):v for k,v in json.loads((ROOT/'input_graph.json').read_text()).items()}
rawRanks={int(k):v for k,v in json.loads((ROOT/'drain_ranks.json').read_text()).items()}
rawLeaves=json.loads((ROOT/'leaves.json').read_text())

p=Literal(graph_text,'k215_tree');G=p.tree('node');p.done()
if G!=rawG:raise ValueError('Printed graph differs from JSON')
p=Literal(graph_text,'rank_tree');ranks=p.tree('nat');p.done()
if ranks!=rawRanks:raise ValueError('Printed ranks differ from JSON')

for side in ['source','reference']:
    p=Literal(binding_text,'locations_'+side);L=p.tree('positive');p.done()
    if L.keys()!=G.keys():raise ValueError('Incomplete location domain')
    for v,c in L.items():
        bits=[]
        while c>1:
            bits.append(str(c%2));c//=2
        if c!=1 or ''.join(bits)!=rawLeaves[side][v][0]:
            raise ValueError('Bad path code at '+str((side,v)))
        if G[v]['op']!=rawLeaves[side][v][1]:
            raise ValueError('Bad operation label at '+str((side,v)))

result={'status':'PASS','graph_vertices':len(G),'rank_records':len(ranks),
        'source_addresses':len(G),'reference_addresses':len(G),
        'checks':['exact printed graph versus JSON','exact rank table versus JSON',
                  'unique sorted keys in all balanced trees','complete address domains',
                  'every decoded source/reference path and operation'],
        'files':{n:sha(ROOT/n) for n in ['input_graph.json','drain_ranks.json','leaves.json',
                                       'K215DrainData.v','K215GraphBinding.v']}}
(ROOT/'data_binding.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
