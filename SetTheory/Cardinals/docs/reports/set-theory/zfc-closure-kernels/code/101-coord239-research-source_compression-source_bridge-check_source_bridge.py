#!/usr/bin/env python3
"""Independently extract the exact rotation240 source from pinned Lean text.

Reads the actual row definitions, parses and evaluates the complete rawLookup
conditional tree, then applies the two explicitly parsed wrapper definitions.
Does not import/execute Lean and does not infer data from theorem conclusions.
Only the tiny literal expression grammar below is accepted.
"""
from pathlib import Path
from collections import Counter
import re,json,hashlib,argparse,sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Source checking requires enabled assertions; disable -O and PYTHONOPTIMIZE.')

HERE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--sites',type=Path,default=HERE.parent/'sites_logical.json',
                    help='Exact logical source JSON to compare with the derived leaves.')
parser.add_argument('--output-dir',type=Path,default=HERE,
                    help='Directory for the derived rows and source-bridge receipt.')
args=parser.parse_args()
OUTPUT=args.output_dir
OUTPUT.mkdir(parents=True,exist_ok=True)
PIN='13ec39ed43148b1807f51ed6e6528e1c84659562'
META=json.loads((HERE/'source_fetches.json').read_text())
texts={}
for m in META:
    p=HERE/(m['name']+'.lean');b=p.read_bytes()
    assert m['ref']==PIN and len(b)==m['byte_count']
    assert hashlib.sha256(b).hexdigest()==m['sha256']
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==m['blob_sha']
    texts[m['name']]=b.decode()


def tokens(s,pattern):
    out=[];i=0
    while i<len(s):
        if s[i].isspace():i+=1;continue
        m=re.compile(pattern).match(s,i)
        assert m,('unrecognized literal syntax',s[i:i+80])
        out.append(m.group());i=m.end()
    return out


class Reader:
    def __init__(self,ts):self.ts=ts;self.i=0
    def pop(self,want=None):
        assert self.i<len(self.ts),'truncated expression'
        x=self.ts[self.i];self.i+=1
        assert want is None or x==want,(want,x)
        return x
    def peek(self):return self.ts[self.i]if self.i<len(self.ts)else None
    def done(self):assert self.i==len(self.ts),self.ts[self.i:]


def parse_row(s):
    r=Reader(tokens(s,r'\(|\)|,|\.(?:node|inc|decnz|brk|cont|halt)\b|[0-9]+'))
    def edge():
        if r.peek()=='(':
            r.pop('(');x=edge();r.pop(')');return x
        x=r.pop();assert x.startswith('.')
        k=x[1:];v=None if k=='halt'else int(r.pop())
        return k,v
    r.pop('(');a=edge();r.pop(',');b=edge();r.pop(')');r.done()
    return a,b


base=texts['ProgramRouting245']
row_block=base.split('abbrev Row := Edge × Edge\n',1)[1].split('private def rawLookup',1)[0]
rows={}
for line in row_block.splitlines():
    if not line.strip():continue
    m=re.fullmatch(r'private def row([0-9]{3}) : Row := (.+)',line)
    assert m,('unexpected row declaration',line)
    n=int(m[1]);assert n not in rows;rows[n]=parse_row(m[2])
assert set(rows)==set(range(203))
lookup=base.split('private def rawLookup (n : Nat) : Row :=\n',1)[1].split('\ndef nodes ',1)[0]
r=Reader(tokens(lookup,r'if\b|n\b|<|[0-9]+|then\b|else\b|row[0-9]{3}\b'))

def expr():
    t=r.pop()
    if t.startswith('row'):return ('row',int(t[3:]))
    assert t=='if';r.pop('n');r.pop('<');n=int(r.pop());r.pop('then')
    a=expr();r.pop('else');b=expr();return ('if_lt',n,a,b)

lookup_ast=expr();r.done()
def lookup_index(ast,n):
    if ast[0]=='row':return ast[1]
    return lookup_index(ast[2]if n<ast[1]else ast[3],n)
assert all(lookup_index(lookup_ast,n)==n for n in range(203))
# These exact definition bodies identify the finite function actually used.
nb=base.split('def nodes (n : Nat) : Row :=\n',1)[1].split('\ndef program',1)[0]
assert ' '.join(nb.split())=='if n < 203 then rawLookup n else (.halt, .halt)'
pb=base.split('def program : Program where\n',1)[1].split('\ntheorem ',1)[0]
assert ' '.join(pb.split())=='nodes := nodes root := 202 nnodes := 203'


def wrapper(name,parent,signature,expected_overrides):
    text=texts[name]
    body=text.split('def nodes (n : Nat) : '+signature+' :=\n',1)[1].split('\ndef program',1)[0]
    # The accepted body is a chain of constant-index row overrides ending in
    # exactly the identified parent's nodes function. No wildcards are used.
    rest=' '.join(body.split());overrides={}
    while rest.startswith('if n = ')or rest.startswith('else if n = '):
        rest=rest.removeprefix('else ')
        m=re.match(r'if n = ([0-9]+) then ',rest);assert m
        n=int(m[1]);rest=rest[m.end():]
        row_text,sep,rest=rest.partition(' else ');assert sep
        assert n not in overrides;overrides[n]=parse_row(row_text)
    assert rest==parent+'.program.nodes n',rest
    assert overrides==expected_overrides,overrides
    kind='RegisterPath.Program'if name=='SourceRotation240'else'Program'
    pbody=text.split('def program : '+kind+' where\n',1)[1].split('\ntheorem ',1)[0]
    assert ' '.join(pbody.split())==('nodes := nodes root := '+parent+'.program.root nnodes := '+parent+'.program.nnodes')
    return overrides

rot244=wrapper('ProgramRotation244','ProgramRouting245','Edge × Edge',
               {5:(('decnz',6),('cont',2)),6:(('inc',0),('node',5))})
rot240=wrapper('SourceRotation240','ProgramRotation244','RegisterPath.Edge × RegisterPath.Edge',
               {169:(('inc',5),('node',5))})
a=dict(rows);a.update(rot244);b=dict(a);b.update(rot240)
ops={'inc':'CI','decnz':'CD','brk':'CB','cont':'CC','halt':'CH'}

def expand(program):
    reached=set();leaves=[]
    for n,pair in program.items():
        for op,v in pair:
            if op=='node':assert 0<=v<n,('nondecreasing child',n,v)
            elif op in ('inc','decnz'):assert 0<=v<9
            elif op in ('brk','cont'):assert v>=1
            else:assert (op,v)==('halt',None)
    def visit(n,p):
        reached.add(n)
        for bit,(op,v)in enumerate(program[n]):
            q=p+str(bit)
            if op=='node':visit(v,q)
            else:leaves.append([q,ops[op],v])
    visit(202,'');return leaves,reached

L0,_=expand(rows);L1,_=expand(a);L2,reached=expand(b)
assert (len(L0),len(L1),len(L2))==(6460,6459,6455)
expected=args.sites.read_bytes()
encoded=(json.dumps(L2,indent=2)+'\n').encode()
assert encoded==expected,'derived list is not byte-identical to delivered source'
assert hashlib.sha256(encoded).hexdigest()=='74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d'
assert max(len(x[0])for x in L2)==51
assert sum(2 if x[1]=='CD'else 1 for x in L2)==8386
assert L2[0]==['000','CD',8]
assert len(reached)==202 and set(b)-reached=={4}

(OUTPUT/'rotation240_derived_rows.json').write_text(json.dumps({str(k):v for k,v in b.items()},indent=2)+'\n')
record=dict(status='PASS_INDEPENDENT_PINNED_SOURCE_DERIVATION',repo='VladimirReshetnikov/ProveIt',commit=PIN,
 source_snapshots=META,checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 parsed_literal_rows=203,parsed_raw_lookup=True,lookup_indices_checked=203,
 bounded_nodes_default=['halt','halt'],root=202,nnodes=203,strictly_decreasing_child_indices=True,
 wrapper_overrides={'ProgramRotation244':rot244,'SourceRotation240':rot240},
 expanded_counts={'routed245':len(L0),'rotation244':len(L1),'rotation240':len(L2)},
 reached_nodes=len(reached),unreachable_nodes=sorted(set(b)-reached),maximum_depth=51,
 guarded_cases=8386,first_leaf=L2[0],operation_counts=dict(Counter(x[1]for x in L2)),
 source_byte_equality=True,source_sha256=hashlib.sha256(encoded).hexdigest(),
 scope='Exact ordinary literal-source bridge, extracted from actual definitions at the pinned GitHub commit. No Lean compiler invoked; no source equivalence or consistency theorem re-proved here.')
(OUTPUT/'independent_source_bridge.json').write_text(json.dumps(record,indent=2)+'\n')
print({k:v for k,v in record.items()if k not in ('source_snapshots','wrapper_overrides')})
