#!/usr/bin/env python3
"""Reproduce the decoder-only work census for the pinned K215 sources.

Independent finite source/trace audit, not a Lean proof or timing benchmark.
Never imports repository generators and writes no repository files.
Usage: python decoder_prefix_census.py REPO [OUTPUT_JSON]
"""
from __future__ import annotations
from collections import Counter
from pathlib import Path
import ast, hashlib, json, re, subprocess, sys

BASE = '2ca3a5c16f0876d2cab842056353c03a1ed2f5f0'
LEANDIR = Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC')
PINS = {
    'K215Decoder.lean': '8663e195ec5a08d1137547eaf7332cfc32ef7c353e473437bbc3fc06cf45c373',
    'KTable215.lean': '429775b1774d41e94ba3b7283f7f50ea45bc13716d4ef27fccffe1f686a8d24c',
}

def array(text: str, name: str):
    return text.split(f'def {name} :', 1)[1].split('#[', 1)[1].split('\n]', 1)[0]

def bits(text: str):
    return ast.literal_eval(text.replace('true', 'True').replace('false', 'False'))

def read_decoder(path: Path):
    text = path.read_text()
    nodes = []
    for line in array(text, 'sourceNodes').splitlines():
        if not line.strip(): continue
        m = re.fullmatch(r'\s*\.(leaf|fork) (\d+) (\d+),?\s*', line)
        assert m, line
        nodes.append((m[1], int(m[2]), int(m[3])))
    blocks = []
    for line in array(text, 'blocks').splitlines():
        if not line.strip(): continue
        m = re.fullmatch(r'\s*⟨(\d+), (\d+), (\[[^]]*\]), (\d+)⟩,?\s*', line)
        assert m, line
        blocks.append((int(m[1]), int(m[2]), bits(m[3]), int(m[4])))
    roles = []
    edge_re = r'\(\.(internal|primitive) (\d+) (\d+|⟨(?:true|false), (?:1|\(-1\)), \d+⟩)\)'
    for line in array(text, 'roles').splitlines():
        if not line.strip(): continue
        m = re.fullmatch(r'\s*⟨(\d+), (\d+), (\[[^]]*\]), (.*)⟩,?\s*', line)
        assert m, line
        edges = re.findall(edge_re, m[4])
        assert len(edges) == 2, line
        roles.append((int(m[1]), int(m[2]), bits(m[3]), [
            (kind, int(a), int(b) if kind == 'internal' else b)
            for kind,a,b in edges]))
    return nodes, blocks, roles

def read_table(path: Path):
    text=path.read_text().split('def table215 :',1)[1].split(':= [',1)[1].split('\n\ndef tm215',1)[0]
    table={}
    q=0
    for line in text.splitlines():
        if not line.strip(): continue
        matches=re.findall(r'none|some \((true|false), (true|false), (\d+)\)',line)
        assert len(matches)==2,(q,line)
        for bit,(w,d,z) in enumerate(matches):
            if w: table[q, bool(bit)] = (w=='true',1 if d=='true' else -1,int(z))
        q+=1
    return table

def verify_local_blocks(blocks, table):
    """Read only assigned cells; require complete restoration and head +1."""
    for q0,q1,word,steps in blocks:
        assert steps>0 and word
        initial = {i-len(word)+1:b for i,b in enumerate(word)}
        tape=initial.copy(); q=q0; head=0
        for _ in range(steps):
            assert head in tape, (q0,q1,word,'unknown cell',head)
            w,d,q=table[q,tape[head]]; tape[head]=w; head+=d
        assert (q,head,tape)==(q1,1,initial)

def traverse(nodes, blocks, roles, table):
    leaves=[]; internal_occurrences=Counter(); role_occurrences=Counter()
    def walk(rid,word,clock):
        node,q,suffix,edges=roles[rid]
        assert (nodes[node][0]=='fork')
        assert suffix == ([True]+word)[-2:]
        role_occurrences[rid]+=1
        for bit,edge in enumerate(edges):
            child=nodes[node][1+bit]
            assert child<node
            kind,a,b=edge
            if kind=='internal':
                target=roles[a]; block=blocks[b]
                assert nodes[child][0]=='fork' and target[0]==child
                assert block[0]==q and block[1]==target[1]
                assert block[2] == (suffix+[bool(bit)])[-len(block[2]):]
                internal_occurrences[b]+=1
                walk(a,word+[bool(bit)],clock+block[3])
            else:
                assert child==a and nodes[a][0]=='leaf'
                action = re.fullmatch(r'⟨(true|false), (1|\(-1\)), (\d+)⟩', b)
                assert action
                assert table[q,bool(bit)] == (action[1]=='true',
                    1 if action[2]=='1' else -1, int(action[3]))
                _,op,arg=nodes[a]
                leaves.append(dict(word=word+[bool(bit)],clock=clock,q=q,
                                   bit=bool(bit),op=op,arg=arg,rid=rid))
    assert roles[0][:3]==(201,84,[True])
    walk(0,[],0)
    return leaves, internal_occurrences, role_occurrences

def verify_leaf_runs(leaves,table):
    """Literal prefix runs; a read outside the known prefix fails the audit."""
    for leaf in leaves:
        word=leaf['word']; initial={-1:True,**dict(enumerate(word))}
        tape=initial.copy(); q=84; head=0
        for _ in range(leaf['clock']):
            assert head in tape, (leaf,'outside prefix',head)
            w,d,q=table[q,tape[head]]; tape[head]=w; head+=d
        assert (q,head,tape)==(leaf['q'],len(word)-1,initial),leaf

def main():
    repo=Path(sys.argv[1]).resolve()
    decoder=repo/LEANDIR/'K215Decoder.lean'; tm=repo/LEANDIR/'KTable215.lean'
    for path in (decoder,tm):
        assert hashlib.sha256(path.read_bytes()).hexdigest()==PINS[path.name], path
    nodes,blocks,roles=read_decoder(decoder);table=read_table(tm)
    verify_local_blocks(blocks,table)
    assert len(table)==430
    leaves,edges,visits=traverse(nodes,blocks,roles,table)
    verify_leaf_runs(leaves,table)
    weights=lambda leaf: 2 if leaf['op']==1 else 1
    opnames={0:'inc',1:'decnz',2:'break',3:'continue',4:'halt'}
    prims=Counter(opnames.get(leaf['op'],'halt') for leaf in leaves)
    interfaces={(x['rid'],x['bit']) for x in leaves}
    shared_families=Counter((x['op'],x['arg'],x['q'],x['bit']) for x in leaves)
    out={
        'status':'FINITE_SOURCE_AND_LITERAL_TRACE_CHECKS_PASS',
        'baseline_commit':BASE,
        'actual_checkout':subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),
        'source_sha256':{str(x.relative_to(repo)):hashlib.sha256(x.read_bytes()).hexdigest() for x in (decoder,tm)},
        'scope':'Decoder prefixes only; no primitive-tail/kernel check or speedup benchmark.',
        'nodes':len(nodes),'blocks':len(blocks),'roles':len(roles),
        'leaf_occurrences':len(leaves),'branch_outcomes':sum(map(weights,leaves)),
        'primitive_leaf_occurrences':dict(prims),'primitive_role_edges':len(interfaces),
        'reachable_role_occurrences':sum(visits.values()),
        'internal_edge_occurrences':sum(edges.values()),
        'one_trace_per_internal_edge_occurrence':sum(blocks[b][3]*n for b,n in edges.items()),
        'one_trace_per_checked_block':sum(b[3] for b in blocks),
        'decoder_prefix_steps_per_leaf_sum':sum(x['clock'] for x in leaves),
        'decoder_prefix_steps_per_branch_sum':sum(x['clock']*weights(x) for x in leaves),
        'decoder_prefix_clock_min':min(x['clock'] for x in leaves),
        'decoder_prefix_clock_max':max(x['clock'] for x in leaves),
        'leaf_path_length_min':min(len(x['word']) for x in leaves),
        'leaf_path_length_max':max(len(x['word']) for x in leaves),
        'branch_prefix_input_bits_sum':sum((len(x['word'])-1)*weights(x) for x in leaves),
        'largest_primitive_families':[
            dict(op=opnames.get(op,'halt'),arg=arg,state=q,bit=bit,occurrences=n)
            for (op,arg,q,bit),n in shared_families.most_common(12)],
        'zero_prefix_clock_occurrences':sum(x['clock']==0 for x in leaves),
    }
    assert out['actual_checkout']==BASE
    assert len(nodes)==202 and len(blocks)==281 and len(roles)==234
    assert len(leaves)==4751 and out['branch_outcomes']==6176
    text=json.dumps(out,indent=2)+'\n'
    if len(sys.argv)>2: Path(sys.argv[2]).write_text(text)
    print(text,end='')

if __name__=='__main__': main()
