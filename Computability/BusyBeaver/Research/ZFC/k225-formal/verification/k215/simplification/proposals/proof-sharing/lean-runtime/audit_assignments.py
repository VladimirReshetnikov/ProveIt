#!/usr/bin/env python3
"""Finite current-source audit of the inherited 1,422 template assignments.

This is evidence for integration, not a proof of all-leaf semantic coverage.
Assertions are not used as validation gates, so python -O cannot disable checks.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re


def require(b, why):
    if not b:
        raise ValueError(why)


def scan_bound(word):
    count = 0
    for b in word:
        count = count + 1 if b == '0' else 0
        if count >= 8:
            return None
    return count


def strip(word, bit, n):
    word = list(word)
    while n and word:
        if word.pop() == bit:
            n -= 1
    return ''.join(word), n


def increment(word):
    out = list(word)
    i = len(out) - 1
    while i >= 0 and out[i] == '1':
        out[i] = '0'
        i -= 1
    if i < 0:
        return ''.join(out), True
    out[i] = '1'
    return ''.join(out), False


def norm(segs):
    out = []
    for s in segs:
        if s[0] == 'x':
            out.append(tuple(s))
            continue
        cur = (s[1], 0, 1) if s[0] == 'b' else (s[1], s[2], s[3])
        if cur[1:] == (0, 0):
            continue
        if out and out[-1][0] == cur[0]:
            old = out.pop()
            cur = (cur[0], old[1] + cur[1], old[2] + cur[2])
        out.append(cur)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--repo', required=True, type=Path)
    ap.add_argument('--output', type=Path, default=Path(__file__).parent/'assignment_audit.json')
    args = ap.parse_args()
    repo = args.repo
    base = repo/'Computability/BusyBeaver/Research/ZFC'
    prior = base/'k225-formal/verification/k215/simplification/proposals/round13-left-frame/runtime'
    inputs = {
        'sites':base/'candidate-k215/sites215.json',
        'assignments':prior/'LEFT_FRAME_DISCOVERY.json',
        'templates':prior/'FORMAL_TEMPLATES.json',
        'decoder':repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/K215Decoder.lean',
        'table':repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KTable215.lean',
    }
    sites = json.loads(inputs['sites'].read_text())
    discovery = json.loads(inputs['assignments'].read_text())
    templates = json.loads(inputs['templates'].read_text())['templates_data']
    decoder = inputs['decoder'].read_text()
    nodes_body = decoder.split('def sourceNodes :',1)[1].split('#[',1)[1].split(']',1)[0]
    nodes = [(kind,int(a),int(b)) for kind,a,b in re.findall(r'\.(leaf|fork) (\d+) (\d+)',nodes_body)]
    roles = []
    for line in decoder.split('def roles : Array Role := #[',1)[1].split('\n\n',1)[0].splitlines():
        if not line.strip() or line.strip()==']':
            continue
        m=re.fullmatch(r'\s*⟨(\d+), (\d+), \[([^]]*)\], (.*)⟩[,\]]*',line)
        require(m is not None,'Unsupported role syntax')
        node,q,context,edges_text=m.groups()
        edges=[]
        for em in re.finditer(r'\(\.internal (\d+) (\d+)\)|\(\.primitive (\d+) ⟨(true|false), (\(?-?1\)?), (\d+)⟩\)',edges_text):
            a,b,n,w,d,z=em.groups()
            edges.append(('internal',int(a),int(b)) if a is not None
                         else ('primitive',int(n),(int(w=='true'),int(d.strip('()')),int(z))))
        require(len(edges)==2,'Role arity')
        ctx=tuple(int(b.strip()=='true') for b in context.split(',') if b.strip())
        roles.append((int(node),int(q),ctx,edges))
    require((len(nodes),len(roles))==(202,234),'Unexpected source/role dimensions')
    body=inputs['table'].read_text().split('def table215 : List (Row × Row) := [',1)[1].split(']\n',1)[0]
    row_text=re.findall(r'none|some \((?:true|false), (?:true|false), \d+\)',body)
    table={}
    for i,row in enumerate(row_text):
        if row=='none':
            continue
        w,d,q=re.fullmatch(r'some \((true|false), (true|false), (\d+)\)',row).groups()
        table[i//2,i%2]=(int(w=='true'),1 if d=='true' else -1,int(q))
    require(len(table)==430,'Expected 430 live formal table rows')
    opcodes={0:'CI',1:'CD',2:'CB',3:'CC',4:'CH'}
    ports={}
    for pc,op,arg in sites:
        rid,node,hist=0,201,(1,)
        for b in map(int,pc[:-1]):
            n,q,ctx,edges=roles[rid]
            require(n==node and ctx==hist[-2:],'Routed prefix mismatch')
            require(nodes[n][0]=='fork','Expected fork')
            edge=edges[b]
            require(edge[0]=='internal','Premature source leaf')
            rid,node,hist=edge[1],nodes[n][1+b],hist+(b,)
        n,q,ctx,edges=roles[rid]
        require(n==node and ctx==hist[-2:],'Routed final role mismatch')
        b=int(pc[-1]);edge=edges[b]
        require(edge[0]=='primitive','Missing primitive entry')
        require(nodes[n][0]=='fork' and nodes[n][1+b]==edge[1],'Source child mismatch')
        kind,code,r=nodes[edge[1]]
        require((kind,opcodes[code],r)==('leaf',op,0 if op=='CH' else arg),'Wrong source action')
        require(table[q,b]==edge[2],'Wrong primitive table row')
        ports[pc]=q
    seen=set();by_op=Counter();by_template=Counter();prefix_zero=0
    for g in discovery['guard_records']:
        site=g['site']; require(site not in seen,'Duplicate source assignment');seen.add(site)
        pc,op,arg=sites[site];t=templates[g['template']]
        key=t['key'];P,S=pc[:g['cut']],pc[g['cut']:]
        require((ports[pc],S,op,arg)==tuple(key[1:5]),'Template entry/source mismatch')
        E,delta=key[6],key[9]
        require(len(pc)<=48 and S,'Bad path bound or empty suffix')
        require(scan_bound(P[::-1])==g['home_scan_bound'],'Invalid Home prefix guard')
        require(t['start']==[ports[pc],False,[['b',int(b)] for b in S[:-1][::-1]],
                [['b',int(S[-1])],['r',0,1,16],['b',1],['x','none',0]]],
                'Wrong symbolic local entry')
        bit='1' if op=='CC' else '0'
        stripped,remaining=strip(S,bit,arg)
        require(remaining==0,'Control action crosses preserved prefix')
        if op=='CC':
            result,overflow=stripped,False
            whole,_=strip(pc,bit,arg)
        else:
            require(op=='CB','Non-control assignment')
            result,overflow=increment(stripped)
            whole=increment(strip(pc,bit,arg)[0])[0]
        require(not overflow and result==E and whole==P+E,'Wrong framed source action')
        require(len(S)-len(E)==delta,'Wrong gap delta')
        require(t['pre_home'][:3]==[2,True,[]],'Wrong Home boundary')
        expected=[['b',int(b)] for b in E]+[['r',0,1,16+delta],['b',1],['x','none',0]]
        require(norm(t['pre_home'][3])==norm(expected),'Wrong symbolic right endpoint')
        by_op[op]+=1;by_template[t['id']]+=1
        prefix_zero+=P.endswith('0')
    controls={i for i,(_,op,_) in enumerate(sites) if op in ('CB','CC')}
    omitted=sorted(controls-seen)
    require(len(seen)==1422 and len(omitted)==3 and len(by_template)==35,'Coverage census changed')
    require([{'site':i,'pc':sites[i][0],'op':sites[i][1],'arg':sites[i][2]} for i in omitted]
            ==discovery['literal_controls'],'Wrong literal fallback family')
    result={'status':'FINITE_ASSIGNMENT_AUDIT_PASS','source_leaves':len(sites),
        'primitive_ports_rebound':len(ports),'formal_table_rows':len(table),
        'template_count':len(templates),'template_uses':len(seen),'uses_by_operation':dict(by_op),
        'uses_by_template':dict(sorted(by_template.items())), 'prefixes_ending_zero':prefix_zero,
        'fallback_controls':discovery['literal_controls'],
        'scope':'Finite exact source/routing/action/gap audit; not a kernel coverage theorem',
        'input_sha256':{k:hashlib.sha256(p.read_bytes()).hexdigest() for k,p in inputs.items()}}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
