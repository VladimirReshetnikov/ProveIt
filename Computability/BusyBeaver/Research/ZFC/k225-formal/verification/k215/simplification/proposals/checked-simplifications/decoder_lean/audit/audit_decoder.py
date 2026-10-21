#!/usr/bin/env python3
"""Independent data binding and malformed controls; no generator imports.
This ordinary audit complements, but is not itself, Lean kernel verification.
"""
import argparse, copy, hashlib, json, re
from pathlib import Path

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def parse_action(s):
    m=re.fullmatch(r'⟨(true|false),\s*(\(-1\)|-?\d+),\s*(\d+)⟩',s.strip())
    assert m,s
    return (int(m[1]=='true'),int(m[2].strip('()')),int(m[3]))
def native_table(p):
    t={}
    for line in p.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        assert d in ('L','R') and b in (0,1) and w in (0,1)
        assert (q,b) not in t
        t[q,b]=(w,1 if d=='R' else -1,z)
    assert len(t)==430
    return t

def lean_table(s):
    a=s.split('def nativeRows : Array (Option (Action × Action)) := #[',1)[1].split('\n]',1)[0]
    t={}
    for q,line in enumerate(a.strip().splitlines()):
        line=line.strip().removesuffix(',')
        if line=='none':continue
        m=re.fullmatch(r'some \((⟨[^⟩]+⟩), (⟨[^⟩]+⟩)\)',line);assert m,line
        t[q,0]=parse_action(m[1]);t[q,1]=parse_action(m[2])
    return t

def lean_nodes(s):
    a=s.split('def sourceNodes : Array Node := #[',1)[1].split('\n]',1)[0]
    ops=['CI','CD','CB','CC','CH'];out=[]
    for line in a.strip().splitlines():
        m=re.fullmatch(r'\.(leaf|fork) (\d+) (\d+),?',line.strip());assert m,line
        a,b=int(m[2]),int(m[3])
        out.append([ops[a],None if ops[a]=='CH' else b] if m[1]=='leaf' else [a,b])
    return out

def lean_blocks(s):
    a=s.split('def blocks : Array Block := #[',1)[1].split('\n]',1)[0];out=[]
    for line in a.strip().splitlines():
        m=re.fullmatch(r'⟨(\d+), (\d+), \[([^]]*)\], (\d+)⟩,?',line.strip());assert m,line
        word=''.join('1' if x.strip()=='true' else '0' for x in m[3].split(',')) if m[3] else ''
        assert all(x.strip() in ('true','false') for x in m[3].split(','))
        out.append({'entry':int(m[1]),'exit':int(m[2]),'word':word,'steps':int(m[4])})
    return out

def lean_roles(s):
    a=s.split('def roles : Array Role := #[',1)[1].split('\n]',1)[0];out=[]
    edge=r'\(\.(?:internal \d+ \d+|primitive \d+ ⟨(?:true|false), (?:\(-1\)|-?\d+), \d+⟩)\)'
    for line in a.strip().splitlines():
        m=re.fullmatch(r'⟨(\d+), (\d+), \[([^]]*)\], ('+edge+'), ('+edge+')⟩,?',line.strip());assert m,line
        suffix=''.join('1' if x.strip()=='true' else '0' for x in m[3].split(',')) if m[3] else ''
        es=[]
        for e in [m[4],m[5]]:
            mi=re.fullmatch(r'\(\.internal (\d+) (\d+)\)',e)
            if mi:es.append({'kind':'internal','role':int(mi[1]),'block':int(mi[2])})
            else:
                mp=re.fullmatch(r'\(\.primitive (\d+) (⟨[^⟩]+⟩)\)',e);assert mp,e
                es.append({'kind':'primitive','node':int(mp[1]),'action':list(parse_action(mp[2]))})
        out.append({'node':int(m[1]),'state':int(m[2]),'suffix':suffix,'edges':es})
    return out

def structure(t,nodes,roles,blocks,root):
    if not roles or (roles[0]['node'],roles[0]['state'],roles[0]['suffix'])!=(root,84,'1'):return False
    for r in roles:
        if not 1<=len(r['suffix'])<=2:return False
        if not 0<=r['node']<len(nodes):return False
        n=nodes[r['node']]
        if isinstance(n[0],str):return False
        for bit,e in enumerate(r['edges']):
            child=n[bit]
            if not 0<=child<r['node'] or child>=len(nodes):return False
            cn=nodes[child]
            if e['kind']=='primitive':
                if not isinstance(cn[0],str) or e['node']!=child or tuple(e['action'])!=t.get((r['state'],bit)):return False
            else:
                if isinstance(cn[0],str) or not 0<=e['role']<len(roles) or not 0<=e['block']<len(blocks):return False
                sr=roles[e['role']];b=blocks[e['block']];w=r['suffix']+str(bit)
                suffix=w[len(w)-len(b['word']):]
                if not (sr['node']==child and sr['suffix']==w[-2:] and b['entry']==r['state'] and b['exit']==sr['state'] and len(b['word'])<=len(w) and b['word']==suffix):return False
    return True

def expand(nodes,i,p=''):
    n=nodes[i]
    if isinstance(n[0],str):return [[p,*n]]
    assert 0<=n[0]<i and 0<=n[1]<i
    return expand(nodes,n[0],p+'0')+expand(nodes,n[1],p+'1')

def replay(t,b):
    if not b['word'] or b['steps']<=0:return 'empty_or_nonpositive'
    initial={i-len(b['word'])+1:int(v) for i,v in enumerate(b['word'])}
    cells=initial.copy();q=b['entry'];h=0
    for i in range(b['steps']):
        if h not in cells:return 'read_unspecified_cell'
        if (q,cells[h]) not in t:return 'undefined_transition'
        w,d,q=t[q,cells[h]];cells[h]=w;h+=d
    if q!=b['exit']:return 'wrong_exit'
    if h!=1:return 'wrong_head'
    if cells!=initial:return 'tape_not_restored'
    return 'pass'

def main():
    p=argparse.ArgumentParser();p.add_argument('decoder_root',type=Path);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    root=a.decoder_root; inp=root/'inputs';s=(root/'K215Decoder.lean').read_text()
    cert=json.loads((inp/'decoder_context_certificate.json').read_text());gen=json.loads((root/'generation.json').read_text())
    t=native_table(inp/'k215.native.tm'); lt=lean_table(s);assert t==lt
    states={q for q,b in t};assert len(states)==215 and 254 not in states
    assert all(z in states or z==254 for w,d,z in t.values())
    nodes=lean_nodes(s);assert nodes==cert['nodes']
    sites=json.loads((inp/'sites215.json').read_text());assert expand(nodes,cert['source_root'])==sites
    blocks=lean_blocks(s);assert len(blocks)==281
    roles=lean_roles(s);assert len(roles)==len(cert['roles'])==234
    for r,old in zip(roles,cert['roles']):
        assert (r['node'],r['state'],r['suffix'])==(old['node'],old['state'],old['suffix'])
        for e,oe in zip(r['edges'],old['edges']):
            assert e['kind']==oe['kind']
            if e['kind']=='primitive':assert e==oe
            else:
                assert e['role']==oe['role'] and blocks[e['block']]['steps']==oe['steps']
    assert structure(t,nodes,roles,blocks,cert['source_root'])
    assert cert['root_role']==0
    reachable=set();todo=[0]
    while todo:
        i=todo.pop()
        if i in reachable:continue
        reachable.add(i)
        todo += [e['role'] for e in roles[i]['edges'] if e['kind']=='internal']
    assert len(reachable)==len(roles)
    structural_controls={}
    def bad(name,mutate,expect=False):
        ns,rs,bs=copy.deepcopy((nodes,roles,blocks));mutate(ns,rs,bs)
        accepted=structure(t,ns,rs,bs,cert['source_root'])
        assert accepted==expect,(name,accepted)
        structural_controls[name]={'structure_accepts':accepted,'expected':expect}
    bad('empty_root_suffix',lambda ns,rs,bs:rs[0].update(suffix=''))
    bad('wrong_root_state',lambda ns,rs,bs:rs[0].update(state=0))
    bad('out_of_range_target_role',lambda ns,rs,bs:rs[0]['edges'][0].update(role=999))
    bad('out_of_range_block',lambda ns,rs,bs:rs[0]['edges'][0].update(block=999))
    bad('nondecreasing_root_child',lambda ns,rs,bs:ns[201].__setitem__(0,201))
    bad('wrong_primitive_action',lambda ns,rs,bs:rs[2]['edges'][0].update(action=[0,1,999]))
    bad('wrong_primitive_node',lambda ns,rs,bs:rs[2]['edges'][0].update(node=1))
    # These controls deliberately illustrate obligations not enforced by structureCheck.
    bad('zero_steps_requires_separate_block_check',lambda ns,rs,bs:bs[0].update(steps=0),True)
    bad('leaf_semantics_not_checked_here',lambda ns,rs,bs:ns[0].__setitem__(1,999),True)
    bad('duplicate_roles_not_forbidden',lambda ns,rs,bs:rs.append(copy.deepcopy(rs[1])),True)
    assert blocks==[{k:b[k] for k in ('entry','exit','word','steps')} for b in gen['blocks']]
    valid=[replay(t,b) for b in blocks];assert all(x=='pass' for x in valid)
    controls={}
    for name,modify in [('drop_leftmost_cell',lambda b:{**b,'word':b['word'][1:]}),
                        ('wrong_exit',lambda b:{**b,'exit':999}),
                        ('one_fewer_step',lambda b:{**b,'steps':b['steps']-1}),
                        ('zero_duration',lambda b:{**b,'steps':0})]:
        results=[replay(t,modify(b)) for b in blocks]
        assert all(x!='pass' for x in results),(name,results)
        controls[name]={'tested':len(results),'rejected':len(results),
                        'reasons':{x:results.count(x) for x in sorted(set(results))}}
    first={**blocks[0],'word':'1'};r=replay(t,first);assert r!='pass'
    controls['first_block_wrong_scanned_bit']={'tested':1,'rejected':1,'reason':r}
    result={'status':'PASS','native_rows_bound':len(t),'working_states':len({q for q,b in t}),
            'lean_nodes_bound':len(nodes),'expanded_occurrences_bound':len(sites),
            'local_blocks_bound_and_replayed':len(blocks),'lean_roles_bound':len(roles),'root_reachable_roles':len(reachable),
            'internal_edges':sum(e['kind']=='internal' for r in roles for e in r['edges']),
            'primitive_edges':sum(e['kind']=='primitive' for r in roles for e in r['edges']),
            'structural_controls':structural_controls,
            'window_width_counts':{str(k):sum(len(b['word'])==k for b in blocks) for k in (1,2,3)},
            'malformed_controls':controls,
            'hashes':{str(p.relative_to(root)):digest(p) for p in (root/'FramedWindow.lean',root/'DecoderCertificate.lean',root/'generate_data.py',root/'K215Decoder.lean',root/'generation.json',inp/'k215.native.tm',inp/'sites215.json',inp/'decoder_context_certificate.json')},
            'scope':'Independent ordinary binding/replay; no full source path/runtime/ZFC endpoint and no additional kernel claim.'}
    a.out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='hashes'},indent=2))
if __name__=='__main__':main()
