"""Owned exact native/formal table, routing and trace-label audit."""
if not __debug__:
    raise RuntimeError('Assertions must be enabled')
import hashlib,json,re
from pathlib import Path
import check_framed_templates as F
D=Path(__file__).parent
rename=lambda q:{301:102,302:120,254:230}.get(q,q)
s=(D/'reference/KTable215.lean').read_text()
body=s.split('def table215 : List (Row × Row) := [',1)[1].split(']\n',1)[0]
rows=re.findall(r'none|some \((?:true|false), (?:true|false), \d+\)',body)
assert len(rows)%2==0
formal={}
for i,row in enumerate(rows):
    if row=='none':continue
    w,dr,z=re.fullmatch(r'some \((true|false), (true|false), (\d+)\)',row).groups()
    formal[i//2,i%2]=(int(w=='true'),1 if dr=='true'else -1,int(z))
assert len(formal)==len(F.T)==430
assert formal=={(rename(q),b):(w,d,rename(z))for(q,b),(w,d,z)in F.T.items()}
# Rebind the inherited native port map to the current formal RoutedEntry data.
decoder=(D/'reference/K215Decoder.lean').read_text()
nodes_text=decoder.split('def sourceNodes :',1)[1].split('#[',1)[1].split(']',1)[0]
nodes=[(k,int(a),int(b))for k,a,b in re.findall(r'\.(leaf|fork) (\d+) (\d+)',nodes_text)]
roles=[]
for line in decoder.split('def roles : Array Role := #[',1)[1].split('\n\n',1)[0].splitlines():
    if not line.strip()or line.strip()==']':continue
    m=re.match(r'\s*⟨(\d+), (\d+), \[([^]]*)\], (.*)⟩[,\]]*',line);assert m
    node,q,ctx,es=m.groups();edges=[]
    for e in re.finditer(r'\(\.internal (\d+) (\d+)\)|\(\.primitive (\d+) ⟨(true|false), (\(?-?1\)?), (\d+)⟩\)',es):
        a,b,n,w,dr,z=e.groups()
        edges.append(('internal',int(a),int(b))if a is not None else('primitive',int(n),(int(w=='true'),int(dr.strip('()')),int(z))))
    assert len(edges)==2
    roles.append((int(node),int(q),tuple(int(b.strip()=='true')for b in ctx.split(',')if b.strip()),edges))
assert(len(nodes),len(roles))==(202,234)
ops={0:'CI',1:'CD',2:'CB',3:'CC',4:'CH'}
sites=json.loads((F.OLD/'inputs/K215_Formal.sites.json').read_text());ports=json.loads((F.OLD/'PORT_BINDING.json').read_text())['ports']
for pc,op,arg in sites:
    rid=0;node=201;hist=(1,)
    for b in map(int,pc[:-1]):
        n,q,ctx,es=roles[rid];assert n==node and ctx==hist[-2:]
        assert nodes[n][0]=='fork';edge=es[b];assert edge[0]=='internal'
        rid=edge[1];node=nodes[n][1+b];hist+=(b,)
    n,q,ctx,es=roles[rid];assert n==node and ctx==hist[-2:]
    bit=int(pc[-1]);edge=es[bit];assert edge[0]=='primitive'
    assert nodes[n][0]=='fork'and nodes[n][1+bit]==edge[1]
    kind,code,r=nodes[edge[1]]
    assert(kind,ops[code],r)==('leaf',op,0 if op=='CH'else arg)
    assert formal[q,bit]==edge[2]and q==rename(ports[pc])
# Translate EVERY state occurrence, not only template entry states.
x=json.loads((D/'LEFT_FRAME_DISCOVERY.json').read_text());seen=set();translated=[];count=0
conf=lambda s:(rename(s[0]),s[1],tuple(tuple(z)for z in s[2]),tuple(tuple(z)for z in s[3]))
for template in x['templates_data']:
    nt=dict(template);nt['key']=list(template['key']);nt['key'][1]=rename(nt['key'][1])
    nt['start']=conf(template['start']);nt['pre_home']=conf(template['pre_home']);nt['trace']=[]
    for e in template['trace']:
        seen.update((e['before'][0],e['after'][0]));before=conf(e['before']);after=conf(e['after'])
        got,m,kind=F.A.step(formal,None,before)
        assert got==after and m==e['moved'] and kind==e['kind'];count+=1
        nt['trace'].append(dict(before=before,after=after,moved=m,kind=kind))
    translated.append(nt)
(D/'FORMAL_TEMPLATES.json').write_text(json.dumps(dict(state_labels='Maintained KTable215 labels',native_to_formal={301:102,302:120,254:230},templates_data=translated),separators=(',',':')))
result=dict(status='EXACT_FORMAL_LABEL_BINDING_PASS',table_rows=430,source_ports_rebound=len(sites),templates=35,trace_steps_translated_and_rechecked=count,native_special_states_encountered=sorted(seen&{301,302,254}),state_mapping={301:102,302:120,254:230},formal_table_sha256=hashlib.sha256(s.encode()).hexdigest(),decoder_sha256=hashlib.sha256(decoder.encode()).hexdigest(),scope='Owned finite parsed equality and translated step replay; not kernel compilation.')
(D/'LABEL_MAPPING.json').write_text(json.dumps(result,indent=2));print(result)
