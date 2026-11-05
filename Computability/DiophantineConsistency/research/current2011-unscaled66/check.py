#!/usr/bin/env python3
"""Exact shared-factor identity, literal row ledger, and complete degree leader."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
import gzip,hashlib,json
from collections import Counter
from pathlib import Path
HERE=Path(__file__).resolve().parent;TASK=HERE.parents[1]
PARENT=TASK/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
CERT=TASK/'research/fourteen-normalized-product106/CERTIFICATE.json'
P106=TASK/'research/fourteen-normalized-product106/polynomial.json'
GRAPH_SHA='bf9e05905fe84f74edade75ba7d373bd6955aa035867af89a6026d9a21719e75'
PARENT_SHA='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
CERT_SHA='16358ce2d453371d2f2d1cad8ab22136ea61ec9ff77200a55264ad56d4a57879'
def sha(x):return hashlib.sha256(x).hexdigest()
def need(x,msg):
    if not x:raise RuntimeError(msg)
def add(a,b,sign=1):
    c=dict(a)
    for k,v in b.items():
        c[k]=c.get(k,0)+sign*v
        if not c[k]:del c[k]
    return c
def mul(a,b):
    c={}
    for x,u in a.items():
        for y,v in b.items():
            k=tuple(i+j for i,j in zip(x,y));c[k]=c.get(k,0)+u*v
    return {k:v for k,v in c.items() if v}
def atom(i,n):
    x=[0]*n;x[i]=1;return {tuple(x):1}
def const(v,n):return {(0,)*n:v} if v else {}
def decode(rows):return {tuple(e):v for e,v in rows}
def degree(p,nvars):return max(sum(k[:nvars]) for k in p)
def live(rows,out):
    edges={r[0]:r[2:] for r in rows};seen=set();leaves=set();todo=[out]
    while todo:
        n=todo.pop()
        if n in edges and n not in seen:seen.add(n);todo.extend(edges[n])
        elif isinstance(n,str) and n not in edges:leaves.add(n)
    return seen,leaves
def main():
    raw=(HERE/'polynomial.json').read_bytes();old=PARENT.read_bytes();cert=CERT.read_bytes();p106raw=P106.read_bytes()
    need(sha(raw)==GRAPH_SHA and sha(old)==PARENT_SHA and sha(cert)==CERT_SHA,'input hash')
    g=json.loads(raw);p=json.loads(old);c=json.loads(cert);rows=g['source']
    need(sha(p106raw)=='0485cd1e884b918d766261b1780be117238f0813a965c6d8ae4d805176a5f6e1','degree source graph hash')
    p106=json.loads(p106raw)
    need(rows[:51]==p['source'][:51] and rows[50]==['V','-','f2inner','c'],'shared prefix')
    tail=[['i2','*','i','i'],['i2Dc2','*','i2','Dc2'],['strongTerm','*','i2Dc2','c2'],
      ['Z','-','f2','strongTerm'],['auxCoefficient','*','Delta','strongTerm'],
      ['V2','*','V','V'],['y2','*','y','y'],['squareGap','-','V2','y2'],
      ['auxProduct','*','auxCoefficient','squareGap'],['Na','+','auxProduct','y2'],
      ['product0','*','N0','N1'],['product1','*','product0','Na'],
      ['product2','*','product1','Nt'],['product3','*','product2','Z'],['polynomial','-','product3',1]]
    need(rows[51:]==tail and len(rows)==66,'exact tail')
    need(p106['source'][:51]==rows[:51],'degree source shared prefix')
    reference={r[0]:r for r in p106['source']}
    ours={r[0]:r for r in rows}
    for name in ('i2','i2Dc2','V2','y2'):
        need(reference[name]==ours[name],'degree source row '+name)
    need(reference['strong_term']==['strong_term','*','i2Dc2','c2'] and
         reference['Z']==['Z','-','f2','strong_term'] and
         reference['square_gap']==['square_gap','-','V2','y2'],'degree source strong/gap cuts')
    need(g['witnesses']==p['witnesses'] and g['fixed_numerals']==p['fixed_numerals'],'input order')
    need(g['coefficient_binding']==p['coefficient_binding'],'coefficient metadata')
    known=set(g['witnesses']+g['fixed_numerals']);counts=Counter()
    for n,op,x,y in rows:
        need(n not in known and op in ('+','-','*'),'invalid row')
        need(all(isinstance(z,int) or z in known for z in (x,y)),'non-topological row')
        known.add(n);counts[op]+=1
    used,leaves=live(rows,g['output']);need(len(used)==66 and leaves==set(g['witnesses']+g['fixed_numerals']),'dead graph input')
    need(dict(counts)=={'*':38,'+':16,'-':12}==g['operation_counts'],'operation count')
    # Independent exact ring identity on abstract prefix outputs. C represents c².
    P,Q,W,D,F,I,C,V,Y=(atom(i,9) for i in range(9));one=const(1,9)
    st=mul(mul(mul(I,I),mul(D,C)),C)
    s2=mul(mul(I,mul(D,C)),mul(I,mul(D,C)))
    need(s2==mul(D,st),'shared strong term')
    gap=add(V,Y,-1);na=add(mul(s2,gap),Y);prefix=mul(mul(mul(P,Q),na),W)
    parent=add(mul(prefix,add(mul(D,F),s2,-1)),D,-1)
    new=add(mul(prefix,add(F,st,-1)),one,-1)
    need(parent==mul(D,new),'full factor identity')
    bad=add(mul(prefix,add(F,st,-1)),const(2,9),-1)
    need(parent!=mul(D,bad),'wrong final constant control')
    # Complete degree leader, using independently reproduced parent-106
    # certificate's exact component leaders; no Lean degree claim.
    need(c['graph_sha256']=='0485cd1e884b918d766261b1780be117238f0813a965c6d8ae4d805176a5f6e1','degree certificate graph')
    syms=c['degree']['symbols'];need(len(syms)==18 and syms[:14]==g['witnesses'],'degree symbol order')
    leaders={name:decode(c['degree']['all_gate_leaders'][name]['complete_leader']) for name in ('Delta','N0','N1','Nt','Z','square_gap')}
    need([degree(leaders[k],14) for k in ('Delta','N0','N1','Nt','Z','square_gap')]==[12,22,18,2,34,16],'factor leader degree')
    # f² has degree 2, so the leading strongTerm is minus the leading Z.
    strong=mul(const(-1,18),leaders['Z'])
    aux=mul(mul(leaders['Delta'],strong),leaders['square_gap'])
    need(degree(aux,14)==62,'auxiliary leader degree')
    leader=mul(mul(mul(mul(leaders['N0'],leaders['N1']),aux),leaders['Nt']),leaders['Z'])
    need(degree(leader,14)==138,'output degree')
    selected={'J':80,'beta':80,'eta':13,'gamma':1,'i':4,'w':10,'s':23,'T':2,'f':4,'z':1}
    exponent=tuple(selected.get(x,0) for x in syms);need(leader.get(exponent)==-8,'selected nonzero coefficient')
    # No other fixed-port monomial can combine with this witness monomial
    # after specializing the ports, so its coefficient stays -8*beta^80.
    same_witness=[(e,v) for e,v in leader.items() if e[:14]==exponent[:14]]
    need(same_witness==[(exponent,-8)],'fixed-port specialization could cancel selected coefficient')
    portrecords={}
    for name,e in p['coefficient_binding']['ports'].items():
        compressed=(PARENT.parent/'coefficients'/e['file']).read_bytes();need(sha(compressed)==e['gzip_sha256'],'port gzip '+name)
        data=gzip.decompress(compressed);need(sha(data)==e['raw_sha256'] and len(data)==e['raw_bytes'],'port raw '+name)
        portrecords[name]={'raw_sha256':e['raw_sha256'],'bytes':len(data)}
        if name=='beta':need(int.from_bytes(data,'big')>0,'beta nonpositive')
    print(json.dumps({'status':'PASS','checker_sha256':sha(Path(__file__).read_bytes()),
      'graph_sha256':GRAPH_SHA,'parent_sha256':PARENT_SHA,'degree_parent_certificate_sha256':CERT_SHA,
      'operations':dict(counts),'live_gates':66,'live_variables':len(g['witnesses']),'live_integer_ports':len(g['fixed_numerals']),
      'identity':'parent65 = Delta * unscaled66','wrong_constant_control':'rejected',
      'degree':138,'leader_terms':len(leader),'selected_coefficient':'-8*beta^80',
      'selected_unknown_exponents':{k:v for k,v in selected.items() if k in g['witnesses']},
      'port_records':portrecords,'scope':'exact external ring and leader check; no Lean model or iPRA theorem'},indent=2,sort_keys=True))
if __name__=='__main__':main()
