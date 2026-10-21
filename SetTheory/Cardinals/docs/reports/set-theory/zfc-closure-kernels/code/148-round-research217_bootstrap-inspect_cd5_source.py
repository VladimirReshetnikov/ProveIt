#!/usr/bin/env python3
"""Owned exact CD5-role binding, invariant transport, and three local prices."""
from pathlib import Path
import hashlib,json,sys
D=Path(__file__).resolve().parent
ROOT=D.parent
sys.path.insert(0,str(ROOT/'research218_published_encoding'))
import audit_construction as A
P=A.P
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=ROOT/'latest218_baseline/candidate-k218/sites218.json'
oldsource=ROOT/'latest219_baseline/candidate-k219/sites219.json'
sites=json.loads(source.read_text());oldsites=json.loads(oldsource.read_text())
root=P.tree(sites);oldroot=P.tree(oldsites)
assert [s[1:]for s in sites]==[s[1:]for s in oldsites]
cfg=A.continuation_cfg(root)
assert cfg==A.continuation_cfg(oldroot)
facts_path=ROOT/'research218_source/invariant_facts.json'
facts=json.loads(facts_path.read_text())
assert H(facts_path)=='df0c94f02523d79569949ae1a33b4b289cec515edaef4e2f9d1068086d2475b4'
def bucket(n):return n if n<8 else 8+n%2
def image(mask,delta):
    result=0
    for atom in range(10):
        if not(mask>>atom&1):continue
        samples=[atom]if atom<8 else[atom,atom+2]
        for n in samples:
            if n+delta>=0:result|=1<<bucket(n+delta)
    return result
seed=[3,0,0,0,3,0,0,0,0]
assert all(facts[0][i]>>bucket(v)&1 for i,v in enumerate(seed))
enabled=0;excluded=[]
for i,(op,arg,targets)in enumerate(cfg):
    if not targets:continue
    st=facts[i]
    for which,target in enumerate(targets):
        if st is None:excluded.append([i,which]);continue
        out=st.copy()
        if op=='CI':out[arg]=image(out[arg],1)
        elif op=='CD':
            selected=out[arg]&(~1 if which==1 else 1)
            if not selected:excluded.append([i,which]);continue
            out[arg]=image(selected,-1)if which==1 else 1
        assert facts[target]is not None and all(a&~b==0 for a,b in zip(out,facts[target]))
        enabled+=1
assert enabled==6161 and len(excluded)==5 and facts[4609]is not None

E=A.at(root,'11110')
assert E==A.at(oldroot,'111110')
roles=[]
for start,end,name,meaning in [
    (4567,4576,'AX gate: c=b','Compare b=h+y with selector payload c; clear top when equal.'),
    (4585,4594,'AX gate: c=a','Compare a=d+x with retained c; clear top when equal.'),
    (4599,4608,'NIP','Compare incoming cache h with one; halt exactly on equality.'),
    (4708,4717,'MP','Compare incoming cache h with implication(top,d+x); select MP success.')]:
    p=sites[start][0][:-3]
    assert A.at(root,p)==E
    assert [i for i,s in enumerate(sites)if s[0].startswith(p)]==list(range(start,end+1))
    roles.append(dict(name=name,meaning=meaning,macro_path=p,indices=[start,start+5],
                      first_cd5_old_decoder_role=301,cleanup_cd5_old_decoder_role=88,
                      first_cd5_facts=facts[start],cleanup_cd5_facts=facts[start+5]))

nip_path='110100101';nip=A.at(root,nip_path)
assert nip[0]==('CI',6) and nip[1][0]==(E,('CH',None))
D5=('CD',5);D6=('CD',6);B=('CB',1);Halt=('CH',None)
U=(D5,((D5,('CC',1)),B));special=((D5,(U,Halt)),nip[1][1])
variants=[('nip_special',A.replace(root,nip_path,special),
           'Requires scratch6=0 at NIP entry; keeps the h=1 halting case.'),
          ('nip_preserve_equality',A.replace(root,nip_path,((D5,(E,Halt)),nip[1][1])),
           'Requires scratch6=0 at NIP entry; keeps the h=1 halting case.'),
          ('nip_skip_zero6_cleanup',A.replace(root,nip_path+'10011',B),
           'Requires scratch6=0 at this cleanup entry, established by the transported invariant.')]
assert A.at(root,nip_path+'10011')==((D6,('CC',2)),B)
# A fourth, genuinely guarded proposal uses the selector register, which is
# zero at every equality entry. Transfer first; the renamed equality clears it.
assert all(facts[r['indices'][0]][3]==1 for r in roles)
def rename_5_to_3(n):
    if P.leaf(n):return (n[0],3 if n[0] in ('CD','CI') and n[1]==5 else n[1])
    return (rename_5_to_3(n[0]),rename_5_to_3(n[1]))
via3=((D5,(('CI',3),('CC',2))),rename_5_to_3(E))
def replace_equality(n):
    if n==E:return via3
    if P.leaf(n):return n
    return (replace_equality(n[0]),replace_equality(n[1]))
variants.append(('equality_scratch3',replace_equality(root),
    'Given R3=0, transfer R5 into R3 and run equality on R3/R6. Both operands and R3 '
    'are cleared; the equality exit and other registers are preserved.'))
table=A.R.table(ROOT/'latest218_baseline/candidate-k218/k218.native.tm')
prices=[]
for name,t,contract in variants:
    outdir=D/name;outdir.mkdir(exist_ok=True)
    ss=A.flatten(t);(outdir/'sites.json').write_bytes(A.compact(ss))
    rec=dict(name=name,source_nodes=len(P.nodes(t))+len({(op,arg)for _,op,arg in ss}),
             primitive_occurrences=len(ss),contract=contract,
             remaining_exact_E_occurrences=sum(1 for p,o,a in ss if o=='CD'and a==5 and p.endswith('000')and p[:-3]in {r['macro_path']for r in roles if r['name']!='NIP'}))
    try:
        raw,price=P.compile(table,root,t)
        (outdir/'raw.native.tm').write_bytes(P.M.enc(raw))
        rec['raw_physical_price']=price
        rec['raw_table_sha256']=H(outdir/'raw.native.tm')
    except Exception as exc:rec['raw_pricing_error']=repr(exc)
    (outdir/'price.json').write_text(json.dumps(rec,indent=2)+'\n')
    prices.append(rec)
result=dict(status='EXACT_SOURCE_ROLES_AND_POSTFIXED_INVARIANT_TRANSPORT_CHECKED',
    source_sha256=H(source),old_source_sha256=H(oldsource),facts_sha256=H(facts_path),
    unchanged_ordinal_control_graph=True,enabled_edges_checked=enabled,excluded_edges=excluded,
    halt_site_still_nonbottom=True,equality_macro=E,roles=roles,local_prices=prices,
    scope='All eight decrements remain abstractly capable of zero and positive branches. '
          'The proved NIP guard is scratch6=0, not cache!=1. Source-only or raw '
          'allocation prices are not verified machine candidates; full runtime and '
          'blank initialization would be separate obligations.')
(D/'CD5_SOURCE_ROLES_AND_PRICES.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in('equality_macro','local_prices')},indent=2))
for p in prices:
    print(p['name'],'nodes',p['source_nodes'],'leaves',p['primitive_occurrences'],
          'physical',p.get('raw_physical_price',{}).get('states'),
          'removed',p.get('raw_physical_price',{}).get('removed'),
          'added',p.get('raw_physical_price',{}).get('added'),p.get('raw_pricing_error'))
