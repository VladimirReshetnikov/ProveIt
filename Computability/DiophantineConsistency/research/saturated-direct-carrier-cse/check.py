#!/usr/bin/env python3
"""Independent complete pointwise direct-carrier and inherited degree audit."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
from math import comb
import gzip,json,sys
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SEALS={'research/ten-positive-saturated-pell':'14961a7122489a6b9f4833892c6f4a67ec4b267ae2cc50f9a7b06c4b6587cd33','research/ten-positive-reused-b-weight':'7042b65701b37773f62b65a4191fdfaaff5d15dccab0374ee5b6e15dcb2c2d1b','research/ten-positive-uncentered-b-weight':'e4fe2d2e3d502619cfda003341fd08b49efea408ccdd569d3a551c64dd8f7ac0','research/indexed-tile-enumeration':'e077a476c38cb9abd96217887d16b011f6f5e16847036702720d69fcf91b1f84','candidates/one-page-short10':'72d1f34b64d6d01f33eb6c4b7dfef24dcb23bacbc50fb08d947e8f875056ed3a'}
ROUTES=[('ten-positive-saturated-pell','direct_saturated_upper','direct_saturated_upper97',97,258,11,124,29,61,1),('ten-positive-saturated-pell','direct_saturated_sharp','direct_saturated_sharp98',98,254,10,122,28,60,1),('ten-positive-reused-b-weight','direct_saturated_upper','direct_reused_b_upper96',96,258,11,124,29,61,1),('ten-positive-reused-b-weight','direct_saturated_sharp','direct_reused_b_sharp97',97,254,10,122,28,60,1),('ten-positive-uncentered-b-weight','direct95','direct_uncentered94',94,262,10,126,30,62,-1)]
def need(ok,why):
    if not ok:raise ValueError(why)
def load(p):return json.loads(p.read_bytes())
def digest(p):return sha256(p.read_bytes()).hexdigest()
def C(c):return {():c} if c else {}
def V(s):return {(s,):1}
def add(a,b,sign=1):
    r=dict(a)
    for m,c in b.items():r[m]=r.get(m,0)+sign*c
    return {m:c for m,c in r.items() if c}
def mul(a,b):
    r={}
    for m,c in a.items():
        for n,d in b.items():k=tuple(sorted(m+n));r[k]=r.get(k,0)+c*d
    return {m:c for m,c in r.items() if c}
def cut(rows,target,boundary):
    defs={r[0]:r for r in rows};memo={s:V(s) for s in boundary}
    def visit(s):
        if type(s) is int:return C(s)
        if s in memo:return memo[s]
        need(s in defs,'unbound free polynomial atom');_,op,a,b=defs[s];aa,bb=visit(a),visit(b);memo[s]=mul(aa,bb) if op=='*' else add(aa,bb,-1 if op=='-' else 1);return memo[s]
    return visit(target)
def topology(packet):
    need(packet['witnesses']==['J','F','alpha','i','T','x','Y','n','eta','zeta'] and packet['fixed_numerals']==['beta','K0','MC','MF'] and packet['domain']=='strictly positive integers' and packet['output']=='N','entire ten-positive four-port signature')
    known=set(packet['witnesses']+packet['fixed_numerals']);defs={}
    for key,op,a,b in packet['source']:
        need(key not in known and op in ['+','-','*'] and all(type(s) is int or s in known for s in [a,b]),'complete binary source topology');known.add(key);defs[key]=[a,b]
    todo=['N'];live=set()
    while todo:
        s=todo.pop()
        if type(s) is int or s in live:continue
        live.add(s);todo+=defs.get(s,[])
    need(live==known and len(defs)==packet['operations'] and dict(Counter(r[1] for r in packet['source']))==packet['operation_breakdown'],'all live gates, ports, inputs and full census')
def route(folder,entry,cuts):
    dirname,stem,target,count,degree,*_=entry;parent_path=ROOT/'research'/dirname/(stem+'.json');old=load(parent_path);new=load(folder/(target+'.json'));topology(old);topology(new)
    need((folder/'parents'/dirname/(stem+'.json')).read_bytes()==parent_path.read_bytes(),'whole copied parent graph '+target)
    consumers=[r[0] for r in old['source'] if 'q4' in r[2:]];need(consumers==['P1'] and ['qbJ','*','q','bJ'] in old['source'],'actual sole old consumer and existing shared product '+target)
    rows=[];mapping=[];deleted=[];changed=[]
    for i,row in enumerate(old['source']):
        if row[0]=='q4':need(row==['q4','*','q3','q'],'actual private product');deleted.append(dict(parent_index=i,row=row));continue
        actual=list(row)
        if row[0]=='P1':need(row==['P1','*','q4','bJ'],'actual old root product');actual=['P1','*','q3','qbJ'];changed.append(dict(parent_index=i,new_index=len(rows),old=row,new=actual))
        mapping.append(dict(parent_index=i,new_index=len(rows),row=actual));rows.append(actual)
    need(len(deleted)==len(changed)==1,'exact one-gate contraction')
    expected=deepcopy(old);expected.update(name=target,source=rows,operations=len(rows),operation_breakdown=dict(Counter(r[1] for r in rows)),parent_sha256=digest(parent_path),parent_manifest_sha256=digest(parent_path.parent/'MANIFEST.json'),proof='PROOF.md',proof_status='Exact free polynomial equality to whole sealed parent by sole-consumer direct-carrier contraction; all ordinary/native contracts unchanged.')
    need(new==expected and new['operations']==count and new['exact_degree']==degree and new['operation_breakdown']['*']==old['operation_breakdown']['*']-1 and all(new['operation_breakdown'][s]==old['operation_breakdown'][s] for s in ['+','-']),'ENTIRE new source/header and exact cost improvement '+target)
    need(cuts[target]==dict(parent='research/'+dirname+'/'+stem+'.json',parent_sha256=digest(parent_path),q4_consumers=consumers,deleted_rows=deleted,changed_rows=changed,complete_parent_to_new_rows=mapping),'every old/new row and sole consumer '+target)
    want=mul(mul(V('q3'),V('q')),V('bJ'));need(cut(old['source'],'P1',{'q3','q','bJ'})==cut(rows,'P1',{'q3','q','bJ'})==want,'actual free carrier polynomial identity '+target)
    return old,new
def ray(rows,inputs):
    def plus(a,b,sign=1):
        c=list(a)+[0]*max(0,len(b)-len(a))
        for i,n in enumerate(b):c[i]+=sign*n
        while c and not c[-1]:c.pop()
        return c
    def times(a,b):
        c=[0]*(len(a)+len(b)-1) if a and b else []
        for i,n in enumerate(a):
            if n:
                for j,m in enumerate(b):
                    if m:c[i+j]+=n*m
        while c and not c[-1]:c.pop()
        return c
    env={s:[0,1] for s in inputs}|{s:[n] for s,n in dict(beta=2,K0=3,MC=5,MF=7).items()}
    for key,op,a,b in rows:
        aa=[a] if type(a) is int else env[a];bb=[b] if type(b) is int else env[b];env[key]=times(aa,bb) if op=='*' else plus(aa,bb,-1 if op=='-' else 1)
    return len(env['N'])-1,env['N'][-1]
def restricted_search(packet):
    rows=packet['source'];defs={r[0]:r for r in rows};uses={r[0]:[] for r in rows}
    for row in rows:
        for a in row[2:]:
            if a in uses:uses[a].append(row[0])
    found=[]
    for i,(key,op,a,b) in enumerate(rows):
        if op not in ['+','*']:continue
        for child,other in [(a,b),(b,a)]:
            if child not in defs or defs[child][1]!=op or uses[child]!=[key]:continue
            atoms=defs[child][2:]+[other]
            for candidate in rows[:i]:
                if candidate[0]==child or candidate[1]!=op:continue
                for left in range(3):
                    if sorted([atoms[j] for j in range(3) if j!=left],key=str)==sorted(candidate[2:],key=str):found.append(dict(target=key,delete=child,reuse=candidate[0],other=atoms[left]))
    return found
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args();pins=load(HERE/'SOURCE_PINS.json');need(pins['closed_dependencies']==SEALS,'all five exact calibrated seals');inventory=set()
    for dirname,h in SEALS.items():
        folder=ROOT/dirname;need(digest(folder/'MANIFEST.json')==h,'exact reviewed seal '+dirname);files=load(folder/'MANIFEST.json')['files'];need(set(files)=={str(p.relative_to(folder)) for p in folder.rglob('*') if p.is_file() and p!=folder/'MANIFEST.json'},'complete closed inventory '+dirname)
        for n,h in files.items():need(digest(folder/n)==h,'whole sealed dependency member')
        inventory|={str(p.relative_to(ROOT)) for p in folder.rglob('*') if p.is_file()}
    need(set(pins['files'])==inventory,'complete dependency pin inventory')
    for n,h in pins['files'].items():need(digest(ROOT/n)==h,'whole immutable dependency '+n)
    if (HERE/'MANIFEST.json').exists():
        files=load(HERE/'MANIFEST.json')['files'];need(set(files)=={str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and p!=HERE/'MANIFEST.json'},'closed own inventory')
        for n,h in files.items():need(digest(HERE/n)==h,'whole own sealed member '+n)
    for dirname in {r[0] for r in ROUTES}:
        for n in ['PROOF.md','MANIFEST.json','CHECK.json','CHECK_OPTIMIZED.json']:need((HERE/'parents'/dirname/n).read_bytes()==(ROOT/'research'/dirname/n).read_bytes(),'whole copied degree/ordinary parent '+dirname+'/'+n)
    base=ROOT/'research/ten-positive-uncentered-b-weight';primary=load(base/'zero89.json')['coefficient_binding'];indexed=load(base/'INDEXED_BINDING.json');need(load(HERE/'INDEXED_BINDING.json')==indexed,'whole alternate indexed binding');bindings=[]
    for label,binding in [('bfs',primary),('indexed_bfs',indexed)]:
        values={}
        for port,pin in binding['ports'].items():
            payload=(HERE/binding['path']/pin['file']).read_bytes();raw=gzip.decompress(payload);value=int.from_bytes(raw,'little');need(payload==(base/binding['path']/pin['file']).read_bytes() and sha256(payload).hexdigest()==pin['gzip_sha256'] and sha256(raw).hexdigest()==pin['raw_sha256'] and value.bit_length()==pin['bits'] and len(raw)==(value.bit_length()+7)//8,'whole gzip/raw numeral '+label+port);values[port]=value
        need(values['beta']>=31 and values['beta']%2==1 and values['K0']>0 and 0<values['MC']<values['beta']<values['MF']<2*values['beta'],'whole fixed-port box');bindings.append(dict(tuple=label,K_raw_sha256=binding['ports']['K0']['raw_sha256'],all_four_payloads=True))
    cuts=load(HERE/'CUTS.json');need(set(cuts)=={r[2] for r in ROUTES},'all five exact row-map routes');results=[]
    for entry in ROUTES:
        dirname,stem,target,count,degree,tp,qp,xp,yp,sign=entry;old,new=route(HERE,entry,cuts);need(new['coefficient_binding']==primary,'entire primary tuple unchanged')
        record=next(c for c in load(ROOT/'research'/dirname/'CHECK.json')['candidates'] if c['name']==stem);need(record['exact_degree']==degree and record.get('equation_sha256',record.get('whole_graph_sha256'))==digest(ROOT/'research'/dirname/(stem+'.json')),'actual graph bound to entire parent global-degree certificate')
        # Complete leading form is sign*2^tp*q0^qp*(q0+x)^xp*Y^yp*i^10*(eta+zeta)^32*(q0-F)^2.
        need(qp+xp+yp+10+32+2==degree,'whole highest form homogeneous degree');leading={}
        for xi in range(xp+1):
            for et in range(33):
                for ff in range(3):
                    mon=(qp+xp-xi+2-ff,xi,yp,10,et,32-et,ff);leading[mon]=sign*2**tp*comb(xp,xi)*comb(32,et)*comb(2,ff)*(-1)**ff
        need(leading[(qp,xp,yp,10,32,0,2)]==sign*2**tp,'actual nonzero fixed-beta selected coefficient')
        rd,lc=ray(new['source'],new['witnesses']);need((rd,str(lc))==(record.get('exact_ray_degree',record.get('univariate_degree')),record.get('exact_ray_leading_coefficient',record.get('univariate_leading_coefficient'))),'complete independent actual output ray')
        results.append(dict(name=target,operations=count,operation_breakdown=new['operation_breakdown'],exact_degree=degree,whole_output_polynomial_equal_to_parent=True,parent_graph_sha256=digest(ROOT/'research'/dirname/(stem+'.json')),new_graph_sha256=digest(HERE/(target+'.json')),whole_highest_form_terms=len(leading),whole_highest_form_sha256=sha256(repr(sorted(leading.items())).encode()).hexdigest(),selected_coefficient=dict(sign=sign,two_power=tp,beta_power=qp),complete_ray_degree=rd,complete_ray_leading_coefficient=str(lc)))
    search={s:restricted_search(load(base/(s+'.json'))) for s in ['zero89','direct95']};need(search=={'zero89':[],'direct95':[dict(target='P1',delete='q4',reuse='qbJ',other='q3')]},'complete restricted two-gate reassociation enumeration')
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),candidates=results,whole_coherent_bindings=bindings,restricted_associative_search=search,search_is_not_a_general_lower_bound=True,whole_dependency_files=len(inventory),parent_or_producer_or_incoming_code_executed=False,canonical_or_common_files_modified=False,source_pins={n:digest(HERE/n) for n in ['README.md','PROOF.md','SOURCE_PINS.json','build.py','check.py']},scope='Exact free polynomial equality and whole-source row induction; all global degree/ordinary/native statements transfer from their complete pinned parents.')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():need(args.output.read_text()==text,'refuse changed receipt overwrite')
    else:args.output.write_text(text)
    print(json.dumps(dict(status='PASS',optimized_python=bool(sys.flags.optimize),complete_routes=5,exact_multiplication_saving_per_route=1),sort_keys=True))
if __name__=='__main__':main()
