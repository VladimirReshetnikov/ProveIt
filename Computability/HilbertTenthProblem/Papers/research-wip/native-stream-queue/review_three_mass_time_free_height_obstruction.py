#!/usr/bin/env python3
"""Independent bounded source and positive-fiber audit; no author imports."""
import argparse, hashlib, json, random
from fractions import Fraction
from pathlib import Path
PARENT = {
    'three_mass_target_free_height.py': '7df5a60888976b55599014406c9b325a86428da6603f527b8a6fb35cff783d49',
    'three_mass_target_free_height.json': 'a263e7423cdc57b8fceb66ef9021be843c8a9c69a7f897ee4d3e38eac2488830',
    'three_mass_target_free_height.md': '61c207bf1d50729667fe2ea9dd94c49f66e2d4a848a0d6d12968e9dfd9f01e7a',
}
AUTHOR = {
    'three_mass_time_free_height_obstruction.py': '1d532fa63d4fa5c3e31c6faf6208825fdf615cc168df30c811fb83f967c1e240',
    'three_mass_time_free_height_obstruction.json': '8e58b354cb3036c0d0610efb572e80b4816b6002b629541bfd72f00c9c0f59b5',
    'three_mass_time_free_height_obstruction.md': '4bf862ab9b38a1b0e180d34bb071f3c67b8022a99275b3df5fb136df3d916e55',
}
def need(ok, message):
    if not ok: raise ValueError(message)
def digest(data): return hashlib.sha256(data).hexdigest()
def same(a,b):
    if type(a) is not type(b): return False
    if type(a) is dict: return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
    if type(a) is list: return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
    return a==b
def read_pins(root,pins):
    out={}
    for name,want in pins.items():
        data=(root/name).read_bytes();need(digest(data)==want,'pin '+name);out[name]=data
    return out
def evaluate(rows,values):
    env=values.copy()
    for name,op,a,b in rows:
        a=env[a] if type(a) is str else a;b=env[b] if type(b) is str else b
        need(op in ('+','-','*'),'arithmetic operation')
        env[name]=a+b if op=='+' else a-b if op=='-' else a*b
    return env
def ledger(rows,free,output):
    known=set(free);defs={};M=0
    for name,op,a,b in rows:
        need(name not in known and op in ('+','-','*'),'fresh arithmetic row')
        need(all(type(x)is int or type(x)is str and x in known for x in (a,b)),'closed operands')
        defs[name]=(a,b);known.add(name);M+=op=='*'
    live=set();stack=[output]
    while stack:
        x=stack.pop()
        if type(x)is int or x in live:continue
        live.add(x);stack.extend(defs.get(x,()))
    need(live==known,'all source and free coordinates live')
    return M,len(rows)-M

def verify(root,artifacts):
    pb=read_pins(root,PARENT);ab=read_pins(artifacts,AUTHOR)
    parent=json.loads(pb['three_mass_target_free_height.json'])
    proposal=json.loads(ab['three_mass_time_free_height_obstruction.json'])
    need(proposal['source_sha256']==AUTHOR['three_mass_time_free_height_obstruction.py'],'author source receipt')
    parents=[f['packet'] for f in parent['forms']];forms=proposal['forms']
    need(len(forms)==len(parents)==4,'four literal forms')
    expected={'clock_incdec':591,'clock_zero3':466,'clock_nop':464,'clock_positive3':467}
    counts=dict(literal_full_sources=0,paid_live_gates=0,height_cut_identities=0,clock_cut_identities=0,whole_numeric_identities=0,rational_cases=0,positive_fiber_points=0)
    rng=random.Random(137438954087);records=[]
    for old,new in zip(parents,forms):
        need(old['variant']==new['variant'] and old['variant'] in expected,'form names')
        need(same(old['parameters'],new['parameters']) and same(old['auxiliaries'],new['auxiliaries']) and same(old['comparisons'],new['comparisons']),'retained complete interface')
        defs={n:(op,a,b) for n,op,a,b in old['source']};h=old['interfaces']['height']
        need(defs[h]==('+','bridge_height_without_time','T') and defs['bridge_height_without_time']==('+','bridge_input','height_slack'),'literal old height')
        users=lambda x:[r[0] for r in old['source'] if x in r[2:]]
        need(users('bridge_height_without_time')==[h] and all('bridge_height_without_time' not in p for p in old['comparisons']),'private removable height register')
        tail=old['comparisons'][-1][1];op,product,time=defs[tail]
        need((op,time)==('+','T') and users('T')==[h,tail],'only time consumers')
        op,modulus,quotient=defs[product]
        need(op=='*' and defs[quotient]==('-','clock_quotient_hat',1) and users('clock_quotient_hat')==[quotient] and users(quotient)==[product] and users(product)==[tail],'private quotient cone')
        need(defs[modulus][0]=='-' and defs[modulus][2]==1,'literal B minus one');radix=defs[modulus][1]
        rows=[([n,'+','bridge_input','height_slack'] if n==h else [n,o,a,b]) for n,o,a,b in old['source'] if n!='bridge_height_without_time']
        finalizer=old['polynomial_source'][len(old['source']):]
        need(same(rows,new['source']) and same(rows+finalizer,new['polynomial_source']) and new['output']==old['output'],'actual source and entire finalizer')
        # A tiny exact ring for independently expanded local identities.
        zero=(0,)*5
        def const(v):return {zero:v} if v else {}
        def atom(i):return {tuple(int(j==i) for j in range(5)):1}
        def add(a,b,sign=1):
            c=a.copy()
            for m,v in b.items():c[m]=c.get(m,0)+sign*v
            return {m:v for m,v in c.items() if v}
        def mul(a,b):
            c={}
            for m,v in a.items():
                for n,w in b.items():
                    k=tuple(x+y for x,y in zip(m,n));c[k]=c.get(k,0)+v*w
            return {m:v for m,v in c.items() if v}
        n0,eta,T,d,hat=[atom(i) for i in range(5)]
        need(add(add(n0,add(eta,T,-1)),T)==add(n0,eta),'expanded height identity')
        lhs=add(mul(d,add(hat,const(1),-1)),T)
        rhs=add(mul(d,add(add(hat,const(1),-1),const(1),-1)),add(T,d))
        need(lhs==rhs,'expanded clock compensation')
        # Sole-consumer checks connect these local identities to every retained
        # operand and the unchanged full SOS. No other cone sees changed ports.
        M,A=ledger(rows+finalizer,old['parameters']+old['auxiliaries'],old['output'])
        need(M+A==expected[old['variant']] and len(finalizer)==56,'paid complete count')
        om,oa=ledger(old['polynomial_source'],old['parameters']+old['auxiliaries'],old['output'])
        need((om-M,oa-A)==(0,1),'exactly one addition deleted')
        counts['literal_full_sources']+=1;counts['paid_live_gates']+=M+A;counts['height_cut_identities']+=1;counts['clock_cut_identities']+=1
        for i in range(4):
            values={n:rng.randrange(-2,4) for n in old['parameters']+old['auxiliaries']}
            if i>=2:values={n:Fraction(v,2) for n,v in values.items()};counts['rational_cases']+=1
            a=evaluate(rows+finalizer,values);prior=dict(values,height_slack=values['height_slack']-values['T'])
            shifted=dict(values,T=values['T']+a[modulus],clock_quotient_hat=values['clock_quotient_hat']-1)
            b=evaluate(old['polynomial_source'],prior);c=evaluate(rows+finalizer,shifted)
            need(a[new['output']]==b[old['output']]==c[new['output']],'two full numeric identities')
            need(all(a[u]-a[v]==b[u]-b[v]==c[u]-c[v] for u,v in old['comparisons']),'all retained differences')
            counts['whole_numeric_identities']+=2
        records.append(dict(variant=old['variant'],M=M,A=A,operations=M+A,positive_witnesses=len(old['auxiliaries']),comparisons=19,source_sha256=digest(json.dumps(rows+finalizer,separators=(',',':')).encode())))
    # Independent direct source-machine evaluation, without author's fixture.
    p=parents[0];mp=p['mapping'];need((mp['K'],mp['initial'],mp['halt'],mp['modulus'])==(5,1,3,30),'actual incdec recipe')
    current=1;path=[current];ticks=[]
    for step in range(2):
        q,r=divmod(current-1,30);a,b=mp['table'][r];c,d=mp['clocks'][r]
        current=a*q+b;path.append(current);ticks.append(c*q+d)
    need(path==[1,7,3] and ticks==[308,308],'literal two-step genuine history')
    C=next(r[2] for r in p['source'] if r[1]=='*' and r[3]=='bridge_height_square')
    B=C*1024**2;need(C==131072 and B==2**37,'actual radix')
    packed=308+308*B;L=sum(ticks);Q=(packed-L)//(B-1)
    need(Q==308 and (packed-L)%(B-1)==0 and 1024>1+L,'positive seed at eta_parent407')
    # Reconstruct the genuine parent outer assignment independently.
    J=B+1;P=B*B;classes=sorted({a for a,b in mp['table']})
    selectors=[int(r==0)+B*int(r==6) for r in range(30)]
    values={n:1 for n in p['auxiliaries']}
    values.update(x=0,y=1,T=L,height_slack=407,quotient_hat=1,
                  global_slack=P-J-1-(len(classes)-1),clock_quotient_hat=309)
    values.update({f'edge{i}_hat':v+1 for i,v in enumerate(selectors)})
    need(all(values[n]>0 for n in p['auxiliaries']),'strict positive outer seed')
    native_ports={'native__q','native__scaled_A','native__padded_A','native__scaled_B','native__padded_B','native__scaled_Z','native__F3'}
    outer=[r for r in p['source'] if not r[0].startswith('native__') or r[0] in native_ports]
    env=evaluate(outer,values)
    need(env[p['interfaces']['height']]==1024 and env['bridge_target']==3,'seed height and terminal state')
    need(all(env[a]==env[b] for a,b in [p['comparisons'][0],p['comparisons'][1],p['comparisons'][-1]]),'all three genuine outer comparisons')
    X=(env['native__padded_A']-12)//16;Y=(env['native__padded_B']-10)//16;Z=(env['native__F3']-8)//16
    need((X&Y)==Z and all(env[n]>0 for n in native_ports),'actual prescribed joined AND and positive native inputs')
    need(len(proposal['incdec_outer_fiber'])==5,'five saved fiber records')
    for k,record in zip((0,1,2,307,308),proposal['incdec_outer_fiber']):
        T=L+k*(B-1);hat=Q+1-k
        need(hat>0 and T>=0 and (B-1)*(hat-1)+T==packed,'positive compensated clock')
        need(record['requested_time']==T and record['clock_quotient_hat']==hat and record['height_slack']==1023 and record['radix']==B and record['height']==1024,'actual saved fiber')
        counts['positive_fiber_points']+=1
    need(L+B-1==137438954087,'explicit false time')
    return dict(status='PASS_INDEPENDENT_TIME_FREE_HEIGHT_OBSTRUCTION',source_sha256=digest(Path(__file__).read_bytes()),parent_pins=PARENT,author_pins=AUTHOR,counts=counts,forms=records,incdec=dict(path=path,ticks=ticks,height=1024,radix=B,true_time=L,false_time=L+B-1,old_slack=407,new_slack=1023),scope='Independent complete source/height/clock identities and literal two-step positive fiber; full positive native extension inherited from the pinned maintained theorem, not materialized. No unsafe compiler promotion; no counterexample claim for the three one-step programs.')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--artifacts',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();result=verify(a.root,a.artifacts)
    if a.expect:need(same(result,json.loads(a.expect.read_text())),'exact typed receipt')
    if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(result['status'],result['counts'])
if __name__=='__main__':main()
