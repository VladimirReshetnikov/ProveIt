#!/usr/bin/env python3
"""Independent closed-form numeral and literal-array audit; no imports of authors."""
import argparse, hashlib, json, math
from pathlib import Path
PINS={
 'matrix193_irregular_selector.py':'2ffdae00fe9f41e42f7b8230340ab9345a9dfb813317c8a43a2823647d930a38',
 'matrix193_irregular_selector.json':'8811d84fb6d7ad07270e0a0718c6ec866e21bbb7b40de835d8f06abe7b55f05e',
 'matrix193_irregular_selector.md':'81d46fcf7c3a8dea5df229b7e1d5e6c485f2e8b8e466677e7ea24b59112d36a5'}

def need(b,s):
    if not b:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def load(b):
    def pairs(rows):
        d={}
        for k,v in rows:need(k not in d,'duplicate');d[k]=v
        return d
    def bad(x):raise ValueError('noninteger '+x)
    return json.loads(b,object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def same(a,b):
    if type(a)is not type(b):return False
    if isinstance(a,dict):return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
    if isinstance(a,list):return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
    return a==b
def metadata(v):
    return {'sign':(v>0)-(v<0),'magnitude_bits':abs(v).bit_length(),
      'signed_magnitude_sha256':sha((b'-' if v<0 else b'+')+abs(v).to_bytes((abs(v).bit_length()+7)//8,'big'))}
def evaluate(rows,env,p):
    e={k:v%p for k,v in env.items()}
    for n,op,a,b in rows:
        a=a if type(a)is int else e[a];b=b if type(b)is int else e[b]
        e[n]=(a*b if op=='*' else a+b if op=='+' else a-b)%p
    return e

def verify(root,author):
    raw={}
    for n,h in PINS.items():
        b=(author/n).read_bytes();need(sha(b)==h,'author pin '+n);raw[n]=b
    a=load(raw['matrix193_irregular_selector.json'])
    need(a['source_sha256']==PINS['matrix193_irregular_selector.py'],'self pin')
    for n,h in a['pins'].items():need(sha((root/n).read_bytes())==h,'parent pin '+n)
    table=a['transition_table'];recipe=a['fixed_numeral_recipe'];nodes=recipe['nodes']
    need(len(nodes)==96 and len(set(nodes))==96 and nodes[0]==0,'nodes')
    need(nodes==[(r['G'][0]-table[0]['G'][0])//5 for r in table],'node binding')
    D=math.lcm(*(abs(math.prod(nodes[i]-nodes[k] for k in range(96) if k!=i)) for i in range(96)))
    columns=['K0','K1','K2','K3','G0','G1','G2','G3'];constants={'C:D':D};den=[];divisions=0
    # Direct closed formula, sharing each denominator among all eight columns.
    # This does not use the author's divided-difference recurrence.
    for j in range(96):
        den=[v*(nodes[i]-nodes[j]) for i,v in enumerate(den)]
        den.append(math.prod(nodes[j]-nodes[k] for k in range(j)))
        weights=[]
        for v in den:
            q,r=divmod(D,v);need(r==0,'closed denominator');weights.append(q);divisions+=1
        for col in columns:
            c=sum(table[i][col[0]][int(col[1])]*weights[i] for i in range(j+1))
            binding=recipe['coefficient_bindings'][col][j]
            need((binding is None)==(c==0),'zero coefficient binding')
            if binding:
                need(binding=='C:'+col+':'+str(j),'coefficient ID');constants[binding]=c
    need({k:metadata(v) for k,v in constants.items()}==recipe['fixed_numeral_metadata'],'every exact fixed numeral fingerprint')
    parent=load((root/'matrix193_newton_selector.json').read_bytes())
    need(table==parent['transition_table'] and a['initial_state']==parent['initial_state'] and a['endpoint']==parent['endpoint'],'table and endpoints')
    ledgers={};checks=0
    for name,v in a['variants'].items():
        known=set(v['ports'])|set(constants);by={};M=0
        for n,op,l,r in v['instructions']:
            need(n not in known and op in ['+','-','*'],'row')
            need(all(type(x)is int or type(x)is str and x in known for x in [l,r]),'closure')
            known.add(n);by[n]=(l,r);M+=op=='*'
        live=set();todo=[v['output']]
        while todo:
            x=todo.pop()
            if type(x)is int or x in live:continue
            live.add(x);todo.extend(by.get(x,()))
        need(live==set(by)|set(v['ports'])|set(constants),'all live')
        ledgers[name]={'M':M,'A':len(by)-M,'total':len(by)}
        need(all(v['ledger'][k]==val for k,val in ledgers[name].items()),'ledger')
        for prime in [1000000007,1000000009]:
            need(D%prime!=0,'nondegenerate modular scale')
            for i,tile in enumerate(table):
                x=[i-37,5];y=[-9,2*i+1]
                def row(v,m):return [v[0]*m[0]+v[1]*m[2],v[0]*m[1]+v[1]*m[3]]
                ports=dict(zip(['x0','x1','y0','y1','next_x0','next_x1','next_y0','next_y1'],x+y+row(x,tile['K'])+row(y,tile['G'])))
                ports.update(selector=nodes[i],n=0,next_n=0)
                env=dict(constants);env.update(ports)
                need(evaluate(v['instructions'],env,prime)[v['output']]==0,'every tile whole source modulo prime');checks+=1
    sync=a['variants']['real_synchronized'];down=a['variants']['real_countdown']
    oldsync=parent['variants']['real_synchronized'];olddown=parent['variants']['real_countdown']
    rename={oldsync['output']:sync['output']};tail=[]
    for n,op,l,r in olddown['instructions'][len(oldsync['instructions']):]:
        new='g'+str(len(sync['instructions'])+len(tail));tail.append([new,op,rename.get(l,l),rename.get(r,r)]);rename[n]=new
    need(len(tail)==26 and down['instructions']==sync['instructions']+tail,'complete inherited suffix')
    return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'author_pins':PINS,
      'ledgers':ledgers,'all_exact_coefficient_values':768,'exact_closed_formula_divisions':divisions,
      'matched_fixed_numeral_metadata':len(constants),'whole_source_modular_checks':checks,
      'scope':'Independent exact reconstruction of all fixed numerals and full source structure; modular samples supplement the unrestricted proof read. No predecessor code runs.'}
def main():
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--author-root',type=Path)
    m=p.add_mutually_exclusive_group(required=True);m.add_argument('--output',type=Path);m.add_argument('--expect',type=Path)
    a=p.parse_args();r=verify(a.root,a.author_root or a.root)
    if a.expect:need(same(r,load(a.expect.read_bytes())),'exact receipt')
    else:
        with a.output.open('x') as f:f.write(json.dumps(r,sort_keys=True,indent=2)+'\n')
    print(json.dumps(r,sort_keys=True))
if __name__=='__main__':main()
