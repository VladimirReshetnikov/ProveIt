#!/usr/bin/env python3
"""New independent canonical old-main emitter, data-only input and degree audit."""
import array, hashlib, json, pathlib
ROOT=pathlib.Path('/workspace/shared/ant-fusion-next-20261004/owned_report44')
OUT=pathlib.Path(__file__).resolve().parent
def data(name):return json.loads((ROOT/name).read_text())
class Main:
    def __init__(self,arity):
        self.raw=['RawLeft','RawRight'] if arity==2 else ['RawInput']
        self.known=set(self.raw);self.witnesses=[];self.hash=hashlib.sha256()
        self.deg=array.array('I');self.leading=[];self.M=self.A=0;self.residuals=[];self.constants=set()
        self.removed=0;self.retainedM=self.retainedA=0;self.section=''
        self.record(['raw_positive',self.raw])
    def record(self,x):self.hash.update((json.dumps(x,separators=(',',':'))+'\n').encode())
    def var(self,name):
        assert name not in self.known;self.known.add(name);self.witnesses.append(name)
        self.record(['positive',name]);return name
    def info(self,x):
        if type(x)==int:
            assert 0<=x<len(self.deg);return self.deg[x],self.leading[x]
        if x.startswith('C:'):
            self.constants.add(x)
            tail=x[2:];return (0,int(tail)) if tail.lstrip('-').isdigit() else (0,None)
        assert x in self.known
        return (1,1) if x=='History:W' else (1,None)
    def gate(self,op,a,b):
        i=len(self.deg);da,la=self.info(a);db,lb=self.info(b)
        d=da+db if op=='*' else max(da,db)
        if op=='*': lead=la*lb if la is not None and lb is not None else None
        elif da>db:lead=la
        elif da<db:lead=(-lb if op=='-' else lb) if lb is not None else None
        elif la is not None and lb is not None:lead=la-lb if op=='-' else la+lb
        else:lead=None
        if lead==0:lead=None # preserve conservative upper bound, never infer canceled degree
        self.record([i,op,a,b]);self.deg.append(d);self.leading.append(lead)
        if op=='*':self.M+=1
        else:self.A+=1
        if 1264<=i<2305260:
            start,kind=(1264,'tile') if i<1153262 else (1153262,'first')
            step=i-start;j=575998-step//2
            expected=[i,'*',f'C:{kind}:575999' if step==0 else i-1,'History:W'] if step%2==0 else [i,'+',i-1,f'C:{kind}:{j}']
            assert [i,op,a,b]==expected
            self.removed+=1
        else:
            for x in (a,b):
                assert type(x)!=int or not(1264<=x<2305260) or x in (1153261,2305259)
            if op=='*':self.retainedM+=1
            else:self.retainedA+=1
        return i
    def add(self,a,b):return self.gate('+',a,b)
    def sub(self,a,b):return self.gate('-',a,b)
    def mul(self,a,b):return self.gate('*',a,b)
    def power(self,a,n):
        if n==0:return 'C:1'
        v=a
        for bit in bin(n)[3:]:
            v=self.mul(v,v)
            if bit=='1':v=self.mul(v,a)
        return v
    def eq(self,a,b):
        for x in (a,b):
            assert type(x)!=int or not(1264<=x<2305260) or x in (1153261,2305259)
        da,la=self.info(a);db,lb=self.info(b);degree=max(da,db)
        lead=la if da>db else (-lb if lb is not None else None) if db>da else (la-lb if la is not None and lb is not None else None)
        self.record(['residual_pair',len(self.residuals),a,b,self.section])
        self.residuals.append(dict(a=a,b=b,section=self.section,upper_degree=degree,pure_W_leading=lead))
    def json_nodes(self,d,refs,eqkey='equations'):
        def ref(x):return 'C:'+str(x) if type(x)==int else refs[x]
        for out,op,a,b in d['nodes']:refs[out]=self.gate(op,ref(a),ref(b))
        for a,b in d[eqkey]:self.eq(ref(a),ref(b))
        return {k:ref(v) for k,v in d.get('outputs',{}).items()}
    def horner(self,kind,n):
        v=f'C:{kind}:{n-1}'
        for j in range(n-2,-1,-1):v=self.add(self.mul(v,'History:W'),f'C:{kind}:{j}')
        return v

def main(arity):
    d=Main(arity)
    if arity==1:d.var('RawLeft');d.var('RawRight')
    parent={p:d.var('Parent:'+p) for p in ['InitialMemoryPlus','FinalMemoryPlus','InitialHead','FinalHead','FinalSignPlus']}
    d.section='History';h=data('history/history174.json');refs=dict(parent)
    for w in h['witnesses']:refs[w]=d.var('History:'+w)
    d.json_nodes(h,refs,'equalities');assert len(d.deg)==174
    assert [refs[k] for k in ['W','Wp','Q']]==['History:W','History:Wp','History:Q']
    d.section='Init';start=len(d.deg)
    X,H,K,P=[d.var('Init:'+w) for w in ['HorizontalExtra','HalfRowsPower','HalfPeriodRepunit','PaddingPower']]
    hx=d.add(X,'C:1');d.eq(d.sub(refs['Wp'],'C:1'),d.mul('C:Cx',hx))
    G=d.power(refs['W'],576000)
    d.eq(d.sub(H,'C:1'),d.mul(d.sub(G,'C:1'),K));d.eq(refs['Q'],d.mul(H,H))
    hy=d.mul(K,d.add(H,'C:1'))
    rec=data('data/pair_inline-dag.json');r={'G':G,'RawLeft':'RawLeft','RawRight':'RawRight'}
    for w in rec['witnesses']:r[w]=d.var('Init:Recoder:'+w)
    result=d.json_nodes(rec,r);A,B,T=[result[k] for k in ['A','B','T']]
    gm=d.mul(A,G);d.eq(H,d.mul(P,gm));d.eq(parent['InitialHead'],d.mul('C:Cu',H))
    assert len(d.deg)==1264
    tile=d.horner('tile',576000);assert tile==1153261
    first=d.horner('first',576000);assert first==2305259
    anchor=d.horner('anchor',584)
    bg=d.mul(hy,d.add(d.mul(hx,tile),d.mul(refs['Wp'],first)))
    pw={e:d.power(refs['W'],e) for e in [575450,23945,263945,264000,24000]}
    anch=d.mul(d.mul(pw[575450],A),anchor)
    middle=d.add(d.mul(pw[24000],T),B)
    tail=d.mul(d.mul(pw[263945],d.add(pw[264000],'C:1')),middle)
    marker=d.add(pw[23945],tail)
    removed=d.mul(d.mul('C:C198',d.add(refs['W'],'C:1')),marker)
    delta=d.mul(d.mul('C:Cbase',P),d.sub(anch,removed))
    d.eq(parent['InitialMemoryPlus'],d.add(d.add(bg,delta),'C:1'))
    assert len(d.deg)-start==2306387
    d.section='Endpoint';ep=data('data/endpoint_folded_fixed_numerals_source.json')
    e={'W':refs['W'],'FinalHead':parent['FinalHead'],'FinalSignPlus':parent['FinalSignPlus'],'1':'C:1','K':'C:EndpointK','C':'C:Cx','D':'C:EndpointD'}
    for w in ep['new_positive_witnesses']:e[w]=d.var('Endpoint:'+w)
    for row in ep['gates']:e[row['out']]=d.gate({'add':'+','sub':'-','mul':'*'}[row['op']],*(e[a] for a in row['args']))
    for a,b in ep['equalities']:d.eq(e[a],e[b])
    if arity==1:
        d.section='Pairing';s=d.add('RawLeft','RawRight');s1=d.sub(s,'C:1');s2=d.sub(s1,'C:1')
        prod=d.mul(s2,s1);yy=d.mul('C:2','RawRight');rhs=d.add(prod,yy);lhs=d.mul('C:2','RawInput');d.eq(lhs,rhs)
    top=max(x['upper_degree'] for x in d.residuals)
    topres=[dict(index=i,**row) for i,row in enumerate(d.residuals) if row['upper_degree']==top]
    assert top==1152000 and [r['index'] for r in topres]==[64,178]
    assert all(r['pure_W_leading']==-1 for r in topres)
    other=max(r['upper_degree'] for r in d.residuals if r['upper_degree']<top)
    assert other==1127949
    squares=[]
    for r in d.residuals:
        diff=d.sub(r['a'],r['b']);squares.append(d.mul(diff,diff))
    final=squares[0]
    for v in squares[1:]:final=d.add(final,v)
    d.record(['eq',final,'C:0']);d.info('C:0')
    assert d.deg[final]==2304000 and d.leading[final]==2
    target={2:'c16901162e09b07d1e0c27b28e29dcc12a9b6137391fce85e3f150a3fed37eac',1:'85a161972769207e4f5d4212214630535208f69d6736bca2b46a8aff8276a22a'}[arity]
    assert d.hash.hexdigest()==target
    surviving={k for k in d.constants if not k.startswith(('C:tile:','C:first:'))}
    assert len(surviving)==598 and 'C:-1' not in surviving
    assert len(d.witnesses)==(465 if arity==2 else 467)
    fused=json.loads((ROOT.parent/'fused-receipt.json').read_text())['joins'][str(arity)]
    wd=hashlib.sha256(json.dumps(d.witnesses,separators=(',',':')).encode()).hexdigest()
    assert wd==fused['positive_witness_names_sha256']
    assert d.removed==2303996
    return dict(arity=arity,canonical_sha256=d.hash.hexdigest(),M=d.M,A=d.A,total=len(d.deg),retained_M=d.retainedM,retained_A=d.retainedA,removed=d.removed,witness_count=len(d.witnesses),witness_digest=wd,residual_count=len(d.residuals),top_residuals=topres,other_maximum_residual_upper_degree=other,exact_final_degree=2304000,leading_homogeneous_part='2 W^2304000',surviving_constant_ports=len(surviving),outside_consumers_of_removed_interior=0,initializer_bg_gate=bg)
res={'status':'PASS_INDEPENDENT_OLD_MAIN_RECONSTRUCTION_AND_EXACT_DEGREE','sources':{str(a):main(a) for a in (2,1)}}
res['checker_sha256']=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()
(OUT/'old-main-check-receipt.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps(res,indent=2))
