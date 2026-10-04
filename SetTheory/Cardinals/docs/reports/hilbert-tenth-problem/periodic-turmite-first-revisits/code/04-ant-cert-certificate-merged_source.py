#!/usr/bin/env python3
"""Recovered edition of the complete arithmetic certificate, 2026-10-04.
New implementation bytes; old canonical arithmetic-stream hashes are comparison targets.
Frozen source/code is read as data only. Only newly authored code runs.
"""
if not __debug__:raise RuntimeError('Optimized Python is unsupported')
import argparse,hashlib,json,pathlib,re,os
from array import array
from contextlib import ExitStack
ROOT=pathlib.Path(__file__).resolve().parent
U,V,X0,Y0=481238074400,576000,481225262775,29948
PARENTS=['InitialMemoryPlus','FinalMemoryPlus','InitialHead','FinalHead','FinalSignPlus']
OLD_STREAM={2:'c16901162e09b07d1e0c27b28e29dcc12a9b6137391fce85e3f150a3fed37eac',1:'85a161972769207e4f5d4212214630535208f69d6736bca2b46a8aff8276a22a'}

def jline(x):return json.dumps(x,separators=(',',':'))+'\n'
def load(path):return json.loads((ROOT/path).read_text())
def sha(path):return hashlib.sha256((ROOT/path).read_bytes()).hexdigest()
def chain(n):return 0 if n<2 else n.bit_length()-1+n.bit_count()-1

def constant_ok(s):
    if type(s)is not str or not s.startswith('C:'):return False
    k=s[2:]
    if k.lstrip('-').isdigit():return int(k) in {-1,0,1,2,3,4,6,8,9}
    if k in {'Cu','Cx','Cbase','C198','EndpointK','EndpointD'}:return True
    m=re.fullmatch(r'(tile|first|anchor):(\d+)',k)
    return bool(m and int(m[2])<(584 if m[1]=='anchor' else V))

class Complete:
    def __init__(self,stream=None,arity=2):
        self.raw=['RawLeft','RawRight'] if arity==2 else ['RawInput']
        self.stream=stream;self.n=0;self.M=0;self.A=0;self.degrees=array('I');self.witnesses=[]
        self.known=set(self.raw);self.residuals=[];self.digest=hashlib.sha256();self.used_constants=set()
        self.record(['raw_positive',self.raw])
    def record(self,row):
        s=jline(row);self.digest.update(s.encode())
        if self.stream:self.stream.write(s)
    def degree(self,a):
        if type(a)is int:
            if not 0<=a<self.n:raise ValueError(('Forward or invalid gate',a,self.n))
            return self.degrees[a]
        if type(a)is not str:raise ValueError('Bad reference type')
        if constant_ok(a):self.used_constants.add(a);return 0
        if a not in self.known:raise ValueError(('Undeclared positive coordinate',a))
        return 1
    def witness(self,name):
        if name in self.known or name.startswith('C:'):raise ValueError('Duplicate witness')
        self.known.add(name);self.witnesses.append(name);self.record(['positive',name]);return name
    def gate(self,op,a,b):
        if op not in ['+','-','*']:raise ValueError('Bad opcode')
        x,y=self.degree(a),self.degree(b);out=self.n
        self.record([out,op,a,b]);self.degrees.append(x+y if op=='*' else max(x,y));self.n+=1
        if op=='*':self.M+=1
        else:self.A+=1
        return out
    def equation(self,a,b,section):
        bound=max(self.degree(a),self.degree(b));self.residuals.append((a,b,section,bound))
        self.record(['residual_pair',len(self.residuals)-1,a,b,section])
    def sos(self):
        first=self.n;squares=[]
        for a,b,section,bound in self.residuals:
            r=self.gate('-',a,b);squares.append(self.gate('*',r,r))
        F=squares[0]
        for z in squares[1:]:F=self.gate('+',F,z)
        self.degree(F);self.degree('C:0');self.record(['eq',F,'C:0'])
        return {'start':first,'end':self.n,'output':F,'equations':1,'M':len(squares),'A':2*len(squares)-1}

class Module:
    def __init__(self,d,section,ports):
        self.d=d;self.section=section;self.ports=dict(ports);self.start=d.n;self.n=0;self.M=0;self.A=0;self.eqs=0;self.w=[];self.digest=hashlib.sha256()
    def tr(self,x):
        if type(x)is int:
            if not 0<=x<self.n:raise ValueError('Local forward reference')
            return self.start+x
        if constant_ok(x):return x
        if x not in self.ports:raise ValueError(('Unknown local port',self.section,x))
        return self.ports[x]
    def witness(self,name):
        if name in self.ports:raise ValueError('Module witness collision')
        self.ports[name]=self.d.witness(self.section+':'+name);self.w.append(name);return name
    def gate(self,op,a,b):
        self.digest.update(jline([self.n,op,a,b]).encode())
        out=self.d.gate(op,self.tr(a),self.tr(b));assert out==self.start+self.n
        self.n+=1
        if op=='*':self.M+=1
        else:self.A+=1
        return self.n-1
    def add(self,a,b):return self.gate('+',a,b)
    def sub(self,a,b):return self.gate('-',a,b)
    def mul(self,a,b):return self.gate('*',a,b)
    def eq(self,a,b):
        self.digest.update(jline(['eq',a,b]).encode());self.eqs+=1;self.d.equation(self.tr(a),self.tr(b),self.section)
    def power(self,a,n):
        if n==0:return 'C:1'
        z=a
        for bit in bin(n)[3:]:
            z=self.mul(z,z)
            if bit=='1':z=self.mul(z,a)
        return z
    def horner(self,base,coeffs):
        it=iter(coeffs);z=next(it)
        for c in it:z=self.add(self.mul(z,base),c)
        return z
    def receipt(self):return dict(M=self.M,A=self.A,total=self.n,equations=self.eqs,positive_witnesses=len(self.w),source_interval=[self.start,self.start+self.n],local_dag_sha256=self.digest.hexdigest())

def insert_json(m,data,ports):
    tr=dict(ports)
    for w in data['witnesses']:
        if type(w)is not str or w in tr:raise ValueError('Bad JSON witness')
        tr[w]=m.witness(w)
    def r(x):
        if type(x)is int:return 'C:'+str(x)
        if type(x)is not str or x not in tr:raise ValueError(('Unbound JSON reference',x))
        return tr[x]
    for out,op,a,b in data['nodes']:
        if type(out)is not str or out in tr:raise ValueError('Duplicate source output')
        tr[out]=m.gate(op,r(a),r(b))
    for a,b in data['equations']:m.eq(r(a),r(b))
    return {k:r(v)for k,v in data.get('outputs',{}).items()}

def initializer(m):
    X=m.witness('HorizontalExtra');H=m.witness('HalfRowsPower');K=m.witness('HalfPeriodRepunit');P=m.witness('PaddingPower')
    hx=m.add(X,'C:1');m.eq(m.sub('Wp','C:1'),m.mul('C:Cx',hx))
    G=m.power('W',V)
    m.eq(m.sub(H,'C:1'),m.mul(m.sub(G,'C:1'),K));m.eq('Q',m.mul(H,H))
    hy=m.mul(K,m.add(H,'C:1'))
    pair=load('data/pair_inline-dag.json');rp={'G':G,'RawLeft':'RawLeft','RawRight':'RawRight'}
    for w in pair['witnesses']:rp[w]=m.witness('Recoder:'+w)
    def r(x):return 'C:'+str(x) if type(x)is int else rp[x]
    recoder_start=m.n
    for out,op,a,b in pair['nodes']:
        if out in rp:raise ValueError('Recoder output collision')
        rp[out]=m.gate(op,r(a),r(b))
    for a,b in pair['equations']:m.eq(r(a),r(b))
    A,B,T=[r(pair['outputs'][name])for name in ['A','B','T']]
    gm=m.mul(A,G);m.eq(H,m.mul(P,gm));m.eq('InitialHead',m.mul('C:Cu',H))
    tile=m.horner('W',(f'C:tile:{j}'for j in range(V-1,-1,-1)))
    first=m.horner('W',(f'C:first:{j}'for j in range(V-1,-1,-1)))
    anchor=m.horner('W',(f'C:anchor:{j}'for j in range(583,-1,-1)))
    bg=m.mul(hy,m.add(m.mul(hx,tile),m.mul('Wp',first)))
    powers={e:m.power('W',e)for e in [V-550,23945,263945,264000,24000]}
    anch=m.mul(m.mul(powers[V-550],A),anchor)
    middle=m.add(m.mul(powers[24000],T),B)
    tail=m.mul(m.mul(powers[263945],m.add(powers[264000],'C:1')),middle)
    marker_tail=m.add(powers[23945],tail)
    removed=m.mul(m.mul('C:C198',m.add('W','C:1')),marker_tail)
    delta=m.mul(m.mul('C:Cbase',P),m.sub(anch,removed))
    m.eq('InitialMemoryPlus',m.add(m.add(bg,delta),'C:1'))
    assert (recoder_start,m.n)==(32,2306387)
    return {'G':m.tr(G),'A':m.tr(A),'B':m.tr(B),'T':m.tr(T)}

def endpoint(m):
    src=load('data/endpoint_folded_fixed_numerals_source.json')
    refs={'W':'W','FinalHead':'FinalHead','FinalSignPlus':'FinalSignPlus','1':'C:1','K':'C:EndpointK','C':'C:Cx','D':'C:EndpointD'}
    for w in src['new_positive_witnesses']:refs[w]=m.witness(w)
    for row in src['gates']:
        out=row['out'];assert out not in refs
        refs[out]=m.gate({'mul':'*','add':'+','sub':'-'}[row['op']],*[refs[a]for a in row['args']])
    for a,b in src['equalities']:m.eq(refs[a],refs[b])
    return {'WToV':m.tr(refs[src['power_targets']['WToV']]),'WToY0':m.tr(refs[src['power_targets']['T']])}

def strict_prefix(history_literals):
    baseM=V*(U-1)+584*220+chain(U)+chain(U-219)+chain(198)
    baseA=V*(U-1)+584*220+4
    if not set(history_literals)<={0,1,2,3,4,6,8,9}:raise ValueError('Unpaid numeral')
    extraM=chain(X0)+1;extraA=4
    return dict(M=baseM+extraM,A=baseA+extraA,total=baseM+baseA+extraM+extraA,base_initializer_prefix={'M':baseM,'A':baseA},additional={'M':extraM,'A':extraA},strict_literals=[1,3])

def build(stream=None,arity=2):
    if arity not in [1,2]:raise ValueError('Invalid raw arity')
    d=Complete(stream,arity)
    if arity==1:d.witness('RawLeft');d.witness('RawRight')
    parent={p:d.witness('Parent:'+p)for p in PARENTS}
    full=load('history/history174.json');hdata={'nodes':full['nodes'],'equations':full['equalities'],'witnesses':full['witnesses']}
    h=Module(d,'History',parent);insert_json(h,hdata,{p:p for p in PARENTS});hc=h.receipt()
    assert [hc[k]for k in ['total','M','A','equations','positive_witnesses']]==[174,72,102,48,61]
    geometry={k:h.tr(k)for k in ['W','Wp','Q']}
    im=Module(d,'Init',dict(geometry,InitialHead=parent['InitialHead'],InitialMemoryPlus=parent['InitialMemoryPlus'],RawLeft='RawLeft',RawRight='RawRight'))
    aliases=initializer(im);ic=im.receipt()
    assert ic['local_dag_sha256']=='503215b20d317cfb9e6e40ec82eb26044afbdedf26f37e03029bcd7dc0a04130'
    assert [ic[k]for k in ['total','M','A','equations','positive_witnesses']]==[2306387,1153192,1153195,234,396]
    ep=Module(d,'Endpoint',dict(W=geometry['W'],FinalHead=parent['FinalHead'],FinalSignPlus=parent['FinalSignPlus']))
    ep_aliases=endpoint(ep);ec=ep.receipt()
    assert [ec[k]for k in ['total','M','A','equations','positive_witnesses']]==[42,37,5,3,3]
    pc=None
    if arity==1:
        pm=Module(d,'Pairing',{'RawInput':'RawInput','RawLeft':'RawLeft','RawRight':'RawRight'})
        s=pm.add('RawLeft','RawRight');s1=pm.sub(s,'C:1');s2=pm.sub(s1,'C:1')
        prod=pm.mul(s2,s1);r2=pm.mul('C:2','RawRight');rhs=pm.add(prod,r2);x2=pm.mul('C:2','RawInput');pm.eq(x2,rhs)
        pc=pm.receipt();assert [pc[k]for k in ['total','M','A','equations','positive_witnesses']]==[7,3,4,1,0]
    conjunction=dict(M=d.M,A=d.A,total=d.n,equations=len(d.residuals),positive_witnesses=len(d.witnesses))
    bounds=[r[3]for r in d.residuals];top=max(bounds)
    top_eq=[{'global_residual':i,'section':r[2],'upper_degree':r[3]}for i,r in enumerate(d.residuals)if r[3]==top]
    sos=d.sos();literals=sorted({int(c[2:])for c in d.used_constants if c[2:].lstrip('-').isdigit()});strict=strict_prefix(literals)
    result={'status':'PASS_LITERAL_COMPLETE_JOIN','raw_positive_inputs':d.raw,'positive_witness_count':len(d.witnesses),'positive_witnesses':d.witnesses,'raw_port_count':arity,'parent_ports_quantified':parent,'geometry_aliases':geometry,'initializer_expression_aliases':aliases,'endpoint_expression_aliases':ep_aliases,'components':{'history':hc,'initializer':ic,'endpoint':ec,'pairing':pc},'conjunction':conjunction,'sum_of_squares':sos,'single_polynomial':{'M':d.M,'A':d.A,'total':d.n,'equations':1,'positive_witnesses':len(d.witnesses),'exact_degree':4*V},'degree':{'max_residual_upper_degree':top,'top_residuals':top_eq,'other_max_upper_degree':max(r[3]for r in d.residuals if r[3]<top),'final_upper_degree':d.degrees[sos['output']],'exactness':'The only degree-2v residuals have leading homogeneous term -W^(2v); final leading part is 2W^(4v). See PROOF.md.'},'strict_prefix':strict,'strict_single_polynomial_total':d.n+strict['total'],'source_sha256':d.digest.hexdigest(),'fixed_coefficient_port_count':len(d.used_constants),'ordinary_integer_literals':literals,'residual_degree_bounds':bounds,'fixed_coefficient_categories':{'tile_rows':V,'first_column_rows':V,'anchor_rows':584,'named':['Cu','Cx','Cbase','C198','EndpointK','EndpointD']},'data_hashes':{p:sha(p)for p in ['history/history174.json','data/pair_inline-dag.json','data/endpoint_folded_fixed_numerals_source.json']}}
    result['recovery']={'edition':'recovered-20261004-v2','old_stream_sha256':OLD_STREAM[arity],'canonical_stream_byte_identity_verified':result['source_sha256']==OLD_STREAM[arity],'implementation_byte_identity_claimed':False}
    return result

def output_destination(path):
    path=pathlib.Path(path)
    if os.path.lexists(path):raise FileExistsError('Output must be new: '+str(path))
    parent=path.parent.resolve(strict=True)
    if not parent.is_dir():raise ValueError('Output parent must be an existing directory')
    dest=parent/path.name
    if dest==ROOT or ROOT in dest.parents:raise ValueError('Output must be outside the resolved source tree')
    if os.path.lexists(dest):raise FileExistsError('Output already exists: '+str(dest))
    return dest

def output_paths(receipt,emit=None):
    paths=[output_destination(receipt)]
    if emit is not None:paths.append(output_destination(emit))
    if len(paths)==2 and paths[0]==paths[1]:raise ValueError('Receipt and emit destinations must differ')
    return paths

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',required=True);p.add_argument('--emit');p.add_argument('--arity',type=int,choices=[1,2],default=2);a=p.parse_args()
    paths=output_paths(a.output,a.emit)
    with ExitStack()as stack:
        receipt=stack.enter_context(paths[0].open('x',encoding='utf-8'))
        stream=stack.enter_context(paths[1].open('x',encoding='utf-8'))if len(paths)==2 else None
        r=build(stream,a.arity);json.dump(r,receipt,indent=2);receipt.write('\n')
    print(json.dumps({k:r[k]for k in ['status','conjunction','single_polynomial','strict_prefix','strict_single_polynomial_total','source_sha256','recovery']},indent=2))
