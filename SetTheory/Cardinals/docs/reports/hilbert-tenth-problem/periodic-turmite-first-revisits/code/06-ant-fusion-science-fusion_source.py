#!/usr/bin/env python3
"""Literal 1/3 source with initializer/background fusion; no ant simulation.

Inspected OWN arithmetic generators are copied locally and authenticated before
import. Frozen Report47 profiles are data, never executable saved schedules.
No large coefficient integer is instantiated: all arithmetic is symbolic.
"""
import argparse, collections, hashlib, importlib.util, json, pathlib, struct, sys
from array import array
ROOT=pathlib.Path(__file__).resolve().parent
sys.dont_write_bytecode=True
S=576000; NB=960; BW=600; V=240619037200; U=2*V; R=601547591
KINDS=('DUP','NAND','MOVE_LEFT','MOVE_RIGHT')
OLD_STREAM={2:'c16901162e09b07d1e0c27b28e29dcc12a9b6137391fce85e3f150a3fed37eac',1:'85a161972769207e4f5d4212214630535208f69d6736bca2b46a8aff8276a22a'}

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pins():
    p=json.loads((ROOT/'INPUT_PINS.json').read_text())
    for name,row in p.items():assert sha(ROOT/name)==row['sha256'],name
    assert p['owned_report47/occurrence_compiler.py']['sha256']=='90fd5c01e807ddb906ad86b442f86092b516f0f00300c3f9c46462858e8072d1'
    assert p['owned_report44/merged_source.py']['sha256']=='eafe92d6e57782347f430a4f1d6ea5693bd6a48300d2db0294b3ab7026b96395'
    return p

def owned(name,relative):
    spec=importlib.util.spec_from_file_location(name,ROOT/relative)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod

def load_profiles():
    path=ROOT/'data/profiles';manifest=json.loads((path/'MANIFEST.json').read_text())
    out={}
    for name in ('H','B','F'):
        md=manifest['profiles'][name]
        assert sha(path/md['column_ids_file'])==md['column_ids_sha256']
        assert sha(path/md['dictionary_file'])==md['dictionary_sha256']
        dic=json.loads((path/md['dictionary_file']).read_text())
        masks=[int(v,16) for v in dic['mask_hex_by_id']]
        assert dic['height']==400 and dic['y0']==50 and all(0<=v<1<<400 for v in masks)
        ids=struct.unpack('<576000H',(path/md['column_ids_file']).read_bytes())
        out[name]=[masks[v] for v in ids]
    out['Hlow']=[v&((1<<25)-1) for v in out['H']]
    out['Hhigh']=[v>>25 for v in out['H']]
    out['first']=[v>>25&1 for v in out['H']]
    q={}
    for name in KINDS:
        md=manifest['corrections'][name];assert sha(path/md['file'])==md['sha256']
        data=json.loads((path/md['file']).read_text())
        dic=[tuple(int(v,16) for v in row) for row in data['signed_masks_by_id']]
        assert data['width']==1200 and data['height']==400 and len(data['profile_id_by_dx'])==1200
        assert all(not(p&m) and 0<=p<1<<400 and 0<=m<1<<400 for p,m in dic)
        q[name]=[dic[v] for v in data['profile_id_by_dx']]
    return out,q

def grouped(arr,phase):
    """Complete finite equality certificate: disjoint groups partition 960 blocks."""
    groups=collections.defaultdict(list)
    for k in range(NB):
        block=tuple(arr[(288650-(BW*k+r)-phase)%S] for r in range(BW))
        groups[block].append(k)
    assert sorted(k for seq in groups.values() for k in seq)==list(range(NB))
    return list(groups.items())

def runs(seq):
    assert seq and list(seq)==sorted(set(seq))
    ans=[];a=b=seq[0]
    for k in seq[1:]:
        if k==b+1:b=k
        else:ans.append((a,b-a+1));a=b=k
    ans.append((a,b-a+1));return ans

def geometric(d,z,n):
    assert n>=1
    p=z;g='one'
    for bit in bin(n)[3:]:
        oldp=p;p=d.gate('*',p,p);g=d.gate('+',g,d.gate('*',oldp,g))
        if bit=='1':g=d.gate('+',g,p);p=d.gate('*',p,z)
    return p,g

class Profiles:
    """Same paid signed ternary Horner grammar as Report47, copied by inspection."""
    def __init__(self,d,zero,minus):self.d=d;self.zero=zero;self.minus=minus;self.cache={};self.hist={}
    def get(self,width,plus,minus=0):
        assert not(plus&minus) and 0<=plus<1<<width and 0<=minus<1<<width
        if not(plus|minus):return self.zero
        key=width,plus,minus
        if key in self.cache:return self.cache[key]
        def digit(k):return 'one' if plus>>k&1 else self.minus if minus>>k&1 else self.zero
        a=digit(width-1)
        for k in range(width-2,-1,-1):a=self.d.gate('+',self.d.gate('*',a,'three'),digit(k))
        self.cache[key]=a;self.hist[width]=self.hist.get(width,0)+1;return a

def prepare(d,occmod,profiles,q):
    stages={};last=(d.M,d.A)
    def stage(name):
        nonlocal last
        stages[name]={'M':d.M-last[0],'A':d.A-last[1],'total':d.M+d.A-sum(last)};last=d.M,d.A
    o=occmod.Occurrences(d,json.loads((ROOT/'data/physical_program.json').read_text()))
    occ,orr=o.compile();stage('occurrence_constants')
    zero=o.zero;minus=d.gate('-',zero,'one');two=d.gate('+','one','one');pf=Profiles(d,zero,minus)
    # Preserve the exact Report47 construction/cache inventory, even unused profiles.
    for name,width in [('H',400),('B',400),('F',400),('Hlow',25),('Hhigh',375)]:
        for value in profiles[name]:pf.get(width,value)
    for name in KINDS:
        for pair in q[name]:pf.get(400,*pair)
    assert pf.hist=={400:736,25:21,375:81}
    stage('small_profiles_and_basic_literals')
    _,G=geometric(d,o.z,R)
    powers={e:d.power('three',e) for e in [375,V-425,V-400,V-25,U-25]}
    stage('geometric_sum_and_fixed_shifts')
    labels={};anchor=json.loads((ROOT/'data/anchor_patch.json').read_text());adata=[[0]*221 for _ in range(584)];seen=set()
    for x,y,old,new in anchor['patch']:
        j=289200-x;i=y+144;assert 0<=j<584 and 0<=i<=220 and (j,i) not in seen
        seen.add((j,i));adata[j][i]=new-old
    symbols={-1:minus,0:zero,1:'one'}
    for j,row in enumerate(adata):
        a=symbols[row[220]]
        for i in range(219,-1,-1):a=d.gate('+',d.gate('*',a,'three'),symbols[row[i]])
        labels[f'anchor:{j}']=a
    stage('anchor_rows')
    labels['Cu']=d.power('three',U);labels['Cbase']=d.power('three',U-219);labels['C198']=d.power('three',198)
    labels['Cx']=d.gate('-',labels['Cu'],'one')
    four=d.gate('+',two,two);six=d.gate('+','three','three');eight=d.gate('+',four,four);nine=d.gate('*','three','three')
    labels['EndpointK']=d.power('three',481225262775);labels['EndpointD']=d.gate('-',labels['Cx'],'one')
    labels.update({'0':zero,'1':'one','2':two,'3':'three','4':four,'6':six,'8':eight,'9':nine})
    stage('remaining_named_constants')
    assert len(labels)==598
    return dict(labels=labels,occ=occ,pf=pf,G=G,Z=o.z,powers=powers,stages=stages,occurrence_receipt=orr)

class Fusion:
    def __init__(self,d,W,prepared,profiles,q):
        self.d=d;self.W=W;self.p=prepared;self.profiles=profiles;self.q=q;self.zero=prepared['labels']['0'];self.stats={}
        self.last=d.M,d.A;self.block_cache={};self.weight_cache={};self.ypow={0:'one'};self.geom={1:'one'}
        self.Y=d.power(W,600);self.ypow[1]=self.Y;self.stage('spatial_base_power')
    def stage(self,name):
        self.stats[name]={'M':self.d.M-self.last[0],'A':self.d.A-self.last[1],'total':self.d.M+self.d.A-sum(self.last)}
        self.last=self.d.M,self.d.A
    def horner(self,base,coeffs):
        assert coeffs
        a=coeffs[-1]
        for c in reversed(coeffs[:-1]):a=self.d.gate('+',self.d.gate('*',a,base),c)
        return a
    def power_y(self,n):
        if n not in self.ypow:self.ypow[n]=self.d.power(self.Y,n)
        return self.ypow[n]
    def geo_y(self,n):
        if n not in self.geom:self.geom[n]=geometric(self.d,self.Y,n)[1]
        return self.geom[n]
    def sum(self,seq):
        assert seq
        a=seq[0]
        for b in seq[1:]:a=self.d.gate('+',a,b)
        return a
    def weight(self,seq):
        key=tuple(seq)
        if key not in self.weight_cache:
            terms=[]
            for start,length in runs(seq):
                p=self.power_y(start);g=self.geo_y(length)
                terms.append(g if start==0 else p if length==1 else self.d.gate('*',p,g))
            self.weight_cache[key]=self.sum(terms)
        return self.weight_cache[key]
    def fixed(self,name,phase):
        width={'Hlow':25,'Hhigh':375,'first':1}.get(name,400);terms=[]
        for block,seq in grouped(self.profiles[name],phase):
            # Identical arithmetic coefficient tuples share an entire spatial Horner.
            coeffs=tuple(('one' if v else self.zero) if name=='first' else self.p['pf'].get(width,v) for v in block)
            if coeffs not in self.block_cache:self.block_cache[coeffs]=self.horner(self.W,coeffs)
            terms.append(self.d.gate('*',self.block_cache[coeffs],self.weight(seq)))
        return self.sum(terms)
    def corrections(self):
        ans={};qb={}
        for kind in KINDS:
            for b,(lo,hi) in enumerate([(0,51),(51,651),(651,1200)]):
                coeffs=[self.zero]*600
                for dx in range(lo,hi):
                    r=50+600*b-dx;assert 0<=r<600
                    coeffs[r]=self.p['pf'].get(400,*self.q[kind][dx])
                qb[kind,b]=self.horner(self.W,coeffs)
        self.stage('correction_short_horners')
        for phase in (0,S//2):
            terms=[]
            for kind in KINDS:
                for b in range(3):
                    coeffs=[self.zero]*960;seen=set()
                    for s,t in enumerate(self.p['occ'][kind]):
                        k=(480-b-s-phase//600)%960
                        assert k not in seen;seen.add(k);coeffs[k]=t
                    t=self.horner(self.Y,coeffs);terms.append(self.d.gate('*',qb[kind,b],t))
            ans[phase]=self.sum(terms)
        self.stage('rotated_occurrence_horners_and_products');return ans
    def build(self):
        corr=self.corrections()
        req=[('H',S//2),('B',0),('B',S//2),('F',0),('F',S//2),('Hlow',0),('Hhigh',0),('first',0)]
        f={key:self.fixed(*key) for key in req};self.stage('fixed_block_polynomials_and_weights')
        d=self.d;p=self.p;power=p['powers']
        bulk={phase:d.gate('+',d.gate('*',p['G'],f['B',phase]),corr[phase]) for phase in (0,S//2)}
        full=d.gate('+',f['H',S//2],d.gate('+',d.gate('*',p['Z'],bulk[S//2]),d.gate('*',power[V-400],f['F',S//2])))
        cut=d.gate('+',f['Hhigh',0],d.gate('+',d.gate('*',power[375],bulk[0]),d.gate('*',power[V-425],f['F',0])))
        tile=d.gate('+',d.gate('+',cut,d.gate('*',power[V-25],full)),d.gate('*',power[U-25],f['Hlow',0]))
        self.stage('fused_tile_assembly')
        return tile,f['first',0],{'stages':self.stats,'distinct_spatial_blocks':len(self.block_cache),'distinct_block_weights':len(self.weight_cache),'cached_Y_powers':sorted(self.ypow),'cached_Y_geometric_lengths':sorted(self.geom)}

class Stream:
    """Topological literal source plus exact authenticated old-main transform."""
    def __init__(self,source,prepared,profiles,q,arity):
        self.source=source;self.p=prepared;self.profiles=profiles;self.q=q;self.arity=arity
        self.n=source.n;self.M=source.M;self.A=source.A;self.digest=source.digest.copy();self.known=set();self.raw=[];self.witnesses=[];self.residuals=[];self.final=[]
        self.old_ids=array('i');self.removed=0;self.retained=0;self.used=set();self.active=None;self.removed_sections=[];self.fusion=None
    def valid(self,x):
        assert (type(x)is int and 0<=x<self.n) or (type(x)is str and (x in ('one','three') or x in self.known)),('bad operand',x,self.n)
    def gate(self,op,a,b):
        assert op in ('+','-','*');self.valid(a);self.valid(b);out=self.n
        self.digest.update(f'{out}\t{op}\t{a}\t{b}\n'.encode());self.n+=1
        if op=='*':self.M+=1
        else:self.A+=1
        return out
    def power(self,a,n):
        assert n>=0
        if n==0:return 'one'
        out=a
        for bit in bin(n)[3:]:
            out=self.gate('*',out,out)
            if bit=='1':out=self.gate('*',out,a)
        return out
    def record(self,row):self.digest.update((json.dumps(row,separators=(',',':'))+'\n').encode())
    def bind(self,x):
        if type(x)is int:
            assert 0<=x<len(self.old_ids) and self.old_ids[x]>=0,('removed or forward reference',x)
            return self.old_ids[x]
        if x.startswith('C:'):
            k=x[2:];assert k in self.p['labels'];self.used.add(k);return self.p['labels'][k]
        assert x in self.known;return x
    def arithmetic(self,row):
        oldid,op,a,b=row;assert oldid==len(self.old_ids)
        if self.active is None and a in ('C:tile:575999','C:first:575999'):
            kind=a.split(':')[1];assert op=='*'
            assert kind==('tile' if not self.removed_sections else 'first')
            if kind=='tile':
                self.old_W=b
                f=Fusion(self,self.bind(b),self.p,self.profiles,self.q)
                self.tile,self.first,self.fusion=f.build()
            else:assert b==self.old_W
            self.active=dict(kind=kind,start=oldid,step=0)
        if self.active is not None:
            sec=self.active;step=sec['step'];k=step//2;j=S-2-k
            assert 0<=j<S-1
            expected=[oldid,'*',f'C:{sec["kind"]}:{S-1}' if step==0 else oldid-1,self.old_W] if step%2==0 else [oldid,'+',oldid-1,f'C:{sec["kind"]}:{j}']
            assert row==expected,('dense Horner mismatch',row,expected)
            self.old_ids.append(-1);self.removed+=1;sec['step']+=1
            if sec['step']==2*(S-1):
                self.old_ids[-1]=self.tile if sec['kind']=='tile' else self.first
                self.removed_sections.append(dict(sec,end=oldid+1));self.active=None
        else:
            self.old_ids.append(self.gate(op,self.bind(a),self.bind(b)));self.retained+=1
    def write(self,text):
        row=json.loads(text);head=row[0]
        if type(head)is int:self.arithmetic(row)
        elif head=='raw_positive':
            assert not self.known;self.raw=row[1];assert self.raw==(['RawLeft','RawRight'] if self.arity==2 else ['RawInput'])
            self.known.update(self.raw);self.record(row)
        elif head=='positive':
            name=row[1];assert name not in self.known and name not in ('one','three') and not name.startswith('C:')
            self.known.add(name);self.witnesses.append(name);self.record(row)
        elif head=='residual_pair':
            assert row[1]==len(self.residuals);a,b=self.bind(row[2]),self.bind(row[3]);self.valid(a);self.valid(b)
            self.residuals.append((a,b,row[4]));self.record([head,row[1],a,b,row[4]])
        elif head=='eq':
            assert not self.final;self.final=[self.bind(row[1]),self.bind(row[2])]
            assert self.final==[self.n-1,self.p['labels']['0']];self.record([head,*self.final])
        else:raise ValueError(row)
        return len(text)
    def receipt(self,old):
        assert old['source_sha256']==OLD_STREAM[self.arity]
        assert self.witnesses==old['positive_witnesses'] and len(self.witnesses)==(465 if self.arity==2 else 467)
        assert len(self.residuals)==(285 if self.arity==2 else 286) and len(self.final)==2
        assert [r['kind'] for r in self.removed_sections]==['tile','first'] and self.active is None
        assert self.removed==4*(S-1) and self.retained==old['single_polynomial']['total']-self.removed
        assert self.n==self.M+self.A and self.used==set(self.p['labels'])
        return dict(status='PASS_FUSED_LITERAL_SOURCE',arity=self.arity,M=self.M,A=self.A,total=self.n,source_sha256=self.digest.hexdigest(),raw_positive_inputs=self.raw,positive_witnesses=len(self.witnesses),positive_witness_names_sha256=hashlib.sha256(json.dumps(self.witnesses,separators=(',',':')).encode()).hexdigest(),residual_metadata_records=len(self.residuals),final_equations=1,final_operands=self.final,retained_old_main_gates=self.retained,removed_dense_horner_gates=self.removed,removed_sections=self.removed_sections,old_main_source_sha256=old['source_sha256'],all_other_main_records_preserved=True,bound_constant_labels=len(self.used),unresolved_coefficient_operands=0,literal_leaves=[1,3],variable_degree_preserved=2304000,fusion=self.fusion)

def block_receipt(profiles):
    result={}
    for name in profiles:
        result[name]={}
        for phase in (0,S//2):
            gs=grouped(profiles[name],phase)
            result[name][phase]={'groups':len(gs),'blocks':[{'mask_tuple_sha256':hashlib.sha256(json.dumps(block,separators=(',',':')).encode()).hexdigest(),'positions':seq,'runs':runs(seq)} for block,seq in gs]}
    return result

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True);a=ap.parse_args()
    assert __debug__;input_pins=pins();profiles,q=load_profiles()
    occurrence=owned('owned_occurrence','owned_report47/occurrence_compiler.py');old=owned('owned_main','owned_report44/merged_source.py')
    d=occurrence.Source(digest=True);prepared=prepare(d,occurrence,profiles,q);joins={}
    for arity in (2,1):
        s=Stream(d,prepared,profiles,q,arity);receipt=old.build(stream=s,arity=arity);joins[arity]=s.receipt(receipt)
    result={'status':'PASS_BOTH_FUSED_LITERAL_SOURCES','prefix':d.receipt(),'prefix_stages':prepared['stages'],'profile_cache_by_width':prepared['pf'].hist,'joins':joins,'block_array_identities':block_receipt(profiles),'input_pins':input_pins,'source_sha256':sha(pathlib.Path(__file__)),'no_upstream_execution':True,'giant_coefficients_instantiated':False}
    with pathlib.Path(a.out).open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps({k:result[k] for k in ('status','prefix','prefix_stages','joins')},indent=2))

if __name__=='__main__':main()
