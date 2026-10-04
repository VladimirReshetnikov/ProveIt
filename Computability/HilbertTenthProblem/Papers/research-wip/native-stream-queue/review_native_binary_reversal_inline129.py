#!/usr/bin/env python3
"""Independent complete-array and polynomial audit; all predecessor files are data."""
import argparse
import hashlib
import json
from pathlib import Path

DEFAULT = Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
AUTHOR = {
 'native_binary_reversal_inline129.py':'fe5ffa4fdc3a8e8b4fc7cc65111936fe302cf6aeba16cde62f57489ddd8c9498',
 'native_binary_reversal_inline129.json':'aa0b923b5a7eb7100e024fdf4715a16880710a65f424a7e319c3f0db0eca3a68',
 'native_binary_reversal_inline129.md':'b2fa2c6a46d7a7500c52bcfb3259026c7321bf158b57cbabbeb0f7d330c92abb'}
PARENT = {
 'native_binary_reversal130.py':'ed6e355f365f78015e5326d087047923b47967936a95712e1c8372b0481ef0ca',
 'native_binary_reversal130.json':'1ef05ab68b9de6030d71abcdb2a3caeb2932d53b531192d99937b018d7c17197',
 'native_binary_reversal130.md':'d5af03d5d30cb3e0a851d2c2a29bf17beb6a3373657a6ca295d2a9a1804a8c73',
 'review_native_binary_reversal130.md':'544a2c6727e0292e4594ffd0f2935e0ba6e6b43039ef40056f94c003103516dc'}

def need(ok, why):
    if not ok: raise ValueError(why)
def sha(b): return hashlib.sha256(b).hexdigest()
def unique(items):
    result = {}
    for k,v in items:
        need(k not in result,'duplicate JSON key'); result[k]=v
    return result
def parse(b): return json.loads(b,object_pairs_hook=unique)
def encoded(d): return (json.dumps(d,sort_keys=True,indent=2)+'\n').encode()

class Polynomial:
    """Sparse integer polynomials with fixed-length exponent vectors."""
    def __init__(self,names):
        self.names=names; self.unit=(0,)*len(names)
    def constant(self,c): return {self.unit:c} if c else {}
    def variable(self,name):
        v=list(self.unit);v[self.names.index(name)]=1;return {tuple(v):1}
    def plus(self,p,q,sign=1):
        result=dict(p)
        for m,c in q.items():result[m]=result.get(m,0)+sign*c
        return {m:c for m,c in result.items()if c}
    def product(self,p,q):
        result={}
        for m,c in p.items():
            for n,d in q.items():
                k=tuple(a+b for a,b in zip(m,n));result[k]=result.get(k,0)+c*d
        return {m:c for m,c in result.items()if c}
    def run(self,rows,initial):
        env=dict(initial)
        for dst,op,a,b in rows:
            x=self.constant(a) if type(a)is int else env[a]
            y=self.constant(b) if type(b)is int else env[b]
            env[dst]=self.product(x,y) if op=='*' else self.plus(x,y,1 if op=='+' else -1)
        return env
    def residuals(self,env,eqs):
        def val(x):return self.constant(x) if type(x)is int else env[x]
        return [self.plus(val(a),val(b),-1)for a,b in eqs]
    def sos(self,polys):
        total={}
        for p in polys:total=self.plus(total,self.product(p,p))
        return total
    def record(self,p):
        return [{'powers':{v:k for v,k in zip(self.names,m)if k},'coefficient':c}for m,c in sorted(p.items())]

def graph_audit(rows,ports,outputs):
    available=set(ports);need(len(available)==len(ports),'unique ports');deps={}
    for row in rows:
        need(type(row)is list and len(row)==4,'row grammar')
        name,op,a,b=row;need(name not in available and op in ['+','-','*'],'unique producer/op')
        need(all(type(x)is int or type(x)is str and x in available for x in [a,b]),'topology '+name)
        available.add(name);deps[name]=[v for v in [a,b]if type(v)is str]
    used=set();pending=list(outputs)
    while pending:
        v=pending.pop()
        if type(v)is int or v in used:continue
        need(v in available,'output binding');used.add(v);pending.extend(deps.get(v,[]))
    need(used==available,'dead ports or rows '+repr(available-used))
    mul=sum(r[1]=='*' for r in rows)
    return dict(M=mul,A=len(rows)-mul,total=len(rows))

def check_variant(parent,v,scale):
    removed={'Ahat','P'}if scale else {'Ahat'}
    ports=parent['parameters_positive']+[x for x in parent['positive_witnesses']if x not in removed]
    need(v['parameters_positive']==['x','q','z']==parent['parameters_positive'],'external parameters')
    need(v['positive_witnesses']==ports[3:],'positive witness order')
    expected={r[0]:list(r)for r in parent['source']if r[0]!='congruence_right'}
    need(len(expected)==129,'parent removed row')
    expected['and__scaled_Z']=['and__scaled_Z','*',16,'scaled_reverse_sum']
    expected['and__F3']=['and__F3','+','and__scaled_Z',8]
    if scale:
        for row in expected.values():
            row[2:]=['repunit_P'if x=='P'else x for x in row[2:]]
    need({r[0]:r for r in v['source']}==expected and len(v['source'])==129,'complete producer definitions')
    if not scale:need(v['source']==[expected[r[0]]for r in parent['source']if r[0]in expected],'unreordered first chart')
    deleted=[3,0]if scale else [3]
    need(parent['comparisons'][3]==['Ahat','congruence_right'] and parent['comparisons'][0]==['repunit_P','P'],'parent boundaries')
    eq=[e for i,e in enumerate(parent['comparisons'])if i not in deleted]
    need(eq==v['comparisons'],'all retained comparisons')
    need(v['inline_scale']is scale,'scale metadata')
    count=graph_audit(v['source'],ports,[x for e in eq for x in e])
    need(count==v['producer_cost']==dict(M=66,A=63,total=129),'producer ledger')
    final=list(v['source'])
    final += [[f'new_residual_{i}','-',a,b]for i,(a,b)in enumerate(eq)]
    final += [[f'new_square_{i}','*',f'new_residual_{i}',f'new_residual_{i}']for i in range(len(eq))]
    for i in range(1,len(eq)):final.append([f'new_sum_{i}','+','new_square_0'if i==1 else f'new_sum_{i-1}',f'new_square_{i}'])
    output=f'new_sum_{len(eq)-1}'
    need(v['full_source']==final and v['output']==output,'complete literal SOS')
    cost=graph_audit(final,ports,[output])
    need(cost==v['polynomial_cost']==(dict(M=98,A=126,total=224)if scale else dict(M=99,A=128,total=227)),'polynomial ledger')
    need(v['witnesses']==len(ports)-3==(46 if scale else 47)and v['equations']==len(eq)==(32 if scale else 33),'dimensions')
    p=Polynomial(ports);variables={x:p.variable(x)for x in ports};env=p.run(final,variables)
    # Independently specify witness restorations in actual supplied variables.
    D=p.product(variables['q'],p.plus(p.product(p.plus(variables['q'],p.constant(1),-1),p.plus(variables['quotient_hat'],p.constant(1),-1)),variables['z']))
    restoration=dict(variables);restoration['Ahat']=p.plus(D,p.constant(1))
    if scale:restoration['P']=p.plus(p.product(p.plus(p.product(p.constant(2),variables['q']),p.constant(1),-1),variables['J']),p.constant(1))
    old=p.run(parent['full_source'],restoration)
    need(env['scaled_reverse_sum']==D,'restored actual D')
    common=0
    for r in v['source']:
        name=r[0];expected_value=p.plus(env[name],p.constant(16))if name=='and__scaled_Z'else env[name]
        need(old[name]==expected_value,'full retained register pullback '+name);common+=1
    oldres=p.residuals(old,parent['comparisons']);newres=p.residuals(env,eq)
    need(all(not oldres[i]for i in deleted),'removed residuals identically zero')
    need([r for i,r in enumerate(oldres)if i not in deleted]==newres,'every residual pullback')
    poly=p.sos(newres);need(poly==env[output]==old[parent['output']],'whole SOS pullback identity')
    deg=max(sum(m)for m in poly);lead={m:c for m,c in poly.items()if sum(m)==deg}
    powers={'and__w':4,'and__s':8,'and__k':4,'q':24 if scale else 12,'J'if scale else 'P':12}
    mon=tuple(powers.get(x,0)for x in ports)
    need(deg==v['degree']==(52 if scale else 40),'exact degree')
    need(lead=={mon:2**(60 if scale else 48)},'full exact leading homogeneous form')
    need(v['leading_coefficient']==lead[mon]and v['leading_monomial']==powers,'leader metadata')
    need(len(poly)==v['polynomial_terms']==(1207 if scale else 411),'full monomial count')
    degrees=[max((sum(m)for m in r),default=-1)for r in newres]
    return dict(producer_cost=count,polynomial_cost=cost,witnesses=len(ports)-3,equations=len(eq),all_ports_and_rows_live=True,
       restored_register_checks=common,retained_residual_checks=len(eq),deleted_residuals_zero=len(deleted),whole_SOS_pullback=True,
       polynomial_terms=len(poly),exact_degree=deg,leading_form=p.record(lead),residual_degrees=degrees,
       exact_polynomial_sha256=sha(encoded(p.record(poly))),changed_intermediate='parent and__scaled_Z = child and__scaled_Z + 16; all other retained values equal')

def finite_checks():
    positives=0
    for q in range(1,7):
        for z in range(1,7):
            for qh in range(1,7):
                for j in range(1,7):
                    D=q*((q-1)*(qh-1)+z);P=(2*q-1)*j+1
                    need(D+1>0 and P>=2 and 16*(D+1)-8==16*D+8,'positive total restoration')
                    positives+=1
    words=0;zeroquot=0;allones=0
    for n in range(2,10):
        q=2**n;B=2*q;P=B**n;J=sum(B**i for i in range(n));K=sum((2*B)**i for i in range(n))
        for x in range(1,q):
            bits=[(x//2**i)%2 for i in range(n)]
            z=sum(bits[i]*2**(n-1-i)for i in range(n));R=sum(bits[n-1-i]*B**i for i in range(n))
            quotient,rem=divmod(R-z,q-1);need(rem==0 and quotient>=0,'positive quotient hat')
            D=q*((q-1)*quotient+z)
            selected=sum(2**i for i in range((n+2)*n)if ((2*x*K)//2**i)%2 and ((q*J)//2**i)%2)
            need(D==selected and 0<z<q and (B-1)*J+1==P and (2*B-1)*K+1==q*P,'word/repunit identities')
            need(2*x*K<q*P and q*J<q*P,'prescribed-scale input ranges')
            words+=1;zeroquot+=quotient==0;allones+=x==q-1
    return dict(positive_restoration_assignments=positives,includes_q_one=True,words_n2_through9=words,zero_quotient_cases=zeroquot,all_ones_cases=allones,full_native_Pell_zero_tuples=0)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=DEFAULT);ap.add_argument('--author-root',type=Path)
    g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args()
    roots=[(a.author_root or a.root,AUTHOR),(a.root,PARENT)];blobs={};pins=[]
    for base,expected in roots:
        for name,h in expected.items():
            b=(base/name).read_bytes();need(sha(b)==h,'pin '+name);blobs[name]=b;pins.append(dict(name=name,bytes=len(b),sha256=h))
    author=parse(blobs['native_binary_reversal_inline129.json']);parent_packet=parse(blobs['native_binary_reversal130.json']);parent=parent_packet['certificate']
    need(author['source_sha256']==AUTHOR['native_binary_reversal_inline129.py'],'author helper binding')
    need(author['parent_json']==dict(name='native_binary_reversal130.json',bytes=len(blobs['native_binary_reversal130.json']),sha256=PARENT['native_binary_reversal130.json']),'actual parent binding')
    snapshot=encoded(parent_packet);asnapshot=encoded(author)
    need(set(author['variants'])=={'inline_output','inline_output_and_scale'},'two variants')
    results={name:check_variant(parent,author['variants'][name],scale)for name,scale in [('inline_output',False),('inline_output_and_scale',True)]}
    need(snapshot==encoded(parent_packet)and asnapshot==encoded(author),'in-memory data immutability')
    for base,expected in roots:
        for name in expected:need((base/name).read_bytes()==blobs[name],'file immutability')
    result=dict(status='PASS',reviewer_source_sha256=sha(Path(__file__).read_bytes()),pins=pins,variants=results,finite_checks=finite_checks(),
       scope='Exact arrays, all-ring pullbacks and positive restored-coordinate bijections relative to authenticated reversal130 theorem; no fresh full native-kernel proof or enormous Pell witness. Parent/author helpers never executed/imported.',
       parent_array_unchanged=True,author_array_unchanged=True,repository_mutations=False)
    receipt=encoded(result)
    if a.output:a.output.write_bytes(receipt)
    else:need(a.expect.read_bytes()==receipt,'exact reviewer replay')
    print(json.dumps({'status':'PASS','variants':{k:{f:v[f]for f in ['producer_cost','polynomial_cost','witnesses','equations','exact_degree','polynomial_terms']}for k,v in results.items()},'finite_checks':result['finite_checks'],'receipt_sha256':sha(receipt)},indent=2))
if __name__=='__main__':main()
