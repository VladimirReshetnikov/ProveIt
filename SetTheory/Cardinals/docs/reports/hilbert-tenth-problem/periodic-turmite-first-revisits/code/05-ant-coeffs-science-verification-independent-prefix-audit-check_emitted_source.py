#!/usr/bin/env python3
"""Inspect-approved new compiler with an independent validating arithmetic sink.

This runs only the newly authored symbolic compiler and finite JSON set helpers.
It does not import/execute upstream code, saved schedules or any ant/controller.
All gates are independently reference-checked, counted, hashed and evaluated
modulo a small prime. Every old coefficient label is then checked. Modular
checks supplement the exact algebra/geometry proofs; they do not replace them.
"""
import array
import hashlib
import importlib.util
import json
import sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
NEW=Path('/workspace/shared/ant-coefficient-compression')
ASSETS=Path('/workspace/shared/report44-recovery-20261004/certificate/dependencies/recipe_assets')
ANCHOR=Path('/workspace/shared/report44-recovery-20261004/certificate/data/anchor_patch.json')
PROFILES=Path('/workspace/shared/ant-motif-overlap/profiles')
P=1000003

def need(ok,reason):
    if not ok:raise ValueError(reason)

class AuditSink:
    def __init__(self):
        self.values=array.array('I');self.n=0;self.M=0;self.A=0;self.sha=hashlib.sha256()
    def value(self,r):
        if type(r) is str:
            need(r in ('one','three'),('Unpaid literal',r));return 1 if r=='one' else 3
        need(type(r) is int and 0<=r<self.n,('Bad reference',r,self.n))
        return self.values[r]
    def gate(self,op,a,b):
        x=self.value(a);y=self.value(b)
        need(op in ('+','-','*'),('Bad opcode',op))
        result=(x+y if op=='+' else x-y if op=='-' else x*y)%P
        out=self.n;self.sha.update(f'{out}\t{op}\t{a}\t{b}\n'.encode())
        self.values.append(result);self.n+=1
        if op=='*':self.M+=1
        else:self.A+=1
        return out
    def power(self,a,n):
        # Independently authored left-to-right binary chain; identical specified
        # grammar is required to reproduce the candidate's canonical stream.
        need(type(n) is int and n>=0,('Exponent',n))
        if n==0:return 'one'
        result=a
        bit=1 << (n.bit_length()-2) if n>1 else 0
        while bit:
            result=self.gate('*',result,result)
            if n&bit:result=self.gate('*',result,a)
            bit//=2
        return result
    def receipt(self):return dict(M=self.M,A=self.A,total=self.n,sha256=self.sha.hexdigest())

def load_new():
    sys.path.insert(0,str(NEW))
    spec=importlib.util.spec_from_file_location('inspected_new_prefix',NEW/'full_prefix.py')
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    base=m.Occurrences
    class Observed(base):
        def compile(self):
            result=super().compile();m.audit_occurrence_outputs=result[0];return result
    m.Occurrences=Observed
    return m

def main():
    # Sources were inspected as text before this audit execution.
    m=load_new();program=json.loads((ASSETS/'ca/physical_program.json').read_text())
    anchor=json.loads(ANCHOR.read_text())
    d=AuditSink();labels,result=m.build(d,program,anchor)
    reported=json.loads((NEW/'full-prefix-receipt.json').read_text())
    need(d.receipt()==reported['source'],('Source mismatch',d.receipt(),reported['source']))
    need(result['output_alias_sha256']==reported['output_alias_sha256'],'Alias stream mismatch')
    for label,ref in labels.items():d.value(ref)
    S=576000;U=481238074400;V=U//2;R=601547591
    pow3=[pow(3,j,P) for j in range(400)]
    mask_cache={}
    def ternary(mask):
        if mask not in mask_cache:mask_cache[mask]=sum(pow3[j] for j in range(mask.bit_length()) if mask>>j&1)%P
        return mask_cache[mask]
    profiles={}
    rawH=None
    for kind in ('H','B','F'):
        dictionary=[int(v,16) for v in json.loads((PROFILES/f'{kind}.masks.json').read_text())['mask_hex_by_id']]
        ids=array.array('H');ids.frombytes((PROFILES/f'{kind}.u16le').read_bytes())
        if sys.byteorder!='little':ids.byteswap()
        profiles[kind]=[ternary(dictionary[i]) for i in ids]
        if kind=='H':rawH=[dictionary[i] for i in ids]
    corr=[0]*S
    for kind in ('DUP','NAND','MOVE_LEFT','MOVE_RIGHT'):
        q=json.loads((PROFILES/f'Q_{kind}.json').read_text())
        pairs=[(int(a,16),int(b,16)) for a,b in q['signed_masks_by_id']]
        values=[(ternary(a)-ternary(b))%P for a,b in pairs]
        nonzero=[(dx,values[i]) for dx,i in enumerate(q['profile_id_by_dx']) if pairs[i]!=(0,0)]
        for s,tref in enumerate(m.audit_occurrence_outputs[kind]):
            t=d.value(tref)
            for dx,v in nonzero:
                x=600*(s+1)+dx
                need(0<=x<S,'Pair exceeds horizontal domain')
                corr[x]=(corr[x]+t*v)%P
    z=pow(3,400,P)
    # Division-free independent geometric-sum check by binary affine composition.
    def geom(n):
        power=1;total=0;block_power=z;block_total=1
        while n:
            if n&1:total=(total+power*block_total)%P;power=power*block_power%P
            block_total=block_total*(1+block_power)%P;block_power=block_power*block_power%P;n//=2
        return total
    G=geom(R)
    bulk=[(profiles['B'][x]*G+corr[x])%P for x in range(S)]
    checked={'tile':0,'first':0,'anchor':0,'named_and_small':0}
    for j in range(S):
        x=(288650-j)%S;opposite=(x-S//2)%S
        # Direct physical intervals b in [75,2V+75), with period-2 staggering.
        expected=(ternary(rawH[x]>>25)
            +pow(3,375,P)*bulk[x]
            +pow(3,V-425,P)*profiles['F'][x]
            +pow(3,V-25,P)*profiles['H'][opposite]
            +pow(3,V+375,P)*bulk[opposite]
            +pow(3,2*V-425,P)*profiles['F'][opposite]
            +pow(3,2*V-25,P)*ternary(rawH[x]&((1<<25)-1)))%P
        need(d.value(labels[f'tile:{j}'])==expected,('Tile residue',j))
        need(d.value(labels[f'first:{j}'])==((rawH[x]>>25)&1),('First bit',j))
        checked['tile']+=1;checked['first']+=1
    expected_anchor=[0]*584
    for a,b,old,new in anchor['patch']:
        expected_anchor[289200-a]+=(new-old)*pow(3,b+144,P)
    for j,e in enumerate(expected_anchor):
        need(d.value(labels[f'anchor:{j}'])==e%P,('Anchor residue',j));checked['anchor']+=1
    targets={'Cu':pow(3,U,P),'Cx':pow(3,U,P)-1,'Cbase':pow(3,U-219,P),'C198':pow(3,198,P),
             'EndpointK':pow(3,481225262775,P),'EndpointD':pow(3,U,P)-2}
    targets.update({str(i):i for i in (0,1,2,3,4,6,8,9)})
    for name,e in targets.items():
        need(d.value(labels[name])==e%P,('Named coefficient',name));checked['named_and_small']+=1
    wanted={f'{kind}:{j}' for kind,n in (('tile',S),('first',S),('anchor',584)) for j in range(n)}|set(targets)
    need(set(labels)==wanted,'Old coefficient label set differs')
    need(sum(checked.values())==1152598,'Label count')
    receipt=dict(status='PASS_INDEPENDENT_SINK_AND_ALL_LABEL_CHECK',source=d.receipt(),
                 coefficient_labels_checked=checked,total_labels=len(labels),modulus=P,
                 output_alias_sha256=result['output_alias_sha256'],
                 caveat='Modular all-label tests supplement the exact event, geometry and coefficient-identity proof. No huge fixed coefficient is expanded.',
                 new_witnesses=0,new_equations=0,only_literal_leaves=[1,3],
                 checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (HERE/'emitted-source-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
