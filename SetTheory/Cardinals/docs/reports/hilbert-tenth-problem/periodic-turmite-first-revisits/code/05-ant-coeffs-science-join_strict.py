#!/usr/bin/env python3
"""New literal-language binding adapter for inspected, pinned OWN Report44 source.
This imports only our new prefix and the authenticated own-code arithmetic generator;
no physical-ant, upstream recipe, upstream Python or upstream saved schedule executes.
"""
import argparse,hashlib,importlib.util,json,pathlib
from occurrence_compiler import Source
from full_prefix import build as build_prefix
ROOT=pathlib.Path(__file__).resolve().parent
MAIN_PIN='eafe92d6e57782347f430a4f1d6ea5693bd6a48300d2db0294b3ab7026b96395'
MAIN_STREAMS={2:'c16901162e09b07d1e0c27b28e29dcc12a9b6137391fce85e3f150a3fed37eac',1:'85a161972769207e4f5d4212214630535208f69d6736bca2b46a8aff8276a22a'}

def owned_main():
    path=ROOT/'main_source/merged_source.py'
    assert hashlib.sha256(path.read_bytes()).hexdigest()==MAIN_PIN
    spec=importlib.util.spec_from_file_location('pinned_owned_report44',path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    return mod

class Joined:
    def __init__(self,prefix,labels,arity):
        self.n=prefix.n;self.M=prefix.M;self.A=prefix.A;self.offset=prefix.n
        self.digest=prefix.digest.copy();self.labels=labels;self.arity=arity
        self.known=set();self.raw=[];self.witnesses=[];self.main_gates=0;self.residuals=0;self.equations=0;self.used=set();self.records=0
        self.final=None
    def valid(self,a):
        assert (type(a) is int and 0<=a<self.n) or (type(a) is str and (a in ('one','three') or a in self.known)),('invalid joined operand',a,self.n)
    def bind(self,a):
        if type(a) is int:
            assert 0<=a<self.main_gates
            return self.offset+a
        assert type(a) is str
        if a.startswith('C:'):
            key=a[2:];assert key in self.labels,('unresolved fixed coefficient',a)
            self.used.add(key);out=self.labels[key]
            assert out in ('one','three') if isinstance(out,str) else type(out) is int and 0<=out<self.offset
            return out
        assert a in self.known,('undeclared main coordinate',a)
        return a
    def record(self,row):
        self.digest.update((json.dumps(row,separators=(',',':'))+'\n').encode());self.records+=1
    def write(self,text):
        # Complete.record supplies exactly one canonical JSON record per write.
        row=json.loads(text);head=row[0]
        if type(head) is int:
            assert head==self.main_gates and len(row)==4
            _,op,a,b=row;assert op in ('+','-','*')
            a,b=self.bind(a),self.bind(b);self.valid(a);self.valid(b)
            self.digest.update(f'{self.n}\t{op}\t{a}\t{b}\n'.encode())
            self.n+=1;self.main_gates+=1
            if op=='*':self.M+=1
            else:self.A+=1
        elif head=='raw_positive':
            assert not self.raw and not self.known and len(row)==2
            self.raw=row[1];assert self.raw==(['RawLeft','RawRight'] if self.arity==2 else ['RawInput'])
            assert len(set(self.raw))==len(self.raw) and all(type(x) is str and x not in ('one','three') and not x.startswith('C:') for x in self.raw)
            self.known.update(self.raw);self.record(row)
        elif head=='positive':
            assert len(row)==2;name=row[1]
            assert type(name) is str and name not in self.known and name not in ('one','three') and not name.startswith('C:')
            self.known.add(name);self.witnesses.append(name);self.record(row)
        elif head=='residual_pair':
            assert len(row)==5 and row[1]==self.residuals
            a,b=self.bind(row[2]),self.bind(row[3]);self.valid(a);self.valid(b)
            self.record([head,row[1],a,b,row[4]]);self.residuals+=1
        elif head=='eq':
            assert len(row)==3 and self.equations==0
            a,b=self.bind(row[1]),self.bind(row[2]);self.valid(a);self.valid(b)
            assert a==self.n-1 and b==self.labels['0']==0
            self.record([head,a,b]);self.equations+=1;self.final=[a,b]
        else:raise ValueError(('unsupported record',row))
        return len(text)
    def receipt(self,old):
        assert old['source_sha256']==MAIN_STREAMS[self.arity]
        assert self.main_gates==old['single_polynomial']['total']
        assert self.witnesses==old['positive_witnesses']
        assert self.used==set(self.labels) and len(self.used)==1152598
        assert self.equations==1 and self.residuals==(285 if self.arity==2 else 286)
        assert self.M+self.A==self.n==self.offset+self.main_gates
        return {'status':'PASS_ACTUAL_LITERAL_JOIN','arity':self.arity,'M':self.M,'A':self.A,'total':self.n,'source_sha256':self.digest.hexdigest(),'prefix_gate_count':self.offset,'main_gate_count':self.main_gates,'old_main_stream_sha256':old['source_sha256'],'old_main_stream_identity_verified':True,'raw_positive_inputs':self.raw,'positive_witnesses':len(self.witnesses),'positive_witness_names_sha256':hashlib.sha256(json.dumps(self.witnesses,separators=(',',':')).encode()).hexdigest(),'residual_metadata_records':self.residuals,'final_equations':self.equations,'final_operands':self.final,'bound_fixed_coefficient_labels':len(self.used),'unresolved_coefficient_operands':0,'free_coefficient_declarations':0,'literal_leaves':[1,3],'variable_degree_preserved':2304000,'record_format':'Arithmetic: TSV id,op,a,b. Domain/residual/final records: compact JSONL, in old main order. Prefix precedes all main records.'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True);a=ap.parse_args()
    assert __debug__,'Assertions required'
    p=Source(digest=True)
    assets=ROOT/'data/recipe_assets'
    program=json.loads((assets/'ca/physical_program.json').read_text());anchor=json.loads((ROOT/'data/anchor_patch.json').read_text())
    labels,pr=build_prefix(p,program,anchor)
    assert p.n==29081374 and p.digest.hexdigest()=='6a01d7c1d8ee6b268d49c921b3263b578c152e49c62810d5aa877a4103cb9759'
    old=owned_main();joins={}
    for arity in (2,1):
        d=Joined(p,labels,arity);main_receipt=old.build(stream=d,arity=arity);joins[arity]=d.receipt(main_receipt)
    paths=[ROOT/'join_strict.py',ROOT/'full_prefix.py',ROOT/'occurrence_compiler.py']+list(sorted((ROOT/'main_source').rglob('*.py')))+list(sorted((ROOT/'main_source').rglob('*.json')))
    result={'status':'PASS_BOTH_ACTUAL_STRICT_JOINS','prefix':p.receipt(),'joins':joins,'pins':{str(x.relative_to(ROOT)):hashlib.sha256(x.read_bytes()).hexdigest() for x in paths},'executed_code_boundary':'Only new coefficient/profile code, this new binding adapter, and authenticated own Report44 arithmetic generator. No upstream Python, physical-ant program, color recipe, or upstream saved schedule executes.'}
    out=pathlib.Path(a.out)
    with out.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
