#!/usr/bin/env python3
"""Splice the separately supplied own-code pair dilation DAG into the fixed wrapper.
Only JSON arithmetic data are read. No recoder script or upstream code is run.
The splice uses the wrapper's existing G=W^576000 wire and expression aliases.
"""
if not __debug__:raise RuntimeError('Optimized mode unsupported: checks require assertions')
import argparse,hashlib,json,pathlib,os
from bridge_dag import DAG,V,build_uniform_wrapper,uniform_wrapper_cost,strict_cost

def output_destination(path):
    """Require a fresh destination outside this source tree; never overwrite."""
    path=pathlib.Path(path)
    if os.path.lexists(path):raise FileExistsError('Output already exists')
    parent=path.parent.resolve(strict=True)
    if not parent.is_dir():raise ValueError('Output parent must be a directory')
    dest=parent/path.name
    root=pathlib.Path(__file__).resolve().parent
    if dest==root or root in dest.parents:raise ValueError('Output must be outside the source tree')
    if os.path.lexists(dest):raise FileExistsError('Output already exists')
    return dest

def save_new_output(path,text):
    dest=output_destination(path)
    with dest.open('x',encoding='utf-8') as stream:stream.write(text)

class PairSource:
    def __init__(self,path):
        raw=pathlib.Path(path).read_bytes();self.sha256=hashlib.sha256(raw).hexdigest()
        data=json.loads(raw);assert set(data)=={'nodes','equations','witnesses','outputs'}
        assert type(data['outputs']) is dict and set(data['outputs'])=={'A','B','T'}
        self.nodes=data['nodes'];self.witnesses=data['witnesses']
        # Normalize the already-inlined source to a local output-binding view.
        # These three bindings are aliases, never asserted equations.
        self.equations=data['equations']+[[key,data['outputs'][key]] for key in ['A','B','T']]
        assert len(set(self.witnesses))==len(self.witnesses)
        assert all(type(w) is str and w not in {'G','RawLeft','RawRight','A','B','T'} for w in self.witnesses)
        known=set(self.witnesses)|{'G','RawLeft','RawRight'};counts={'M':0,'A':0};self.numerals=set()
        def ref(x):
            if type(x) is int:self.numerals.add(x);return
            assert type(x) is str and x in known,x
        for i,row in enumerate(self.nodes):
            assert type(row) is list and len(row)==4
            out,op,a,b=row
            assert out=='g'+str(i) and out not in known and op in ['+','-','*']
            ref(a);ref(b);known.add(out);counts['M' if op=='*' else 'A']+=1
        assert [eq[0] for eq in self.equations[-3:]]==['A','B','T']
        self.outputs={eq[0]:eq[1] for eq in self.equations[-3:]}
        for eq in self.equations[:-3]:
            assert len(eq)==2
            ref(eq[0]);ref(eq[1])
        for val in self.outputs.values():ref(val)
        self.cost=dict(counts,total=len(self.nodes),equations=len(self.equations)-3,positive_witnesses=len(self.witnesses))

class Spliced(DAG):
    def __init__(self,pair,period_y=V,emit=False):
        super().__init__(emit);self.pair=pair;self.period_y=period_y;self.radix=None;self.aliases=None
        self.shared_radix_calls=0;self.recoder_start=None;self.recoder_end=None
    def power(self,a,n):
        result=super().power(a,n)
        if a=='W' and n==self.period_y:
            assert self.radix is None
            self.radix=result;self.shared_radix_calls+=1
        return result
    def inject(self):
        assert self.radix is not None and self.aliases is None
        mapping={'G':self.radix,'RawLeft':'RawLeft','RawRight':'RawRight'}
        for name in self.pair.witnesses:mapping[name]=self.witness('Recoder:'+name)
        def tr(x):return 'C:'+str(x) if type(x) is int else mapping[x]
        self.recoder_start=self.nodes
        for out,op,a,b in self.pair.nodes:mapping[out]=super().gate(op,tr(a),tr(b))
        self.recoder_end=self.nodes
        for a,b in self.pair.equations[:-3]:super().eq(tr(a),tr(b))
        self.aliases={'Dilation'+name:tr(val) for name,val in self.pair.outputs.items()}
    def gate(self,op,a,b):
        if a in ['DilationA','DilationB','DilationT'] or b in ['DilationA','DilationB','DilationT']:
            if self.aliases is None:self.inject()
            a=self.aliases.get(a,a);b=self.aliases.get(b,b)
        return super().gate(op,a,b)

def compose(path,period_y=V,emit=False):
    pair=PairSource(path);d=Spliced(pair,period_y,emit)
    receipt=build_uniform_wrapper(period_y,dag=d)
    assert d.aliases is not None and d.shared_radix_calls==1
    want={k:uniform_wrapper_cost(period_y)[k]+pair.cost[k] for k in ['M','A','total','equations','positive_witnesses']}
    assert all(receipt[k]==val for k,val in want.items()),(receipt,want)
    receipt.update(pair_source_sha256=pair.sha256,pair_inline_cost=pair.cost,
                   recoder_source_interval=[d.recoder_start,d.recoder_end],
                   shared_radix_chain_count=d.shared_radix_calls,
                   output_aliases=d.aliases,pair_integer_literals=sorted(pair.numerals),
                   claimed_scope='All-length initialization component conditional on separately proved pair recoder theorem and inherited parent geometry. No complete universal history/endpoint total.')
    assert pair.numerals <= {0,1,2,3,4}
    strict=strict_cost();strict['A']+=1;strict['total']+=1
    receipt['strict_combined_constant_prefix']=strict
    receipt['strict_initialization_total']=receipt['total']+strict['total']
    return receipt

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--pair-dag',required=True,type=pathlib.Path);parser.add_argument('--output',type=pathlib.Path);parser.add_argument('--emit',action='store_true');args=parser.parse_args()
    if args.output:output_destination(args.output)
    result=compose(args.pair_dag,emit=args.emit);payload=json.dumps(result,indent=2)+'\n'
    if args.output:save_new_output(args.output,payload)
    print(payload,end='')
