#!/usr/bin/env python3
"""New symbolic coefficient compiler. Reads JSON data only; no ant/schedule execution.
Compiles instruction specifications to arithmetic occurrence polynomials at Z=3^400.
The sink counts a literal topological (+,-,*) source and optionally hashes/emits it.
"""
import argparse, hashlib, json, pathlib

class Source:
    def __init__(self, emit=None, digest=False):
        self.n=0;self.M=0;self.A=0;self.emit=emit
        self.digest=hashlib.sha256() if digest else None
    def gate(self,op,a,b):
        assert op in ('+','-','*')
        assert all(v in ('one','three') if isinstance(v,str) else type(v) is int and 0<=v<self.n for v in (a,b))
        out=self.n;self.n+=1
        if op=='*':self.M+=1
        else:self.A+=1
        if self.emit is not None or self.digest is not None:
            line=f'{out}\t{op}\t{a}\t{b}\n'
            if self.emit is not None:self.emit.write(line)
            if self.digest is not None:self.digest.update(line.encode())
        return out
    def power(self,a,n):
        assert n>=0
        if n==0:return 'one'
        out=a
        for bit in bin(n)[3:]:
            out=self.gate('*',out,out)
            if bit=='1':out=self.gate('*',out,a)
        return out
    def receipt(self):
        return dict(M=self.M,A=self.A,total=self.n,sha256=self.digest.hexdigest() if self.digest is not None else None)

# This explicit list is the finite word-level interchange specification.
# It is data for algebraic lowering, never applied to a tape or ant state.
INTERCHANGE=(('DUP',0),('DUP',2),('DUP',1),('DUP',3),('NAND',2),('DUP',2),('NAND',1),('NAND',2),('NAND',1),('DUP',1),('DUP',0),('DUP',2),('NAND',1),('DUP',1),('NAND',0),('NAND',1),('NAND',0),('DUP',1),('DUP',3),('NAND',2),('DUP',2),('NAND',1),('NAND',2),('NAND',1))

class Occurrences:
    def __init__(self,source,program):
        self.d=source;self.p=program;self.K=program['active_columns']-1
        self.zero=source.gate('-','one','one');self.z=source.power('three',400)
        self.powers={0:'one',1:self.z};self.position='one';self.time=0
        self.events={(op,d):[self.zero]*(self.K+2) for op in ('MOVE_LEFT','MOVE_RIGHT') for d in (-1,1)}
        self.direct={op:[self.zero]*self.K for op in ('DUP','NAND')}
        self.metrics=dict(runs=0,directional_runs=0,singleton_runs=0,words=0,interchanges=0,copies=0)
    def run(self,op,start,step,length):
        assert op in ('MOVE_LEFT','MOVE_RIGHT','DUP','NAND')
        assert length>=0 and step in (-1,1)
        if not length:return
        assert 0<=start<self.K and 0<=start+step*(length-1)<self.K
        if length not in self.powers:self.powers[length]=self.d.power(self.z,length)
        nxt=self.d.gate('*',self.position,self.powers[length])
        if op in self.direct:
            assert length==1
            self.direct[op][start]=self.d.gate('+',self.direct[op][start],self.position)
            self.metrics['singleton_runs']+=1
        else:
            arr=self.events[op,step]
            # index s+1 includes the two unused exterior event coordinates -1,K.
            arr[start+1]=self.d.gate('+',arr[start+1],self.position)
            stop=start+step*length
            arr[stop+1]=self.d.gate('-',arr[stop+1],nxt)
            self.metrics['directional_runs']+=1
        self.position=nxt;self.time+=length;self.metrics['runs']+=1
    def word(self,op,m,i):
        assert op in ('DUP','NAND') and 0<=i<m
        self.metrics['words']+=1
        if op=='DUP':
            self.run('MOVE_RIGHT',m-1,-1,m-i-1);self.run('DUP',i,1,1)
        else:
            assert i<m-1
            self.run('NAND',i,1,1);self.run('MOVE_LEFT',i+1,1,m-i-2)
    def interchange(self,m,i):
        self.metrics['interchanges']+=1
        before=self.time;size=m
        for op,j in INTERCHANGE:
            self.word(op,size,i+j);size+=1 if op=='DUP' else -1
        assert size==m and self.time-before==24*(m-i)+14
    def copy(self,m,i):
        self.metrics['copies']+=1
        self.word('DUP',m,i)
        for offset in range(m-i-1):self.interchange(m+1,i+1+offset)
    def compile(self):
        # prefix_rows is deliberately not read: no saved schedule drives this compiler.
        boundaries=[0]
        for node in self.p['nodes']:
            typ=node['type']
            if typ=='RANGE':
                start,stop,step=(node[k] for k in ('start','stop','step'))
                self.run(node['op'],start,step,len(range(start,stop,step)))
            elif typ=='ROW':self.run(node['op'],node['i'],1,1)
            elif typ=='COPY':self.copy(node['m'],node['i'])
            elif typ=='GATE':
                self.copy(node['m'],node['u']);self.copy(node['m']+1,node['v']);self.run('NAND',node['m'],1,1)
            else:raise ValueError(typ)
            boundaries.append(self.time)
        assert self.time==self.p['program_rows']
        sweeps={}
        for key,events in self.events.items():
            op,step=key;v=self.zero;out=[None]*self.K
            for s in (range(self.K) if step==1 else range(self.K-1,-1,-1)):
                v=self.d.gate('+',self.d.gate('*',v,self.z),events[s+1]);out[s]=v
            sweeps[key]=out
        outputs=dict(self.direct)
        for op in ('MOVE_LEFT','MOVE_RIGHT'):
            outputs[op]=[self.d.gate('+',sweeps[op,1][s],sweeps[op,-1][s]) for s in range(self.K)]
        return outputs,dict(self.metrics,time_rows=self.time,top_level_nodes=len(self.p['nodes']),cached_lengths=len(self.powers),boundary_sha256=hashlib.sha256(json.dumps(boundaries,separators=(',',':')).encode()).hexdigest(),source=self.d.receipt())

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--program',required=True);ap.add_argument('--out',required=True);ap.add_argument('--digest',action='store_true');ap.add_argument('--emit');a=ap.parse_args()
    p=json.loads(pathlib.Path(a.program).read_text())
    sink=open(a.emit,'x') if a.emit else None
    try:
        d=Source(sink,a.digest);o=Occurrences(d,p);outputs,receipt=o.compile()
    finally:
        if sink is not None:sink.close()
    receipt.update(status='NEW_SYMBOLIC_OCCURRENCE_COMPILER',program_sha256=hashlib.sha256(pathlib.Path(a.program).read_bytes()).hexdigest(),compiler_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),output_labels={k:len(v) for k,v in outputs.items()},operations='addition, subtraction, multiplication; only literals 1 and 3',no_upstream_execution=True)
    pathlib.Path(a.out).write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
