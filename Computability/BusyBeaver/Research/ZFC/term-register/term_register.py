"""Executable Wade-structured inc/decrement ReadNode; no complete TM count.

Source selection is pinned by recover_wade_dag.git_bytes. All new operations
below lower to the existing Sequence/Register interface. Host arithmetic occurs
only in independent test/reference utilities, never in the generated helper.
"""
from pathlib import Path
import importlib.util,sys

REGISTERS=('candidate','index','cursor','ok','is_zero','tag','left','right',
           'count','node_number','todo','cmp_a','cmp_b','quotient','bit',
           'unary_loop','copy_scratch','less')


def load_backend(repo,scratch):
    research=repo/'Computability/BusyBeaver/Research/ZFC'
    spec=importlib.util.spec_from_file_location('pinned_recover',research/'recover_wade_dag.py')
    helper=importlib.util.module_from_spec(spec);sys.modules[spec.name]=helper;spec.loader.exec_module(helper)
    scratch.mkdir(parents=True,exist_ok=True)
    for name in ('TMBuilder.py','tm.py','tmdb.py','LICENSE.wade'):
        (scratch/name).write_bytes(helper.git_bytes(None,'ZF/generator/'+name))
    sys.path.insert(0,str(scratch));import TMBuilder
    return TMBuilder


def seq(*items):
    items=[x for x in items if x!=()]
    if not items:return ()
    if len(items)==1:return items[0]
    return items[0],seq(*items[1:])


class Program:
    def __init__(self,backend):
        self.b=backend.TMBuilder();self.r={n:self.b.reg(n) for n in REGISTERS};self.labels=0
    def clear(self,n):return self.b.while_decnz(self.r[n],())
    def inc(self,n):return self.r[n].inc
    def dec(self,n):return self.r[n].decnz
    def move(self,out,source):return self.b.while_decnz(self.r[source],self.inc(out))
    def copy(self,out,source):
        assert out!=source and 'copy_scratch' not in (out,source)
        return seq(self.clear(out),self.clear('copy_scratch'),
            self.b.while_decnz(self.r[source],seq(self.inc(out),self.inc('copy_scratch'))),
            self.move(source,'copy_scratch'))
    def branch(self,n,positive=(),zero=()):
        """Nondestructive zero test, resolved into actual break levels."""
        self.labels+=1;label='case'+str(self.labels)
        return self.b.label(label,seq(seq(self.dec(n),seq(self.inc(n),positive,'break_'+label)),zero))
    def guarded(self,body):return self.branch('ok',body)
    def pop(self):
        """ok1,cursor>0 -> bit=(n-1)%2,cursor=(n-1)//2; empty clearsok.

        All operations are increment/decrement. Quotient is scratch and is zero
        on return; bit is0/1. On already failed input this helper is inert except
        resetting its local bit/quotient scratch.
        """
        pair=self.branch('cursor',seq(self.dec('cursor'),self.inc('quotient')),self.inc('bit'))
        positive=seq(self.dec('cursor'),self.b.while_decnz(self.r['cursor'],pair),self.move('cursor','quotient'))
        return seq(self.clear('bit'),self.clear('quotient'),self.guarded(self.branch('cursor',positive,self.clear('ok'))))
    def unary(self,out):
        assert out not in ('cursor','ok','bit','quotient','unary_loop')
        body=seq(self.pop(),self.guarded(self.branch('bit',seq(self.inc(out),self.inc('unary_loop')))))
        return seq(self.clear(out),self.clear('unary_loop'),self.guarded(self.inc('unary_loop')),
                   self.b.while_decnz(self.r['unary_loop'],body))
    def fixed2(self,out):
        return seq(self.clear(out),self.pop(),self.guarded(self.branch('bit',seq(self.inc(out),self.inc(out)))),
                   self.pop(),self.guarded(self.branch('bit',self.inc(out))))
    def lt(self,a,b):
        """Preserve a,b; less is the result. All comparison scratch is cleared."""
        assert a not in ('cmp_a','cmp_b','less') and b not in ('cmp_a','cmp_b','less')
        return seq(self.clear('less'),self.copy('cmp_a',a),self.copy('cmp_b',b),
            self.b.while_decnz(self.r['cmp_a'],self.branch('cmp_b',self.dec('cmp_b'),self.clear('cmp_a'))),
            self.branch('cmp_b',self.inc('less')),self.clear('cmp_b'))
    def require_lt(self,a,b):return self.guarded(seq(self.lt(a,b),self.branch('less',(),self.clear('ok'))))
    def read_node(self):
        work=[n for n in REGISTERS if n not in ('candidate','index')]
        record=seq(self.branch('count',self.dec('count'),self.clear('ok')),
            self.guarded(seq(self.inc('node_number'),self.fixed2('tag'),self.unary('left'),self.unary('right'),
                self.require_lt('left','node_number'),self.require_lt('right','node_number'),
                self.guarded(self.branch('tag',(),self.branch('left',(),self.branch('right',(),self.clear('ok'))))))))
        body=seq(*(self.clear(n) for n in work),self.inc('ok'),self.copy('cursor','candidate'),self.unary('count'),
            self.guarded(self.branch('index',seq(self.copy('todo','index'),
                self.b.while_decnz(self.r['todo'],self.guarded(record))),self.inc('is_zero'))),
            self.branch('ok',(),seq(*(self.clear(n) for n in ('is_zero','tag','left','right')))),
            *(self.clear(n) for n in ('count','node_number','todo','cmp_a','cmp_b','quotient','bit','unary_loop','copy_scratch','less')))
        root=self.b.add_sequence(body);self.b.sequences[root].name='main().0';return root


def execute(builder,root,values,fuel=10_000_000):
    """Literal structured Wade semantics over increment/decrement registers."""
    remaining=fuel;ops=0;calls=0;byname={n:i for i,n in enumerate(REGISTERS)}
    def run(edge):
        nonlocal remaining,ops,calls
        remaining-=1;calls+=1
        if remaining<0:raise RuntimeError('register interpreter fuel exhausted')
        if isinstance(edge,(tuple,list)):
            edge=builder.add_sequence(edge)
        if isinstance(edge,int):
            while True:
                left,right=builder.sequences[edge].seq
                result=run(left)
                if result[0]=='break':return ('normal',) if result[1]==1 else ('break',result[1]-1)
                if result[0]!='normal':return result
                result=run(right)
                if result[0]=='continue':
                    if result[1]==1:continue
                    return 'continue',result[1]-1
                return result
        if edge.startswith('_break.'):
            level=int(edge.split('.')[1])
            return ('normal',) if level==0 else ('break',level)
        if edge.startswith('_continue.'):return 'continue',int(edge.split('.')[1])
        if edge=='halt':return 'halt',
        _,name,kind=edge.split('.');j=byname[name];ops+=1
        if kind=='inc':values[j]+=1;return 'normal',
        assert kind=='decnz'
        if values[j]:values[j]-=1;return 'normal',
        return 'break',1
    result=run(root)
    return {'control':result,'register_operations':ops,'structured_calls':calls}


def word_code(bits):
    out=0
    for bit in reversed(bits):out=2*out+int(bit)+1
    return out


def code_word(n):
    out=[]
    while n:
        n,bit=divmod(n-1,2);out.append(str(bit))
    return ''.join(out)


def reference(bits,index):
    """Selected-prefix semantics, deliberately NOT full-certificate decoding."""
    pos=0;ok=1;zero=tag=left=right=0
    def bit():
        nonlocal pos,ok
        if pos==len(bits):ok=0;return 0
        b=int(bits[pos]);pos+=1;return b
    def unary():
        out=0
        while ok:
            b=bit()
            if not ok or b==0:break
            out+=1
        return out
    count=unary()
    if ok and index==0:zero=1
    elif ok:
        for j in range(1,index+1):
            if not ok:break
            if count==0:ok=0;break
            count-=1
            tag=2*bit() if ok else 0
            if ok:tag+=bit()
            left=unary() if ok else 0;right=unary() if ok else 0
            if ok and not(left<j and right<j):ok=0
            if ok and tag==left==right==0:ok=0
    if not ok:zero=tag=left=right=0
    return {'ok':ok,'is_zero':zero,'tag':tag,'left':left,'right':right,'cursor':word_code(bits[pos:])}
