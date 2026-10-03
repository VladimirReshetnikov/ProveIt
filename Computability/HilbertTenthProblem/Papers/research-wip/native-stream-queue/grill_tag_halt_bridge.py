#!/usr/bin/env python3
"""Exact corrected Genera-to-Grill halt cleanup; no ordinary-input universality claim."""
import argparse, collections, hashlib, itertools, json
from pathlib import Path

if not __debug__:
    raise RuntimeError('Run without -O')

SOURCES = {
    'grill': 'https://esolangs.org/w/index.php?title=Grill_Tag&oldid=181950',
    'genera': 'https://esolangs.org/w/index.php?title=Genera_Tag&oldid=182460',
    'live_grill_checked': 'https://esolangs.org/wiki/Grill_Tag',
    'live_genera_checked': 'https://esolangs.org/wiki/Genera_Tag',
}
REFERENCE = 'review_grill_encoding_e.py'
REFERENCE_SHA = '66c64fc95574b4d938a3a05e443215f802825677129a17e3cd38fae4150a12f3'

def require(ok, message):
    if not ok: raise ValueError(message)

def digest(x):
    return hashlib.sha256(x if isinstance(x, bytes) else x.encode()).hexdigest()

def exact(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if type(a) in (list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def natural(x):return type(x) is int and x>=0

def grill(n):
    require(natural(n), 'natural grill length')
    return '0'+'10'*n

def schema(widths, rules, halt):
    require(type(widths) is tuple and len(widths)>=2 and all(type(w) is int and w in (0,1) for w in widths), 'width tuple')
    n=len(widths)
    require(halt is None or type(halt) is int and 0<=halt<n, 'halt index')
    require(type(rules) is dict, 'rule map')
    active=[y for y in range(n) if y!=halt]
    require(set(rules)==set(itertools.product(range(2),active)), 'complete nonhalting rules')
    for k,v in rules.items():
        require(type(k) is tuple and len(k)==2 and all(type(i) is int for i in k), 'rule key type')
        require(type(v) is tuple and len(v)==2 and all(type(y) is int and 0<=y<n for y in v), 'two-symbol production')
    return n,28*(n+1)

def encode(y, widths, mode, *, halt=None, published=False):
    require(type(y) is int and 0<=y<len(widths), 'symbol')
    require(type(widths) is tuple and all(type(w) is int and w in (0,1) for w in widths), 'widths')
    require(mode in ('E','L','R') and type(published) is bool,'encoding mode')
    require(halt is None or type(halt) is int and 0<=halt<len(widths),'halt index')
    a=28*(len(widths)+1)
    extra=3*a//2 if y==halt else 7*a*(1-widths[y])
    if mode=='E':
        # For y==halt, E* is an intermediate cleanup word, not a source input.
        return '0'*(14*y+7)+grill(a-3)+grill(7)+grill(a-(2 if published else 4))+'0'*(3*a-14*y-10+extra)
    if mode=='L':
        return '0'*(a-3)+grill(14*y+7)+grill(3)+grill(3*a-14*y-10)+'10'*extra
    return '0'+grill(14*y+7)+grill(3)+grill(3*a-14*y-10+extra)+'0'*(a-4)

def compile_program(widths,rules,*,halt=None):
    n,a=schema(widths,rules,halt)
    runs=[0]*(14*a);written=set()
    for p,y in itertools.product(range(2),range(n)):
        local=[(28*y+17,a-3),(28*y+19,7),(28*y+21,a-4),
               (28*y+a+13,a-3),(28*y+a+15,7),(28*y+a+17,a-4)]
        if y!=halt:
            u,v=rules[p,y]
            def extra(z):return 3*a//2 if z==halt else 7*a*(1-widths[z])
            local.extend([(14*y+2*a+3,14*u+7),(14*y+2*a+5,3),
                (14*y+2*a+7,3*a-14*u-10+extra(u)),(14*y+2*a+9,0),
                (14*y+2*a+11,14*v+7),(14*y+2*a+13,3),
                (14*y+2*a+15,3*a-14*v-10+extra(v))])
        for k,value in local:
            k+=7*a*p
            require(0<=k<len(runs) and k not in written and k%2==1 and natural(value),'disjoint exact run slots')
            runs[k]=value;written.add(k)
    require(sum(v>0 for v in runs)==24*n-(12 if halt is not None else 0),'exact nonzero run count')
    return tuple(runs)

def generation(word,phase,runs):
    require(type(word) is str and set(word)<=set('01'),'binary word')
    require(type(phase) is int and 0<=phase<len(runs),'phase')
    require(type(runs) is tuple and runs and all(natural(n) for n in runs),'program')
    out=''.join(grill(runs[(phase+i)%len(runs)]) for i,c in enumerate(word) if c=='1')
    return out,(phase+len(word))%len(runs)

def literal_fifo(word,phase,runs,limit):
    # Independent microstep oracle; does not call generation or grill.
    q=collections.deque(int(c) for c in word);steps=0;h=hashlib.sha256()
    while q:
        require(steps<limit,'FIFO bound exceeded')
        bit=q.popleft();n=runs[phase]
        if bit:
            q.append(0)
            for _ in range(n):q.append(1);q.append(0)
        h.update(f'{phase}:{bit}:{n}:{len(q)};'.encode())
        phase=(phase+1)%len(runs);steps+=1
    return dict(steps=steps,final_phase=phase,trace_sha256=h.hexdigest())

def lr_word(v,widths,halt):
    return ''.join(encode(y,widths,'L' if i%2==0 else 'R',halt=halt) for i,y in enumerate(v))

def cleanup(v,widths,runs,phase,halt):
    require(type(v) is tuple and len(v)>0 and len(v)%2==0 and v.count(halt)==1,'one halt in an even word')
    a=28*(len(widths)+1);require(phase in (0,7*a),'normal generation phase')
    j=v.index(halt);before=v[:j];after=v[j+1:]
    word=lr_word(v,widths,halt)
    tail_ones=sum((3*a+7*a*(1-widths[y])) for y in after)
    expected=''.join(encode(y,widths,'E',halt=halt) for y in before)+encode(halt,widths,'E',halt=halt)+'0'*tail_ones
    first,p1=generation(word,phase,runs)
    require(first==expected and p1==(phase+3*a)%(14*a),'first halt cleanup word/phase')
    second,p2=generation(first,p1,runs)
    require(second=='0'*(2*a*(j+1)),'second cleanup all-zero word')
    third,p3=generation(second,p2,runs)
    require(third=='','last cleanup empty')
    lengths=[len(word),len(first),len(second)]
    require(all(lengths),'all preceding generations nonempty')
    require(lengths[0]==sum(10*a if y==halt else 7*a+14*a*(1-widths[y]) for y in v),'LR length formula')
    require(lengths[1]==sum(7*a+7*a*(1-widths[y]) for y in before)+17*a//2+tail_ones,'E-star length formula')
    return dict(symbols=list(v),halt_index=j,initial_phase=phase,generation_lengths=lengths,
                remaining_steps=sum(lengths),final_phase=p3,
                words_sha256=[digest(word),digest(first),digest(second)])

def verify(root):
    source=Path(root)/REFERENCE;data=source.read_bytes();require(digest(data)==REFERENCE_SHA,'reference pin')
    old={'__name__':'_pinned_grill_reference','__file__':str(source)};exec(compile(data,str(source),'exec'),old)
    counts=collections.Counter();proof=hashlib.sha256();fixtures=[]
    # The existing nonhalt compiler is an exact specialization of this transcription.
    for bits in itertools.product(range(2),repeat=4):
        rules={(p,y):(bits[2*p+y],1-bits[2*p+y]) for p,y in itertools.product(range(2),repeat=2)}
        for widths in itertools.product(range(2),repeat=2):
            q=compile_program(widths,rules)
            require(list(q)==old['compiler'](rules,widths,84),'old complete program specialization')
            for y,mode in itertools.product(range(2),('E','L','R')):
                require(encode(y,widths,mode)==old['encoding'](y,widths[y],84,mode),'old encoding specialization')
            counts['prior_program_specializations']+=1;counts['prior_encoding_specializations']+=6
    # All local E transitions for alphabets of size2..4 and all consistent nonhalt widths.
    for n in range(2,5):
        halt=n-1;a=28*(n+1)
        for w in itertools.product(range(2),repeat=n-1):
            widths=w+(0,)
            base={(p,y):(0,0) for p,y in itertools.product(range(2),range(n-1))}
            for p,y,u,v in itertools.product(range(2),range(n-1),range(n),range(n)):
                rules=dict(base);rules[p,y]=(u,v);q=compile_program(widths,rules,halt=halt)
                actual,next_phase=generation(encode(y,widths,'E',halt=halt),7*a*p,q)
                expected=encode(u,widths,'L',halt=halt)+encode(v,widths,'R',halt=halt)
                require(actual==expected and next_phase==7*a*((p+widths[y])%2),'E production, including halt')
                counts['local_E_word_phase_identities']+=1;proof.update(digest(actual).encode())
    # Local support and normal/shifted recoding for many independently varied scales.
    for n in range(2,13):
        a=28*(n+1);halt=n-1;widths=tuple(y%2 for y in range(n))
        rules={(p,y):((y+p)%n,(y+1+p)%n) for p,y in itertools.product(range(2),range(n-1))}
        q=compile_program(widths,rules,halt=halt)
        support={i%(7*a) for i,k in enumerate(q) if k}
        require(all(i%2 and 0<i<5*a//2 for i in support),'odd short support')
        require(support.isdisjoint({(i+3*a)%(7*a) for i in support}),'support shifted disjoint')
        counts['modular_support_bounds']+=1
        for y,p,mode in itertools.product(range(n),range(2),('L','R')):
            word=encode(y,widths,mode,halt=halt);out,_=generation(word,7*a*p,q)
            require(out==encode(y,widths,'E',halt=halt),'normal LR recoding incl halt-star')
            shifted,_=generation(word,7*a*p+3*a,q)
            require(shifted=='0'*word.count('1'),'shifted LR erasure')
            counts['normal_LR_identities']+=1;counts['shifted_LR_identities']+=1
        for y,p in itertools.product(range(n),range(2)):
            word=encode(y,widths,'E',halt=halt);out,_=generation(word,7*a*p+3*a,q)
            require(out=='0'*(2*a),'shifted E/star erasure')
            counts['shifted_E_identities']+=1
    # Exhaustive bounded halt placements: n2/3, all nonhalt width assignments,
    # every even word of length2,4,6 containing exactly one halt, both phases.
    for n in (2,3):
        halt=n-1;a=28*(n+1)
        for w in itertools.product(range(2),repeat=n-1):
            widths=w+(0,);rules={(p,y):((y+p)%n,(y+1)%n) for p,y in itertools.product(range(2),range(n-1))}
            q=compile_program(widths,rules,halt=halt)
            for length in (2,4,6):
                for pos in range(length):
                    for rest in itertools.product(range(n-1),repeat=length-1):
                        v=rest[:pos]+(halt,)+rest[pos:]
                        for phase in (0,7*a):
                            f=cleanup(v,widths,q,phase,halt)
                            proof.update(json.dumps(f,sort_keys=True).encode());counts['complete_halt_cleanup_cases']+=1
    # Genuine source-to-empty cases with halt in either output slot, both widths
    # and both initial positions. The literal FIFO trace begins at the E input.
    for width,pos,initial_phase in itertools.product(range(2),range(2),range(2)):
        widths=(width,0);halt=1;a=84;pair=(halt,0) if pos==0 else (0,halt)
        rules={(p,0):pair for p in range(2)};q=compile_program(widths,rules,halt=halt)
        initial=encode(0,widths,'E',halt=halt);v,phase=generation(initial,initial_phase*7*a,q)
        require(v==lr_word(pair,widths,halt),'genuine produced halt word')
        f=cleanup(pair,widths,q,phase,halt);f.update(width=width,source_initial_phase=initial_phase,
            source_initial_word_sha256=digest(initial),program_sha256=digest(json.dumps(q)),
            total_first_halt=len(initial)+f['remaining_steps'])
        fifo=literal_fifo(initial,initial_phase*7*a,q,f['total_first_halt'])
        require(fifo['steps']==f['total_first_halt'] and fifo['final_phase']==f['final_phase'],'first-empty FIFO equality')
        f['fifo']=fifo;fixtures.append(f);counts['independent_first_empty_traces']+=1
    # The E prose discrepancy is preserved explicitly; never silently repaired.
    for n in range(2,13):
        widths=tuple(y%2 for y in range(n))
        for y in range(n):
            require(len(encode(y,widths,'E',published=True))==len(encode(y,widths,'E'))+4,'E typo remains four bits')
            counts['published_E_four_bit_discrepancies']+=1
    # Exact numerical E encoding: a concrete port specification for a future loader.
    def value(word):return int(word[::-1],2) if word else 0
    for n in range(2,13):
        a=28*(n+1);g=lambda k:2*(4**k-1)//3
        A=2**7*(g(a-3)+2**(2*a-5)*g(7)+2**(2*a+10)*g(a-4))
        for width in (0,1):
            widths=(width,)*n
            for y in range(n):
                word=encode(y,widths,'E')
                require(value(word)==A*2**(14*y),'literal E numeral factorization')
                require(len(word)==7*a*(2-width),'exact E width')
                counts['E_numeral_and_width_identities']+=1
    # Binary input alphabet0/1 of width1; symbol2 is the halt symbol.
    widths=(1,1,0);a=112;K=2**(7*a);D=2**14
    g=lambda k:2*(4**k-1)//3
    A=2**7*(g(a-3)+2**(2*a-5)*g(7)+2**(2*a+10)*g(a-4))
    for length in range(1,9):
        for x in range(2**(length-1),2**length):
            bits=tuple((x>>i)&1 for i in range(length))
            R=sum(bit*K**i for i,bit in enumerate(bits));J=sum(K**i for i in range(length))
            X=A*(J+(D-1)*R);P0=K**length
            word=''.join(encode(bit,widths,'E',halt=2) for bit in bits)
            require(value(word)==X and 2**len(word)==P0 and 0<3*X<P0,'binary E loader ports')
            require((K-1)*J==P0-1,'geometric sum port')
            counts['canonical_binary_loader_port_identities']+=1
    # Literal source-domain guards; no float/bool symbol or run is accepted.
    bad=[lambda:grill(True),lambda:grill(1.0),lambda:compile_program((True,0),{(0,0):(0,0),(1,0):(0,0)},halt=1),
         lambda:compile_program((1,0),{(0,0):(0,0)},halt=1),
         lambda:compile_program((1,0),{(0,0):(True,0),(1,0):(0,0)},halt=1),
         lambda:compile_program((1,0),{(False,0):(0,0),(1,0):(0,0)},halt=1)]
    for f in bad:
        try:f()
        except (ValueError,TypeError):counts['malformed_calls_rejected']+=1
        else:raise ValueError('Bad caller accepted')
    return dict(status='PASS_CORRECTED_ENCODED_HALT_BRIDGE',source_sha256=digest(Path(__file__).read_bytes()),
                reference_sha256=REFERENCE_SHA,sources=SOURCES,checks=dict(sorted(counts.items())),
                aggregate_identity_sha256=proof.hexdigest(),first_halt_fixtures=fixtures,
                scope='General proof concerns corrected block-encoded valid Genera executions; finite checks are bounded evidence. No fixed universal source, ordinary input loader, padding-robustness or universal arithmetic count is established.')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    parser.add_argument('--output',type=Path);parser.add_argument('--expect',type=Path);args=parser.parse_args()
    result=verify(args.root)
    if args.expect:require(exact(result,json.loads(args.expect.read_text())),'saved receipt mismatch')
    if args.output:args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':result['status'],'checks':result['checks']},sort_keys=True))
if __name__=='__main__':main()
