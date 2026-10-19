#!/usr/bin/env python3
"""Universal local contracts and an exact controller counterexample.

A small mathematical word/list-induction checker is used for the contracts.
This is not a Lean/Rocq certificate or a blank-machine consistency theorem.
The optional980-action search is a bounded diagnostic only.
"""
from pathlib import Path
import argparse,hashlib,json,time
import literal_reference as lit
import word_induction as m

ROOT=Path(__file__).resolve().parent
SHA=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()


def load(name):
    return lit.read_table(ROOT/name)


def reset(t):
    m.TABLE={k:(w,'R' if d==1 else 'L',n) for k,(w,d,n) in t.items()}
    m.DERIVED.clear();m.BLOCK_PROOFS.clear();m.WORD_IDENTITY_PROVED=False
    m.prove_blocks();return m.prove_word_identity()


def offset_contracts(t):
    word=reset(t)
    p,s=m.E.var('width_pre'),m.E.var('width_suf');x=m.E.var('x')
    a,b=m.Blocks('B','pre'),m.Blocks('B','suf')
    l,z=m.Context('arbitrary_left'),m.Blank();r=m.Context('arbitrary_right_after_next_separator')
    out=[m.prove('offset_positive_decrement',
      m.Conf(95,'R',[l],[a,m.bit(0),m.bit(0),m.ones(x+2),b,z]),
      m.Conf(48,'L',[m.bit(1),l],[a]+m.B(x+1)+[b,z]),
      2*p+6,m.E(),allow_lists=True),
      m.prove('offset_zero_decrement',
      m.Conf(95,'R',[l],[a,m.bit(0),m.bit(0),m.bit(1),m.bit(0),r]),
      m.Conf(112,'L',[l],[a]+m.B(m.E(1))+[m.bit(0),r]),
      2*p+7,m.E(-1),allow_lists=True),
      m.prove('offset_increment',
      m.Conf(73,'R',[l],[a,m.bit(0),m.bit(0),m.ones(x),b,z]),
      m.Conf(48,'L',[l],[a]+m.B(x+1)+[b]+m.B(m.E())+[z]),
      2*(p+x+s+2)+5,m.E(-1),allow_lists=True)]
    return dict(word_identity=word,block_proofs=list(m.BLOCK_PROOFS.values()),contracts=out)


def prefix_left_contracts(t):
    word=reset(t)
    v,p,k=m.E.var('v'),m.E.var('width_pre'),m.E.var('k')
    l,r=m.Context('arbitrary_left'),m.Context('arbitrary_right')
    a=m.Blocks('B','pre')
    D=lambda x:[m.ones(x+1),m.bit(0)]
    proof=m.prove('left_shift131_block',
      m.Conf(131,'L',m.reverse(m.B(v))+[l],[r]),
      m.Conf(131,'L',[l],D(v)+[r]),v+2,-1*(v+2))
    m.BLOCK_PROOFS['left_shift131_block']=proof
    m.DERIVED[131,'L','B',True]=('left_shift131_block','D')
    # Base and one-block step for the free-word identity0D(A)=B(A)0.
    assert m.norm([m.bit(0)])==m.norm([m.bit(0)])
    assert m.norm([m.bit(0)]+D(v))==m.norm(m.B(v)+[m.bit(0)])
    original_norm=m.norm
    def norm(word,rewrite=False):
        out=original_norm(word,rewrite)
        for i in range(len(out)-1):
            x,y=out[i:i+2]
            if isinstance(x,m.Run) and x.bit==0 and x.length.c>=1 and isinstance(y,m.Blocks) and y.family=='D' and not y.rev:
                return norm(out[:i]+[m.Run(0,x.length+-1),m.Blocks('B',y.name),m.bit(0)]+out[i+2:],rewrite)
            if isinstance(x,m.Blocks) and x.family=='D' and x.rev and isinstance(y,m.Run) and y.bit==0 and y.length.c>=1:
                return norm(out[:i]+[m.bit(0),m.Blocks('B',x.name,True),m.Run(0,y.length+-1)]+out[i+2:],rewrite)
        return out
    m.norm=norm
    try:
        inc=m.prove('prefix_left_increment_with_temporary_one_run',
          m.Conf(73,'R',[m.ones(k+1),m.bit(0),m.bit(0),l],
              [a,m.bit(0),m.bit(0),m.ones(v),r]),
          m.Conf(48,'L',[l],[m.bit(0),m.ones(k+1),a]+m.B(v+1)+[r]),
          2*p+k+6,-1*(k+4),allow_lists=True)
    finally:m.norm=original_norm
    # The zero-decrement simplification from the existing delete255 proposal.
    x=m.E.var('x');b=m.Blocks('B','suf');z=m.Blank()
    dec0=m.prove('prefix_left_zero_decrement',
      m.Conf(95,'R',[l],[a,m.bit(0),m.bit(0)]+m.B(x)+[b,z]),
      m.Conf(112,'L',[l],[a]+m.B(m.E())+m.B(x)+[b,z]),
      2*p+5,m.E(-1),allow_lists=True)
    decp=m.prove('prefix_left_positive_decrement',
      m.Conf(95,'R',[l],[a,m.bit(0),m.bit(0),m.ones(x+1),b,z]),
      m.Conf(48,'L',[m.bit(1),l],[a]+m.B(x)+[b,z]),
      2*p+4,m.E(),allow_lists=True)
    return dict(word_identity=word,block_proofs=list(m.BLOCK_PROOFS.values()),
      extra_word_identity=dict(base='0D([])=B([])0',step='0D(v)D(A)=B(v)0D(A)=B(v)B(A)0',identity='0D(A)=B(A)0'),
      contracts=[inc,dec0,decp])


def counterexample(ref,mutant):
    pc='01010';regs=[1,4,2,0,3,1,4,2,0];spares=[1,1]
    initial=lit.paint(pc,181,regs,spares,0)
    changed=regs.copy();changed[lit.PHYSICAL[8]]+=1
    ordinary=lit.expected(pc,'CI',8,regs,spares,0,181)
    expected_new=(0,lit.paint('01011',180,changed,spares,0))
    wrong=(0,lit.paint('011',180,changed,spares,0))
    records={}
    for name,t,goal in [('reference246',ref,(ordinary[0],ordinary[1])),('prefix_left245',mutant,wrong)]:
        q,h,one=96,0,initial.copy();seen_inc=False;entered=None;history=[]
        for step in range(1,20001):
            bit=int(h in one)
            if not seen_inc and q==73:
                seen_inc=True;entered=dict(step=step-1,state=q,head=h)
            w,d,q=t[q,bit];one.add(h) if w else one.discard(h);h+=d
            if seen_inc and q==96:
                assert (h,one)==goal,(name,step,h)
                records[name]=dict(steps=step,state=q,head=h,ones=sorted(one),increment_entry=entered)
                break
        else:raise AssertionError('No post-increment dispatcher within20000steps')
    assert records['reference246']['steps']==1618
    assert records['prefix_left245']['steps']==1540
    assert records['prefix_left245']['ones']!=sorted(expected_new[1])
    return dict(source=dict(pc=pc,header_distance=181,physical_registers=regs,spares=spares,head=0,ones=sorted(initial)),
      records=records,mutant_actual_pc='011',mutant_required_pc='01011',mutant_header_distance=180,
      mutant_expected_ones=sorted(expected_new[1]),
      result='The first post-increment dispatch is the wrongPC despite the correct register increment and one-cell left movement of the file.')


def entry_search(t):
    pc='01010';regs=[1,4,2,0,3,1,4,2,0];spares=[1,1]
    changed=regs.copy();changed[lit.PHYSICAL[8]]+=1
    want=lit.paint('01011',180,changed,spares,0)
    q,h,one=96,0,lit.paint(pc,181,regs,spares,0)
    for prefix in range(20000):
        if (q,int(h in one))==(57,1):break
        w,d,q=t[q,int(h in one)];one.add(h) if w else one.discard(h);h+=d
    else:raise AssertionError('entry not reached')
    assert prefix==794
    start=(q,h,one.copy());states=sorted({q for q,b in t});ledger=[];survivors=[]
    for dst in states:
        for w in (0,1):
            for d in (-1,1):
                trial=t.copy();trial[57,1]=(w,d,dst)
                q,h,source=start;one=source.copy();status='fuel_limit'
                for tick in range(prefix+1,20001):
                    x,move,q=trial[q,int(h in one)]
                    one.add(h) if x else one.discard(h);h+=move
                    if q==254:status='halt';break
                    if q==96 and h==0 and one==want:
                        status='pass';survivors.append([w,d,dst,tick]);break
                ledger.append([w,d,dst,status,tick])
    assert len(ledger)==980 and not survivors
    return dict(scope='One explicit preparedCI8 fixture only; endpoints at everytick1..20000; no impossibility or blank-machine claim.',
      changed_row=[57,1],recipes=980,shared_unchanged_prefix=794,fuel=20000,survivors=survivors,ledger=ledger)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--search-entry',action='store_true');ap.add_argument('--output',type=Path,default=ROOT/'runtime-verification.json');args=ap.parse_args()
    if not __debug__:raise SystemExit('Run with assertions enabled')
    ref=load('reference246_old.tm');off=load('offset246_old.tm');left=load('partial_prefix_left245_old.tm')
    assert len(ref)==492 and len(off)==492 and len(left)==490
    assert {q for q,b in off}=={q for q,b in ref}
    assert {q for q,b in left}=={q for q,b in ref}-{255}
    assert all(dst in {q for q,b in left}|{254} for w,d,dst in left.values())
    expected_off=dict(ref);expected_off.update({(75,0):(1,-1,131),(75,1):(1,1,255),(255,0):(0,-1,112),(255,1):(1,-1,63)})
    expected_left={k:v for k,v in ref.items() if k[0]!=255};expected_left.update({(75,0):(0,-1,112),(83,0):(1,-1,112)})
    assert off==expected_off and left==expected_left
    result=dict(status='PASS',claim='Universal local arithmetic contracts and exact finite controller counterexample; no sub246 consistency machine established.',
      inputs={p.name:SHA(p) for p in [ROOT/'reference246_old.tm',ROOT/'offset246_old.tm',ROOT/'partial_prefix_left245_old.tm',ROOT/'word_induction.py',ROOT/'literal_reference.py',Path(__file__)]},
      offset=offset_contracts(off),prefix_left=prefix_left_contracts(left),counterexample=counterexample(ref,left))
    if args.search_entry:result['entry_repair_search']=entry_search(left)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status=result['status'],offset_contracts=len(result['offset']['contracts']),prefix_left_contracts=len(result['prefix_left']['contracts']),
      baseline_counterexample_steps=1618,mutant_counterexample_steps=1540,entry_recipes=980 if args.search_entry else None),indent=2))

if __name__=='__main__':main()
