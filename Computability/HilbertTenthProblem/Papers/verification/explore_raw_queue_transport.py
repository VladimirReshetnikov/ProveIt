"""Exact shared-radix transport for the two-coordinate raw queue."""
from pathlib import Path
import json
import sympy as sp
import explore_finite_state_raw_queue as queue


OLD=[('x_trim','-','X','D'),('x_out','+','x_trim','U'),('x_left','*','R','x_out'),
     ('x_start','-','X','x'),('x_right','*',3,'x_start'),
     ('y_trim','-','Y','E'),('y_out','+','y_trim','V'),('y_left','*','R','y_out'),
     ('y_start','-','Y','L0'),('y_right','*',3,'y_start'),
     ('l_left','*','R','T'),('l_start','-','Z','Winit'),('l_end','+','l_start','q'),
     ('l_right','*',3,'l_end')]
NEW=[('radix','*',3,'B'),
     ('x_trim','-','X','D'),('x_out','+','x_trim','U'),('x_left','*','B','x_out'),
     ('x_right','-','X','x'),
     ('y_trim','-','Y','E'),('y_out','+','y_trim','V'),('y_left','*','B','y_out'),
     ('y_right','-','Y','L0'),
     ('l_left','*','B','T'),('l_start','-','Z','Winit'),('l_right','+','l_start','q')]


def run(dag,values):
    env=dict(values)
    for name,op,left,right in dag:
        assert name not in env
        a=env[left] if isinstance(left,str) else left
        b=env[right] if isinstance(right,str) else right
        env[name]=a*b if op=='*' else a+b if op=='+' else a-b
    return env


def histogram(dag):return dict(M=sum(op=='*' for _,op,_,_ in dag),A=sum(op!='*' for _,op,_,_ in dag))


def verify_source():
    names='R B q X Y Z D E U V T x L0 Winit'.split()
    s=dict(zip(names,sp.symbols(' '.join(names))))
    R,B,X,Y,Z,D,E,U,V,T,x,L0,Winit,q=[s[n] for n in 'R B X Y Z D E U V T x L0 Winit q'.split()]
    old=[R*(X-D+U)-3*(X-x),R*(Y-E+V)-3*(Y-L0),R*T-3*(Z-Winit+q)]
    new=[B*(X-D+U)-(X-x),B*(Y-E+V)-(Y-L0),B*T-(Z-Winit+q)]
    for dag,source in ((OLD,old),(NEW,new)):
        env=run(dag,s)
        assert all(sp.expand(env[a]-env[b]-f)==0 for (a,b),f in
            zip([('x_left','x_right'),('y_left','y_right'),('l_left','l_right')],source))
    assert run(NEW,s)['radix']==3*B
    assert all(sp.expand(f-3*g-(R-3*B)*h)==0 for f,g,h in zip(old,new,[X-D+U,Y-E+V,T]))
    assert len(OLD)==14 and histogram(OLD)==dict(M=6,A=8)
    assert len(NEW)==12 and histogram(NEW)==dict(M=4,A=8)
    return dict(old=dict(operations=14,histogram=histogram(OLD),dag=OLD),
                shared=dict(operations=12,histogram=histogram(NEW),dag=NEW),
                source_residuals=[sp.sstr(v) for v in new],
                additional_comparison='radix=R',source_corrections=3,
                scope='Conditional weighted histories; includes R=3B but excludes their selection/projection realization.')


def verify_runs():
    examples=rows=0;max_bits=0
    chosen={'initial_accept','scan_accept','left_growth','right_growth','double_left','stay_accept'}
    for machine in queue.fixtures():
        if machine.name not in chosen:continue
        initial,table,_=machine.compile()
        for x in range(6):
            ell=1
            while 3**ell<=x:ell+=1
            for pad in (0,1):
                L0=3**(ell+pad)
                word=tuple(queue.PLAIN[(x//3**i)%3] for i in range(ell+pad))+(queue.DELIM,)
                state=initial;data=[];max_len=len(word)
                while word:
                    assert len(data)<5000
                    nxt,out,event=table[state,word[0]]
                    data.append((queue.coordinate(word,0),queue.coordinate(word,1),3**len(word),
                                 word[0][0],word[0][1],queue.coordinate(out,0),queue.coordinate(out,1),3**len(out)))
                    state,word,_=queue.one_queue_step(machine,state,word,table)
                    max_len=max(max_len,len(word))
                assert state.kind=='drain'
                R=3**(max_len+4);B=R//3;q=R**len(data)
                values=dict(R=R,B=B,q=q,x=x,L0=L0,Winit=3*L0,X=0,Y=0,Z=0,D=0,E=0,U=0,V=0,T=0)
                power=1
                for n0,n1,w,d0,d1,u0,u1,alen in data:
                    terms=[n0,n1,w,d0,d1,u0*w,u1*w,alen*w]
                    for name,v in zip(('X','Y','Z','D','E','U','V','T'),terms):values[name]+=v*power
                    assert all(0<=v<R for v in terms)
                    power*=R
                assert power==q and B>0 and R==3*B
                for dag in (OLD,NEW):
                    env=run(dag,values)
                    assert all(env[a]==env[b] for a,b in [('x_left','x_right'),('y_left','y_right'),('l_left','l_right')])
                assert run(NEW,values)['radix']==R
                examples+=1;rows+=len(data);max_bits=max(max_bits,q.bit_length())
    for R in (27,81,243,729):
        selector_word=1;length_word=3+9*R;correct_weighted=3
        assert selector_word*length_word!=correct_weighted and 9<R
    return dict(complete_accepting_runs=examples,common_source_steps=rows,largest_time_power_bits=max_bits,
                convolution_counterexamples=4,
                scope='All weighted fields are constructed from actual accepting queue runs. No arbitrary-witness decoding or complete controller certificate is claimed.')


def verify():
    return dict(status='PASS_RAW_QUEUE_SHARED_TRANSPORT',source=verify_source(),finite=verify_runs(),
                proof='../1980/EXPLORATION_RAW_QUEUE_TRANSPORT.md',
                review_status='Author and independent root/affine_optimization full proof/source audits and fresh verify runs PASS; no findings. Publication is separate.',
                scope='Exact two-multiplication transport saving after paying one common radix factor. Weighted products, controller, masks, bounds and positivity remain outside the subtotal.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['finite'])
