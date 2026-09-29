"""Independent one-blank initialization audit; author files remain untouched."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2]/'verification'))
import explore_constant_length_raw_queue as m

counts=dict(runs=0,normalizations=0,microsteps=0,accepted=0,rejected=0,
            fixed_stay_cutoffs=0,positive_history_tuples=0,zero_padding_rejections=0)
for machine in m.fixtures():
    initial,table,_=machine.compile()
    for x in range(40):
        minimal=1
        while 3**minimal<=x:minimal+=1
        for pad in range(4):
            ell=minimal+pad;L=3**ell;W=9*L;R=3*W
            word=tuple(m.PLAIN[x//3**j%3] for j in range(ell))+(m.PLAIN[m.BLANK],m.DELIM)
            assert m.coordinate(word,0)==x and m.coordinate(word,1)==5*L
            assert 3**len(word)==W
            state=initial;history=[]
            def micro():
                global state,word
                nxt,out,event=table[state,word[0]]
                history.append((tuple(m.coordinate(word,i) for i in range(2)),word[0],out))
                state,word,observed=m.step(machine,state,word,table)
                assert state==nxt and event==observed and len(word)==ell+2
                assert all(a==m.PLAIN[0] for a in word)==(state.kind=='accept')
                if state.kind not in ('erase','accept'):assert m.DELIM in word
                counts['microsteps']+=1
                return event
            for j in range(ell+2):event=micro()
            assert event=='loaded'
            tape,head=m.decode(word);q=machine.initial;normalized=False
            for macro in range(200):
                if q in machine.accept|machine.reject:break
                expected,reason=m.direct(machine,q,tape,head)
                while micro() not in ('pass','reject'):pass
                if expected is None:
                    assert state.kind=='loop';break
                old=q;q,tape,head=expected
                assert m.decode(word)==(tape,head)
                if old.startswith('norm.') and q==machine.client_initial:
                    canonical=m.canonical(x)
                    assert tape==canonical+[m.BLANK]*(ell+1-len(canonical)) and head==0
                    normalized=True;counts['normalizations']+=1
            assert normalized
            if state.kind=='erase':
                for j in range(ell+2):event=micro()
                assert event=='zero' and state.kind=='accept'
            if state.kind=='accept':
                counts['accepted']+=1
                X=[0,0];D=[0,0];A=[0,0];power=1
                for coord,head,out in history:
                    for i in range(2):
                        X[i]+=coord[i]*power;D[i]+=head[i]*power;A[i]+=out[i]*power
                    power*=R
                assert min(X+D+A)>0
                for i,I in enumerate((x,5*L)):
                    assert W*(X[i]-D[i]+W*A[i])==X[i]-I
                counts['positive_history_tuples']+=1
            elif state.kind=='loop':counts['rejected']+=1
            else:
                assert machine.name=='infinite_stay';counts['fixed_stay_cutoffs']+=1
            counts['runs']+=1
    state=initial;word=(m.PLAIN[m.BLANK],m.DELIM)
    for j in range(20):
        state,word,event=m.step(machine,state,word,table)
        assert any(a!=m.PLAIN[0] for a in word)
    assert state.kind=='loop'
    counts['zero_padding_rejections']+=1
print(dict(status='PASS_INDEPENDENT_ONE_BLANK_AUDIT',**counts))
