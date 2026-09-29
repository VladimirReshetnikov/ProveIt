"""Independent 13-operation queue-interface idea; no author files changed."""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'))
import explore_constant_length_raw_queue as m

class DelayedLoader(m.Machine):
    def transition(self,state,symbol):
        bad=(m.State('loop'),symbol,'reject')
        if state.kind=='mark_first':
            if symbol not in m.PLAIN[:3]:return bad
            a=m.PLAIN.index(symbol)
            return m.State('load_tail',held=m.MARKED[a]),m.DELIM,''
        if state.kind=='load_tail':
            if symbol==m.DELIM:
                a,marked=m.DECODE[state.held]
                if a!=0:return bad
                blank=m.MARKED[m.BLANK] if marked else m.PLAIN[m.BLANK]
                return m.State('load_rotate'),blank,''
            if symbol not in m.PLAIN[:3]:return bad
            return m.State('load_tail',held=symbol),state.held,''
        if state.kind=='load_rotate':
            return (self.start(self.initial),m.DELIM,'loaded') if symbol==m.DELIM else bad
        return super().transition(state,symbol)

client=m.normalizer(m.Machine('initial_accept',{},'accept'))
machine=DelayedLoader(client.name,client.delta,client.initial,client.accept,client.reject)
initial,table,states=machine.compile()
counts=dict(initial_words=0,accepted=0,rejected=0,normalized=0,microsteps=0,
            positive_terminal_transports=0)
for ell in range(7):
    L=3**ell;W=3*L;R=3*W
    for x in range(L):
        state=initial
        word=tuple(m.PLAIN[x//3**j%3] for j in range(ell))+(m.DELIM,)
        assert m.coordinate(word,0)==x and m.coordinate(word,1)==L
        assert 3**len(word)==W
        rows=[];loaded=False
        for _ in range(1000):
            nxt,out,event=table[state,word[0]]
            rows.append((tuple(m.coordinate(word,i) for i in range(2)),word[0],out))
            state,word,event2=m.step(machine,state,word,table)
            assert event==event2 and state==nxt and len(word)==ell+1
            assert all(a==m.PLAIN[0] for a in word)==(state.kind=='accept')
            if state.kind not in ('erase','accept'):assert m.DELIM in word
            if event=='loaded':
                loaded=True
                tape,head=m.decode(word)
                wanted=[x//3**j%3 for j in range(max(ell-1,0))]+[m.BLANK]
                assert tape==wanted and head==0
            if event=='pass' and state.kind=='erase':
                canonical=m.canonical(x)
                assert m.decode(word)==(canonical+[m.BLANK]*(ell-len(canonical)),0)
                counts['normalized']+=1
            counts['microsteps']+=1
            if state.kind in ('accept','loop'):break
        else:raise AssertionError('unexpected cutoff')
        accepts=(ell>=2 and x<3**(ell-1))
        assert (state.kind=='accept')==accepts
        if accepts:
            counts['accepted']+=1
            X=[0,0];D=[0,0];A=[0,0];power=1
            for coord,head,out in rows:
                for i in range(2):
                    X[i]+=coord[i]*power;D[i]+=head[i]*power;A[i]+=out[i]*power
                power*=R
            assert min(X+D+A)>0
            for i,I in enumerate((x,L)):
                assert W*(X[i]-D[i]+W*A[i])==X[i]-I
            counts['positive_terminal_transports']+=1
        else:counts['rejected']+=1
        counts['initial_words']+=1
print(dict(status='PASS_DELAYED_BLANK_LOADER',controls=len(states),entries=len(table),**counts))
