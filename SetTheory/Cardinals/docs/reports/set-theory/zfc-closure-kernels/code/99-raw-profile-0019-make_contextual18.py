#!/usr/bin/env python3
"""Add a contextual state-18 proposal interface to the exact-word LNS.

This file is deliberately separate from the frozen main experiment packet.
The final dictionary must pass the new context audit AND actual-table proofs.
"""
from pathlib import Path
W=Path(__file__).resolve().parent
s=(W/'anneal_fine_lns.cpp').read_text()
s=s.replace('vector<string> words;', 'int contextualC=-1;\nvector<string> words;')
old='bool permitted(int a,int b){return (!terminal(a)||(allowed.at(a)&1))&&(!terminal(b)||(allowed.at(b)&2));}'
new='''// Optimistic proposal predicate.  A direct C on the left is allowed only
// provisionally; context_ok below makes the containing word right-only.
bool permitted(int a,int b){return (a==contextualC||!terminal(a)||(allowed.at(a)&1))&&(!terminal(b)||(allowed.at(b)&2));}

int derived_mask(int q,const Grammar&g,unordered_map<int,int>&memo,unordered_set<int>&visiting){
 if(terminal(q))return allowed.at(q);
 auto found=memo.find(q);if(found!=memo.end())return found->second;
 auto row=g.find(q);if(row==g.end()||!visiting.insert(q).second)return 0;
 auto r=row->second;int left=derived_mask(r.a,g,memo,visiting),right=derived_mask(r.b,g,memo,visiting);
 int answer=3;
 if(r.a==contextualC)answer=2; // incoming1 then left0 gives suffix10
 else if(!(left&1))answer=0;
 if(!(right&2))answer=0;
 visiting.erase(q);memo[q]=answer;return answer;
}
bool context_ok(const Grammar&g,const vector<int>&route){
 unordered_map<int,int>memo;unordered_set<int>visiting;
 for(int q:roots)if(derived_mask(q,g,memo,visiting)!=3)return false;
 for(int q:route)if(derived_mask(q,g,memo,visiting)!=3)return false;
 // Also reject any charged word not covered by the declared roots.  Normal
 // collect() has already established reachability, but this is inexpensive.
 for(auto [q,r]:g)if(!derived_mask(q,g,memo,visiting))return false;
 return true;
}'''
assert old in s;s=s.replace(old,new)
s=s.replace('int wordmask(int q){return terminal(q)?allowed.at(q):3;}',
            'int wordmask(int q){return q==contextualC?3:terminal(q)?allowed.at(q):3;}')
old='allowed[intern(c)]=m;}oldGrammar=initial;'
new='allowed[intern(c)]=m;}contextualC=intern("C");if(!allowed.count(contextualC)||allowed.at(contextualC)!=2)return 12;oldGrammar=initial;'
assert old in s;s=s.replace(old,new)
old='auto ip=fullprop(initial);cerr<<"INITIAL "'
new='if(!context_ok(initial,initialroute)){cerr<<"initial contextual masks fail"<<endl;return 13;}auto ip=fullprop(initial);cerr<<"INITIAL "'
assert old in s;s=s.replace(old,new)
old='if(!collect(next,nextroute)){closure_rejections++;continue;}int nn=next.size();'
new='if(!collect(next,nextroute)){closure_rejections++;continue;}if(!context_ok(next,nextroute))continue;int nn=next.size();'
assert old in s;s=s.replace(old,new)
s=s.replace('"\\n\\\"rules_count\\\":"<<g.size()', '"\\n\\\"rules_count\\\":"<<g.size()')
(W/'anneal_fine_contextual18.cpp').write_text(s)
print(W/'anneal_fine_contextual18.cpp')
