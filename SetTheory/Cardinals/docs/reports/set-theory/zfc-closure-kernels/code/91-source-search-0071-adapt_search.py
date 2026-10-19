#!/usr/bin/env python3
"""Apply explicit checked text adaptations to the attributed zero6 annealer."""
from pathlib import Path
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'machine_reduction/base/zfc245-proof-20261018'
s=(BASE/'code/state_reduction/anneal_routes_zero6.cpp').read_text()
changes=[
 ('unordered_map<char,int> atomExpr','unordered_map<int,int> atomExpr'),
 ('unordered_map<char,int> allowed','unordered_map<int,int> allowed'),
 ('return words[q].size()==1;','return allowed.count(q);'),
 ('allowed[words[a][0]]','allowed.at(a)'),('allowed[words[b][0]]','allowed.at(b)'),
 ('atomExpr.at(words[q][0])','atomExpr.at(q)'),
 ('for(auto[c,m]:allowed)active.push_back(intern(string(1,c)));','for(auto[c,m]:allowed)active.push_back(c);'),
 ('char c;int m;f>>c>>m;allowed[c]=m;','string c;int m;f>>c>>m;allowed[intern(c)]=m;'),
 ('char c;int a;cf>>c>>a;atomExpr[c]=a;','string c;int a;cf>>c>>a;atomExpr[intern(c)]=a;'),
 ('if(!next.count(part)){','if(!terminal(part)&&!next.count(part)){'),
 ('words[ab[b]].size()>30','words[ab[b]].size()>60'),
 ('words[ab[0]].size()+words[ab[1]].size()>80','words[ab[0]].size()+words[ab[1]].size()>160'),
 ('words[ab[0]].size()+words[ab[1]].size()>160||!permitted(ab[0],ab[1]))return false;','words[ab[0]].size()+words[ab[1]].size()>320||!permitted(ab[0],ab[1]))return false;'),
 ('if(move_kind<65){','if(move_kind<55){'),
 ('else if(move_kind<80){','else if(move_kind<68){'),
 ('else if(move_kind<88)changed=route_contexts','else if(move_kind<85)changed=resegment_move(next,nextroute,rng);\n else if(move_kind<91)changed=route_contexts'),
 ('\\\"status\\\":\\\"ABSTRACT_ROUTING_GRAMMAR_ONLY\\\"','\\\"status\\\":\\\"ABSTRACT_FINE_ROUTING_GRAMMAR_ONLY\\\"'),
]
for before,after in changes:
    assert before in s,before
    s=s.replace(before,after)
new=r'''
// New: change macro boundaries using exact closed-token substrings. Every
// accepted child has an existing implementation or one newly supplied rule.
bool resegment_move(Grammar&g,vector<int>&route,mt19937_64&rng){
 vector<int> active;for(auto[q,r]:g)if(words[q].size()<=160)active.push_back(q);
 if(active.empty())return false;int q=active[rng()%active.size()];string w=words[q];
 struct Option {Rule top;int newq;Rule child;};vector<Option> opts;
 auto known=[&](const string&v,int side){auto it=ids.find(v);if(it==ids.end())return -1;int a=it->second;
   return ((!terminal(a)&&g.count(a))||(terminal(a)&&(allowed.at(a)&(1<<side))))?a:-1;};
 for(size_t k=1;k<w.size();k++){
   string ls=w.substr(0,k),rs=w.substr(k);int a=known(ls,0),b=known(rs,1);
   if(a>=0&&b>=0)opts.push_back({{a,b},-1,{-1,-1}});
   // Add at most one new pure sequence node, with arbitrary macro boundaries.
   for(int side=0;side<2;side++){
     if((side==0?b:a)<0)continue;string v=side==0?ls:rs;
     int nq=intern(v);if(terminal(nq)||g.count(nq))continue;
     for(size_t j=1;j<v.size();j++){
       int x=known(v.substr(0,j),0),y=known(v.substr(j),1);
       if(x>=0&&y>=0)opts.push_back({side==0?Rule{nq,b}:Rule{a,nq},nq,{x,y}});
     }
   }
 }
 if(opts.empty())return false;auto o=opts[rng()%opts.size()];g[q]=o.top;
 if(o.newq>=0)g[o.newq]=o.child;return true;
}
'''
assert 'int main(int argc' in s
s=s.replace('int main(int argc',new+'\nint main(int argc')
s=s.replace('// Routing-aware extension of ProveIt incoming anneal5.cpp; see NOTICE.txt.',
'''// Exact fine-token extension of the attributed routing-aware zero6 annealer.
// Original implementation: ProveIt incoming zfc245-proof-20261018; see NOTICE.
// New here: variable-length atomic keys and joint macro-boundary mutations.
// Search is heuristic. All resulting dictionaries require independent audit.''')
(HERE/'anneal_fine.cpp').write_text(s)
print('Applied',len(changes),'checked adaptations and a macro-boundary move.')
