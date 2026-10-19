from pathlib import Path
HERE=Path(__file__).resolve().parent
s=(HERE/'anneal_cold.cpp').read_text()
start=s.index('int main(')
extra=r'''
using Plan=vector<pair<int,Rule>>;
vector<Plan> force_word(int q,const vector<Constraint>&cs,const Grammar&g,mt19937_64&rng){
 if(cs.empty())return terminal(q)||g.count(q)?vector<Plan>{Plan{}}:vector<Plan>{};
 vector<Constraint>bs[2];bool has=false;
 for(auto c:cs){if(c.prefix.empty()){if(c.target!=q)return {};}else{bs[c.prefix[0]-'0'].push_back({c.target,c.prefix.substr(1)});has=true;}}
 if(!has)return terminal(q)||g.count(q)?vector<Plan>{Plan{}}:vector<Plan>{};
 if(terminal(q))return {};
 vector<Plan>ret;string w=words[q];int seen=0;
 vector<int>ks(w.size()-1);iota(ks.begin(),ks.end(),1);shuffle(ks.begin(),ks.end(),rng);
 for(int k:ks){
  int a=intern(w.substr(0,k)),b=intern(w.substr(k));if(!permitted(a,b))continue;
  auto as=force_word(a,bs[0],g,rng);if(as.empty())continue;
  auto bs2=force_word(b,bs[1],g,rng);if(bs2.empty())continue;
  for(auto pa:as)for(auto pb:bs2){
   Plan p=pa;p.insert(p.end(),pb.begin(),pb.end());p.push_back({q,{a,b}});
   ret.push_back(p);if(ret.size()>=8)return ret;
  }
 }
 return ret;
}
bool context_move(Grammar&g,vector<int>&route,mt19937_64&rng){
 int i=rng()%groups.size();vector<int>opts;
 for(auto[q,r]:g)if(q!=route[i])opts.push_back(q);
 shuffle(opts.begin(),opts.end(),rng);
 for(int j=0;j<min(12,int(opts.size()));j++){
  int q=opts[j];auto plans=force_word(q,groups[i].cs,g,rng);if(plans.empty())continue;
  auto plan=plans[rng()%plans.size()];for(auto[v,r]:plan)g[v]=r;
  route[i]=q;return true;
 }
 return false;
}
'''
s=s[:start]+extra+s[start:]
s=s.replace('if(move_kind<52){','if(move_kind<5)changed=context_move(next,nextroute,rng);\n else if(move_kind<52){')
(HERE/'anneal_context.cpp').write_text(s)
