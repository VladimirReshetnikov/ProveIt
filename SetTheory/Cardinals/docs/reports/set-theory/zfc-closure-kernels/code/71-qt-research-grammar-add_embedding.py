from pathlib import Path
p=Path(__file__).resolve().parent
s=(p/'anneal_cluster.cpp').read_text()
new=r'''
// New: install a folded-entry route in an already charged SOURCE word,
// including words longer than the legacy 320-token router synthesis cap.
// Required projections are synthesized jointly, with up to one fresh helper
// in an unconstrained remainder. This can repurpose AX itself as a router.
struct EmbedPlan {int q; vector<pair<int,Rule>> edits;};
long long embed_proposals=0,embed_completed=0;
bool viable(int q,const vector<Constraint>&cs){
 const string& w=words[q];
 for(auto c:cs){
  const string& t=words[c.target];
  if(c.prefix.empty()){if(q!=c.target)return false;continue;}
  if(t.size()>=w.size()||w.find(t)==string::npos)return false;
  if(c.prefix.find('1')==string::npos&&w.compare(0,t.size(),t))return false;
  if(c.prefix.find('0')==string::npos&&w.compare(w.size()-t.size(),t.size(),t))return false;
 }
 return true;
}
vector<EmbedPlan> embed_plans(int q,const vector<Constraint>&cs,const Grammar&g,mt19937_64&rng){
 vector<EmbedPlan> plans;
 if(!viable(q,cs))return plans;
 bool empty=false;for(auto c:cs)if(c.prefix.empty())empty=true;
 if(empty){if((terminal(q)||g.count(q))&&matches(g,q,cs))plans.push_back({q,{}});return plans;}
 if(cs.empty()){
  if(terminal(q)||g.count(q)){plans.push_back({q,{}});return plans;}
  string w=words[q];
  for(size_t k=1;k<w.size();k++){
   auto ai=ids.find(w.substr(0,k)),bi=ids.find(w.substr(k));
   if(ai==ids.end()||bi==ids.end())continue;
   int a=ai->second,b=bi->second;
   if((terminal(a)||g.count(a))&&(terminal(b)||g.count(b))&&permitted(a,b))plans.push_back({q,{{q,{a,b}}}});
  }
  if(plans.size()>6){shuffle(plans.begin(),plans.end(),rng);plans.resize(6);}
  return plans;
 }
 if(terminal(q))return plans;
 if(g.count(q)&&matches(g,q,cs))plans.push_back({q,{}});
 vector<Constraint> child[2];for(auto c:cs)child[c.prefix[0]-'0'].push_back({c.target,c.prefix.substr(1)});
 string w=words[q];
 for(size_t k=1;k<w.size();k++){
  int a=intern(w.substr(0,k)),b=intern(w.substr(k));
  if(!viable(a,child[0])||!viable(b,child[1])||!permitted(a,b))continue;
  auto left=embed_plans(a,child[0],g,rng);if(left.empty())continue;
  auto right=embed_plans(b,child[1],g,rng);if(right.empty())continue;
  for(auto l:left)for(auto r:right){
   EmbedPlan p{q,l.edits};p.edits.insert(p.edits.end(),r.edits.begin(),r.edits.end());p.edits.push_back({q,{a,b}});plans.push_back(p);
  }
 }
 if(plans.size()>30){shuffle(plans.begin(),plans.end(),rng);plans.resize(30);}
 return plans;
}
bool embed_route_move(Grammar& g,vector<int>& route,mt19937_64& rng){
 embed_proposals++;
 int i=rng()%groups.size();vector<int> active;
 for(auto[q,r]:g)if(viable(q,groups[i].cs)&&q!=route[i])active.push_back(q);
 if(active.empty())return false;
 int q=active[rng()%active.size()];auto plans=embed_plans(q,groups[i].cs,g,rng);
 if(plans.empty())return false;
 // Prefer small exact edits, but permit a multi-helper route installation.
 auto extra=[&](const EmbedPlan&p){int n=0;for(auto [v,r]:p.edits)n+=!g.count(v);return n;};
 if(rng()%4){int best=100;for(auto p:plans)best=min(best,extra(p));
  plans.erase(remove_if(plans.begin(),plans.end(),[&](const auto&p){return extra(p)>best;}),plans.end());}
 auto p=plans[rng()%plans.size()];for(auto[v,r]:p.edits)g[v]=r;
 route[i]=q;embed_completed++;return true;
}
'''
s=s.replace('int main(int argc',new+'\nint main(int argc')
s=s.replace('int move_kind=rng()%115;','int move_kind=rng()%125;')
s=s.replace('else changed=destroy_move(next,nextroute,rng);','else if(move_kind<115)changed=destroy_move(next,nextroute,rng);\n else changed=embed_route_move(next,nextroute,rng);')
s=s.replace('" closure_rejections "<<closure_rejections','" embed_proposals "<<embed_proposals<<" embed_completed "<<embed_completed<<" closure_rejections "<<closure_rejections')
(p/'anneal_embed.cpp').write_text(s)
