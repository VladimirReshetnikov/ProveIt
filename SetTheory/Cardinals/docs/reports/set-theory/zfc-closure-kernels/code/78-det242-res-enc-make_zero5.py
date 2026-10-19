from pathlib import Path
p=Path(__file__).resolve().parent
s=(p/'anneal_cluster.cpp').read_text()
stats=r'''
// New objective: count all source leaves whose path contains six consecutive
// zero edges, with exact DAG multiplicity and the whole source context.
struct ZStat{long long leaves;long long good[6];};
ZStat zjoin(ZStat a,ZStat b){ZStat c;c.leaves=a.leaves+b.leaves;for(int k=0;k<6;k++)c.good[k]=(k<5?a.good[k+1]:0)+b.good[0];return c;}
ZStat zword(int,const Grammar&,unordered_map<int,ZStat>&,unordered_map<int,ZStat>&,unordered_set<int>&);
ZStat zexpr(int x,const Grammar&g,unordered_map<int,ZStat>&wm,unordered_map<int,ZStat>&em,unordered_set<int>&seen){auto it=em.find(x);if(it!=em.end())return it->second;auto e=exprs[x];ZStat p;if(e.kind=='L'){p.leaves=1;for(int k=0;k<6;k++)p.good[k]=1;}else if(e.kind=='W')p=zword(e.a,g,wm,em,seen);else p=zjoin(zexpr(e.a,g,wm,em,seen),zexpr(e.b,g,wm,em,seen));em[x]=p;return p;}
ZStat zword(int q,const Grammar&g,unordered_map<int,ZStat>&wm,unordered_map<int,ZStat>&em,unordered_set<int>&seen){auto it=wm.find(q);if(it!=wm.end())return it->second;if(!seen.insert(q).second){ZStat bad;bad.leaves=1000000000;for(int k=0;k<6;k++)bad.good[k]=0;return bad;}ZStat p;if(terminal(q))p=zexpr(atomExpr.at(q),g,wm,em,seen);else{auto it=g.find(q);Rule r=it==g.end()?oldGrammar.at(q):it->second;p=zjoin(zword(r.a,g,wm,em,seen),zword(r.b,g,wm,em,seen));}seen.erase(q);wm[q]=p;return p;}
long long badpaths(const Grammar&g){unordered_map<int,ZStat>wm,em;unordered_set<int>seen;auto x=zexpr(originalExpr,g,wm,em,seen);return x.leaves-x.good[0];}
double quality(const Grammar&g){return g.size()+0.30*badpaths(g);}
'''
s=s.replace('int main(int argc,char**argv)',stats+'\nint main(int argc,char**argv)')
s=s.replace('int currentn=current.size(),bestn=currentn;','int currentn=current.size(),bestn=currentn;double current_score=quality(current),best_score=current_score;cerr<<"INITIAL_BAD "<<badpaths(initial)<<" quality "<<current_score<<endl;')
s=s.replace('int nn=next.size();double phase=', 'int nn=next.size();auto np=fullprop(next);if(np.depth>64||np.zero>7)continue;double next_score=quality(next);double phase=')
s=s.replace('bool ok=nn<=currentn||(nn<=bestn+5&&uni(rng)<exp((currentn-nn)/temp));if(ok){auto p=fullprop(next);if(p.zero>6||p.depth>64)ok=false;}', 'bool ok=next_score<=current_score||(nn<=136&&next_score<=best_score+8&&uni(rng)<exp((current_score-next_score)/temp));')
s=s.replace('currentn=nn;accepted++;','currentn=nn;current_score=next_score;accepted++;')
s=s.replace('if(currentn==bestn&&uni(rng)<0.015){best=current;bestroute=curroute;}', 'if(current_score==best_score&&uni(rng)<0.015){best=current;bestroute=curroute;bestn=currentn;}')
s=s.replace('if(currentn<bestn){best=current;bestroute=curroute;bestn=currentn;', 'if(current_score<best_score){best=current;bestroute=curroute;bestn=currentn;best_score=current_score;')
s=s.replace('if(bestn<=stopcount)break;', 'cout<<" QUALITY "<<best_score<<" badpaths "<<badpaths(best)<<endl;if(bestn<=stopcount&&badpaths(best)==0)break;')
s=s.replace('currentn=current.size();restarts++;', 'currentn=current.size();current_score=quality(current);restarts++;')
(p/'anneal_zero5.cpp').write_text(s)
