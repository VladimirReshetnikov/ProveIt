from pathlib import Path
HERE=Path(__file__).resolve().parent
p=(HERE/'anneal_cold.cpp')
s=p.read_text()
s=s.replace('Grammar oldGrammar;','Grammar oldGrammar;\nint ax_index=-1,originalAX=-1;')
s=s.replace('Prop wordprop(int q,const Grammar&g,unordered_map<int,Prop>&wm,unordered_map<int,Prop>&em,unordered_set<int>&seen){','Prop wordprop(int q,const Grammar&g,unordered_map<int,Prop>&wm,unordered_map<int,Prop>&em,unordered_set<int>&seen){if(q==originalAX&&roots[ax_index]!=q)q=roots[ax_index];')
s=s.replace('f<<"{\\n\\\"status','f<<"{\\n\\\"root_word_overrides\\\":{\\\"76\\\":\\\""<<words[roots[ax_index]]<<"\\\"},\\n\\\"status')
start=s.index('int main(')
extra=r'''
vector<pair<string,string>> aliases={
 {"eijkKCeijkbIqkjG","M"},
 {"eijkKCeijkbIeijklqkjGqkjGlleijklqkjG","N"},
 {"eijkKCeijkKCeijkfgqkjGl","O"},
 {"eijklqkjGqkjGeijklqkjGeijkKCeijkfgqkjGl","P"},
 {"qkjGllqkjG","R"},{"qkjGlleijklqkjG","S"},
 {"eijkl","V"},{"qkjGl","W"},{"eijkKCqkjGl","X"},
 {"eijkbIeijkfg","Y"},{"eijkfgeijkbIeijkfgeijkbI","Z"},
 {"eijkfgeijkbIqkjGl","a"},{"qkg","o"},{"EFg","p"}
};
void fringe(const Grammar&g,int q,int lo,int hi,vector<int>&parts){
 if(lo==hi)return;
 if(lo==0&&hi==(int)words[q].size()){parts.push_back(q);return;}
 auto r=g.at(q);int n=words[r.a].size();
 if(lo<n)fringe(g,r.a,lo,min(hi,n),parts);
 if(hi>n)fringe(g,r.b,max(lo-n,0),hi-n,parts);
}
int reparse(Grammar&g,const vector<int>&p,mt19937_64&rng){
 int n=p.size();if(!n)return -1;
 vector<vector<int>> q(n,vector<int>(n+1)),cost(n,vector<int>(n+1,1000000)),cut(n,vector<int>(n+1,-1));
 for(int i=0;i<n;i++){
  string w;
  for(int j=i+1;j<=n;j++){w+=words[p[j-1]];q[i][j]=intern(w);}
  cost[i][i+1]=0;
 }
 for(int k=2;k<=n;k++)for(int i=0;i+k<=n;i++){
  int j=i+k,v=q[i][j];
  if(g.count(v)){cost[i][j]=0;cut[i][j]=-2;continue;}
  for(int h=i+1;h<j;h++){
   if(!permitted(q[i][h],q[h][j]))continue;
   int c=1+cost[i][h]+cost[h][j];
   if(c<cost[i][j]||(c==cost[i][j]&&rng()%2)){cost[i][j]=c;cut[i][j]=h;}
  }
 }
 if(cost[0][n]>=1000000)return -1;
 vector<pair<int,int>>todo={{0,n}};
 while(!todo.empty()){
  auto[i,j]=todo.back();todo.pop_back();int k=cut[i][j];
  if(k<0)continue;
  g[q[i][j]]={q[i][k],q[k][j]};todo.push_back({i,k});todo.push_back({k,j});
 }
 return q[0][n];
}
bool rewrite_move(Grammar&g,vector<int>&route,mt19937_64&rng){
 int old=roots[ax_index];string w=words[old];
 auto [a,b]=aliases[rng()%aliases.size()];
 if(rng()%4==0)swap(a,b);
 vector<int>spots;
 for(size_t i=w.find(a);i!=string::npos;i=w.find(a,i+1))spots.push_back(i);
 if(spots.empty())return false;
 int at=spots[rng()%spots.size()];
 vector<int>parts;fringe(g,old,0,at,parts);
 for(char c:b)parts.push_back(intern(string(1,c)));
 fringe(g,old,at+a.size(),w.size(),parts);
 int root=reparse(g,parts,rng);if(root<0)return false;
 roots[ax_index]=root;return true;
}
'''
s=s[:start]+extra+s[start:]
s=s.replace('oldGrammar=initial;','oldGrammar=initial;\n ax_index=max_element(roots.begin(),roots.end(),[](int a,int b){return words[a].size()<words[b].size();})-roots.begin(); originalAX=roots[ax_index];')
s=s.replace('int currentn=current.size(),bestn=currentn;', 'int currentn=current.size(),bestn=currentn,currentAX=originalAX,bestAX=originalAX;')
s=s.replace('if(move_kind<52){','if(rng()%1000<5)changed=rewrite_move(next,nextroute,rng);\n else if(move_kind<52){')
s=s.replace('if(!changed||!route_contexts(next,nextroute,rng))continue;', 'if(!changed||!route_contexts(next,nextroute,rng)){roots[ax_index]=currentAX;continue;}')
s=s.replace('currentn=nn;accepted++;}', 'currentn=nn;currentAX=roots[ax_index];accepted++;}else roots[ax_index]=currentAX;')
s=s.replace('if(currentn==bestn&&uni(rng)<0.015){best=current;bestroute=curroute;}', 'if(currentn==bestn&&uni(rng)<0.015){best=current;bestroute=curroute;bestAX=currentAX;}')
s=s.replace('bestn=currentn;lastbest=iter;', 'bestn=currentn;bestAX=currentAX;lastbest=iter;')
s=s.replace('currentn=current.size();restarts++;', 'currentn=current.size();currentAX=orig?originalAX:bestAX;roots[ax_index]=currentAX;restarts++;')
s=s.replace('save(output,best,bestroute,iter,seed,elapsed);cout<<"DONE', 'roots[ax_index]=bestAX;save(output,best,bestroute,iter,seed,elapsed);cout<<"DONE')
(HERE/'anneal_semantic.cpp').write_text(s)
