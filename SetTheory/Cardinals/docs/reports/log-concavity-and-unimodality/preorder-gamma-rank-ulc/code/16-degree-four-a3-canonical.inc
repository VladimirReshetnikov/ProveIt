using Key=__uint128_t;
Key canonical(vector<unsigned> r){
 int z=r.size();vector<int>color(z,0);int nc=1;
 while(true){vector<vector<int>>sig(z);map<vector<int>,int>ids;for(int i=0;i<z;i++){sig[i].assign(1+2*nc,0);sig[i][0]=color[i];for(int j=0;j<z;j++){if(r[i]>>j&1)sig[i][1+color[j]]++;if(r[j]>>i&1)sig[i][1+nc+color[j]]++;}ids.emplace(sig[i],0);}int cc=0;for(auto&[s,k]:ids)k=cc++;vector<int>newc(z);for(int i=0;i<z;i++)newc[i]=ids[sig[i]];color=newc;if(cc==nc)break;nc=cc;}
 vector<vector<int>>groups(nc);for(int i=0;i<z;i++)groups[color[i]].push_back(i);
 vector<vector<vector<int>>>perms(nc);
 for(int c=0;c<nc;c++){
  map<pair<unsigned,unsigned>,vector<int>>twins;for(int v:groups[c]){unsigned col=0;for(int i=0;i<z;i++)if(r[i]>>v&1)col|=1u<<i;twins[{r[v],col}].push_back(v);}
  vector<vector<int>>classes;vector<int>seq;for(auto&[key,vs]:twins){int id=classes.size();classes.push_back(vs);for(int v:vs)seq.push_back(id);}
  do{vector<int>used(classes.size()),p;for(int id:seq)p.push_back(classes[id][used[id]++]);perms[c].push_back(p);}while(next_permutation(seq.begin(),seq.end()));
 }
 Key best=~Key(0);vector<int>order;
 function<void(int)>rec=[&](int c){if(c<nc){for(auto&p:perms[c]){order.insert(order.end(),p.begin(),p.end());rec(c+1);order.resize(order.size()-p.size());}return;}Key key=0;for(int i=0;i<z;i++)for(int j=0;j<z;j++)if(r[order[i]]>>order[j]&1)key|=Key(1)<<(i*z+j);best=min(best,key);};rec(0);return best;
}
vector<unsigned> decode(Key key,int z){vector<unsigned>r(z);for(int i=0;i<z;i++)for(int j=0;j<z;j++)if(key>>(i*z+j)&1)r[i]|=1u<<j;return r;}
