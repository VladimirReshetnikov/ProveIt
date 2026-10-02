// Exact scan of every ten-element preorder using canonical unlabeled quotient posets.
// Canonicalization refines directed colors, then enumerates within-class permutations.
// Only exact true twins are suppressed. All maximal-element extensions are generated.
// Positive compositions of 10 expand each naturally labeled quotient poset.
#include <bits/stdc++.h>
using namespace std; using ll=long long;
struct Support{unsigned a,b;int k;};
vector<Support> supports; unsigned rows[10];int m;vector<unsigned> qrows;vector<int> blocks;
ll cases=0,degree4=0,bad[3]={},counts[11]={}; ll mins[3]={LLONG_MAX,LLONG_MAX,LLONG_MAX};
ll rn[3]={LLONG_MAX,LLONG_MAX,LLONG_MAX},rd[3]={1,1,1};
bool match(unsigned a,unsigned b){if(!a)return true;unsigned v=rows[__builtin_ctz(a)]&b; a&=a-1; while(v){unsigned x=v&-v;v-=x;if(match(a,b^x))return true;}return false;}
bool perfect(unsigned v){if(!v)return true;int i=__builtin_ctz(v);v&=v-1;for(unsigned c=v;c;c&=c-1){int j=__builtin_ctz(c);if(((rows[i]>>j&1)||(rows[j]>>i&1))&&perfect(v^(1<<j)))return true;}return false;}
void witness(string kind,array<ll,5> g,ll value){cout<<kind<<" value="<<value<<" gamma=";for(ll x:g)cout<<x<<",";cout<<" rows=";for(auto x:rows)cout<<x<<",";cout<<" blocks=";for(auto x:blocks)cout<<x<<",";cout<<endl;}
void eval(){int cls[10],p=0;for(int i=0;i<m;i++)for(int j=0;j<blocks[i];j++)cls[p++]=i;fill(rows,rows+10,0);for(int i=0;i<10;i++)for(int j=0;j<10;j++)if(i!=j&&(cls[i]==cls[j]||(qrows[cls[i]]>>cls[j]&1)))rows[i]|=1u<<j;cases++;if(perfect(1023))return;bool degree=false;for(int i=0;i<10&&!degree;i++)for(int j=i+1;j<10;j++)if(perfect(1023^(1u<<i)^(1u<<j))){degree=true;break;}if(!degree)return;degree4++;array<ll,5> g={1,0,0,0,0};for(auto s:supports)if(match(s.a,s.b))g[s.k]++;ll vals[]={3*g[1]*g[1]-8*g[2],4*g[2]*g[2]-9*g[1]*g[3],3*g[3]*g[3]-8*g[2]*g[4]};ll nums[]={3*g[1]*g[1],4*g[2]*g[2],3*g[3]*g[3]},dens[]={8*g[2],9*g[1]*g[3],8*g[2]*g[4]};for(int j=0;j<3;j++){if(vals[j]<0){bad[j]++;witness("FAIL_"+to_string(j+1),g,vals[j]);}if(vals[j]<mins[j]){mins[j]=vals[j];witness("MIN_GAP_"+to_string(j+1),g,vals[j]);}if(rn[j]==LLONG_MAX||nums[j]*rd[j]<rn[j]*dens[j]){rn[j]=nums[j];rd[j]=dens[j];witness("MIN_RATIO_"+to_string(j+1),g,0);cout<<"ratio="<<rn[j]<<"/"<<rd[j]<<endl;}}}
void compose(int idx,int left){if(idx==m-1){blocks[idx]=left;eval();return;}for(int x=1;x<=left-(m-idx-1);x++){blocks[idx]=x;compose(idx+1,left-x);}}

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
int main(){for(unsigned a=1;a<1024;a++){int k=__builtin_popcount(a);if(k>4)continue;unsigned complement=1023^a;for(unsigned b=complement;b;b=(b-1)&complement)if(__builtin_popcount(b)==k)supports.push_back({a,b,k});}cerr<<"supports="<<supports.size()<<endl;vector<vector<unsigned>>last(1);
 for(m=1;m<=10;m++){
  set<Key>keys;for(auto&r:last){int z=r.size();for(unsigned pred=0;pred<(1u<<z);pred++){bool ideal=true;for(int i=0;i<z;i++)if(!(pred>>i&1)&&(r[i]&pred)){ideal=false;break;}if(!ideal)continue;auto nr=r;for(int i=0;i<z;i++)if(pred>>i&1)nr[i]|=1u<<z;nr.push_back(0);keys.insert(canonical(nr));}}
  vector<vector<unsigned>>current;for(Key key:keys){auto r=decode(key,m);current.push_back(r);qrows=r;counts[m]++;blocks.assign(m,0);compose(0,10);}last=move(current);
  cout<<"m="<<m<<" unlabeled_quotients="<<counts[m]<<" cumulative_cases="<<cases<<" degree4="<<degree4<<endl;
 }
 cout<<"FINISHED cases="<<cases<<" degree4="<<degree4<<" failures="<<bad[0]<<","<<bad[1]<<","<<bad[2]<<endl;for(int j=0;j<3;j++)cout<<"inequality="<<j+1<<" min_gap="<<mins[j]<<" min_ratio="<<rn[j]<<"/"<<rd[j]<<endl;
}
