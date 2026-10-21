#include <algorithm>
#include <iostream>
#include <random>
#include <vector>
using namespace std;
struct E {int cost=1000000, choice=-1;};
int n,lim,K,m,seed;vector<E>d;mt19937 rng;
E&get(int i,int j,int l){return d[(i*(n+1)+j)*(K+1)+l];}
void out(int i,int j,int l){E e=get(i,j,l);if(e.choice<0){cout<<(-e.choice-2);return;}int k=e.choice;cout<<"[";out(i,k,l-1);cout<<",";out(k,j,K);cout<<"]";}
int main(){ios::sync_with_stdio(false);cin.tie(nullptr);cin>>n>>lim>>K>>m>>seed;rng.seed(seed);d.resize((n+1)*(n+1)*(K+1));
for(int x=0;x<m;x++){int i,j,l,id;cin>>i>>j>>l>>id;for(int k=l;k<=K;k++)get(i,j,k)={0,-id-2};}
for(int sz=1;sz<=n;sz++)for(int i=0;i+sz<=n;i++){int j=i+sz;for(int l=1;l<=K;l++){E&e=get(i,j,l);if(e.cost==0)continue;int ties=0;for(int k=i+1;k<j;k++){int c=1+get(i,k,l-1).cost+get(k,j,K).cost;if(c<e.cost){e={c,k};ties=1;}else if(seed&&c==e.cost&&rng()%++ties==0)e={c,k};}}}
if(get(0,n,lim).cost>=1000000){cout<<"{\"error\":\"NO_PARSE\"}\n";return 0;}
cout<<"{\"cost\":"<<get(0,n,lim).cost<<",\"tree\":";out(0,n,lim);cout<<"}\n";}
