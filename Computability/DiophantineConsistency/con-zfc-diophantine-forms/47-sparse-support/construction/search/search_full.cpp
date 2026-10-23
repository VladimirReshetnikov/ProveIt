#include <algorithm>
#include <cmath>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
#include <chrono>
using namespace std;
int main(int argc,char**argv){
 int width=argc>1?atoi(argv[1]):160, seconds=argc>2?atoi(argv[2]):30;
 int n,q;ifstream in("support_full.txt");in>>n>>q;
 vector<vector<int>> sel(n,vector<int>(n));for(int x,y;in>>x>>y;){sel[x][y]=sel[y][x]=1;}
 mt19937 rng(42+width);auto start=chrono::steady_clock::now();
 int overall=1e9; long long total_moves=0;
 for(int trial=0;;trial++){
  if(chrono::duration<double>(chrono::steady_clock::now()-start).count()>seconds)break;
  vector<int>w(n),used(width);vector<int>perm(width);iota(perm.begin(),perm.end(),0);shuffle(perm.begin(),perm.end(),rng);
  w[0]=0;used[0]=1;int j=0;for(int i=1;i<n;i++){while(perm[j]==0)++j;w[i]=perm[j++];used[w[i]]=1;}
  vector<int>tot(2*width+1),pro(2*width+1);int score=0;
  auto val=[&](int s){return pro[s]*(tot[s]-pro[s])+pro[s]*(pro[s]-1)/2;};
  auto update=[&](int s,int a,int b){score-=val(s);tot[s]+=a;pro[s]+=b;score+=val(s);};
  for(int i=0;i<n;i++)for(int j=i;j<n;j++)update(w[i]+w[j],1,sel[i][j]);
  for(int it=0;it<2000000;it++){
   ++total_moves;
   if(score<overall){overall=score;if(overall<3)cerr<<"width "<<width<<" score "<<score<<" trial "<<trial<<" move "<<it<<endl;}
   if(score==0){int mn=0;int mx=*max_element(w.begin(),w.end());int span=mx;cout<<"{\"width\":"<<width<<",\"span\":"<<span<<",\"maximum_weight\":"<<span<<",\"weights\":[";for(int i=0;i<n;i++)cout<<(i?",":"")<<w[i];cout<<"],\"moves\":"<<total_moves<<"}"<<endl;return 0;}
   int i=1+rng()%(n-1),nw=rng()%width,ow=w[i];if(used[nw])continue;
   int old=score;
   for(int j=0;j<n;j++)update(ow+w[j],-1,-sel[i][j]);
   w[i]=nw;
   for(int j=0;j<n;j++)update(nw+w[j],1,sel[i][j]);
   double temp=0.15+1.8*(1.0-double(it%200000)/200000);
   bool accept=score<=old || double(rng())/rng.max()<exp(double(old-score)/temp);
   if(accept){used[ow]=0;used[nw]=1;}
   else{for(int j=0;j<n;j++)update(nw+w[j],-1,-sel[i][j]);w[i]=ow;for(int j=0;j<n;j++)update(ow+w[j],1,sel[i][j]);}
   if(it%10000==0&&chrono::duration<double>(chrono::steady_clock::now()-start).count()>seconds)break;
  }
 }
 cerr<<"best "<<overall<<" width "<<width<<" moves "<<total_moves<<endl;return 1;
}
