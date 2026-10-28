#include <bits/stdc++.h>
using namespace std;
int r,E,m; vector<pair<int,int>> edges; mt19937 rng(783421);
using Plan=vector<int>; using Masks=vector<vector<int>>;
Masks masks(const Plan&p){
 vector<vector<int>> cls;int a=(r+2)/3,b=(r+1)/3,c=r-a-b;
 vector<vector<int>> blocks={{p.begin(),p.begin()+a},{p.begin()+a,p.begin()+a+b},{p.begin()+a+b,p.end()}};
 vector<array<vector<int>,3>> ops;
 function<void(vector<int>)> build=[&](vector<int> bl){if(bl.size()<2)return;int n=bl.size()/2;vector<int>A(bl.begin(),bl.begin()+n),B(bl.begin()+n,bl.end()),O;build(A);build(B);for(int v=0;v<r;v++)if(find(bl.begin(),bl.end(),v)==bl.end())O.push_back(v);ops.push_back({A,B,O});};
 for(auto bl:blocks)build(bl);ops.push_back({blocks[0],blocks[1],blocks[2]});Masks out;
 for(auto op:ops){vector<int>C(r);for(int j=0;j<3;j++)for(int v:op[j])C[v]=j;for(int d=0;d<3;d++){vector<int>v;for(auto [x,y]:edges){int i=C[x],j=C[y];v.push_back(i==j?0:((i+j)==(d==0?1:d==1?2:3)?2:5));}out.push_back(v);}}
 return out;
}
int score(const array<Masks,4>&V){
 vector<int> norm[4]; static int g[4][4][64][64];
 for(int p=0;p<4;p++){norm[p].assign(m,0);for(int i=0;i<m;i++)for(int e=0;e<E;e++)norm[p][i]+=V[p][i][e]*V[p][i][e];for(int q=0;q<p;q++)for(int i=0;i<m;i++)for(int j=0;j<m;j++){int t=0;for(int e=0;e<E;e++)t+=V[p][i][e]*V[q][j][e];g[p][q][i][j]=2*t;}}
 int ans=0;for(int i=0;i<m;i++)for(int j=0;j<m;j++)for(int k=0;k<m;k++){int base=norm[0][i]+norm[1][j]+norm[2][k]+g[1][0][j][i]+g[2][0][k][i]+g[2][1][k][j];for(int l=0;l<m;l++)ans=max(ans,base+norm[3][l]+g[3][0][l][i]+g[3][1][l][j]+g[3][2][l][k]);}return ans;
}
void print(array<Plan,4>&P,int Q){cout<<"{\"r\":"<<r<<",\"Q\":"<<Q<<",\"b\":"<<setprecision(16)<<sqrt(2.0*Q/(400*r*r))<<",\"permutations\":[";for(int j=0;j<4;j++){if(j)cout<<",";cout<<"[";for(int i=0;i<r;i++){if(i)cout<<",";cout<<P[j][i];}cout<<"]";}cout<<"]}"<<endl;}
int main(int argc,char**argv){r=argc>1?atoi(argv[1]):13;int trials=argc>2?atoi(argv[2]):20000;E=r*(r-1)/2;m=3*(r-2);for(int i=0;i<r;i++)for(int j=i+1;j<r;j++)edges.push_back({i,j});array<Plan,4>P;array<Masks,4>V;for(int p=0;p<4;p++){P[p].resize(r);iota(P[p].begin(),P[p].end(),0);if(p)shuffle(P[p].begin(),P[p].end(),rng);V[p]=masks(P[p]);}int s=score(V),best=s;array<Plan,4>BP=P;print(P,best);double temp=50.;for(int t=0;t<trials;t++){int p=1+rng()%3,i=rng()%r,j=rng()%r;swap(P[p][i],P[p][j]);auto old=V[p];V[p]=masks(P[p]);int val=score(V);double tp=2.+30.*(1.-double(t%3000)/3000.);if(val<=s||uniform_real_distribution<double>(0,1)(rng)<exp((s-val)/tp)){s=val;if(s<best){best=s;BP=P;print(P,best);}}else{swap(P[p][i],P[p][j]);V[p]=move(old);}if(t%3000==2999){P=BP;for(int j=0;j<4;j++)V[j]=masks(P[j]);s=best;}}
}
