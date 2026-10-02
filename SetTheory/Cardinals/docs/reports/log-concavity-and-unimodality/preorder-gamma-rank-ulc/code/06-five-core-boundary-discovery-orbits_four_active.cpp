#include <array>
#include <vector>
#include <algorithm>
#include <cstdio>
int main(){std::vector<std::pair<int,int>>ed;int ix[5][5];for(int i=0;i<4;i++)for(int j=0;j<5;j++)if(i!=j){ix[i][j]=ed.size();ed.push_back({i,j});}std::array<int,5>p={0,1,2,3,4};std::vector<std::array<int,16>>maps;do{std::array<int,16>m;for(int k=0;k<16;k++)m[k]=ix[p[ed[k].first]][p[ed[k].second]];maps.push_back(m);}while(std::next_permutation(p.begin(),p.begin()+4));std::vector<bool>seen(1<<16,false);for(int c=0;c<(1<<16);c++)if(!seen[c]){int rows[5]={};for(int k=0;k<16;k++)if(c>>k&1)rows[ed[k].first]|=1<<ed[k].second;printf("%d %d %d %d %d %d\n",c,rows[0],rows[1],rows[2],rows[3],rows[4]);for(auto m:maps){int z=0;for(int k=0;k<16;k++)if(c>>k&1)z|=1<<m[k];seen[z]=true;}}}
