from pathlib import Path
p=Path(__file__).resolve().parent/'global_search'
s=(p/'screen.cpp').read_text()
s=s.replace('unsigned incoming[200]={};\n auto inc=[&](int q){for(int b=0;b<2;b++){auto a=rows[q][b];if(a.d&&a.w==b&&a.n>=2000&&a.n<2000+n)incoming[a.n-2000]|=1u<<b;}};', '''unsigned incoming[2500]={};bool badin[2500]={};
 auto inc=[&](int q){for(int b=0;b<2;b++){auto a=rows[q][b];if(a.n>=0&&a.n<2500){if(a.d&&a.w==b)incoming[a.n]|=1u<<b;else badin[a.n]=true;}}};''')
s=s.replace('vector<int> left,right;for(int j=0;j<n;j++){if(incoming[j]==1)left.push_back(2000+j);if(incoming[j]==2)right.push_back(2000+j);}\n vector<vector<int>> edges(n);vector<Op>ops;', '''vector<int> left,right;vector<int> eligible=base;for(int j=0;j<n;j++)eligible.push_back(2000+j);
 static const set<int> BOX={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198};
 for(int q:eligible){if(badin[q]||BOX.count(q))continue;if(incoming[q]==1)left.push_back(q);if(incoming[q]==2)right.push_back(q);}
 vector<vector<int>> edges(2500);vector<Op>ops;''')
s=s.replace('edges[a-2000].push_back(b-2000)','edges[a].push_back(b)')
s=s.replace('vector<int> match(n,-1)','vector<int> match(2500,-1)').replace('vector<bool>seen(n);if(augment(a-2000,seen))','vector<bool>seen(2500);if(augment(a,seen))')
s='#include <set>\n'+s
(p/'screen_full.cpp').write_text(s)
s=(p/'search.cpp').read_text().replace('#include "screen.cpp"','#include "screen_full.cpp"')
(p/'search_full.cpp').write_text(s)
