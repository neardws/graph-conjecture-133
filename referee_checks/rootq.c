/* rootq: test the rooted bounds of the supplement on connected C4-free graphs (graph6 on stdin).
   For each root s: p_s = largest order of an induced path starting at s, D = d(s), m = e(G[N(s)]).
   ROOT(q) (Def S1.1): p_s <= q  =>  S <= (q-1)(n-1) - (q-3)D - m.   Tightest instance q = max(p_s,3).
   Conj S4.5 / Prop S1.3: p_s = q and ecc(s) = q-1  =>  S <= (q-1)(n-1) - (q-3)D - m - (q-2)(q-3).
   Conj S4.4 (radius part): r >= 5 and p = 2r-1  =>  S <= (r-1)n - 2r(r-3), equality only for C_{2r}.
   Prints counts of violations per q and the first few violating graphs. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint32_t set;
static int n; static set adj[32];
static int popc(set x){return __builtin_popcount(x);}
static int bestp;
static void dfs(int last,set B,int len){ if(len>bestp) bestp=len; set c=adj[last]&~B, Bn=B|adj[last]|(1u<<last); for(set t=c;t;t&=t-1) dfs(__builtin_ctz(t),Bn,len+1); }
static int ecc(int v){ set all=(1u<<n)-1, seen=1u<<v, fr=seen; int d=0; while(seen!=all){ set nf=0; for(set t=fr;t;t&=t-1) nf|=adj[__builtin_ctz(t)]; nf&=~seen; if(!nf) return 999; seen|=nf; fr=nf; d++; } return d; }
int main(){
    char line[256]; long viol[20]={0}, tested[20]={0}, viol45[20]={0}, tested45[20]={0}, v44=0, t44=0, eq44=0;
    int shown=0;
    while(fgets(line,sizeof line,stdin)){
        line[strcspn(line,"\r\n")]=0; const unsigned char*p=(const unsigned char*)line; if(*p=='>'||!*p) continue;
        n=*p++-63; memset(adj,0,sizeof adj); int bits=0,val=0;
        for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(!bits){val=*p++-63;bits=6;} bits--; if((val>>bits)&1){adj[i]|=1u<<j;adj[j]|=1u<<i;} }
        int S=0,e=0; for(int v=0;v<n;v++){ int d=popc(adj[v]); e+=d; int t=0; for(set q=adj[v];q;q&=q-1) t+=popc(adj[__builtin_ctz(q)]&adj[v]); t/=2; S+=d-t; }
        e/=2;
        int P=0, r=999;
        for(int s=0;s<n;s++){
            bestp=0; dfs(s,0,1); int ps=bestp; if(ps>P) P=ps;
            int D=popc(adj[s]); int m=0; for(set q=adj[s];q;q&=q-1) m+=popc(adj[__builtin_ctz(q)]&adj[s]); m/=2;
            int es=ecc(s); if(es<r) r=es;
            int q = ps<3?3:ps;
            tested[q]++;
            long rhs=(long)(q-1)*(n-1)-(long)(q-3)*D-m;
            if(S>rhs){ viol[q]++; if(shown<6){ shown++; printf("ROOT(%d) violation: %s root=%d n=%d S=%d D=%d m=%d bound=%ld\n",q,line,s,n,S,D,m,rhs);} }
            if(ps>=4 && es==ps-1){
                tested45[ps]++;
                long rhs2=rhs-(long)(ps-2)*(ps-3);
                if(S>rhs2){ viol45[ps]++; if(shown<12){ shown++; printf("S4.5-type violation (q=%d): %s root=%d n=%d S=%d D=%d m=%d bound=%ld\n",ps,line,s,n,S,D,m,rhs2);} }
            }
        }
        if(r>=5 && P==2*r-1){ t44++; long b=(long)(r-1)*n-2L*r*(r-3); if(S>b){v44++; printf("S4.4 radius violation: %s n=%d r=%d S=%d bound=%ld\n",line,n,r,S,b);} else if(S==b){ eq44++; if(!(e==n && n==2*r)) printf("S4.4 equality not C_2r: %s\n",line);} }
    }
    for(int q=3;q<20;q++) if(tested[q]) printf("ROOT(%d) [roots with p_s=%d]: tested=%ld violations=%ld\n",q,q,tested[q],viol[q]);
    for(int q=4;q<20;q++) if(tested45[q]) printf("terminal bound (S1.3/S4.5) q=%d: tested=%ld violations=%ld\n",q,tested45[q],viol45[q]);
    printf("S4.4 radius part: graphs with r>=5, p=2r-1: %ld, violations=%ld, equality cases=%ld\n",t44,v44,eq44);
    return 0;
}
