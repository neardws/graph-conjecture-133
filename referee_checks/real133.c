/* real133: for each connected graph (graph6 on stdin) compute
   S = sum alpha(G[N(v)]), p = longest induced path order, r = radius,
   c4sub = has 4-cycle subgraph, c4ind = has induced 4-cycle.
   Check REAL-133 with exponent from (a) subgraph convention, (b) induced convention:
     exponent 1:  n*(p - r) >= S ;  exponent 0: p >= r + 1.
   Prints summary: number of graphs, number of violations of each version, max ell, min slack,
   and up to 5 violating graph6 strings per version. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint32_t set;
static int n; static set adj[32];
static int popc(set x){return __builtin_popcount(x);}
static int alpha(set M){
    if(!M) return 0; int best=-1,bd=-1;
    for(set t=M;t;t&=t-1){int v=__builtin_ctz(t);int d=popc(adj[v]&M); if(d>bd){bd=d;best=v;}}
    if(bd==0) return popc(M);
    int a1=alpha(M&~(1u<<best)), a2=1+alpha(M&~(adj[best]|(1u<<best)));
    return a1>a2?a1:a2;
}
static int bestp;
static void dfs(int last,set B,int len){ if(len>bestp) bestp=len; set c=adj[last]&~B, Bn=B|adj[last]|(1u<<last); for(set t=c;t;t&=t-1) dfs(__builtin_ctz(t),Bn,len+1); }
static int ecc(int v){ set all=(1u<<n)-1, seen=1u<<v, fr=seen; int d=0; while(seen!=all){ set nf=0; for(set t=fr;t;t&=t-1) nf|=adj[__builtin_ctz(t)]; nf&=~seen; if(!nf) return 999; seen|=nf; fr=nf; d++; } return d; }
int main(){
    char line[256]; long cnt=0, vsub=0, vind=0; double maxell=0; char maxg[256]="";
    double minslack=1e9; char ming[256]="";
    while(fgets(line,sizeof line,stdin)){
        line[strcspn(line,"\r\n")]=0; const unsigned char*p=(const unsigned char*)line; if(*p=='>'||!*p) continue;
        n=*p++-63; memset(adj,0,sizeof adj); int bits=0,val=0;
        for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(!bits){val=*p++-63;bits=6;} bits--; if((val>>bits)&1){adj[i]|=1u<<j;adj[j]|=1u<<i;} }
        cnt++;
        int S=0; for(int v=0;v<n;v++) S+=alpha(adj[v]);
        bestp=0; for(int s=0;s<n;s++) dfs(s,0,1);
        int r=999; for(int v=0;v<n;v++){int e=ecc(v); if(e<r) r=e;}
        int c4sub=0,c4ind=0;
        for(int u=0;u<n;u++) for(int w=u+1;w<n;w++){ set c=adj[u]&adj[w]; if(popc(c)>=2){ c4sub=1; if(!((adj[u]>>w)&1)){ for(set t=c;t;t&=t-1){int x=__builtin_ctz(t); if(c & ~adj[x] & ~(1u<<x)) c4ind=1;} } } }
        double ell=(double)S/n;
        int ok_sub = c4sub ? (bestp>=r+1) : (n*(bestp-r) >= S);
        int ok_ind = c4ind ? (bestp>=r+1) : (n*(bestp-r) >= S);
        if(!c4sub){ if(ell>maxell){maxell=ell; strcpy(maxg,line);} double sl=(bestp-r)-ell; if(sl<minslack){minslack=sl; strcpy(ming,line);} }
        if(!ok_sub){ vsub++; if(vsub<=5) printf("VIOLATION(subgraph convention) %s S=%d p=%d r=%d\n",line,S,bestp,r); }
        if(!ok_ind){ vind++; if(vind<=5) printf("VIOLATION(induced convention) %s n=%d S=%d ell=%.3f p=%d r=%d\n",line,n,S,ell,bestp,r); }
    }
    printf("graphs=%ld  violations: subgraph-convention=%ld induced-convention=%ld  | C4-free graphs: max ell=%.4f (%s), min slack p-r-ell=%.4f (%s)\n",
           cnt,vsub,vind,maxell,maxg,minslack,ming);
    return 0;
}
