/* extend: read connected graphs (graph6) of order n from stdin; print every one-vertex
   extension G+z (N(z) = U nonempty) that stays in the class:
     - no 4-cycle subgraph (no two vertices of U share a neighbour in G)
     - if argv[2] == "t": triangle-free as well (U independent)
     - no induced path on K vertices, K = argv[1]
   Every connected graph of order n+1 in a hereditary class is G+z for a connected G of order n
   in the class (delete a non-cut vertex), so iterating extend | labelg | sort -u enumerates the class.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint32_t set;
static int n, K, tfree;
static set adj[32];
static int popc(set x){ return __builtin_popcount(x); }

static int found;
static void dfs(int last, set B, int len, int nn, set *A){
    if(len>=K){ found=1; return; }
    set cand = A[last] & ~B;
    set Bn = B | A[last] | (1u<<last);
    for(set t=cand;t && !found;t&=t-1) dfs(__builtin_ctz(t), Bn, len+1, nn, A);
}
/* is there an induced P_K through vertex z in graph A on nn vertices?  (G itself is P_K-free) */
static int has_PK_through(set *A, int nn, int z){
    found=0;
    for(int s=0;s<nn && !found;s++) dfs(s,0,1,nn,A);
    return found;
}

static void out_g6(set *A, int nn){
    char buf[256]; int k=0; buf[k++]=63+nn;
    int bits=0,val=0;
    for(int j=1;j<nn;j++) for(int i=0;i<j;i++){
        val=(val<<1)|((A[i]>>j)&1); bits++;
        if(bits==6){ buf[k++]=63+val; bits=0; val=0; }
    }
    if(bits){ val<<= (6-bits); buf[k++]=63+val; }
    buf[k]=0; puts(buf);
}

static set ext[32];
static void rec(int v, set U, set forbidden){
    /* choose subset U of {0..n-1}; forbidden = vertices that cannot be added (share nbr with U, or adj in tfree mode) */
    if(v==n){
        if(!U) return;
        for(int i=0;i<n;i++) ext[i]=adj[i] | (((U>>i)&1)? (1u<<n):0);
        ext[n]=U;
        if(!has_PK_through(ext,n+1,n)) out_g6(ext,n+1);
        return;
    }
    rec(v+1,U,forbidden);                       /* v not in U */
    if(!((forbidden>>v)&1)){
        /* adding v: forbid any w sharing a neighbour with v */
        set f=forbidden;
        for(int w=0;w<n;w++) if(w!=v && (adj[w]&adj[v])) f|=1u<<w;
        if(tfree) f|=adj[v];
        rec(v+1,U|(1u<<v),f);
    }
}

static int parse_g6(const char *s){
    const unsigned char *p=(const unsigned char*)s;
    n=*p++-63; memset(adj,0,sizeof adj);
    int bits=0,val=0;
    for(int j=1;j<n;j++) for(int i=0;i<j;i++){
        if(!bits){ val=*p++-63; bits=6; }
        bits--; if((val>>bits)&1){ adj[i]|=1u<<j; adj[j]|=1u<<i; }
    }
    return 1;
}
int main(int argc,char**argv){
    K=atoi(argv[1]); tfree = argc>2 && argv[2][0]=='t';
    char line[256];
    while(fgets(line,sizeof line,stdin)){
        line[strcspn(line,"\r\n")]=0; if(!line[0]) continue;
        parse_g6(line);
        rec(0,0,0);
    }
    return 0;
}
