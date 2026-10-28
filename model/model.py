"""Executable model of draft-ietf-sidrops-aspa-verification-28 (Sections 5.2-5.6) and an
RFC 7908-style ground truth (valley-free export rules), for exhaustive checking on small topologies.

Relationship of an ordered pair (x, y), as seen from x:  'prov' (y is x's provider), 'cust', 'peer',
'rs' (y is a non-transparent route server and x its client), 'rsc' (y is an RS-client of RS x).
"""
import itertools
INV={'prov':'cust','cust':'prov','peer':'peer','rs':'rsc','rsc':'rs'}

# ---------- draft-28, Section 5.3: provider authorization function ----------
def authorized(spas, x, y):
    if x not in spas: return 'NoAtt'
    return 'Prov+' if y in spas[x] else 'NotProv+'

def compress(path):
    out=[]
    for a in path:
        if not out or out[-1]!=a: out.append(a)
    return out

# ---------- Section 5.4: bounds;  path is listed origin-first: A[1]=AS(1) .. A[N]=AS(N) ----------
def bounds(spas, A):
    N=len(A)
    au=lambda i: authorized(spas, A[i-1], A[i])      # pair (A(i), A(i+1)), 1-based i
    ad=lambda j: authorized(spas, A[j-1], A[j-2])    # pair (A(j), A(j-1))
    max_up=next((i for i in range(1,N) if au(i)=='NotProv+'), N)
    min_up=next((i for i in range(1,N) if au(i) in ('NoAtt','NotProv+')), N)
    J=max((j for j in range(2,N+1) if ad(j)=='NotProv+'), default=None)
    max_down=N-J+1 if J is not None else N
    J=max((j for j in range(2,N+1) if ad(j) in ('NoAtt','NotProv+')), default=None)
    min_down=N-J+1 if J is not None else N
    return max_up,min_up,max_down,min_down

# ---------- Sections 5.5 / 5.6 (steps 1-3 assumed passed: non-empty, neighbor matches, no AS_SET) ----------
def verify(spas, path, downstream):
    A=compress(path); N=len(A)
    mu,nu,md,nd=bounds(spas,A)
    if not downstream: md=nd=0
    if mu+md<N: return 'Invalid'
    if nu+nd<N: return 'Unknown'
    return 'Valid'

# ---------- ground truth: RFC 7908 / Gao-Rexford export rules ----------
def may_export(learned_from_rel, to_rel):
    """learned_from_rel: relation of the sender as seen by the exporting AS (None = own prefix)."""
    if learned_from_rel is None or learned_from_rel in ('cust','rsc'):   # own or from customer / from RS-client (AS acts as RS)
        if learned_from_rel=='rsc':   # an RS re-advertises client routes to its clients only
            return to_rel=='rsc'
        return True
    return to_rel in ('cust',)       # learned from provider / peer / RS: only to customers

def leak_free(rel, path, receiver):
    """path origin-first; every AS(i) (i>=2 ... N) must legally export to the next AS; AS(1) originates."""
    full=list(path)+[receiver]
    for i in range(len(path)):
        frm=None if i==0 else rel[(full[i],full[i-1])]
        to=rel[(full[i],full[i+1])]
        if not may_export(frm,to): return False
    return True

def spas_of(rel, ases):
    s={x:set() for x in ases}
    for (x,y),r in rel.items():
        if r in ('prov','rs'): s[x].add(y)
    return s
