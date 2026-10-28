"""draft-sriram-sidrops-asra-verification-05, Section 4 (Algorithms A and B, downstream enhancement)."""
from model import authorized, compress, bounds, verify
def fake_link(aspa, asra, x, y, alg):
    c1 = x in aspa and y not in aspa[x]
    c2 = x in asra and y not in (asra[x]['C'] | asra[x]['LP'])
    if alg=='B': return c1 and c2
    c3 = (y not in aspa) or (x not in aspa[y])
    return c1 and c2 and c3
def lateral(aspa, asra, x, y):
    # "AS(i) has ASPA and ASRA asserting that AS(i+1) is a lateral peer (and not a Provider or Customer)"
    return x in aspa and x in asra and y in asra[x]['LP'] and y not in aspa[x] and y not in asra[x]['C']
def verify_asra(aspa, asra, path, downstream, alg):
    out = verify(aspa, path, downstream)
    if not downstream: return out                     # upstream unchanged
    A = compress(path); N = len(A)
    mu, nu, md, nd = bounds(aspa, A)
    if out == 'Invalid': return out                                        # step 1
    if alg=='A':
        if nu == N or nu + nd > N: return out                              # step 2
        hi3 = N - nd; hi4 = N - nd
    else:
        if nu == N: return out
        hi3 = N - 1; hi4 = N - 1
    AS = lambda i: A[i-1]
    for i in range(nu, hi3 + 1):                                           # step 3
        if 1 <= i < N and fake_link(aspa, asra, AS(i), AS(i+1), alg): return 'Invalid'
    for i in range(nu + 1, hi4 + 1):                                       # step 4
        if 1 <= i < N and lateral(aspa, asra, AS(i), AS(i+1)): return 'Invalid'
    return out
