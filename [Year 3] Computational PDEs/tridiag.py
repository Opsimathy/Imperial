#! /usr/bin/python
import numpy as np
from numpy import *
import matplotlib
from matplotlib import pyplot as plt
from matplotlib import animation


N = 5
alpha = 1.0
u = zeros(N)

for it in xrange(0, N):
	u[it] = 1.0

k = arange(N)

## Tri Diagonal Matrix Algorithm(a.k.a Thomas algorithm) solver
def TDMAsolver(a, b, c, d):
    '''
    TDMA solver, a b c d can be NumPy array type or Python list type.
    refer to http://en.wikipedia.org/wiki/Tridiagonal_matrix_algorithm
    '''
    nf = len(a)     # number of equations
    ac, bc, cc, dc = map(np.array, (a, b, c, d))     # copy the array
    for it in xrange(1, nf):
        mc = ac[it]/bc[it-1]
        bc[it] = bc[it] - mc*cc[it-1] 
        dc[it] = dc[it] - mc*dc[it-1]
 
    xc = ac
    xc[-1] = dc[-1]/bc[-1]
 
    for il in xrange(nf-2, -1, -1):
        xc[il] = (dc[il]-cc[il]*xc[il+1])/bc[il]
 
    del bc, cc, dc  # delete variables from memory
 
    return xc

	

a = alpha*ones(N); a[0] = 0; a[N-1] = 1.0 #a[0] = 0;
b = (-2.0)*ones(N); b[0] = -2.0; b[N-1] = -2.0
c = alpha*ones(N); c[0] = 1.0; c[N-1] = 0.0
d = u
print("a b c d :  TDMA-solve arrays : " ) 
print('a: ', a)
print("b: ", b)
print("c: ", c)
print("d: ", d)
u = TDMAsolver(a,b,c,d)
print("TDMAsolution:") 
#	print(u)

nf = len(u)
for i in xrange(0, nf):
#	print('X%d = %0.9f' %(i,ug[i]))
	print('X%d = %0.11e' %(i+1,u[i]))
	
		
