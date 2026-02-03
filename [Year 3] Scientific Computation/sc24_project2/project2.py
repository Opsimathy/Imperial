""" 
    Your college id here: 02216531
    Template code for project 2, contains 9 functions:
    simulate1: complete function for part 1
    part1q1a, part1q1b, part1q1c, part1q2: functions to be completed for part 1
    dualfd1,fd2: complete functions for part 2
    part2q1, part2q2: functions to be completed for part 2
"""
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib.pyplot as plt
#you may use numpy, scipy, and matplotlib as needed


#---------------------------- Code for Part 1 ----------------------------#
def simulate1(n,X0=-1,Nt=2000,tf=1000,g=1.0,mu=0.0,flag_display=False):
    """
    Simulation code for part 1
    Input:
        n: number of ODEs
        X0: initial condition if n-element numpy array. If X0 is an integer, the code will set 
        the initial condition (otherwise an array is expected).
        Nt: number of time steps
        tf: final time
        g,mu: model parameters
        flag_display: will generate a contour plot displaying results if True
    Output:
    t,x: numpy arrays containing times and simulation results
    """

    def model(t, X, n, g, mu):
        """
        Defines the system of ODEs 
        
        Input:
        - t: time 
        - X: array of variables [x_0, x_1, ..., x_{n-1}]
        - g, mu: scalar model parameters
        - n: number of ODEs (size of the system)
         
        Returns:
        - dXdt: array of derivatives [dx_0/dt, dx_1/dt, ..., dx_{n-1}/dt]
        """
        dXdt = np.zeros(n)
        dXdt[0] = X[0]*(1-g*X[-2]-X[0]-g*X[1]+mu*X[-3])
        dXdt[1] = X[1]*(1-g*X[-1]-X[1]-g*X[2])
        dXdt[2:n-1] = X[2:n-1]*(1-g*X[0:n-3]-X[2:n-1]-g*X[3:n])
        dXdt[-1] = X[-1]*(1-g*X[-3]-X[-1]-g*X[0])
        return dXdt

    # Parameters
    t_span = (0, tf)  # Time span for the integration
    if type(X0)==int: #(modified from original version)
        X0 = 1/(2*g+1)+0.001*np.random.rand(n)  # Random initial conditions, modify if needed

    # Solve the system
    solution = solve_ivp(
        fun=model,
        t_span=t_span,
        y0=X0,
        args=(n, g, mu),
        method='BDF',rtol=1e-10,atol=1e-10,
        t_eval=np.linspace(t_span[0], t_span[1], Nt)  # Times to evaluate the solution
    )

    t,x = solution.t,solution.y #(in original version of code this line was inside if-block below)
    if flag_display:
        # Plot the solution
        plt.contour(t,np.arange(n),x,20)
        plt.xlabel('t') #(corrected axis labels)
        plt.ylabel('i')
    return t,x

def part1q1a(n,g,mu,T):
    """Part 1, question 1 (a)
    Use the variable inputs if/as needed.
    Input:
    n: number of ODEs
    g,mu: model parameters
    T: time at which perturbation energy ratio should be maximized
    
    Output:
    xbar: n-element array containing non-trivial equilibrium solution
    xtilde0: n-element array corresponding to computed initial condition
    eratio: computed maximum perturbation energy ratio
    """
    #use/modify code below as needed:

    # Define the system of ODEs
    def ODEs(x):
        dxdt = np.zeros(n)
        dxdt[0] = x[0] * (1 - x[0] - g * (x[n-2] + x[1]) + mu * x[n-3])
        dxdt[1] = x[1] * (1 - x[1] - g * (x[n-1] + x[2]))
        for i in range(2, n-2):
            dxdt[i] = x[i] * (1 - x[i] - g * (x[i-2] + x[i+1]))
        dxdt[n-1] = x[n-1] * (1 - x[n-1] - g * (x[n-3] + x[0]))
        return dxdt

    # Solve for a non-trivial equilibrium
    from scipy.optimize import root
    xbar = root(ODEs, np.ones(n) * 0.5).x  # with an initial guess

    # Construct Jacobian at the equilibrium
    J = np.zeros((n, n))
    for i in range(n):
        if i == 0:
            J[i, i] = 1 - 2 * xbar[i] - g * (xbar[n-2] + xbar[1])
            J[i, n-2] = -g * xbar[i]
            J[i, 1] = -g * xbar[i]
            J[i, n-3] = mu * xbar[i]
        elif i == 1:
            J[i, i] = 1 - 2 * xbar[i] - g * (xbar[n-1] + xbar[2])
            J[i, n-1] = -g * xbar[i]
            J[i, 2] = -g * xbar[i]
        elif i == n-1:
            J[i, i] = 1 - 2 * xbar[i] - g * (xbar[n-3] + xbar[0])
            J[i, n-3] = -g * xbar[i]
            J[i, 0] = -g * xbar[i]
        else:
            J[i, i] = 1 - 2 * xbar[i] - g * (xbar[i-2] + xbar[i+1])
            J[i, i-2] = -g * xbar[i]
            J[i, i+1] = -g * xbar[i]

    # Compute the eigenvalues and eigenvectors
    eigenvalues, eigenvectors = np.linalg.eig(J)
    max_index = np.argmax(np.real(eigenvalues))
    xtilde0 = eigenvectors[:, max_index].real
    eratio = np.exp(2 * np.real(eigenvalues[max_index]) * T)

    return xbar, xtilde0, eratio

def part1q1b():
    """Part 1, question 1(b): 
    Add input/output if/as needed.
    """
    #use/modify code below as needed:
    n = 19
    g = 1.2
    mu = 2.5
    T = 50

    #add code here

    # Compute equilibrium solution and energy ratio using part1q1a
    xbar, _, r_a = part1q1a(n, g, mu, T)

    # Compute energy ratio from simulation
    _, x = simulate1(n=n, tf=T, g=g, mu=mu)
    e_sim = np.linalg.norm(x - xbar[:, None], axis=0)**2
    r_sim = e_sim[-1] / e_sim[0]

    return r_a, r_sim

def part1q1c():
    """Part 1, question 1(c): 
    Add input/output if/as needed.
    """
    #use/modify code below as needed:
    n = 19
    g = 2
    mu = 0

    #add code here

    # Initial setup
    T_values = np.linspace(1, 50, 50)
    eratios = []

    # Iterate over each T value with simulate1 and compute the energy ratio
    for T in T_values:
        _, x = simulate1(n, tf=T, g=g, mu=mu)
        xbar, _, _ = part1q1a(n, g, mu, T)
        e_sim = np.linalg.norm(x - xbar[:, None], axis=0)**2
        eratios.append(e_sim[-1] / e_sim[0])

    # Plot max(e(T)/e(0)) as a function of T
    plt.plot(T_values, eratios, label=r'$\max(e(t=T)/e(t=0))$')
    plt.xlabel(r'$T$')
    plt.ylabel(r'$\max(e(t=T)/e(t=0))$')
    plt.show()

    return None #modify if needed

def part1q2():
    """Part 1, question 2: 
    Add input/output if/as needed.
    """

    #add code here

    # Initial setup
    g = 1
    mu = 0 
    n_values = [9, 20, 59]
    tf_values = [100, 250, 500]
    results = {}

    # Analyse each case
    for n, tf in zip(n_values, tf_values):
        # Simulate the system with final time 250
        t, x = simulate1(n=n, tf=tf, g=g, mu=mu)

        # Discard transient dynamics (first 25%)
        cutoff = int(0.25 * len(t))
        t = t[cutoff:]
        x = x[:, cutoff:]

        # Time series plot for representative components
        for i in range(5):
            plt.plot(t, x[i, :], label=f"x[{i}]")
        plt.title(f"Time Series Plot (n = {n})")
        plt.xlabel("Time")
        plt.ylabel(r'$x(t)$')
        plt.show()

        # Contour plot for all components
        plt.contour(t, np.arange(n), x, 20)
        plt.title(f"Contour Plot (n = {n})")
        plt.xlabel("Time")
        plt.ylabel("Index of State Variable")
        plt.show()

        # Observations for quantitative discussion
        results[n] = {"mean": np.mean(x, axis=1), "std": np.std(x, axis=1)}

    # Discussion and analysis
    print("Quantitative Discussion and Analysis:")
    for n, data in results.items():
        CV = np.mean(data["std"]) / np.mean(data["mean"])
        print(f"n = {n}: Coefficient of Variation = {CV}")
        if CV <= 0.1:
            print("- Dynamics appear stable and synchronised.")
        elif CV <= 0.5:
            print("- Dynamics exhibit oscillatory behaviour.")
        else:
            print("- Dynamics become complex and chaotic.")

    return None #modify if needed

#---------------------------- End code for Part 1 ----------------------------#


#---------------------------- Code for Part 2 ----------------------------#
def dualfd1(f):
    """
    Code implementing implicit finite difference scheme for special case m=1
    Implementation is not efficient.
    Input:
        f: n-element numpy array
    Output:
        df, d2f: computed 1st and 2nd derivatives
    """
    #parameters, grid
    n = f.size
    h = 1/(n-1)
    x = np.linspace(0,1,n)
    
    #fd method coefficients
    #interior points:
    L1 = [7,h,16,0,7,-h]
    L2 = [-9,-h,0,8*h,9,-h]
    
    #boundary points:
    L1b = [1,0,2,-h]
    L2b = [0,h,-6,5*h]

    L1b2 = [2,h,1,0]
    L2b2 = [-6,-5*h,0,-h]

    A = np.zeros((2*n,2*n))
    #iterate filling a row of A each iteration
    for i in range(n):
        #rows 0 and N-1
        if i==0:
            #Set boundary eqn 1
            A[0,0:4] = L1b
            #Set boundary eqn 2
            A[1,0:4] = L2b
        elif i==n-1:
            A[-2,-4:] = L1b2
            A[-1,-4:] = L2b2
        else:
            #interior rows
            #set equation 1
            ind = 2*i
            A[ind,ind-2:ind+4] = L1
            #set equation 2
            A[ind+1,ind-2:ind+4] = L2

    #set up RHS
    b = np.zeros(2*n)
    c31,c22,cb11,cb21,cb31,cb12,cb22,cb32 = 15/h,24/h,-3.5/h,4/h,-0.5/h,9/h,-12/h,3/h
    for i in range(n):
        if i==0:
            b[i] = cb11*f[0]+cb21*f[1]+cb31*f[2]
            b[i+1] = cb12*f[0]+cb22*f[1]+cb32*f[2]
        elif i==n-1:
            b[-2] =-(cb11*f[-1]+cb21*f[-2]+cb31*f[-3])
            b[-1] = -(cb12*f[-1]+cb22*f[-2]+cb32*f[-3])
        else:
            ind = 2*i
            b[ind] = c31*(f[i+1]-f[i-1])
            b[ind+1] = c22*(f[i-1]-2*f[i]+f[i+1])
    out = np.linalg.solve(A,b)
    df = out[::2]
    d2f = out[1::2]
    return df,d2f

def fd2(f):
    """
    Computes the first and second derivatives with respect to x using second-order finite difference methods.
    
    Input:
    f: m x n array whose 1st and 2nd derivatives will be computed with respect to x
    
    Output:
     df, d2f: m x n arrays containing 1st and 2nd derivatives of f with respect to x
    """

    m,n = f.shape
    h = 1/(n-1)
    df = np.zeros_like(f) 
    d2f = np.zeros_like(f)
    
    # First derivative 
    # Centered differences for the interior 
    df[:, 1:-1] = (f[:, 2:] - f[:, :-2]) / (2 * h)

    # One-sided differences at the boundaries
    df[:, 0] = (-3 * f[:, 0] + 4 * f[:, 1] - f[:, 2]) / (2 * h)
    df[:, -1] = (3 * f[:, -1] - 4 * f[:, -2] + f[:, -3]) / (2 * h)
    
    # Second derivative 
    # Centered differences for the interior 
    d2f[:, 1:-1] = (f[:, 2:] - 2 * f[:, 1:-1] + f[:, :-2]) / (h**2)
    
    # One-sided differences at the boundaries
    d2f[:, 0] = (2 * f[:, 0] - 5 * f[:, 1] + 4 * f[:, 2] - f[:, 3]) / (h**2)
    d2f[:, -1] = (2 * f[:, -1] - 5 * f[:, -2] + 4 * f[:, -3] - f[:, -4]) / (h**2)
    
    return df, d2f

def part2q1(f,h):
    """
    Part 2, question 1
    Input:
        f: m x n array whose 1st and 2nd derivatives will be computed with respect to x
    Output:
        df, d2f: m x n arrays containing 1st and 2nd derivatives of f with respect to x
        computed with implicit fd scheme
    """
    #use code below if/as needed
    m,n = f.shape
    h = 1/(n-1)
    x = np.linspace(0,1,n)
    y = np.linspace(0,1,m)
    df = np.zeros_like(f) #modify as needed
    d2f = np.zeros_like(f) #modify as needed

    #Add code here

    # Build A as a sparse pentadiagonal matrix
    size = 2 * n
    lower2 = np.zeros(size)
    lower1 = np.zeros(size)
    main = np.zeros(size)
    upper1 = np.zeros(size)
    upper2 = np.zeros(size)

    for i in range(size):
        # Even index: u'
        if i % 2 == 0:
            if i == 0:
                main[i] = 1
                upper1[i+1] = 2
                upper2[i+2] = -h
            elif i == size - 2:
                main[i] = 1
                lower1[i-1] = 2
                lower2[i-2] = h
            else:
                main[i] = 16
                upper1[i+1] = 7
                lower1[i-1] = 7
                upper2[i+2] = -h
                lower2[i-2] = h
        # Odd index: u''
        else:
            if i == 1:
                main[i] = h
                upper1[i+1] = -6
                upper2[i+2] = 5 * h
            elif i == size - 1:
                main[i] = -h
                lower1[i-1] = -6
                lower2[i-2] = -5 * h
            else:
                main[i] = 8 * h
                upper1[i+1] = 9
                lower1[i-1] = -9
                upper2[i+2] = -h
                lower2[i-2] = -h

    from scipy.sparse import dia_matrix
    A = dia_matrix(([lower2, lower1, main, upper1, upper2], [-2, -1, -0, 1, 2]), shape=(size, size)).tocsr()

    # Constants for the vector b
    c31, c22 = 15 / h, 24 / h
    cb11, cb21, cb31 = -3.5 / h, 4 / h, -0.5 / h
    cb12, cb22, cb32 = 9 / h, -12 / h, 3 / h

    # For each row in f, compute df and d2f
    from scipy.sparse.linalg import spsolve
    for i in range(m):
        b = np.zeros(size)
        f_row = f[i, :]
        for j in range(n):
            if j == 0:
                b[0] = cb11 * f_row[0] + cb21 * f_row[1] + cb31 * f_row[2]
                b[1] = cb12 * f_row[0] + cb22 * f_row[1] + cb32 * f_row[2]
            elif j == n - 1:
                b[-2] = -(cb11 * f_row[-1] + cb21 * f_row[-2] + cb31 * f_row[-3])
                b[-1] = -(cb12 * f_row[-1] + cb22 * f_row[-2] + cb32 * f_row[-3])
            else:
                idx = 2 * j
                b[idx] = c31 * (f_row[j+1] - f_row[j-1])
                b[idx+1] = c22 * (f_row[j-1] - 2 * f_row[j] + f_row[j+1])

        # Solve the system
        out = spsolve(A, b)
        df[i, :] = out[::2]
        d2f[i, :] = out[1::2]

    return df, d2f

def part2q2():
    """
    Part 2, question 2
    Add input/output as needed

    """

    from time import time

    # Initial variables
    n_values = list(range(10, 1001, 10)) # Use n = 10, 20, ..., 1000
    error_fd2 = []
    error_part2q1 = []
    runtime_fd2 = []
    runtime_part2q1 = []

    for n in n_values:
        # Generate f and df
        m = n  # Since m comparable to n
        x = np.linspace(0, 1, n)
        y = np.linspace(0, 1, m)
        X, Y = np.meshgrid(x, y)
        f = np.sin(X) * Y
        df = np.cos(X) * Y  # Exact derivative

        # Run fd2, store runtime and error
        start_time = time()
        df_fd2, _ = fd2(f)
        runtime_fd2.append(time() - start_time)
        error_fd2.append(np.max(df_fd2[:, 1:-1] - df[:, 1:-1]))

        # Run part2q1, store runtime and error
        start_time = time()
        df_part2q1, _ = part2q1(f, 1/(n-1))
        runtime_part2q1.append(time() - start_time)
        error_part2q1.append(np.max(df_part2q1[:, 1:-1] - df[:, 1:-1]))

    # Plot accuracy results
    plt.plot(n_values, np.array(error_part2q1), label="part2q1")
    plt.plot(n_values, np.array(error_fd2), label="fd2")
    plt.xlabel("n")
    plt.ylabel("Error")
    plt.title("Accuracy Comparison (First Derivative)")
    plt.legend()
    plt.show()

    # Plot runtime results
    plt.plot(n_values, np.array(runtime_part2q1), label="part2q1")
    plt.plot(n_values, np.array(runtime_fd2), label="fd2")
    plt.xlabel("n")
    plt.ylabel("Runtime")
    plt.title("Runtime Comparison")
    plt.legend()
    plt.show()

    return None #modify as needed

#---------------------------- End code for Part 2 ----------------------------#

if __name__=='__main__':
    x=0 #please do not remove
    #Add code here to call functions used to generate the figures included in your report.
    print(part1q1b())
    part1q1c()
    part1q2()
    part2q2()
