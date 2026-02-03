""" 
    Your college id here: 02216531
    Template code for project 1, contains 7 functions:
    func2A, func2B, func2C, method1, method2: complete functions for part 1
    part1_test: function to be completed for part 1
    part2: function to be completed for question 2
"""


#----------------- Code for Part 1 -----------------#
def func2A(L,R):
    """
    Called by func2B
    """
    M = [] 
    indL,indR = 0,0
    nL,nR = len(L),len(R)

    for i in range(nL+nR):
        if L[indL][1]<R[indR][1]:
            M.append(L[indL])
            indL = indL + 1
            if indL>=nL:
                M.extend(R[indR:])
                break
        else:
            M.append(R[indR])
            indR = indR + 1
            if indR>=nR:
                M.extend(L[indL:])
                break
    return M

def func2B(X):
    """
    Called by method2
    """
    n = len(X)
    if n==1:
        return X
    else:
        L = func2B(X[:n//2])
        R = func2B(X[n//2:])
        return func2A(L,R)
    

def func2C(L,x):
    """
    Called by method2
    """
    istart = 0
    iend = len(L)-1

    while istart<=iend:
        imid = int(0.5*(istart+iend))
        if x==L[imid][1]:
            return L[imid][0]
        elif x < L[imid][1]:
            iend = imid-1
        else:
            istart = imid+1

    return -1000 


def method1(L,x):
    for ind,l in enumerate(L):
        if x==l:
            return ind        
    return -1000


def method2(L,x,flag=True):
    if flag:
        L2 = list(enumerate(L))
        Lnew = func2B(L2)
        return func2C(Lnew,x),Lnew
    else:
        return func2C(L,x)


def part1_test():  # Here I choose not to use inputs and outputs so as to avoid redundancy
    """Part 1, question 2: investigate trends in wall times of methods 1 and 2.
    Use the variables inputs and outputs if/as needed.
    You may import modules within this function as needed, please do not import
    modules elsewhere without permission.
    """
    #add code here

    def timing(method, L, X):  # A timing test (wall time) for a list L given and another list X for comparing
        from time import time
        start_time = time()  # Record the starting time
        if method == method1:
            for x in X:
                result = method(L, x)  # Proceed with all elements in X
        elif method == method2:
            result, Lnew = method(L, X[0], flag=True)  # Sort the list first and record the sorted list
            for x in X[1:]:  # Then proceed with flag=False to avoid sorting
                result = method(Lnew, x, flag=False)
        return time() - start_time  # Return the time taken

    def random_list(n):  # Generate a random list of length n between 0 and 10000
        from random import randint
        return [randint(0, 10000) for i in range(n)]

    import matplotlib.pyplot as plt  # Use matplotlib to plot

    # Different n and m values: n between 1 and 10000 with an interval of 500,
    # m between 1 and 1000 with an interval of 50
    n_values = list(range(1, 10001, 500))
    m_values = list(range(1, 1001, 50))

    # Plot 1: Fixed small m (10), varying n
    X = random_list(10)
    time_method1, time_method2 = [], []  # Lists for time taken by methods 1 and 2 respectively
    for n in n_values:
        L = random_list(n)
        time_method1.append(timing(method1, L, X))
        time_method2.append(timing(method2, L, X))
    plt.figure()
    plt.plot(n_values, time_method1, label="method1")
    plt.plot(n_values, time_method2, label="method2")
    plt.xlabel("n")
    plt.ylabel("Time")
    plt.title("Fixed small m (10), varying n")
    plt.legend()

    # Plot 2: Fixed large m (1000), varying n
    X = random_list(1000)
    time_method1, time_method2 = [], []
    for n in n_values:
        L = random_list(n)
        time_method1.append(timing(method1, L, X))
        time_method2.append(timing(method2, L, X))
    plt.figure()
    plt.plot(n_values, time_method1, label="method1")
    plt.plot(n_values, time_method2, label="method2")
    plt.xlabel("n")
    plt.ylabel("Time")
    plt.title("Fixed large m (1000), varying n")
    plt.legend()

    # Plot 3: Fixed small n (100), varying m
    L = random_list(100)
    time_method1, time_method2 = [], []
    for m in m_values:
        X = random_list(m)
        time_method1.append(timing(method1, L, X))
        time_method2.append(timing(method2, L, X))
    plt.figure()
    plt.plot(m_values, time_method1, label="method1")
    plt.plot(m_values, time_method2, label="method2")
    plt.xlabel("m")
    plt.ylabel("Time")
    plt.title("Fixed small n (100), varying m")
    plt.legend()

    # Plot 4: Fixed large n (10000), varying m
    L = random_list(10000)
    time_method1, time_method2 = [], []
    for m in m_values:
        X = random_list(m)
        time_method1.append(timing(method1, L, X))
        time_method2.append(timing(method2, L, X))
    plt.figure()
    plt.plot(m_values, time_method1, label="method1")
    plt.plot(m_values, time_method2, label="method2")
    plt.xlabel("m")
    plt.ylabel("Time")
    plt.title("Fixed large n (10000), varying m")
    plt.legend()

#----------------- End code for Part 1 -----------------#


#----------------- Code for Part 2 -----------------#

def part2(A1,A2,L):
    """Part 2: Complete function to find amino acid patterns in
    amino acid sequences, A1 and A2
    Input:
        A1,A2: Length-n strings corresponding to amino acid sequences
        L: List of l sub-lists. Each sub-list contains 2 length-m strings. Each string corresponds to an amino acid sequence
        sequence
    Output:
        F: List of lists containing locations of amino-acid sequence pairs in A1 and A2.
        F[i] should be a list of integers containing all locations in A1 and A2 at
        which the amino acid sequence pair stored in L[i] occur in the same place.
    """

    #use/modify the code below as needed
    n = len(A1) #A2 should be same length
    l = len(L)
    m = len(L[0][0])
    F = [[] for i in range(l)]

    for i in range(l):  # Iterate over all AA pairs in L
        for j in range(n-m+1):  # For each AA pair in L, iterate over all starting positions for A1 and A2 (from 0 to n-m)
            if A1[j:j+m] == L[i][0] and A2[j:j+m] == L[i][1]:  # If both A1 and A2 match
                F[i].append(j)  # Then append the index to F[i]
    return F

#----------------- End code for Part 2 -----------------#

# Test for Part 2



if __name__=='__main__':
    x=0 #please do not remove
    #Add code here to call part1_test and generate the figures included in your report.

    # Test for Part 1

    # part1_test()

    # Test for Part 2
    print(part2("afgabciiabcb", "feadefdsdefe", [["abc", "def"], ["afg", "fea"]]))  # The example given
    print(part2("aaaaa", "bbbbb", [["a", "b"], ["c", "d"]]))  # An example with no matches

    # For larger test we first write a function that generates a random string with elements between 'a' and 'i'
    def random_string(n):
        from random import choice
        return ''.join(choice('abcdefghi') for i in range(n))

    A1 = random_string(1000)  # A1 with length n = 1000
    A2 = random_string(1000)  # A2 with length n = 1000
    L = [[random_string(3), random_string(3)] for i in range(500)]  # L with m = 3 and l = 500

    print(part2(A1, A2, L))  # Test - surprisingly, there are very few (sometimes even no) matches!
