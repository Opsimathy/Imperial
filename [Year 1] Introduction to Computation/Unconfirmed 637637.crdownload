import numpy as np
import numpy.testing as npt
import csv
# from plotchecker import LinePlotChecker
usernamefile = open('usernames.csv', 'r')
usernames = list(csv.reader(usernamefile))[0]
usernamefile.close()
print("Autograder loaded successfully!")
print("Remember to always restart and run all from the Kernel menu before submitting!")

def question0(_globals):
    score = 0
    myusernamefile = open('my_username.txt', 'r')
    my_username = myusernamefile.read().strip().replace('\'','').replace('\"','')
    myusernamefile.close()
    try:
        assert(not(my_username == 'Delete this text, and insert your short form user name'))
    except:
        print('You don\'t seem to have changed the contents of the file.')
        print(f'\n0 out of 5 marks')
        return 0
    else:
        print('You\'ve changed the contents of the file; thank you!')
        score += 1
    try:
        assert(my_username in usernames)
    except:
        print('Unfortunately, your username has not been recognised; contact Phil or Sam.')
        pass
    else:
        print('Your username has been recognised; thank you!')
        score += 4
    print(f'\n{score} out of 5 marks')
    return score
def question1_b(x):
    try:
        npt.assert_approx_equal(x,2.2358803986710964)
    except:
        print("Question 1 (b) failed!! Solution incorrect")
        return 0
    else:
        print("Question 1 (b) passed!!")
        return 1
        
def question1_c(x):
    try:
        npt.assert_approx_equal(x,0.5648793473910495)
    except:
        print("Question 1 (c) failed!! Solution incorrect")
        return 0
    else:
        print("Question 1 (c) passed!!")
        return 1
        
def question1_d(x):
    try:
        npt.assert_equal(x,93326215443944152681699238856266700490715968264381621468592963895217599993229915608941463976156518286253697920827223758251185210916864000000000000000000000000)
    except:
        print("Question 1 (d) failed!! Solution incorrect")
        return 0
    else:
        print("Question 1 (d) passed!!")
        return 1
        
def question1_e(x):
    try:
        assert(x == 6765)
    except:
        print("Question 1 (e) failed!! Solution incorrect")
        return 0
    else:
        print("Question 1 (e) passed!!")
        return 1
        
def question1_f(x1, x2, x3):
    score = 0
    number_of_tests = 3
    try:
        npt.assert_approx_equal(x1, 3.189184782277596)
    except:
        print("Total 1 is incorrect!!")
    else:
        print("Total 1 is correct!!")
        score += 1 
        
    try:
        npt.assert_approx_equal(x2, 3.1415922987403384)
    except:
        print("Total 2 is incorrect!!")
    else:
        print("Total 2 is correct!!")
        score += 1 
        
    try:
        npt.assert_approx_equal(x3, 3.141592653595635)
    except:
        print("Total 3 is incorrect!!")
    else:
        print("Total 3 is correct!!")
        score += 1 
        
    print(f'{score} out of {number_of_tests} tests passed')
    if score > 0:
        return score
    else: 
        raise AssertionError('All tests failed!!') 

        
def question2a(x):
    t = [1.0, 0.3535533905932738, 2.041077998578922e-17, -0.17677669529663687, -0.2, -0.11785113019775795, -2.6242431410300424e-17, 0.08838834764831842, 0.1111111111111111, 0.07071067811865477, 2.783288179880348e-17, -0.05892556509887889, -0.07692307692307693, -0.050507627227610506, -2.857509198010491e-17, 0.04419417382415916, 0.058823529411764705]
    try:
        npt.assert_array_almost_equal(x, t)
    except:
        print("Question 2(a) is incorrect!!")
        return 0
    else:
        print("Question 2(a) is correct!!")
        return 1
        
        
# def question2a_plot(_globals):
#     t = [[1.0, 0.3535533905932738, 2.041077998578922e-17, -0.17677669529663687, -0.2, -0.11785113019775795, -2.6242431410300424e-17, 0.08838834764831842, 0.1111111111111111, 0.07071067811865477, 2.783288179880348e-17, -0.05892556509887889, -0.07692307692307693, -0.050507627227610506, -2.857509198010491e-17, 0.04419417382415916, 0.058823529411764705]]
#     x = np.arange(17).reshape(1, 17)
#     pc = LinePlotChecker(_globals["ax"])
#     try:
#         pc.assert_x_data_allclose(x)
#     except:
#         score = 0
#         print('Incorrect horizontal coordinates')
#     else:
#         score = 1
#         print('Correct horizontal coordinates')
#     try:
#         pc.assert_y_data_allclose(t)
#     except:
#         score = 0
#         print('Incorrect vertical coordinates')
#     else:
#         score *= 1
#         print('Correct vertical coordinates')
#     try:
#         pc.assert_markers_equal(['.'])
#     except:
#         score = 0
#         print('This does not seem to be a point plot')
#     else:
#         score *= 1
#         print('This seems to be a point plot')
#     if score==1:
#         print('Plot correct!!')
#     else:
#         print('Plot incorrect!!')
#     return score

        
def question2b(x):
    t = [5.0, 1.6666666666666667, 2.5, 2.142857142857143, 2.2727272727272725, 2.2222222222222223, 2.2413793103448274, 2.2340425531914896, 2.236842105263158, 2.235772357723577, 2.2361809045226133]
    try:
        npt.assert_array_almost_equal(x, t)
    except:
        print("Question 2(b) is incorrect!!")
        return 0
    else:
        print("Question 2(b) is correct!!")
        return 1
        
        
# def question2b_plot(_globals):
#     t = [[5.0, 1.6666666666666667, 2.5, 2.142857142857143, 2.2727272727272725, 2.2222222222222223, 2.2413793103448274, 2.2340425531914896, 2.236842105263158, 2.235772357723577, 2.2361809045226133]]
#     x = np.arange(11).reshape(1, 11)
#     pc = LinePlotChecker(_globals["ax"])
#     try:
#         pc.assert_x_data_allclose(x)
#     except:
#         score = 0
#         print('Incorrect horizontal coordinates')
#     else:
#         score = 1
#         print('Correct horizontal coordinates')
#     try:
#         pc.assert_y_data_allclose(t)
#     except:
#         score = 0
#         print('Incorrect vertical coordinates')
#     else:
#         score *= 1
#         print('Correct vertical coordinates')
#     try:
#         pc.assert_markers_equal([''])
#     except:
#         score = 0
#         print('This does not seem to be a line plot')
#     else:
#         score *= 1
#         print('This seems to be a line plot')
#     if score==1:
#         print('Plot correct!!')
#     else:
#         print('Plot incorrect!!')
#     return score  
    
    
def question2c(x):
    t = [0.0, 1.0, 0.36787944117144233, 0.6922006275553464, 0.5004735005636368, 0.6062435350855974, 0.545395785975027, 0.5796123355033789, 0.5601154613610891, 0.571143115080177, 0.5648793473910495]
    try:
        npt.assert_array_almost_equal(x, t)
    except:
        print("Question 2(c) is incorrect!!")
        return 0
    else:
        print("Question 2(c) is correct!!")
        return 1
        
        
def question2d(x):
    t = [1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597, 2584, 4181, 6765, 10946, 17711, 28657, 46368, 75025, 121393, 196418, 317811, 514229, 832040, 1346269, 2178309, 3524578, 5702887, 9227465, 14930352, 24157817, 39088169, 63245986, 102334155, 165580141, 267914296, 433494437, 701408733, 1134903170, 1836311903, 2971215073, 4807526976, 7778742049, 12586269025]
    try:
        npt.assert_array_almost_equal(x, t)
    except:
        print("Question 2(d) is incorrect!!")
        return 0
    else:
        print("Question 2(d) is correct!!")
        return 1
        
def question2e_i(x):
    t = [4.0, 2.666666666666667, 3.466666666666667, 2.8952380952380956, 3.3396825396825403, 2.9760461760461765, 3.2837384837384844, 3.017071817071818, 3.2523659347188767, 3.0418396189294032, 3.232315809405594, 3.058402765927333, 3.2184027659273333, 3.0702546177791854, 3.208185652261944, 3.079153394197428, 3.200365515409549, 3.0860798011238346, 3.1941879092319425, 3.09162380666784, 3.189184782277596]
    try:
        npt.assert_array_almost_equal(x, t)
    except:
        print("Question 2(e-i) is incorrect!!")
        return 0
    else:
        print("Question 2(e-i) is correct!!")
        return 1
        
def question2e_ii(x):
    t = [2.0, 2.6666666666666665, 2.933333333333333, 3.0476190476190474, 3.098412698412698, 3.121500721500721, 3.132156732156732, 3.1371295371295367, 3.1394696806461506, 3.140578169680336, 3.141106021601377, 3.1413584725201353, 3.1414796489611394, 3.1415379931734746, 3.1415661593449467, 3.1415797881375944, 3.1415863960370602, 3.141589605588229, 3.1415911669915006, 3.1415919276751456, 3.1415922987403384]
    try:
        npt.assert_array_almost_equal(x, t)
    except:
        print("Question 2(e-ii) is incorrect!!")
        return 0
    else:
        print("Question 2(e-ii) is correct!!")
        return 1
        
def question2e_iii(x):
    t = [3.4641016151377544, 3.0792014356780038, 3.156181471569954, 3.13785289159568, 3.1426047456630846, 3.141308785462883, 3.1416743126988376, 3.141568715941784, 3.141599773811506, 3.14159051093808, 3.1415933045030817, 3.1415924542876463, 3.14159271502038, 3.141592634547314, 3.141592659521714, 3.1415926517339976, 3.1415926541725754, 3.1415926534061653, 3.1415926536478262, 3.1415926535714034, 3.141592653595635]
    try:
        npt.assert_array_almost_equal(x, t)
    except:
        print("Question 2(e-iii) is incorrect!!")
        return 0
    else:
        print("Question 2(e-iii) is correct!!")
        return 1
        
# def question2e_plot(_globals):
#     t1 = [4.0, 2.666666666666667, 3.466666666666667, 2.8952380952380956, 3.3396825396825403, 2.9760461760461765, 3.2837384837384844, 3.017071817071818, 3.2523659347188767, 3.0418396189294032, 3.232315809405594, 3.058402765927333, 3.2184027659273333, 3.0702546177791854, 3.208185652261944, 3.079153394197428, 3.200365515409549, 3.0860798011238346, 3.1941879092319425, 3.09162380666784, 3.189184782277596]
#     t2 = [2.0, 2.6666666666666665, 2.933333333333333, 3.0476190476190474, 3.098412698412698, 3.121500721500721, 3.132156732156732, 3.1371295371295367, 3.1394696806461506, 3.140578169680336, 3.141106021601377, 3.1413584725201353, 3.1414796489611394, 3.1415379931734746, 3.1415661593449467, 3.1415797881375944, 3.1415863960370602, 3.141589605588229, 3.1415911669915006, 3.1415919276751456, 3.1415922987403384]
#     t3 = [3.4641016151377544, 3.0792014356780038, 3.156181471569954, 3.13785289159568, 3.1426047456630846, 3.141308785462883, 3.1416743126988376, 3.141568715941784, 3.141599773811506, 3.14159051093808, 3.1415933045030817, 3.1415924542876463, 3.14159271502038, 3.141592634547314, 3.141592659521714, 3.1415926517339976, 3.1415926541725754, 3.1415926534061653, 3.1415926536478262, 3.1415926535714034, 3.141592653595635]
#     t = [t1, t2, t3]
#     x = np.asarray([np.arange(21), np.arange(21), np.arange(21)])#
#     pc = LinePlotChecker(_globals["ax"])
#     try:
#         pc.assert_x_data_allclose(x)
#     except:
#         score = 0
#         print('Incorrect horizontal coordinates')
#     else:
#         score = 1
#         print('Correct horizontal coordinates')
#     try:
#         pc.assert_y_data_allclose(t)
#     except:
#         score = 0
#         print('Incorrect vertical coordinates')
#     else:
#         score *= 1
#         print('Correct vertical coordinates')
#     try:
#         pc.assert_markers_equal(['','',''])
#     except:
#         score = 0
#         print('This does not seem to be a line plot')
#     else:
#         score *= 1
#         print('This seems to be a line plot')
#     if score==1:
#         print('Plot correct!!')
#     else:
#         print('Plot incorrect!!')
#     return score  
    
def question3_a(x):
    try:
        npt.assert_almost_equal(x, 2.236067843544479)
    except:
        print("Question 3 (a) failed!! Solution incorrect")
        return 0
    else:
        print("Question 3 (a) passed!!")
        return 1
        
def question3_b(x):
    try:
        npt.assert_almost_equal(x, 0.5671430308342419)
    except:
        print("Question 3 (b) failed!! Solution incorrect")
        return 0
    else:
        print("Question 3 (b) passed!!")
        return 1

        
def question3_c(x):
    t = [5.0, 1.6666666666666667, 2.5, 2.142857142857143, 2.2727272727272725, 2.2222222222222223, 2.2413793103448274, 2.2340425531914896, 2.236842105263158, 2.235772357723577, 2.2361809045226133, 2.2360248447204967, 2.236084452975048, 2.2360616844602608, 2.2360703812316713, 2.236067059356593, 2.236068328199384, 2.236067843544479]
    try:
        npt.assert_array_almost_equal(x, t)
    except:
        print("Question 3(c) is incorrect!!")
        return 0
    else:
        print("Question 3(c) is correct!!")
        return 1
        
def question3_d(x):
    t = [0.0, 1.0, 0.36787944117144233, 0.6922006275553464, 0.5004735005636368, 0.6062435350855974, 0.545395785975027, 0.5796123355033789, 0.5601154613610891, 0.571143115080177, 0.5648793473910495, 0.5684287250290607, 0.5664147331468833, 0.5675566373282834, 0.5669089119214953, 0.5672762321755696, 0.5670678983907884, 0.567186050099357, 0.5671190400572149, 0.5671570440012975, 0.5671354902062784, 0.5671477142601192, 0.567140781458298, 0.56714471334657, 0.5671424834013071, 0.5671437480994115, 0.5671430308342419]
    try:
        npt.assert_array_almost_equal(x, t)
    except:
        print("Question 3(d) is incorrect!!")
        return 0
    else:
        print("Question 3(d) is correct!!")
        return 1
        
def question3_e(x):
    try:
        assert(x == 37)
    except:
        print("Question 3(e) is incorrect!!")
        return 0
    else:
        print("Question 3(e) is correct!!")
        return 1
        
def question3_f(n1, n2, n3):
    score = 0
    number_of_tests = 3
    try: 
        assert(n1 == 100000)
    except:
        print("Value for n1 is incorrect!")
    else:
        print("Value for n1 is correct!!")
        score += 1
    try: 
        assert(n2 == 16)
    except:
        print("Value for n2 is incorrect!")
    else:
        print("Value for n2 is correct!!")
        score += 1
    try: 
        assert(n3 == 8)
    except:
        print("Value for n3 is incorrect!")
    else:
        print("Value for n3 is correct!!")
        score += 1
        
    print(f'{score} out of {number_of_tests} tests passed')
    if score > 0:
        return score
    else: 
        raise AssertionError('All tests failed!!') 

def question3_g(digits):
    score = 0
    number_of_tests = 3
    try:
        assert(isinstance(digits, list))
    except:
        print('Your digits don\'t seem to form a list.\n')
    else:
        print('Your digits form a list.\n')
        score += 1
    try:
        assert(digits == [1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1] or digits == [1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1])
    except:
        print('Your list does not contain the correct values.\n')
    else:
        print('Your list contains the correct values.\n')
        score += 1
    try: 
        assert(digits == [1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1])
    except:
        print('Your list seems to be in reverse order.\n')
    else:
        print('Your list is in the right order.\n')
        score += 1
    print(f'{score} out of {number_of_tests} tests passed')
    if score > 0:
        return score
    else: 
        raise AssertionError('All tests failed!!') 

def question3_h(digits):
    score = 0
    number_of_tests = 3
    try:
        assert(isinstance(digits, list))
    except:
        print('Your digits don\'t seem to form a list.\n')
    else:
        print('Your digits form a list.\n')
        score += 1
    try:
        assert(digits == [1, 1, 0, 1, 0, 0, 0, 1, 1, 0] or digits == [0, 1, 1, 0, 0, 0, 1, 0, 1, 1])
    except:
        print('Your list does not contain the correct values.\n')
    else:
        print('Your list contains the correct values.\n')
        score += 1
    try: 
        assert(digits == [1, 1, 0, 1, 0, 0, 0, 1, 1, 0])
    except:
        if digits == [0, 1, 1, 0, 0, 0, 1, 0, 1, 1]:
            print('Your list seems to be in reverse order.\n')
    else:
        print('Your list is in the right order.\n')
        score += 1
    print(f'{score} out of {number_of_tests} tests passed')
    if score > 0:
        return score
    else: 
        raise AssertionError('All tests failed!!')         

def testPyTriple(_globals,n,exists=True):
    pt = _globals["pyTriple"](n)
    if exists:
        a, b, c, product = pt
        return (a>0 and b>0 and a**2 + b**2 == c**2 and a*b*c == product)
    else:
        return (pt == 'No pythagorean triple satisfies that total')
        
def question4(_globals, test0, test1, test2):
    score = 0
    number_of_tests = 3
    try:
        assert(testPyTriple(_globals, test0[0], test0[1]))
    except:
        print(f'Function does not work correctly for n = {test0[0]}')
    else:
        print(f'Function works correctly for n = {test0[0]}')
        score += 1
    try:
        assert(testPyTriple(_globals, test1[0], test1[1]))
    except:
        print(f'Function does not work correctly for n = {test1[0]}')
    else:
        print(f'Function works correctly for n = {test1[0]}')
        score += 1
    try:
        assert(testPyTriple(_globals, test2[0], test2[1]))
    except:
        print(f'Function does not work correctly for n = {test2[0]}')
    else:
        print(f'Function works correctly for n = {test2[0]}')
        score += 1
    
    print(f'{score} out of {number_of_tests} tests passed')
    if score > 0:
        return score
    else: 
        raise AssertionError('All tests failed!!') 

import time        
def question4_timed(_globals,x,exists=True):
    start      = time.time()
    time_limit = 15
    score = 0
    number_of_tests = 2
    try:
        assert(testPyTriple(_globals, x[0], x[1]))
    except:
        print(f'Function does not work correctly for n = {x[0]}')
    else:
        print(f'Function works correctly for n = {x[0]}') 
        score += 1
    try:
        assert(abs(time.time() - start) < time_limit)
    except:
        print(f'Function does not seem to execute quickly for n = {x[0]}; can you make it more efficient?')
    else:
        print(f'Function executes quickly for n = {x[0]}')
        score += 1
    return score
