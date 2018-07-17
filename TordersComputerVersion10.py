#!/usr/bin/env python


#=================================================================================================
##The script imports the modules used in the script
#=================================================================================================

import sys
import xlrd
import xlwt
import numpy as np
import scipy.optimize
import scipy.misc
import scipy.special
import itertools




#=================================================================================================
##The script reads the excel sheet which lists the underlying forms on
##the first column, the corresponding candidates on the second column,
##and their violations starting on the fourth column. The third column
##can contain information concerning the winners, which is ignored by
##the script. The top row list constraint names. The second row can
##contain short constraint names, which are ignored by the script. Here
##is an example of the input excel sheet:

#                            M       F
#                            M       F
#  /t/      [t]    ...       0       0 
#           [d]              1       1 
#  /d/      [t]              1       0
#           [d]    ...       0       1

##Null constraint violations can be expressed with an empty cell rather
##than a zero (the script interprets as a zero any empty cell starting
##from the fourth column). The script assumes that the data appear in the
##first sheet of the input excel file.
#=================================================================================================

excel_fname = sys.argv[1]
excel_data = xlrd.open_workbook(excel_fname)
excel_data_sheet = excel_data.sheet_by_index(0)



#=================================================================================================
#=================================================================================================

only_HG_feasible_mappings = False
print_the_current_mapping = True
optimization_method = 'simplex' #If you are using scipy version 1.0, replace 'simplex' with 'interior-point'
bound = 20


 
#=================================================================================================
##The script builds the two dictionaries Gen and Con. The keys of Gen
##are the underlying forms. The corresponding value is the list of
##candidate surface forms for that underlying form. The keys of Con are
##pairs of an underlying form and a corresponding candidate surface
##form. The corresponding value is the list of constraint violations
##incurred by that mapping.
#=================================================================================================

n = excel_data_sheet.ncols - 3

Gen = {}
Con = {}

for row in range(2, excel_data_sheet.nrows):    
    if excel_data_sheet.cell_value(row, 0) != str() :
        current_underlying_form = str(excel_data_sheet.cell_value(row,0))
        if current_underlying_form not in Gen.keys():
            Gen[current_underlying_form] = []
    current_candidate = str(excel_data_sheet.cell_value(row,1))
    Gen[current_underlying_form] += [ current_candidate ]

    Con[(current_underlying_form, current_candidate)] = []
    for column in range(3, excel_data_sheet.ncols):
        if excel_data_sheet.cell_value(row, column) == str() :
            Con[(current_underlying_form, current_candidate)] += [ 0 ]
        else :
            Con[(current_underlying_form, current_candidate)] += [ excel_data_sheet.cell_value(row, column) ]
                    


#=================================================================================================
##The script builds the two dictionaries losers and
##violation_differences. The keys of losers are pairs of an underlying
##form and a corresponding candidate. The corresponding value is the
##list of candidates for that underlying form different from that
##surface form. The keys of violation_differences are pairs of an
##underlying form and a corresponding candidate. The corresponding value
##is the list of diference vectors for that mapping and the
##corresponding losers.
#=================================================================================================

losers = {}
violation_differences = {}
for x in Gen.keys():
    for y in Gen[x]:
        list_of_losers = [ ]
        matrix_of_violation_differences = [ ]
        for z in Gen[x] :
            if z != y :
                list_of_losers += [ z ]
                matrix_of_violation_differences += [ np.array(Con[(x, z)]) - np.array(Con[(x, y)]) ]                        
        losers[(x,y)] = list_of_losers
        violation_differences[(x, y)] = matrix_of_violation_differences



#=================================================================================================
##The script builds the dictionary D. The keys are the pairs (x,y) of an
##underlying form x and a corresponding surface candidate y. The
##corresponding value is a list called Matrix. This list Matrix has an
##entry for each lozer candidate z. And the entry of Matrix
##corresponding to z is a list of n numbers. The kth number of this list
##is +1, if constraint Ck is winner-preferring relative to the
##underlying/winner/loser form triplet (x, y, z); it is 0, if the
##constraint is even; it is -Omega-1, if the constraint is
##loser-preferring. Where Omega is the number of winner-preferring
##constraints relative to (x, y, z).
#=================================================================================================

D = {}
for x in Gen.keys():
    for y in Gen[x]:
        Matrix = [ ]
        for z in losers[(x,y)] :
            Omega = 0
            for k in range(n) :
                if Con[(x, z)][k] > Con[(x, y)][k] :
                    Omega += 1
            column = []
            for k in range(n) :
                if Con[(x, z)][k] > Con[(x, y)][k] :
                    column += [ +1 ]
                if Con[(x, z)][k] == Con[(x, y)][k] :
                    column += [ 0 ]
                if Con[(x, z)][k] < Con[(x, y)][k] :
                    column += [ -Omega-1 ]                
            Matrix += [ column ]
        D[(x, y)] = Matrix



#=================================================================================================
##The script builds the dictionary E. The keys are the pairs (x,y) of an
##underlying form x and a corresponding surface candidate y. The
##corresponding value is a list called Matrix. This list Matrix has an
##entry for each loser z. And the entry of Matrix corresponding to z is
##a list of n numbers. The kth number of this list is -1, if constraint
##Ck is loser-preferring relative to the underlying/winner/loser form
##triplet (x, y, z); it is 0, if the constraint is even; it is Lambda+1,
##if the constraint is winner-preferring. Where Lambda is the number of
##loser-preferring constraints relative to (x, y, z).
#=================================================================================================

E = {}
for x in Gen.keys():
    for y in Gen[x]:
        Matrix = []
        for z in losers[(x,y)] :
            Lambda = 0
            for k in range(n) :
                if Con[(x, z)][k] < Con[(x, y)][k] :
                    Lambda += 1
            column = []
            for k in range(n) :
                if Con[(x, z)][k] > Con[(x, y)][k] :
                    column += [ Lambda+1 ]
                if Con[(x, z)][k] == Con[(x, y)][k] :
                    column += [ 0 ]
                if Con[(x, z)][k] < Con[(x, y)][k] :
                    column += [ -1 ]
            Matrix += [ column ]
        E[(x, y)] = Matrix



#=================================================================================================
##This subroutine checks whether there exists a ranking whose
##corresponding OT grammar maps the underlying form x to the surface
##form y. This is done by checking that there exists a nonnegative
##weight vector w such that the matrix product of D[(x,y)] times w is a
##strictly positive vector, or equivalently a vector whose components
##are all larger than 1.
#=================================================================================================

def Is_this_an_OT_feasible_mapping(x,y) :   
    m = len(Gen[x]) - 1
    opt_res = scipy.optimize.linprog(c=np.zeros(n), A_ub=-np.array(D[(x,y)]), b_ub=-np.ones(m), bounds=(0, None), method=optimization_method)
    return opt_res.success



#=================================================================================================
##This subroutine checks whether there exists a nonnegative weight
##vector whose corresponding HG grammar maps the underlying form x to
##the surface form y. This is done by checking that there exists a
##nonnegative weight vector w such that the matrix product of
##violation_differences[(x,y)] times w is a strictly positive vector, or
##equivalently a vector whose components are all larger than 1.
#=================================================================================================

def Is_this_an_HG_feasible_mapping(x,y) :
    m = len(Gen[x]) - 1
    opt_res = scipy.optimize.linprog(c=np.zeros(n), A_ub=-np.array(violation_differences[(x,y)]), b_ub=-np.ones(m), bounds=(0, None), method=optimization_method)
    return opt_res.success



#=================================================================================================
#=================================================================================================

def Is_this_an_OT_Torder(x, y, x_hat, y_hat) :
    OT_condition = True
    if Is_this_an_OT_feasible_mapping(x,y) == True :
        m = len(Gen[x]) - 1
        m_hat = len(Gen[x_hat]) - 1
        for j in range(m_hat):
            opt_res = scipy.optimize.linprog(c=np.zeros(m), A_ub=np.transpose(D[(x,y)]), b_ub=E[(x_hat, y_hat)][j], bounds=(0, None), method=optimization_method)
            if opt_res.success == False :
                OT_condition = False
                break                                                                                        
    return OT_condition



#=================================================================================================
#=================================================================================================

def Does_this_satisfy_the_HG_nontrivial_necessary_and_sufficient_condition(x, y, x_hat, y_hat) :
    DO.write('- Does the HG non-trivial sufficient and necessary condition hold?\n')
    HG_nontrivial_condition = True
    list_of_lambdas = []
    m = len(losers[(x,y)])
    m_hat = len(losers[(x_hat, y_hat)])
    for j in range(m_hat):
        consequent_difference_vector = violation_differences[(x_hat, y_hat)][j]
        antecedent_violation_differences = violation_differences[(x,y)]
        opt_res = scipy.optimize.linprog(c=np.zeros(m), A_ub=np.transpose(antecedent_violation_differences), b_ub=consequent_difference_vector, bounds=(0, None), method=optimization_method)
        if opt_res.success == False :
            HG_nontrivial_condition = False
            z_hat = losers[(x_hat, y_hat)][j]
            DO.write('    NO, because the condition fails for instance for the consequent difference vector\n')
            DO.write('      C(' + str(x_hat) + ', ' + str(y_hat) + ', ' + str(z_hat) + ') = ' + str(consequent_difference_vector) + '\n') 
            DO.write('    as the antecedent difference vectors are as follows:\n')
            for i in range(m):
                z = losers[(x,y)][i]
                antecedent_difference_vector = violation_differences[(x, y)][i]
                DO.write('      C(' + str(x) + ', ' + str(y) + ', ' + str(z) + ') = ' + str(antecedent_difference_vector) + '\n')
            break
        else :
            list_of_lambdas += [ opt_res.x ]

    if HG_nontrivial_condition == True :
        DO.write('    YES, because the antecedent difference vectors are as follows:\n')
        for i in range(m): 
            z = losers[(x,y)][i]
            antecedent_difference_vector = violation_differences[(x, y)][i]
            DO.write('      C(' + str(x) + ', ' + str(y) + ', ' + str(z) + ') = ' + str(antecedent_difference_vector) + '\n')
        DO.write('    and therefore each consequent difference vector satisfies the condition for instance with lambdas as follows:\n')
        for j in range(m_hat): 
            z_hat = losers[(x_hat, y_hat)][j]
            consequent_difference_vector = violation_differences[(x_hat,y_hat)][j]
            lambdas = list_of_lambdas[j]
            DO.write('      (' + str(x_hat) + ', ' + str(y_hat) + ', ' + str(z_hat) + ') = ' + str(consequent_difference_vector) + ':   lambdas = ' + str(lambdas) + '\n')        

    return HG_nontrivial_condition

            

#=================================================================================================
#=================================================================================================

def Does_this_satisfy_the_ME_necessary_candidate_condition(x, y, x_hat, y_hat) :
    DO.write('- Does the ME necessary candidate condition hold?\n')
    m = len(Gen[x]) -1
    m_hat = len(Gen[x_hat]) -1
    if m >= m_hat :
        DO.write('    YES, because m_hat = ' + str(len(Gen[x_hat])-1) + ' and m = ' + str(len(Gen[x])-1) + ' and therefore m_hat <= m.\n')
        return True
    else:
        DO.write('    NO, because m_hat = ' + str(len(Gen[x_hat])-1) + ' and m = ' + str(len(Gen[x])-1) + ' and therefore m_hat not <= m.\n')
        return False
            


#=================================================================================================
#=================================================================================================

def Does_this_satisfy_the_ME_first_necessary_constraint_condition(x, y, x_hat, y_hat) :
    DO.write('- Does the ME first necessary constraint condition hold?\n')
    m = len(Gen[x]) -1
    m_hat = len(Gen[x_hat]) -1
    ant_sum_vector = np.zeros(n)
    cons_sum_vector = np.zeros(n)
    if m != m_hat :
        ME_first_necessary_constraint_condition = True
        DO.write('    YES, but vacuously, because m = ' + str(m) + ' is different from m_hat = ' + str(m_hat) + '.\n')
    else:
        for i in range(m) :
            ant_sum_vector += np.array(violation_differences[(x,y)][i])
        for j in range(m_hat) :
            cons_sum_vector += np.array(violation_differences[(x_hat, y_hat)][j])
        if np.amin(ant_sum_vector <= cons_sum_vector) == True :
            ME_first_necessary_constraint_condition = True
            DO.write('    YES, because m = m_hat = ' + str(m) + ' and the sum of the consequent difference vector is\n')
            DO.write('      ' + str(cons_sum_vector) + '\n')
            DO.write('    which is indeed larger than the sum of the antecedent difference vectors which is\n')
            DO.write('      ' + str(ant_sum_vector) + '\n')
        else :
            ME_first_necessary_constraint_condition = False
            DO.write('    NO, because m = m_hat = ' + str(m) + ' but the sum of the consequent difference vectors is\n')
            DO.write('      ' + str(cons_sum_vector) + '\n')
            DO.write('    which is not larger than the sum of the antecedent difference vectors which is\n')
            DO.write('      ' + str(ant_sum_vector) + '\n')
    return ME_first_necessary_constraint_condition            



#=================================================================================================
#=================================================================================================

def Does_this_satisfy_the_ME_second_necessary_constraint_condition(x, y, x_hat, y_hat) :
    DO.write('- Does the ME second necessary constraint condition hold?\n')
    ME_second_necessary_constraint_condition = True
    list_of_lambdas = []
    m = len(Gen[x]) - 1
    m_hat = len(Gen[x_hat]) - 1
    for j in range(m_hat) :
        consequent_difference_vector = violation_differences[(x_hat, y_hat)][j]
        opt_res = scipy.optimize.linprog(c=np.zeros(m), A_ub=np.transpose(violation_differences[(x,y)]), b_ub=consequent_difference_vector, A_eq=np.ones((1, m)), b_eq=np.ones(1), bounds=(0, None), method=optimization_method)
        if opt_res.success == False :
            ME_second_necessary_constraint_condition = False
            z_hat = losers[(x_hat, y_hat)][j]
            DO.write('    NO, because the condition fails for instance for the consequent difference vector\n')
            DO.write('      C(' + str(x_hat) + ', ' + str(y_hat) + ', ' + str(z_hat) + ') = ' + str(consequent_difference_vector) + '\n')
            DO.write('    as the antecedent difference vectors are as follows:\n')
            for i in range(m) :
                z = losers[(x,y)][i]
                antecedent_difference_vector = violation_differences[(x, y)][i]
                DO.write('      C(' + str(x) + ', ' + str(y) + ', ' + str(z) + ') = ' + str(antecedent_difference_vector) + '\n')
            break
        else :
            list_of_lambdas += [ opt_res.x ]
            
    if ME_second_necessary_constraint_condition == True :
        DO.write('    YES, because the antecedent difference vectors are as follows:\n')
        for i in range(m) :
            z = losers[(x,y)][i]
            antecedent_difference_vector = violation_differences[(x, y)][i]
            DO.write('      C(' + str(x) + ', ' + str(y) + ', ' + str(z) + ') = ' + str(antecedent_difference_vector) + '\n')
        DO.write('    and therefore each consequent difference vector satisfies the condition for instance with lambdas as follows:\n')
        for j in range(m_hat) :
            z_hat = losers[(x_hat, y_hat)][j]
            consequent_difference_vector = violation_differences[(x_hat, y_hat)][j]
            lambdas = list_of_lambdas[j]
            DO.write('      C(' + str(x_hat) + ', ' + str(y_hat) + ', ' + str(z_hat) + ') = ' + str(consequent_difference_vector) + ':   lambdas = ' + str(lambdas) + '\n')        
           
    return ME_second_necessary_constraint_condition
            


#=================================================================================================
#=================================================================================================

def Does_this_satisfy_the_ME_nontrivial_sufficient_condition(x, y, x_hat, y_hat) :
    DO.write('- Does the ME non-trivial sufficient condition hold?\n')
    m = len(Gen[x]) - 1
    m_hat = len(Gen[x_hat])-1
    counterexample = {}
    if (m_hat < bound) and (m - m_hat < bound) :
        for effective_set_of_antecedent_losers in itertools.combinations(range(m), m_hat):      #This subroutine is only called when m >= m_hat
            ME_nontrivial_sufficient_condition = True               
            dictionary_of_lambdas = {}
            for l in range(1, m_hat+1):
                M = int(scipy.special.binom(m_hat, l))
                                                        
                Asum = []
                Asum_dictionary = {}
                for I in itertools.combinations(effective_set_of_antecedent_losers, l) :
                    column = np.zeros(n)
                    for i in I :
                        column += np.array(violation_differences[(x, y)][i])
                    Asum += [ column ]
                    Asum_dictionary[I] = column
                    
                for J in itertools.combinations(range(m_hat), l) :
                    bsum = np.zeros(n)
                    for j in J :
                        bsum += np.array(violation_differences[(x_hat, y_hat)][j])

                    opt_res = scipy.optimize.linprog(c=np.zeros(M), A_ub=np.transpose(Asum), b_ub=bsum, A_eq=np.ones((1, M)), b_eq=np.ones(1), bounds=(0, 1), method=optimization_method)
                    if opt_res.success == False :
                        ME_nontrivial_sufficient_condition = False
                        counterexample[tuple(effective_set_of_antecedent_losers)] = [Asum_dictionary, J, bsum]
                        break
                    if opt_res.success == True :
                        dictionary_of_lambdas[J] = opt_res.x
                               
                if ME_nontrivial_sufficient_condition == False :
                    break
                
            if ME_nontrivial_sufficient_condition == True :
                break
                        
        if ME_nontrivial_sufficient_condition == True :
            list_of_effective_antecedent_losers = str()
            for i in effective_set_of_antecedent_losers:
                z = losers[(x, y)][i]
                list_of_effective_antecedent_losers += ', ' + str(z)

            DO.write('    YES, the condition holds relative to the set of m_hat = ' + str(m_hat) + ' antecedent losers [' + list_of_effective_antecedent_losers.lstrip(', ') +']:\n')
            for J in sorted(dictionary_of_lambdas.keys(), key=len):
                list_consequent_losers = str()
                bsum = np.zeros(n)
                for j in J:
                    bsum += np.array(violation_differences[(x_hat, y_hat)][j])
                    z_hat = losers[(x_hat, y_hat)][j]
                    list_consequent_losers += ', ' + str(z_hat)
                DO.write('      for the set of consequent losers [' + list_consequent_losers.lstrip(', ') + '] = ' + str(bsum) + ' it holds for instance with the following choice of lambdas:\n')
                l = len(J)
                K = 0
                for I in itertools.combinations(effective_set_of_antecedent_losers, l) :
                    column = np.zeros(n)
                    list_antecedent_losers = str()
                    for i in I :
                        column += np.array(violation_differences[(x, y)][i])
                        z = losers[(x,y)][i]
                        list_antecedent_losers += ', ' + str(z)
                    corresponding_lambda = dictionary_of_lambdas[J][K]
                    DO.write('        set of antecedent losers = [' + list_antecedent_losers.lstrip(', ') + '] = ' + str(column) + ': corresponding lambda = ' + str(corresponding_lambda) + '\n')
                    K += 1

        if ME_nontrivial_sufficient_condition == False :
            DO.write('    NO, in fact the condition fails:\n')
            for effective_set_of_antecedent_losers in counterexample.keys():
                list_of_effective_antecedent_losers = str()
                for i in effective_set_of_antecedent_losers:
                    z = losers[(x, y)][i]
                    list_of_effective_antecedent_losers += ', ' + str(z)
                list_of_consequent_losers = str()
                for j in counterexample[effective_set_of_antecedent_losers][1] :
                    z_hat = losers[(x_hat, y_hat)][j]
                    list_of_consequent_losers += ', ' + str(z_hat)
                DO.write('      * for the set of m_hat = ' + str(m_hat) + ' antecedent losers [' + list_of_effective_antecedent_losers.lstrip(', ') + ']\n')
                DO.write('        because the sum of the difference vectors corresponding to the l = ' + str(len(counterexample[effective_set_of_antecedent_losers][1])) + ' consequent losers [' + list_of_consequent_losers.lstrip(', ') + '] is\n')
                DO.write('          ' + str(counterexample[effective_set_of_antecedent_losers][2]) + '\n')
                DO.write('        while the sums over all sets of l = ' + str(len(counterexample[effective_set_of_antecedent_losers][1])) + ' antecedent difference vectors are as follows:\n')
                for I in counterexample[effective_set_of_antecedent_losers][0].keys():
                    current_list_of_antecedent_losers = str()
                    for i in I :
                        z = losers[(x, y)][i]
                        current_list_of_antecedent_losers += ', ' + str(z)
                    DO.write('          ' + current_list_of_antecedent_losers.lstrip(',') + ':   ' + str(counterexample[effective_set_of_antecedent_losers][0][I]) + '\n')
    else:
        ME_nontrivial_sufficient_condition = False
        
    return ME_nontrivial_sufficient_condition



#=================================================================================================
#=================================================================================================

def Does_this_satisfy_the_categorical_trivial_suficient_condition_without_rescaling(x, y, x_hat, y_hat) :
    
    DO.write('- Does the categorical trivial sufficient condition without rescaling hold?\n')
    
    categorical_trivial_sufficient_condition_without_rescaling = True
    list_of_matchings_without_rescaling = []
    m = len(losers[(x,y)])
    m_hat = len(losers[(x_hat, y_hat)])
    for j in range (m_hat):
        admits_a_matching_without_rescaling = False
        consequent_difference_vector = violation_differences[(x_hat, y_hat)][j]
        for i in range(m):
            antecedent_difference_vector = violation_differences[(x, y)][i]
            if np.amin(antecedent_difference_vector <= consequent_difference_vector) == True :
                admits_a_matching_without_rescaling = True
                list_of_matchings_without_rescaling += [(j, i)]
                break
                
        if admits_a_matching_without_rescaling == False :
            categorical_trivial_sufficient_condition_without_rescaling = False
            z_hat = losers[(x_hat, y_hat)][j]
            DO.write('    NO, because for instance the consequent difference vector\n')
            DO.write('      C(' + str(x_hat) + ', ' + str(y_hat) + ', ' + str(z_hat) + ') = ' + str(consequent_difference_vector) + '\n')    
            DO.write('    is not larger than any of the antecedent difference vectors, which are listed below:\n')
            for i in range(m):
                z = losers[(x,y)][i]
                antecedent_difference_vector = violation_differences[(x, y)][i]
                DO.write('      C(' + str(x) + ', ' + str(y) + ', ' + str(z) + ') = ' + str(antecedent_difference_vector) + '\n')
            break

    if categorical_trivial_sufficient_condition_without_rescaling == True :
        DO.write('    YES, because each consequent difference vector can be paired up with a\n')
        DO.write('    smaller antecedent difference vector (possibly with repetitions), for instance as follows:\n')
        for (j, i) in list_of_matchings_without_rescaling :
            antecedent_difference_vector = violation_differences[(x, y)][i]
            z = losers[(x,y)][i]
            consequent_difference_vector = violation_differences[(x_hat, y_hat)][j]
            z_hat = losers[(x_hat, y_hat)][j]
            DO.write('      consequent C(' + str(x_hat) + ', ' + str(y_hat) + ', ' + str(z_hat) + ') = ' + str(consequent_difference_vector) + ' >= antecedent C(' + str(x) + ', ' + str(y) + ', ' + str(z) + ') = ' + str(antecedent_difference_vector) + '\n')                                                    

    return categorical_trivial_sufficient_condition_without_rescaling



#=================================================================================================
#=================================================================================================

def Does_this_satisfy_the_categorical_trivial_suficient_condition_with_rescaling(x, y, x_hat, y_hat) :
    
    DO.write('- Does the categorical trivial sufficient condition with rescaling hold?\n')
    
    categorical_trivial_sufficient_condition_with_rescaling = True
    list_of_matchings_with_rescaling = []
    m = len(losers[(x,y)])
    m_hat = len(losers[(x_hat, y_hat)])
    for j in range (m_hat):
        admits_a_matching_with_rescaling = False
        consequent_difference_vector = violation_differences[(x_hat, y_hat)][j]
        for i in range(m):
            antecedent_difference_vector = violation_differences[(x, y)][i]
            opt_res = scipy.optimize.linprog(c=np.zeros(1), A_ub=np.transpose([antecedent_difference_vector]), b_ub=np.transpose(consequent_difference_vector), bounds=(0, None), method=optimization_method)            
            if opt_res.success == True :
                admits_a_matching_with_rescaling = True
                Lambda = opt_res.x
                list_of_matchings_with_rescaling += [(j, i, Lambda)]
                break
                
        if admits_a_matching_with_rescaling == False :
            categorical_trivial_sufficient_condition_with_rescaling = False
            z_hat = losers[(x_hat, y_hat)][j]
            DO.write('    NO, because for instance the consequent difference vector\n')
            DO.write('      C(' + str(x_hat) + ', ' + str(y_hat) + ', ' + str(z_hat) + ') = ' + str(consequent_difference_vector) + '\n')    
            DO.write('    is not larger than any rescaling of any of the antecedent difference vectors, which are listed below:\n')
            for i in range(m):
                z = losers[(x,y)][i]
                antecedent_difference_vector = violation_differences[(x, y)][i]
                DO.write('      C(' + str(x) + ', ' + str(y) + ', ' + str(z) + ') = ' + str(antecedent_difference_vector) + '\n')
            break

    if categorical_trivial_sufficient_condition_with_rescaling == True :
        DO.write('    YES, because each consequent difference vector can be paired up with a\n')
        DO.write('    smaller rescaled antecedent difference vector (possibly with repetitions), for instance as follows:\n')
        for (j, i, Lambda) in list_of_matchings_with_rescaling :
            antecedent_difference_vector = violation_differences[(x, y)][i]
            z = losers[(x,y)][i]
            consequent_difference_vector = violation_differences[(x_hat, y_hat)][j]
            z_hat = losers[(x_hat, y_hat)][j]
            DO.write('      consequent C(' + str(x_hat) + ', ' + str(y_hat) + ', ' + str(z_hat) + ') = ' + str(consequent_difference_vector) + ' >= antecedent C(' + str(x) + ', ' + str(y) + ', ' + str(z) + ') = ' + str(antecedent_difference_vector) + ' rescaled by ' + str(Lambda) + '\n')                                                    

    return categorical_trivial_sufficient_condition_with_rescaling



#=================================================================================================
#=================================================================================================

def Does_this_satisfy_the_ME_trivial_sufficient_condition(x, y, x_hat, y_hat) :
    DO.write('- Does the ME trivial sufficient condition hold?\n')
    
    list_of_antecedent_difference_vectors = violation_differences[(x, y)]
    m = len(list_of_antecedent_difference_vectors)

    list_of_consequent_difference_vectors = violation_differences[(x_hat, y_hat)]
    m_hat = len(list_of_consequent_difference_vectors)

    antecedent_difference_vectors_which_do_the_job = []
    for j in range(m_hat) :
        antecedent_difference_vectors_which_do_the_job += [ [] ]
        for i in range(m) :
            if min(np.greater_equal(list_of_consequent_difference_vectors[j], list_of_antecedent_difference_vectors[i])) == True:
                antecedent_difference_vectors_which_do_the_job[j] += [ i ]
        
    ME_trivial_sufficient_condition = False

    for choice_of_antecedents in itertools.product(*antecedent_difference_vectors_which_do_the_job):
        if len(set(choice_of_antecedents)) == m_hat :
            ME_trivial_sufficient_condition = True
            break

    if ME_trivial_sufficient_condition == True :
        DO.write('    YES, because each consequent difference vector can be paired up with a\n')
        DO.write('    smaller antecedent difference vector with no repetitions, for instance as follows:\n')
        for j in range(m_hat) :
            i = choice_of_antecedents[j]
            z = losers[(x,y)][i]
            z_hat = losers[(x_hat, y_hat)][j]
            consequent_difference_vector = violation_differences[(x_hat, y_hat)][j]
            antecedent_difference_vector = violation_differences[(x, y)][i]
            DO.write('      consequent C(' + str(x_hat) + ', ' + str(y_hat) + ', ' + str(z_hat) + ') = ' + str(consequent_difference_vector) + ' >= antecedent C(' + str(x) + ', ' + str(y) + ', ' + str(z) + ') = ' + str(antecedent_difference_vector) + '\n')                                                    
            
    if ME_trivial_sufficient_condition == False :
        DO.write('    NO, because it is not possible to pair up each consequent difference vector\n')
        DO.write('    with a smaller antecedent difference vector with no repetitions.\n')

    return ME_trivial_sufficient_condition



#=================================================================================================
#=================================================================================================

def Does_this_satisfy_the_first_corollary_of_the_ME_second_necessary_constraint_condition(x, y, x_hat, y_hat) :
    DO.write('- Does the first corollary of the ME second necessary constraint condition hold?\n')
    antecedent_bounds_consequent = True
    for constraint in range(n) :
        if Con[(x, y)][constraint] < Con[(x_hat, y_hat)][constraint] :
            antecedent_bounds_consequent = False
            constraint_name = str(excel_data_sheet.cell_value(0,3+constraint))
            DO.write('    NO, because for instance the constraint ' + constraint_name + '\n')
            DO.write('      assigns ' + str(Con[(x, y)][constraint]) + ' violations to the antecedent mapping\n')
            DO.write('      but it assigns ' + str(Con[(x_hat, y_hat)][constraint]) + ' violations to the consequent mapping\n')
            break
    if antecedent_bounds_consequent == True :
        DO.write('    YES\n')
    return antecedent_bounds_consequent



#=================================================================================================
#=================================================================================================

def Does_this_satisfy_the_second_corollary_of_the_ME_second_necessary_constraint_condition(x, y, x_hat, y_hat) :
    DO.write('- Does the second corollary of the ME second necessary constraint condition hold?\n')
    minimum = float('inf')
    antecedent_loser_which_achieves_minimum = str()
    for i in range(len(losers[(x,y)])) :
        if sum(violation_differences[(x, y)][i]) < minimum :
            minimum = sum(violation_differences[(x, y)][i])
            anteecdent_loser_which_achieves_minimum = losers[(x,y)][i]
    satisfies = True
    for j in range(len(losers[(x_hat,y_hat)])) :
        if sum(violation_differences[(x_hat, y_hat)][j]) < minimum :
            satisfies = False
            break
    if satisfies == False :
            counterexample_consequent_loser = losers[(x_hat,y_hat)][j]
            DO.write('    NO, because the condition fails for instance for the consequent loser ' + counterexample_consequent_loser + '\n')
            DO.write('      in fact, the sum of its violation differences is equal to ' + str(sum(violation_differences[(x_hat, y_hat)][j])) + '\n')
            DO.write('      while the sum of the violation differences of the antecedent loser ' + anteecdent_loser_which_achieves_minimum + ' is equal to ' + str(minimum) + '\n')
    if satisfies == True :
        DO.write('    YES\n')



#=================================================================================================
#=================================================================================================

def Finding_failing_ME_weights(x, y, x_hat, y_hat) :
    DO.write('- ME condition for counterexample weights:\n')
    m = len(Gen[x]) - 1
    m_hat = len(Gen[x_hat]) - 1
    b = np.ones(m)*(-np.log(m+1))
    for j in range(m_hat):
        Matrix = [ ]
        for i in range(m) :
            Matrix += [ np.array(violation_differences[(x_hat, y_hat)][j]) - np.array(violation_differences[(x, y)][i]) ]
        opt_res = scipy.optimize.linprog(c=np.zeros(n), A_ub=Matrix, b_ub=b, bounds=(0, None), method=optimization_method)
        if opt_res.success == True :
            z_hat = losers[(x_hat, y_hat)][j]
            DO.write('    for the consequent loser ' + str(z_hat) + ', it consists of the following inequalities:\n')
            for i in range(m) :
                z = losers[(x, y)][i]
                DO.write('      C(' + str(x_hat) + ', ' + str(y_hat) + ', ' + str(z_hat) + ') - C(' + str(x) + ', ' + str(y) + ', ' + str(z) + ') = ' + str(Matrix[i]) + 'w <= - ' + str(np.log(m+1)) + '\n')
            DO.write('      which is solved for instance by w =' + str(opt_res.x) + '\n')



#=================================================================================================
##This subroutine takes as input a 4-tuple (x, y, x_hat, y_hat). It
##checks whether the OT implication (x, y) -> (x_hat, y_hat) holds. If
##that is the case, it prints the implication on the file DO together
##with detailed information concerning the status of that implication.
##The subroutine returns five values:
##1) OT_feasibility: takes one of the two values True or False
##2) HG_feasibility: takes one of the two values True or False
##3) OT_Torder: takes one of the four values 'trivial without rescaling', 'trivial with rescaling', 'non-trivial', or 'no'
##4) HG_Torder: takes one of the two values True or False
##5) ME_Torder: takes one of the four values 'no', 'trivial', 'non-trivial', or 'undecided'
#=================================================================================================

def Analyze_and_display(x, y, x_hat, y_hat) :


    #Checks whether the current arrow (x, y) -> (x_hat, y_hat) qualifies as an OT T-order
    OT_feasibility = Is_this_an_OT_feasible_mapping(x,y)
    if ( OT_feasibility == False ) or ( Is_this_an_OT_Torder(x, y, x_hat, y_hat) == True ) :


        #Prints the T-order
        DO.write('\n')
        DO.write('(' + str(x) + ', ' + str(y) + ') -> (' + str(x_hat) + ', ' + str(y_hat) + ')\n')

        #Prints the difference vectors
        DO.write('- The antecedent difference vectors are the following:\n')
        for i in range(len(losers[(x, y)])) :
            DO.write('    C(' + str(x) + ', ' + str(y) + ', ' + str(losers[(x,y)][i]) + ') = ' + str(violation_differences[(x, y)][i]) + '\n')
        DO.write('  and the consequent difference vectors are the following:\n')
        for j in range(len(losers[(x_hat, y_hat)])) :
            DO.write('    C(' + str(x_hat) + ', ' + str(y_hat) + ', ' + str(losers[(x_hat, y_hat)][j]) + ') = ' + str(violation_differences[(x_hat, y_hat)][j]) + '\n')

        #Determines the OT and HG feasibility of the antecedent mapping
        DO.write('- Is the antecedent mapping feasible?\n')
        if OT_feasibility ==  True:
            HG_feasibility = True
            DO.write('    The antecedent mapping is OT feasible and therefore also HG feasible.\n')
        else:
            HG_feasibility = Is_this_an_HG_feasible_mapping(x,y)
            if HG_feasibility == True :
                DO.write('    The antecedent mapping is OT UNfeasible but HG feasible.\n')
            else :
                DO.write('    The antecedent mapping is HG UNfeasible and therefore also OT UNfeasible.\n')

        
        #Determines whether the current arrow satisfies the categorical trivial sufficient condition with or without rescaling    
        if Does_this_satisfy_the_categorical_trivial_suficient_condition_without_rescaling(x, y, x_hat, y_hat) == True :
            OT_Torder = 'trivial without rescaling'
        elif Does_this_satisfy_the_categorical_trivial_suficient_condition_with_rescaling(x, y, x_hat, y_hat) == True :
            OT_Torder = 'trivial with rescaling'
        else : 
            OT_Torder = 'non-trivial'


        #Determines whether the current arrow is an HG T-order
        if ( OT_Torder != 'non-trivial' ) & (HG_feasibility == False ) :
            DO.write('- This is an HG T-order because the triviality condition holds\n')
            DO.write('    and furthermore the antecedent mapping is HG unfeasible.\n')
            HG_Torder = True
            
        elif ( OT_Torder == 'non-trivial' ) & (HG_feasibility == False ) :
            DO.write('- This is an HG T-order because the antecedent mapping is HG unfeasible.\n')
            HG_Torder = True
            

        elif ( OT_Torder != 'non-trivial' ) & (HG_feasibility == True ) :
            DO.write('- This is an HG T-order because the triviality condition holds.\n')
            HG_Torder = True


        else:
            HG_Torder = Does_this_satisfy_the_HG_nontrivial_necessary_and_sufficient_condition(x, y, x_hat, y_hat)


        #Determines whether the current arrow satisfies the ME necessary condition
        if HG_Torder == False :
            ME_Torder = 'no'
        else: 
            ME_necessary_candidate_condition = Does_this_satisfy_the_ME_necessary_candidate_condition(x, y, x_hat, y_hat)
            ME_first_necessary_constraint_condition = Does_this_satisfy_the_ME_first_necessary_constraint_condition(x, y, x_hat, y_hat)
            if OT_Torder == 'trivial without rescaling' :
                ME_second_necessary_constraint_condition = True
                DO.write('- Does the ME second necessary constraint condition hold?\n')
                DO.write('    YES, because the categorical trivial sufficient condition without rescaling actually holds.\n')
            else :
                ME_second_necessary_constraint_condition = Does_this_satisfy_the_ME_second_necessary_constraint_condition(x, y, x_hat, y_hat)
            Does_this_satisfy_the_first_corollary_of_the_ME_second_necessary_constraint_condition(x, y, x_hat, y_hat)
            Does_this_satisfy_the_second_corollary_of_the_ME_second_necessary_constraint_condition(x, y, x_hat, y_hat)
            

            #Determines whetehr the current arrow satisfies the ME sufficient conditions
            if (ME_necessary_candidate_condition == False ) or ( ME_first_necessary_constraint_condition == False) or ( ME_second_necessary_constraint_condition == False ) :
                ME_Torder = 'no'

            elif Does_this_satisfy_the_ME_trivial_sufficient_condition(x, y, x_hat, y_hat) == True :
                ME_Torder = 'trivial'

            elif Does_this_satisfy_the_ME_nontrivial_sufficient_condition(x, y, x_hat, y_hat) == True:
                ME_Torder = 'non-trivial'
            else :
                ME_Torder = 'undecided'



            #Determines counterexample weights for the ME T-orders
            if ME_Torder == 'no' :
                Finding_failing_ME_weights(x, y, x_hat, y_hat)
            
                    
        DO.write('\n')
        DO.write('===========================================================================================================\n')
                            
    else:
        HG_feasibility = str()
        OT_Torder = 'no'
        HG_Torder = False
        ME_Torder = 'no'
                                                                                                                              
    return (OT_feasibility, HG_feasibility, OT_Torder, HG_Torder, ME_Torder)           
        

        
#=================================================================================================
#=================================================================================================

set_OT_Torders_with_OT_feasible_antecedent = set()
set_OT_Torders_with_OT_UNfeasible_but_HG_feasible_antecedent = set()
set_OT_Torders_with_HG_UNfeasible_antecedent = set()

case_descriptions = [ 'Case 1: OT trivial without rescaling, ME trivial:',
                      'Case 2: OT trivial without rescaling, ME non-trivial:',
                      'Case 3: OT trivial without rescaling, ME no:',
                      'Case 4: OT trivial without rescaling, ME undecided:',
                      'Case 5: OT trivial with rescaling, ME trivial:',
                      'Case 6: OT trivial with rescaling, ME non-trivial:',
                      'Case 7: OT trivial with rescaling, ME no:',
                      'Case 8: OT trivial with rescaling, ME undecided:',
                      'Case 9: OT non-trivial, HG yes, ME non-trivial:',
                      'Case 10: OT non-trivial, HG yes, ME no:',
                      'Case 11: OT non-trivial, HG yes, ME undecided:',
                      'Case 12: OT non-trivial, HG no:'                      ]

cases = [ set(), set(), set(), set(), set(), set(), set(), set(), set(), set(), set(), set() ]



                    
#=================================================================================================
#=================================================================================================

DO = open("DetailedOutput.txt","w+")

DO.write('===========================================================================================================\n')
DO.write('BEGINNING OF DETAILED LIST OF OT T-ORDERS\n')
DO.write('===========================================================================================================\n')

for x in Gen.keys():
    for y in Gen[x]:
        if (only_HG_feasible_mappings == False) or (Is_this_an_HG_feasible_mapping(x,y) == True) :
            for x_hat in Gen.keys():
                if x_hat != x :
                    for y_hat in Gen[x_hat]:
                        if (only_HG_feasible_mappings == False) or (Is_this_an_HG_feasible_mapping(x_hat,y_hat) == True) :
                            if print_the_current_mapping == True :
                                print str((x,y, x_hat, y_hat))
                            (OT_feasibility, HG_feasibility, OT_Torder, HG_Torder, ME_Torder) = Analyze_and_display(x, y, x_hat, y_hat)
                            
                            if OT_Torder != 'no' :
                                if OT_feasibility == True : 
                                    set_OT_Torders_with_OT_feasible_antecedent.add((x, y, x_hat, y_hat))
                                elif HG_feasibility == True:
                                    set_OT_Torders_with_OT_UNfeasible_but_HG_feasible_antecedent.add((x, y, x_hat, y_hat))
                                else:
                                    set_OT_Torders_with_HG_UNfeasible_antecedent.add((x, y, x_hat, y_hat))

                                if OT_Torder == 'trivial without rescaling' :
                                    if ME_Torder == 'trivial' :
                                        cases[0].add((x, y, x_hat, y_hat))
                                    elif  ME_Torder == 'non-trivial' :
                                        cases[1].add((x, y, x_hat, y_hat))
                                    elif ME_Torder == 'no' :
                                        cases[2].add((x, y, x_hat, y_hat))
                                    elif ME_Torder == 'undecided' :
                                        cases[3].add((x, y, x_hat, y_hat))

                                elif OT_Torder == 'trivial with rescaling' :
                                    if ME_Torder == 'trivial' :
                                        cases[4].add((x, y, x_hat, y_hat))
                                    elif  ME_Torder == 'non-trivial' :
                                        cases[5].add((x, y, x_hat, y_hat))
                                    elif ME_Torder == 'no' :
                                        cases[6].add((x, y, x_hat, y_hat))
                                    elif ME_Torder == 'undecided' :
                                        cases[7].add((x, y, x_hat, y_hat))
                                        
                                elif OT_Torder == 'non-trivial' :
                                    if HG_Torder == True :
                                        if ME_Torder == 'non-trivial' :
                                            cases[8].add((x, y, x_hat, y_hat))
                                        if ME_Torder == 'no' :
                                            cases[9].add((x, y, x_hat, y_hat))
                                        if ME_Torder == 'undecided' :
                                            cases[10].add((x, y, x_hat, y_hat))
                                    else :
                                        cases[11].add((x, y, x_hat, y_hat))
                                                    
DO.write('END OF DETAILED LIST OF OT T-ORDERS\n')
DO.write('===========================================================================================================\n')
DO.close()



#=================================================================================================
#=================================================================================================

CO = open("CoarseOutput.txt","w+")

CO.write('=============================================================================\n')
CO.write('BEGINNING OF COARSE OUTPUT\n')
CO.write('=============================================================================\n')

CO.write('\n')
CO.write('[A] There are ' + str(len(set_OT_Torders_with_OT_feasible_antecedent)) + ' T-orders with an OT feasible antecedent.\n')
CO.write('They are listed below, sorted into twelve cases:\n')

for index in range(12) :
    CO.write('\n')
    CO.write(' - ' + case_descriptions[index] + '\n')
    this_case_is_empty = True
    for T in cases[index] :
        if T in set_OT_Torders_with_OT_feasible_antecedent :
            this_case_is_empty = False
            x = T[0]
            y = T[1]
            x_hat = T[2]
            y_hat = T[3]
            CO.write('      (' + str(x) + ', ' + str(y) + ') -> (' + str(x_hat) + ', ' + str(y_hat) + ')' +'\n')
    if this_case_is_empty == True :
        CO.write('      none\n')

CO.write('\n')
CO.write('=============================================================================\n')
CO.write('\n')
CO.write('[B] There are ' + str(len(set_OT_Torders_with_OT_UNfeasible_but_HG_feasible_antecedent)) + ' T-orders with an OT unfeasible but HG feasible antecedent.\n')

if len(set_OT_Torders_with_OT_UNfeasible_but_HG_feasible_antecedent) == 0:
    CO.write('\n')
    
else:
    CO.write('They are listed below, sorted into twelve cases:\n')
    for index in range(12) :
        CO.write('\n')
        CO.write(' - ' + case_descriptions[index] + '\n')
        this_case_is_empty = True
        for T in cases[index] :
            if T in set_OT_Torders_with_OT_UNfeasible_but_HG_feasible_antecedent :
                this_case_is_empty = False
                x = T[0]
                y = T[1]
                x_hat = T[2]
                y_hat = T[3]
                CO.write('      (' + str(x) + ', ' + str(y) + ') -> (' + str(x_hat) + ', ' + str(y_hat) + ')\n')
        if this_case_is_empty == True :
            CO.write('      none\n')


CO.write('\n')
CO.write('=============================================================================\n')
CO.write('\n')
CO.write('[C] There are ' + str(len(set_OT_Torders_with_HG_UNfeasible_antecedent)) + ' T-orders with an HG unfeasible antecedent.\n')

if len(set_OT_Torders_with_HG_UNfeasible_antecedent) == 0:
    CO.write('\n')

else:
    CO.write('They are listed below, sorted into twelve cases:\n')
    for index in range(12) :
        CO.write('\n')
        CO.write(' - ' + case_descriptions[index] + '\n')
        this_case_is_empty = True
        for T in cases[index] :
            if T in set_OT_Torders_with_HG_UNfeasible_antecedent :
                this_case_is_empty = False
                x = T[0]
                y = T[1]
                x_hat = T[2]
                y_hat = T[3]
                CO.write('      (' + str(x) + ', ' + str(y) + ') -> (' + str(x_hat) + ', ' + str(y_hat) + ')\n')
        if this_case_is_empty == True :
            CO.write('      none\n')


CO.write('\n')
CO.write('=============================================================================\n')
CO.write('END OF COARSE OUTPUT\n')
CO.write('=============================================================================\n')

CO.close()



#=================================================================================================
#Produces the DOT file for the graph representing the OT T-order,
#namely the collection of implications which hold in OT AND have an OT
#feasible antecedent.
#=================================================================================================

##OT_GRAPH = open("OT_GRAPH.txt","w+")
##
##OT_GRAPH.write('digraph OT_GRAPH {\n')
##OT_GRAPH.write('node [shape=box];')
##for (x, y, x_hat, y_hat) in set_OT_Torders_with_OT_feasible_antecedent :
##    OT_GRAPH.write('"(' + str(x) + ',' + str(y) + ')" -> "(' + str(x_hat) + ',' + str(y_hat) + ')";\n') 
##
##OT_GRAPH.write('}\n')
##OT_GRAPH.close()


##
##OT
##1) a graph with the OT T-order;
##
##2) a graph with the
##HG T-order;
##
##3) a graph with the ME T-order;
##
##4) a graph with the OT-HG
##difference T-order (namely the arrows which hold in OT but are lost in
##HG, as HG T-orders are a subset of OT T-orders);
##
##5) a graph with the
##HG-ME difference T-order (namely, the arrows which hold in HG but are
##lost in ME, as ME T-orders are a subset of HG T-orders);
##
##6) a graph
##with the OT-ME difference T-order (namely, the arrows which hold in OT
##but are lost in ME);
##
##7) a combo graph, with solid lines for the arrows
##that hold in OT, HG, and ME, dashed lines for the arrows which hold in
##OT and HG but not in ME, and dotted lines for the arrows which hold in
##OT but not in HG nor in ME.
##
