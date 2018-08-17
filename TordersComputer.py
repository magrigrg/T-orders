#!/usr/bin/env python


#=================================================================================================
##Improvements to make
#=================================================================================================

##1) single out the mappings which are consistent with every grammar, print them in green
##2) for both green and red mappings, give the used the option of whether to plot them or not
##3) if the graph is disconnected, give the option to print the different components on separate pages
##4) give the option to only plot the dotted lines (no solid lines) in the comparison graphs
##5) The LEGEND still says "arrows". Perhaps make that "lines" now that there are no arrows?
##6) The script still produces only pdfs. Could that be changed to png (optionally)?
##7) The script still appears to try to open windows for the results, which fails on my server. Could that feature be suppressed (optionally)?



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
import random
from graphviz import Digraph    #https://media.readthedocs.org/pdf/graphviz/latest/graphviz.pdf



#=================================================================================================
##The script reads the excel sheet which lists the underlying forms on
##the first column, the corresponding candidates on the second column,
##and their violations starting on the fourth column. The third column
##can contain information concerning the winners, which is ignored by
##the script. The top row list constraint names. The second row can
##contain short constraint names, which are ignored by the script. The
##underlying forms can be repeated on every row or just once. Here is
##an example of the input excel sheet:

#                            M       F
#                            M       F
#  /t/      [t]    ...       0       0 
#           [d]              1       1 
#  /d/      [t]              1       0
#  /d/      [d]    ...       0       1

##Null constraint violations can be expressed with an empty cell
##rather than a zero (the script interprets as a zero any empty cell
##starting from the fourth column). The script assumes that these data
##appear in the first sheet of the input excel file.
#=================================================================================================

excel_fname = sys.argv[1]
excel_data = xlrd.open_workbook(excel_fname)
excel_data_sheet = excel_data.sheet_by_index(0)



#=================================================================================================
#=================================================================================================

only_HG_feasible_mappings = False
print_the_current_enteilment = False
optimization_method = 'simplex'     #In some cases, it is better toreplace 'simplex' with 'interior-point'
bound_on_number_of_candidates_for_checking_ME_nontrivial_sufficient_condition = 10
number_of_trials_for_ME_random_counterexample = 10000
weight_bound_for_ME_random_counterexample = 20
omit_arrows_entailed_transitivity_in_plots = True

 
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
    DO.write('- Does the HG nontrivial sufficient and necessary condition hold?\n')
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
    DO.write('- Does the ME nontrivial sufficient condition hold?\n')
    m = len(Gen[x]) - 1
    m_hat = len(Gen[x_hat])-1
    counterexample = {}
    if (m_hat < bound_on_number_of_candidates_for_checking_ME_nontrivial_sufficient_condition) and (m - m_hat < bound_on_number_of_candidates_for_checking_ME_nontrivial_sufficient_condition) :
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
        DO.write('    Cannot tell, because there are too many candidates and it is therefore impossible to check the condition.\n')

        
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

def Finding_weights_which_violate_ME_second_necessary_constraint_condition(x, y, x_hat, y_hat) :
    DO.write('- Since the ME second necessary constraint conditon fails, here is the condition for counterexample weights:\n')
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
#=================================================================================================

def ME(x, y, weights) :

    weighted_sum_of_winner_violations = 0
    for k in range(n) :
        weighted_sum_of_winner_violations += Con[(x, y)][k] * weights[k]
    numerator = np.exp( - weighted_sum_of_winner_violations )

    denominator = 0
    for u in Gen[x]:
        weighted_sum_of_candidate_violations = 0
        for k in range(n) :
            weighted_sum_of_candidate_violations += Con[(x, u)][k] * weights[k]
        denominator += np.exp( - weighted_sum_of_candidate_violations )

    ME_probability = np.divide(numerator, denominator)

    return ME_probability



#=================================================================================================
#Checks the ME probability inequality by randomly sampling weights
#=================================================================================================

def Finding_ME_random_counterexample(x, y, x_hat, y_hat) :

    ME_random_counterexample_found = False
    for trial in range(number_of_trials_for_ME_random_counterexample):
        trial += 1
        weights = []
        for constraint in range(n) : 
            weights += [ random.uniform(0, weight_bound_for_ME_random_counterexample) ]
        if ME(x_hat, y_hat, weights) < ME(x, y, weights) :
            DO.write('- The following counterexampe weights have been found through random sampling:\n')
            DO.write('     ' + str(weights) + '\n')
            ME_random_counterexample_found = True
            break

    if ME_random_counterexample_found == False :
        DO.write('- No counterexample weights have been found by random sampling.\n')
    
    return ME_random_counterexample_found




#=================================================================================================
##This subroutine takes as input a 4-tuple (x, y, x_hat, y_hat). It
##checks whether the OT implication (x, y) -> (x_hat, y_hat) holds. If
##that is the case, it prints the implication on the file DO together
##with detailed information concerning the status of that implication.
##The subroutine returns five values:
##1) OT_feasibility: takes one of the two values True or False
##2) HG_feasibility: takes one of the two values True or False
##3) OT_Torder: takes one of the two values True or False
##4) HG_Torder: takes one of the five values 'yes trivially without rescaling', 'yes trivially with rescaling', 'yes', or 'no'
##5) ME_Torder: takes one of the five values 'yes trivially', 'yes nontrivially', 'no by principle', 'no by random counterexample', or 'undecided'
#=================================================================================================

def Analyze_and_display(x, y, x_hat, y_hat) :

    #Checks whether the current arrow (x, y) -> (x_hat, y_hat) is an OT T-order
    OT_feasibility = Is_this_an_OT_feasible_mapping(x,y)
    OT_Torder = Is_this_an_OT_Torder(x, y, x_hat, y_hat)
    if ( OT_feasibility == False ) or ( OT_Torder == True ) :

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

        #Determines the HG feasibility of the antecedent mapping
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
       
        #Determines whether the current arrow is an HG T-order:   
        if Does_this_satisfy_the_categorical_trivial_suficient_condition_without_rescaling(x, y, x_hat, y_hat) == True :
            HG_Torder = 'yes trivially without rescaling'
        elif Does_this_satisfy_the_categorical_trivial_suficient_condition_with_rescaling(x, y, x_hat, y_hat) == True :
            HG_Torder = 'yes trivially with rescaling'
        elif HG_feasibility == False :
            DO.write('- This is an HG T-order because the antecedent mapping is HG unfeasible.\n')
            HG_Torder = 'yes'
        elif Does_this_satisfy_the_HG_nontrivial_necessary_and_sufficient_condition(x, y, x_hat, y_hat) == True :
            HG_Torder = 'yes'
        else :
            HG_Torder = 'no'

        #If th current arrow is not an HG T-order, then it is not an ME T-order either
        if HG_Torder == 'no' :
            ME_Torder = 'no by principle'

        #Else, it determines whether the current arrow satisfies the ME necessary conditions
        else:
            #Determines whether the current arrow satisfies the ME necessary candidate condition
            ME_necessary_candidate_condition = Does_this_satisfy_the_ME_necessary_candidate_condition(x, y, x_hat, y_hat)

            #Determines whether the current arrow satisfies the ME first necessary constraint condition
            ME_first_necessary_constraint_condition = Does_this_satisfy_the_ME_first_necessary_constraint_condition(x, y, x_hat, y_hat)

            #Determines whether the current arrow satisfies the ME second necessary constraint condition
            if HG_Torder == 'yes trivially without rescaling' :
                ME_second_necessary_constraint_condition = True
                DO.write('- Does the ME second necessary constraint condition hold?\n')
                DO.write('    YES, because the categorical trivial sufficient condition without rescaling actually holds.\n')
            else :
                ME_second_necessary_constraint_condition = Does_this_satisfy_the_ME_second_necessary_constraint_condition(x, y, x_hat, y_hat)

            #Determines whether the current arrow satisfies the two corollaries of the ME second necessary constraint condition
            Does_this_satisfy_the_first_corollary_of_the_ME_second_necessary_constraint_condition(x, y, x_hat, y_hat)
            Does_this_satisfy_the_second_corollary_of_the_ME_second_necessary_constraint_condition(x, y, x_hat, y_hat)
            
            #If the ME second necessary constraint condition fails, determines counterexample weights
            if ME_second_necessary_constraint_condition == False :
                Finding_weights_which_violate_ME_second_necessary_constraint_condition(x, y, x_hat, y_hat)

            #If any of the necessary ME condition fails, the current arrow fails in ME
            if (ME_necessary_candidate_condition == False ) or ( ME_first_necessary_constraint_condition == False) or ( ME_second_necessary_constraint_condition == False ) :
                ME_Torder = 'no by principle'

            #Checks the trivial ME sufficient condition                
            elif Does_this_satisfy_the_ME_trivial_sufficient_condition(x, y, x_hat, y_hat) == True :
                ME_Torder = 'yes trivially'

            #Tries to find counterexample weights by sampling weights at random    
            elif Finding_ME_random_counterexample(x, y, x_hat, y_hat) == True :
                ME_Torder = 'no by random counterexample'

            #Checks the nontrivial ME sufficient condition
            elif Does_this_satisfy_the_ME_nontrivial_sufficient_condition(x, y, x_hat, y_hat) == True:
                ME_Torder = 'yes nontrivially'

            #Cannot resolve the ME status of the current arrow   
            else :
                ME_Torder = 'undecided'
            
                    
        DO.write('\n')
        DO.write('===========================================================================================================\n')
                            
    else:
        HG_feasibility = 'does not matter'
        OT_Torder = 'no'
        HG_Torder = 'no'
        ME_Torder = 'no'
                                                                                                                              
    return (OT_feasibility, HG_feasibility, OT_Torder, HG_Torder, ME_Torder)           
        

        
#=================================================================================================
#=================================================================================================

set_OT_Torders_with_OT_feasible_antecedent = set()
set_OT_Torders_with_OT_UNfeasible_but_HG_feasible_antecedent = set()
set_OT_Torders_with_HG_UNfeasible_antecedent = set()

case_descriptions = [ 'Case 1: HG trivial without rescaling, ME trivial:',
                      'Case 2: HG trivial without rescaling, ME nontrivial:',
                      'Case 3: HG trivial without rescaling, ME no by failure of necessary conditions:',
                      'Case 4: HG trivial without rescaling, ME no by random counterexample:',
                      'Case 5: HG trivial without rescaling, ME undecided:',
                      'Case 6: HG trivial with rescaling, ME trivial:',
                      'Case 7: HG trivial with rescaling, ME nontrivial:',
                      'Case 8: HG trivial with rescaling, ME no by failure of necessary conditions:',
                      'Case 9: HG trivial with rescaling, ME no by random counterexample:',
                      'Case 10: HG trivial with rescaling, ME undecided:',
                      'Case 11: HG nontrivial, ME nontrivial:',
                      'Case 12: HG nontrivial, ME no by failure of necessary conditions:',
                      'Case 13: HG nontrivial, ME no by random counterexample:',
                      'Case 14: HG nontrivial, ME undecided:',
                      'Case 15: HG no:'                      ]

cases = [ set(), set(), set(), set(), set(), set(), set(), set(), set(), set(), set(), set(), set(), set(), set() ]

                    
#=================================================================================================
#=================================================================================================

DO = open("[2]-Description_of_Torders.txt","w+")

DO.write('===========================================================================================================\n')
DO.write('BEGINNING OF FILE\n')
DO.write('===========================================================================================================\n')

for x in Gen.keys():
    for y in Gen[x]:
        if (only_HG_feasible_mappings == False) or (Is_this_an_HG_feasible_mapping(x,y) == True) :
            for x_hat in Gen.keys():
                for y_hat in Gen[x_hat]:
                    if (x, y) != (x_hat, y_hat) :
                        if print_the_current_enteilment == True :
                            print str((x,y, x_hat, y_hat))
                        (OT_feasibility, HG_feasibility, OT_Torder, HG_Torder, ME_Torder) = Analyze_and_display(x, y, x_hat, y_hat)
                        
                        if OT_Torder == True :
                            if OT_feasibility == True : 
                                set_OT_Torders_with_OT_feasible_antecedent.add((x, y, x_hat, y_hat))
                            elif HG_feasibility == True:
                                set_OT_Torders_with_OT_UNfeasible_but_HG_feasible_antecedent.add((x, y, x_hat, y_hat))
                            else:
                                set_OT_Torders_with_HG_UNfeasible_antecedent.add((x, y, x_hat, y_hat))

                            if HG_Torder == 'yes trivially without rescaling' :
                                if ME_Torder == 'yes trivially' :
                                    cases[0].add((x, y, x_hat, y_hat))
                                elif  ME_Torder == 'yes nontrivially' :
                                    cases[1].add((x, y, x_hat, y_hat))
                                elif ME_Torder == 'no by principle' :
                                    cases[2].add((x, y, x_hat, y_hat))
                                elif ME_Torder == 'no by random counterexample' :
                                    cases[3].add((x, y, x_hat, y_hat))
                                elif ME_Torder == 'undecided' :
                                    cases[4].add((x, y, x_hat, y_hat))

                            elif HG_Torder == 'yes trivially with rescaling' :
                                if ME_Torder == 'yes trivially' :
                                    cases[5].add((x, y, x_hat, y_hat))
                                elif  ME_Torder == 'yes nontrivially' :
                                    cases[6].add((x, y, x_hat, y_hat))
                                elif ME_Torder == 'no by principle' :
                                    cases[7].add((x, y, x_hat, y_hat))
                                elif ME_Torder == 'no by random counterexample' :
                                    cases[8].add((x, y, x_hat, y_hat))
                                elif ME_Torder == 'undecided' :
                                    cases[9].add((x, y, x_hat, y_hat))
                                    
                            elif HG_Torder == 'yes' :
                                if ME_Torder == 'yes nontrivially' :
                                    cases[10].add((x, y, x_hat, y_hat))
                                if ME_Torder == 'no by principle' :
                                    cases[11].add((x, y, x_hat, y_hat))
                                if ME_Torder == 'no by random counterexample' :
                                    cases[12].add((x, y, x_hat, y_hat))
                                if ME_Torder == 'undecided' :
                                    cases[13].add((x, y, x_hat, y_hat))
                                    
                            else :
                                cases[14].add((x, y, x_hat, y_hat))
                                                    
DO.write('END OF FILE\n')
DO.write('===========================================================================================================\n')
DO.close()



#=================================================================================================
#=================================================================================================

CO = open("[1]-List_of_Torders.txt","w+")

CO.write('=============================================================================\n')
CO.write('BEGINNING OF FILE\n')
CO.write('=============================================================================\n')

CO.write('\n')
CO.write('[A] There are ' + str(len(set_OT_Torders_with_OT_feasible_antecedent)) + ' T-orders with an OT feasible antecedent.\n')
CO.write('They are listed below, sorted into twelve cases:\n')

for index in range(15) :
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
    for index in range(15) :
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
    for index in range(15) :
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
CO.write('END OF FILE\n')
CO.write('=============================================================================\n')

CO.close()



#=================================================================================================
#=================================================================================================

set_of_HG_unfeasible_mappings = set()
for entailment in set_OT_Torders_with_HG_UNfeasible_antecedent :
    x = entailment[0]
    y = entailment[1]
    set_of_HG_unfeasible_mappings.add((x,y))

set_of_HG_feasible_but_OT_unfeasible_mappings = set()
for entailment in set_OT_Torders_with_OT_UNfeasible_but_HG_feasible_antecedent :
    x = entailment[0]
    y = entailment[1]
    set_of_HG_feasible_but_OT_unfeasible_mappings.add((x,y))



#=================================================================================================
#=================================================================================================

UNFEASIBLE = open("[3]-List_of_unfeasible_mappings.txt","w+")

UNFEASIBLE.write('=============================================================================\n')
UNFEASIBLE.write('BEGINNING OF FILE\n')
UNFEASIBLE.write('=============================================================================\n\n')

UNFEASIBLE.write('There are ' + str(len(set_of_HG_unfeasible_mappings)) + ' mappings which are unfeasible in HG.\n')
if set_of_HG_unfeasible_mappings != set() :
    UNFEASIBLE.write('They are listed below:\n')
    for (x, y) in set_of_HG_unfeasible_mappings :
        UNFEASIBLE.write('    (' + str(x) + ', ' + str(y) + ')\n')

UNFEASIBLE.write('\n=============================================================================\n\n')

UNFEASIBLE.write('The mappings above are also all unfeasible in OT.\n')
if set_of_HG_feasible_but_OT_unfeasible_mappings == set() :
    UNFEASIBLE.write('There are no additional mappings which are unfeasible in OT (but feasible in HG).\n')
else :
    UNFEASIBLE.write('Furthermore, there are ' + str(len(set_of_HG_feasible_but_OT_unfeasible_mappings)) + ' additional mappings which are unfeasible in OT (but feasible in HG).\n')
    UNFEASIBLE.write('They are listed below:\n')
    for (x, y) in set_of_HG_feasible_but_OT_unfeasible_mappings :
        UNFEASIBLE.write('    (' + str(x) + ', ' + str(y) + ')\n')
    
UNFEASIBLE.write('\n')
UNFEASIBLE.write('=============================================================================\n')
UNFEASIBLE.write('END OF FILE\n')
UNFEASIBLE.write('=============================================================================\n')
UNFEASIBLE.close()



###=================================================================================================
###Allows for a set of undecided entailments
###=================================================================================================
##
##def Produce_dot_file(set_of_entailments, set_of_undecided_entailments, file_name) :
##
##    set_of_mappings = set()
##    for (x, y, x_hat, y_hat) in set_of_entailments.union(set_of_undecided_entailments) :
##        set_of_mappings.add((x,y))
##        set_of_mappings.add((x_hat, y_hat))
##    
##    #constucts a set whose elements are lists of mappings which are equivalent according to set_of_entailments
##    #(while set_of_undecided_entailments is of course ignored in establishing equivalences)
##    set_of_lists_of_equivalent_mappings = set()
##    for (x, y) in set_of_mappings :
##        this_mapping_is_equivalent_to_a_list_already_in_the_set = False
##        for list_of_equivalent_mappings in set_of_lists_of_equivalent_mappings :
##            (x_hat, y_hat) = list_of_equivalent_mappings[0]
##            if ((x, y, x_hat, y_hat) in set_of_entailments) and ((x_hat, y_hat, x, y) in set_of_entailments) :
##                this_mapping_is_equivalent_to_a_list_already_in_the_set = True
##                set_of_lists_of_equivalent_mappings.remove(list_of_equivalent_mappings )
##                set_of_lists_of_equivalent_mappings.add(list_of_equivalent_mappings  + ((x, y),))
##                break
##        if this_mapping_is_equivalent_to_a_list_already_in_the_set == False :
##            set_of_lists_of_equivalent_mappings.add(((x, y),))
##    
##    #Computes entailments between lists of equivalent mappings
##    set_of_entailments_among_lists_of_equivalent_mappings = set()
##    for first_list_of_equivalent_mappings, second_list_of_equivalent_mappings in itertools.product(set_of_lists_of_equivalent_mappings, set_of_lists_of_equivalent_mappings) :
##        (x, y) = first_list_of_equivalent_mappings[0]
##        (x_hat, y_hat) = second_list_of_equivalent_mappings[0]
##        if (x, y, x_hat, y_hat) in set_of_entailments :     #This requires the two lists of equivalent mappings to be different lists
##            set_of_entailments_among_lists_of_equivalent_mappings.add((first_list_of_equivalent_mappings, second_list_of_equivalent_mappings))
##
##    #Removes entailments which are entailed by transitivity
##    if omit_arrows_entailed_transitivity_in_dot_files == True :
##        for first_list_of_equivalent_mappings, second_list_of_equivalent_mappings, third_list_of_equivalent_mappings in itertools.product(set_of_lists_of_equivalent_mappings, set_of_lists_of_equivalent_mappings, set_of_lists_of_equivalent_mappings) : 
##            if (first_list_of_equivalent_mappings, second_list_of_equivalent_mappings) in set_of_entailments_among_lists_of_equivalent_mappings :
##                if (second_list_of_equivalent_mappings, third_list_of_equivalent_mappings) in set_of_entailments_among_lists_of_equivalent_mappings :
##                    if (first_list_of_equivalent_mappings, third_list_of_equivalent_mappings) in set_of_entailments_among_lists_of_equivalent_mappings :
##                        set_of_entailments_among_lists_of_equivalent_mappings.remove(( first_list_of_equivalent_mappings,  third_list_of_equivalent_mappings))
##
##    #Computes undecided entailments between lists of equivalent mappings
##    set_of_undecided_entailments_among_lists_of_equivalent_mappings = set()
##    for first_list_of_equivalent_mappings, second_list_of_equivalent_mappings in itertools.product(set_of_lists_of_equivalent_mappings, set_of_lists_of_equivalent_mappings) :
##        (x, y) = first_list_of_equivalent_mappings[0]
##        (x_hat, y_hat) = second_list_of_equivalent_mappings[0]
##        if (x, y, x_hat, y_hat) in set_of_undecided_entailments :     #This requires the two lists of equivalent mappings to be different lists
##            set_of_undecided_entailments_among_lists_of_equivalent_mappings.add((first_list_of_equivalent_mappings, second_list_of_equivalent_mappings))
##
##    #Initializes the dot file
##    GRAPH = open(file_name+'.dot',"w+")
##    GRAPH.write('digraph ' + file_name + ' {\n')
##    GRAPH.write('    node [shape=box];\n')
##
##    #Writes the lines of the dot file corresponding to established entailments
##    for (antecedent, consequent) in set_of_entailments_among_lists_of_equivalent_mappings :
##        string_corresponding_to_antecedent = str()
##        for (x, y) in antecedent :
##            string_corresponding_to_antecedent += '(' + str(x) + ', ' + str(y) + '),\n'
##        string_corresponding_to_consequent = str()
##        for (x, y) in consequent :
##            string_corresponding_to_consequent += '(' + str(x) + ', ' + str(y) + '),\n'
##        GRAPH.write('    "' + string_corresponding_to_antecedent.rstrip(',\n') + '" -> "' + string_corresponding_to_consequent.rstrip(',\n') + '";\n') 
##
##    #Writes the lines of the dot file corresponding to undecided entailments
##    for (antecedent, consequent) in set_of_undecided_entailments_among_lists_of_equivalent_mappings :
##        string_corresponding_to_antecedent = str()
##        for (x, y) in antecedent :
##            string_corresponding_to_antecedent += '(' + str(x) + ', ' + str(y) + '),\n'
##        string_corresponding_to_consequent = str()
##        for (x, y) in consequent :
##            string_corresponding_to_consequent += '(' + str(x) + ', ' + str(y) + '),\n'
##        GRAPH.write('    "' + string_corresponding_to_antecedent.rstrip(',\n') + '" -> "' + string_corresponding_to_consequent.rstrip(',\n') + '" [style=dotted];\n') 
##
##    #Closes the dot file
##    GRAPH.write('}\n')
##    GRAPH.close()


#=================================================================================================
#=================================================================================================

def Convert_small_box_into_string(small_box) :
    string = str()
    for mapping in small_box :
        x = mapping[0]
        y = mapping[1]
        string += '(' + str(x) + ', ' + str(y) + '),\n'
    return string.rstrip(',\n')



#=================================================================================================
#=================================================================================================

def Convert_big_box_into_string(big_box) :
    string = str()
    for small_box in big_box :
        for mapping in small_box :
            x = mapping[0]
            y = mapping[1]
            string += '(' + str(x) + ', ' + str(y) + '), '
    return string.rstrip(', ')


#=================================================================================================
##Double arrows between two equivalent nodes must also be removed,
##because equivalence should be signaled by boxes, not by double
##arrows. As it is, this removes double arrows for boxes which contain
##at least three nodes. But it might not remove double arrows for
##boxes with only two nodes.
#=================================================================================================

def Remove_entailments_which_follow_by_transitivity(list_of_entailments) :
    list_of_entailments_which_follow_by_transitivity = []
    if omit_arrows_entailed_transitivity_in_plots == True :
        for (x, y) in list_of_entailments :
            for (u, v) in list_of_entailments :
                if y == u :
                    if (x, v) in list_of_entailments :
                        list_of_entailments_which_follow_by_transitivity.append((x, v))
    cleaned_list_of_entailments = []
    for entailment in list_of_entailments :
        if entailment not in list_of_entailments_which_follow_by_transitivity :
            cleaned_list_of_entailments.append(entailment)
    return cleaned_list_of_entailments



##=================================================================================================
##This will have to be gotten rid of and all (x, y, x_hat, y_hat) should be changed to ((x, y), (x_hat, y_hat))
##=================================================================================================

def Split(set_of_tuples_of_four_elements) :
    set_of_pairs_of_pairs = set()
    for (x, y, x_hat, y_hat) in set_of_tuples_of_four_elements :
        set_of_pairs_of_pairs.add( ((x,y), (x_hat, y_hat)) )
    return set_of_pairs_of_pairs          



#=================================================================================================
#Does not allow for a set of undecided entailments
#=================================================================================================

def Produce_graph(superset_of_entailments, subset_of_entailments, set_of_special_nodes, file_name, legend) :

    #Constructs the set of mappings which occur in superset_of_entailments
    set_of_mappings = set()
    for (antecedent_mapping, consequent_mapping) in superset_of_entailments :
        set_of_mappings.add(antecedent_mapping)
        set_of_mappings.add(consequent_mapping)
    
    #Constucts the list of small boxes, namely lists of mappings which are equivalent according to subset_of_entailments
    list_of_small_boxes = []
    for mapping in set_of_mappings :
        this_mapping_is_equivalent_to_a_box = False
        for small_box in list_of_small_boxes :
            other_mapping = small_box[0]
            if ((mapping, other_mapping) in subset_of_entailments) and ((other_mapping, mapping) in subset_of_entailments) :
                this_mapping_is_equivalent_to_a_box = True
                small_box.append(mapping)
                break
        if this_mapping_is_equivalent_to_a_box == False :
            list_of_small_boxes.append( [mapping] )
        
    #Constucts the list of big boxes, namely lists of two or more small boxes which are equivalent according to superset_of_entailments
    list_of_boxes = []
    for small_box in list_of_small_boxes :
        mapping = small_box[0]
        this_small_box_is_equivalent_to_a_box = False
        for box in list_of_boxes :
            other_mapping = box[0][0]
            if ((mapping, other_mapping) in superset_of_entailments) and ((other_mapping, mapping) in superset_of_entailments) :
                this_small_box_is_equivalent_to_a_box = True
                box.append(small_box)
                break
        if this_small_box_is_equivalent_to_a_box == False :
            list_of_boxes.append( [small_box] )

    list_of_big_boxes = []
    list_of_small_boxes_not_contained_in_a_big_box = []
    for box in list_of_boxes :
        if len(box) > 1 :
            list_of_big_boxes.append(box)
        else:
            list_of_small_boxes_not_contained_in_a_big_box.append( box[0] )
##    print file_name
##    print 'big boxes'
##    for big_box in list_of_big_boxes:
##        print big_box
##    print 'small boxes'
##    for small_box in list_of_small_boxes_not_contained_in_a_big_box :
##        print small_box
        
    #Computes the set of solid entailments between two small boxes based on subset_of_entailments
    set_of_solid_arrows = []
    for antecedent_small_box in list_of_small_boxes :
        for consequent_small_box in list_of_small_boxes :
            antecedent_mapping = antecedent_small_box[0]
            consequent_mapping = consequent_small_box[0]
            if (antecedent_mapping, consequent_mapping) in subset_of_entailments :     #This requires the two boxes to be different boxes, because subset_of_entailments contains no entailment between x and itself
                set_of_solid_arrows.append((antecedent_small_box, consequent_small_box))
    cleaned_set_of_solid_arrows = Remove_entailments_which_follow_by_transitivity(set_of_solid_arrows)
    
    #Computes dotted entailments between two small boxes not contained in big boxes which hold according to superset_of_entailments
    set_of_dotted_arrows_from_small_box_to_small_box = []
    for antecedent_small_box in list_of_small_boxes_not_contained_in_a_big_box :
        for consequent_small_box in list_of_small_boxes_not_contained_in_a_big_box :
            if (antecedent_small_box, consequent_small_box) not in set_of_solid_arrows :
                antecedent_mapping = antecedent_small_box[0]
                consequent_mapping = consequent_small_box[0]
                if (antecedent_mapping, consequent_mapping) in superset_of_entailments :     #This requires the two boxes to be different boxes, as above
                    set_of_dotted_arrows_from_small_box_to_small_box.append((antecedent_small_box, consequent_small_box))
##    print 'set_of_dotted_arrows_from_small_box_to_small_box'
##    for arrow in set_of_dotted_arrows_from_small_box_to_small_box:
##        print arrow
        
    #Computes dotted entailments from a big box to a small box based on superset_of_entailments
    set_of_dotted_arrows_from_big_box_to_small_box = []
    for antecedent_big_box in list_of_big_boxes :
        for consequent_small_box in list_of_small_boxes_not_contained_in_a_big_box :
            these_two_boxes_are_already_connected_by_solid_arrows = True
            for antecedent_small_box in antecedent_big_box :
                if (antecedent_small_box, consequent_small_box) not in set_of_solid_arrows :
                    these_two_boxes_are_already_connected_by_solid_arrows = False
                    break
            if these_two_boxes_are_already_connected_by_solid_arrows == False :
                antecedent_mapping = antecedent_big_box[0][0]
                consequent_mapping = consequent_small_box[0]
                if (antecedent_mapping, consequent_mapping) in superset_of_entailments :     #This requires the two boxes to be different boxes, as above
                    set_of_dotted_arrows_from_big_box_to_small_box.append((antecedent_big_box, consequent_small_box))
##    print 'set_of_dotted_arrows_from_big_box_to_small_box'
##    for arrow in set_of_dotted_arrows_from_big_box_to_small_box:
##        print arrow
        
    #Computes dotted entailments from a small box to a big box based on superset_of_entailments
    set_of_dotted_arrows_from_small_box_to_big_box = []
    for antecedent_small_box in list_of_small_boxes_not_contained_in_a_big_box :
        for consequent_big_box in list_of_big_boxes :
            these_two_boxes_are_already_connected_by_solid_arrows = True
            for consequent_small_box in consequent_big_box :
                if (antecedent_small_box, consequent_small_box) not in set_of_solid_arrows :
                    these_two_boxes_are_already_connected_by_solid_arrows = False
                    break
            if these_two_boxes_are_already_connected_by_solid_arrows == False :
                antecedent_mapping = antecedent_small_box[0]
                consequent_mapping = consequent_big_box[0][0]
                if (antecedent_mapping, consequent_mapping) in superset_of_entailments :     #This requires the two boxes to be different boxes, as above
                    set_of_dotted_arrows_from_small_box_to_big_box.append((antecedent_small_box, consequent_big_box))
##    print 'set_of_dotted_arrows_from_small_box_to_big_box'
##    for arrow in set_of_dotted_arrows_from_small_box_to_big_box:
##        print arrow
        
    #Computes dotted entailments from a big box to a big box based on superset_of_entailments
    set_of_dotted_arrows_from_big_box_to_big_box = []
    for antecedent_big_box in list_of_big_boxes :
        for consequent_big_box in list_of_big_boxes :
            these_two_boxes_are_already_connected_by_solid_arrows = True
            for (antecedent_small_box, consequent_small_box) in itertools.product(antecedent_big_box, consequent_big_box) :
                if (antecedent_small_box, consequent_small_box) not in set_of_solid_arrows :
                    these_two_boxes_are_already_connected_by_solid_arrows = False
                    break
            if these_two_boxes_are_already_connected_by_solid_arrows == False :               
                antecedent_mapping = antecedent_big_box[0][0]
                consequent_mapping = consequent_big_box[0][0]
                if (antecedent_mapping, consequent_mapping) in superset_of_entailments :     #This requires the two boxes to be different boxes, as above
                    set_of_dotted_arrows_from_big_box_to_big_box.append((antecedent_big_box, consequent_big_box))
##    print 'set_of_dotted_arrows_from_big_box_to_big_box'
##    for arrow in set_of_dotted_arrows_from_big_box_to_big_box :
##        print arrow
        
##    #Computes
##    set_of_dotted_arrows = set_of_dotted_arrows_from_small_box_to_small_box.union(set_of_dotted_arrows_from_big_box_to_small_box).union(set_of_dotted_arrows_from_small_box_to_big_box).union(set_of_dotted_arrows_from_big_box_to_big_box)
##    cleaned_set_of_dotted_arrows = Remove_entailments_which_follow_by_transitivity(set_of_dotted_arrows).difference(set_of_solid_arrows)
    
    #Starts a graph
    GRAPH = Digraph(file_name, engine='dot')
    GRAPH.graph_attr['compound'] = 'true' #this allows for arrows which start from or point to a subgraph rather than a node
##    GRAPH.graph_attr['concentrate'] = 'true'
##    GRAPH.graph_attr['splines'] = 'headport'
##    GRAPH.graph_attr['splines']='polyline'

    #For each big box, it constructs a subgraph whose nodes are the small boxes with no arrows among them
    for big_box in list_of_big_boxes :
        SUBGRAPH = Digraph('cluster' + Convert_big_box_into_string(big_box) )
        if big_box[0][0] in set_of_special_nodes :
            SUBGRAPH.attr('node', shape='box', fontcolor='red')
        else :
            SUBGRAPH.attr('node', shape='box', fontcolor='black')
        for small_box in big_box :
            SUBGRAPH.node(Convert_small_box_into_string(small_box))
        SUBGRAPH.body.append('style=dashed')
        GRAPH.subgraph(SUBGRAPH)
        
    #For each small box not contained in a big box, it constructs a corresponding node
    for small_box in list_of_small_boxes_not_contained_in_a_big_box :
        if small_box[0] in set_of_special_nodes :
            GRAPH.attr('node', shape='box', fontcolor='red', rank='source')
        else :
            GRAPH.attr('node', shape='box', fontcolor='black')
        GRAPH.node(Convert_small_box_into_string(small_box))
        
    #Writes the solid arrows
    GRAPH.attr('edge', dir='none') 
    for (antecedent_small_box, consequent_small_box) in cleaned_set_of_solid_arrows :
        GRAPH.edge(Convert_small_box_into_string(antecedent_small_box), Convert_small_box_into_string(consequent_small_box))
        
    #Writes the dotted arrows between two small boxes
    GRAPH.attr('edge', style='dashed', dir='none')
#    print '(antecedent_small_box, consequent_small_box)'
    for (antecedent_small_box, consequent_small_box) in set_of_dotted_arrows_from_small_box_to_small_box :
#        print (antecedent_small_box, consequent_small_box)
        GRAPH.edge(Convert_small_box_into_string(antecedent_small_box), Convert_small_box_into_string(consequent_small_box))
#    print '(antecedent_big_box, consequent_small_box)'
    for (antecedent_big_box, consequent_small_box) in set_of_dotted_arrows_from_big_box_to_small_box :
#        print (antecedent_big_box, consequent_small_box) 
        GRAPH.edge(Convert_small_box_into_string(antecedent_big_box[0]), Convert_small_box_into_string(consequent_small_box), ltail='cluster' + Convert_big_box_into_string(antecedent_big_box))
#    print '(antecedent_small_box, consequent_big_box)'
    for (antecedent_small_box, consequent_big_box) in set_of_dotted_arrows_from_small_box_to_big_box :
#        print (antecedent_small_box, consequent_big_box)
        GRAPH.edge(Convert_small_box_into_string(antecedent_small_box), Convert_small_box_into_string(consequent_big_box[0]), lhead='cluster' + Convert_big_box_into_string(consequent_big_box))
#    print '(antecedent_big_box, consequent_big_box)'
    for (antecedent_big_box, consequent_big_box) in set_of_dotted_arrows_from_big_box_to_big_box :
#        print (antecedent_big_box, consequent_big_box)
        GRAPH.edge(Convert_small_box_into_string(antecedent_big_box[0]), Convert_small_box_into_string(consequent_big_box[0]), ltail='cluster' + Convert_big_box_into_string(antecedent_big_box), lhead='cluster' + Convert_big_box_into_string(consequent_big_box))

    #Closes the graph
    comment = 'label = "LEGEND: ' + legend + '"'
    GRAPH.body.append(comment)    
    GRAPH.view()



##=================================================================================================
##Plots the graph representing the OT T-order, namely the collection
##of entailments which hold in OT whose antecedent mappings are OT
##feasible
##=================================================================================================

superset_of_entailments = Split(set_OT_Torders_with_OT_feasible_antecedent)
subset_of_entailments = Split(set_OT_Torders_with_OT_feasible_antecedent)
set_of_special_mappings = set()
file_name = '[4]-Plot_of_OT_Torder'
legend = 'Only OT feasible mappings are considered;\nsolid boxes are OT cycles;\nlines represent arrows from top to bottom;\nsolid arrows are OT entailments;\narrows entailed by transitivity are omitted.'
Produce_graph(superset_of_entailments, subset_of_entailments, set_of_special_mappings, file_name, legend)



##=================================================================================================
##Plots the HG T-order, namely the collection of entailments which
##hold in HG whose antecedent mappings are HG feasible (possibly, OT
##unfeasible)
##=================================================================================================

set_HG_entailments_with_HG_feasible_antecedent = set()
for entailment in set_OT_Torders_with_OT_feasible_antecedent.union(set_OT_Torders_with_OT_UNfeasible_but_HG_feasible_antecedent) :
    if entailment not in cases[14]:
        set_HG_entailments_with_HG_feasible_antecedent.add(entailment)

superset_of_entailments = Split(set_HG_entailments_with_HG_feasible_antecedent)
subset_of_entailments = Split(set_HG_entailments_with_HG_feasible_antecedent)
set_of_special_mappings = set()
file_name = '[5]-Plot_of_HG_Torder'
legend = 'Only HG feasible mappings are considered;\nsolid boxes are HG cycles;\nlines represent arrows from top to bottom;\nsolid arrows are HG entailments\narrows entailed by transitivity are omitted.'
Produce_graph(superset_of_entailments, subset_of_entailments, set_of_special_mappings, file_name, legend)



##=================================================================================================
##Plots the ME T-order, namely the collection of entailments which
##hold in ME (independently of the OT or HG feasibility of their
##antecedent mappings)
##=================================================================================================

set_ME_entailments = set()
##set_undecided_ME_Torders = set()
for entailment in set_OT_Torders_with_OT_feasible_antecedent.union(set_OT_Torders_with_OT_UNfeasible_but_HG_feasible_antecedent).union(set_OT_Torders_with_HG_UNfeasible_antecedent) :
    if entailment in cases[0].union(cases[1]).union(cases[5]).union(cases[6]).union(cases[10]) :
        set_ME_entailments.add(entailment)
##    if entailment in cases[4].union(cases[9]).union(cases[13]) :
##        set_undecided_ME_Torders.add(entailment)

superset_of_entailments = Split(set_ME_entailments)
subset_of_entailments = Split(set_ME_entailments)
set_of_special_mappings = set_of_HG_unfeasible_mappings
file_name = '[6]-Plot_of_ME_Torder'
legend = 'All mappings are considered (both HG feasible and unfeasible);\nred mappings are HG unfeasible;\nsolid boxes are ME cycles;\nlines represent arrows from top to bottom;\nsolid arrows are ME entailments;\nlines entailed by transitivity are omitted.'
Produce_graph(superset_of_entailments, subset_of_entailments, set_of_special_mappings, file_name, legend)



##=================================================================================================
##Plots the comparison between OT and HG T-orders. It has a solid
##arrow for each entailment which holds in HG and a dotted arrow for
##each entailment which holds in OT but not in HG. Only mappings which
##are HG feasible are considered. Those mappings which are HG feasible
##but OT unfeasible are singled out in blue.
##=================================================================================================

superset_of_entailments = Split(set_OT_Torders_with_OT_feasible_antecedent.union(set_OT_Torders_with_OT_UNfeasible_but_HG_feasible_antecedent))
subset_of_entailments = Split(set_HG_entailments_with_HG_feasible_antecedent)
set_of_special_mappings = set_of_HG_feasible_but_OT_unfeasible_mappings
file_name = '[7]-Plot_of_OT_versus_HG_Torders'
legend = 'Only HG feasible mappings are considered;\nred mappings are HG feasible but OT unfeasible;\nsolid boxes are HG (and therefore also OT) cycles;\ndotted boxes are OT cycles which fail in HG;\nlines represent arrows from top to bottom;\nsolid lines are HG (and therefore also OT) entailments;\nsolid lines entailed by transitivity are omitted;\ndotted arrows are HG entailments which fail in OT.'
Produce_graph(superset_of_entailments, subset_of_entailments, set_of_special_mappings, file_name, legend)



##=================================================================================================
##Plots the comparison between HG and ME T-orders. It has a solid
##arrow for each entailment which holds in ME and a dotted arrow for
##each entailment which holds in HG but not in ME. Only mappings which
##are HG feasible are considered.
##=================================================================================================

set_ME_entailments_with_HG_feasible_antecedent = set()
for entailment in set_OT_Torders_with_OT_feasible_antecedent.union(set_OT_Torders_with_OT_UNfeasible_but_HG_feasible_antecedent) :
    if entailment in cases[0].union(cases[1]).union(cases[5]).union(cases[6]).union(cases[10]) :
        set_ME_entailments_with_HG_feasible_antecedent.add(entailment)

superset_of_entailments = Split(set_HG_entailments_with_HG_feasible_antecedent)
subset_of_entailments = Split(set_ME_entailments_with_HG_feasible_antecedent)
set_of_special_mappings = set()
file_name = '[8]-Plot_of_HG_versus_ME_Torders_only_HG_feasible_mappings'
legend = 'Only HG feasible mappings are considered;\nsolid boxes are ME (and therefore also HG) cycles;\ndotted boxes are HG cycles which fail in ME;\nlines represent arrows from top to bottom;\nsolid lines are ME (and therefore also HG) entailments;\nsolid lines entailed by transitivity are omitted;\ndotted lines are HG entailments which fail in ME.'
Produce_graph(superset_of_entailments, subset_of_entailments, set_of_special_mappings, file_name, legend)



##=================================================================================================
##Plots the comparison between HG and ME T-orders. It has a solid
##arrow for each entailment which holds in ME and a dotted arrow for
##each entailment which holds in HG but not in ME. All mappings are
##considered, both the HG feasible and unfeasible ones. HG unfeasible
##mappings are singled out in blue.
##=================================================================================================

set_HG_entailments_with_HG_feasible_or_unfeasible_antecedent = set()
for entailment in set_OT_Torders_with_OT_feasible_antecedent.union(set_OT_Torders_with_OT_UNfeasible_but_HG_feasible_antecedent).union(set_OT_Torders_with_HG_UNfeasible_antecedent) :
    if entailment not in cases[14]:
        set_HG_entailments_with_HG_feasible_or_unfeasible_antecedent.add(entailment)

superset_of_entailments = Split(set_HG_entailments_with_HG_feasible_or_unfeasible_antecedent)
subset_of_entailments = Split(set_ME_entailments)
set_of_special_mappings = set_of_HG_unfeasible_mappings
file_name = '[9]-Plot_of_HG_versus_ME_Torders_including_HG_unfeasible_mappings'
legend = 'All mappings are considered, both HG feasible and unfeasible;\nred mappings are HG unfeasible;\nsolid boxes are ME (and therefore also HG) cycles;\ndotted boxes are HG cycles which fail in ME;\nlines represent arrows from top to bottom;\nsolid lines are ME (and therefore also HG) entailments;\nsolid lines entailed by transitiviy are omitted;\ndotted lines are HG entailments which fail in ME.'
Produce_graph(superset_of_entailments, subset_of_entailments, set_of_special_mappings, file_name, legend)


##=================================================================================================
##=================================================================================================


