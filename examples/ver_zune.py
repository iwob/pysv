#!/usr/bin/env python
import os
import sys
sys.path.insert(1, os.path.abspath('..'))


#---------------------------------------------------------------------------------------------------
#                                 VERIFICATION EXAMPLE: ZUNE BUG
#---------------------------------------------------------------------------------------------------
# This example presents the use of SMT solvers to verify correctness of the well known Zune bug.
#
#
# NOTE: This example is currently work in progress and is not currently working.
#---------------------------------------------------------------------------------------------------

from pysv import smt_verifier
from pysv import utils
from pysv import contract


"""
ORIGINAL ZUNE BUG CODE:
ORIGIN_YEAR = 1980   (1980 was a leap year)
input: days (number of days since ORIGIN_YEAR)
-----------------------------------

year = ORIGIN_YEAR;
while (days > 365)
{
    if (IsLeapYear(year))
    {
        if (days > 366)
        {
            days -= 366;
            year += 1;
        }
        # lack of else statement - not ending loop for 366'th day in a leap year
    }
    else
    {
        days -= 365;
        year += 1;
    }
}
"""




# Only one leap
zune_while = """
# input_days <- input
year = 1980
days = input_days
while days > 365:
    if year % 4 == 0:
        if days > 366:
            days -= 366
            year += 1
        # lack of else statement - not ending loop for 366'th day in a leap year
    else:
        days -= 365
        year += 1
"""
pre = "input_days > 0 and input_days <= 732"
# t1 = (["input_days == 366"], ["year == 1980", "days == 360"]) #366
# t2 = (["input_days == 367"], ["year == 1981", "days == 1"])
# post = contract.formula_test_cases_py([t1, t2])
post = "days < 366"

program_vars = contract.ProgramVars({"input_days":"Int"}, {"year":"Int", "days":"Int"})

env = utils.Options("--loop_unrolling_level 2")

res = smt_verifier.verify(zune_while, pre, post, program_vars, env)
# Printing result
print('\n')
print('----------------------------------------------')
print('                SOLVER RESULT                 ')
print('----------------------------------------------')
if res.decision == 'unsat':
    print('Counterexample not found! Program is correct.')
elif res.decision == 'sat':
    print(res.witness) #model
    print('Counterexample found! Program is incorrect.')
print('----------------------------------------------\n\n')











input_vars = contract.ProgramVars({"days" : 'Int', "year" : 'Int'})
pre = "days > 365 and year >= 1980"
# For this postcondition program doesn't meet the specification because the postcondition
# is based on user intent and cod has a bug.
# post = "((not days == 366 or not year == 1980) or (year2 == 1980 and days2 == 0)) and " +\
#        "((not days == 366 or not year == 1981) or (year2 == 1982 and days2 == 1))"

# For this postcondition program meets the specification because the postcondition
# is based on the code.
#post = "((not days == 366 or not year == 1980) or (year2 == 1980 and days2 == 366)) and " +\
#      "((not days == 366 or not year == 1981) or (year2 == 1982 and days2 == 1))"
t1 = (["days == 366", "year == 1980"], ["year2 == 1980", "days2 == 366"])
t2 = (["days == 366", "year == 1981"], ["year2 == 1982", "days2 == 1"])
post = contract.formula_test_cases_py([t1, t2])


days = 9
year = 1980
if year % 4 == 0:
    if days > 366:
        days -= 366
        year += 1
    else:
        days -= 365
        year += 1
