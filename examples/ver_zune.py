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
from pysv import contract

"""
ORIGINAL ZUNE BUG CODE:
ORIGINYEAR = 1980   (1980 was a leap year)
input: days (number of days since ORIGINYEAR)
-----------------------------------

year = ORIGINYEAR;
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
zune_simplified = """
#year = 1980
#if days > 365: # handled by precondition
days2 = days
year2 = year
if year % 4 == 0:
	if days > 366:
		days2 = days - 366
		year2 = year + 1
	# lack of else statement
else:
	days2 = days - 365
	year2 = year + 1
"""
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
