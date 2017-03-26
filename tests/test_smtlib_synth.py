import unittest
from pysv.smtlib.synth import *
from pysv import contract
from pysv import utils


class TestsSynthesisTestCases(unittest.TestCase):

    def test_old_name(self):
        synth = SynthesisConstrTestCases(contract.TestCases(), utils.Options())
        self.assertEquals("x", synth.old_name("x_T1"))
        self.assertEquals("xxy", synth.old_name("xxy_T12"))
        self.assertEquals("|x'|", synth.old_name("|x_T4'|"))
        self.assertEquals("|xyz'''|", synth.old_name("|xyz_T44'''|"))


    def test_new_name(self):
        synth = SynthesisConstrTestCases(contract.TestCases(), utils.Options())
        self.assertEquals("x_T1", synth.new_name("x", 1))
        self.assertEquals("xxy_T12", synth.new_name("xxy", 12))
        self.assertEquals("|x_T4'|", synth.new_name("|x'|", 4))
        self.assertEquals("|xyz_T44'''|", synth.new_name("|xyz'''|", 44))