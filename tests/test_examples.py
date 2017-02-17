import unittest

class TestsContract(unittest.TestCase):

	def test_duplicates(self):
		import examples.duplicates

	def test_synth_max(self):
		import examples.synth_max
		examples.synth_max.synthesize_max()

	def test_ver1_acc(self):
		import examples.ver_acc

	def test_ver1_max(self):
		import examples.ver_max

	def test_unsat_core(self):
		import examples.unsat_core

	def test_synth_ann_xor(self):
		import examples.synth_ann_xor