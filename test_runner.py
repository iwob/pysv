#!/usr/bin/env python
import unittest


suite = unittest.TestLoader().discover('tests')

if __name__ == "__main__":
    unittest.TextTestRunner(verbosity=2).run(suite)