# pysv (Python Synthesis and Verification)

I created this framework to 1) gain the first-hand experience with formal approaches to verification and synthesis of computer programs, 2) have a testbed for various ideas regarding this topic. The focus of pysv is to provide such utilities for simple programs written in Python. Please keep in mind that this is work in progress and major changes are very likely to happen.

For the pysv to work, SMT solver of choice (by default Z3: [https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3)) needs to be accessible. It suffices to move solver's binary to *solvers_bin* folder.


## Examples of usage
### Command line
Simple programs may be verified from the command line. Here is an example of conducting verification:

`./main.py --verify --pre "x>=0" --post "res>0" --program "res=y+x+5" --local_vars res:Int --input_vars y:Int x:Int`

pysv finds out that program returns incorrect result for x=0, y=-5.

----

To find an example of a correct result being returned by program, you can use *--example* flag:

`./main.py --example --pre "x>=0" --post "res>0" --program "res=y+x+5" --local_vars res:Int --input_vars y:Int x:Int`

pysv finds out that program returns correct result for x=0, y=-4.

----

To find content of the holes so that program meets the specification, you may use *--synthesize* flag:

`./main.py --synthesize --pre "x>=0 and y>=-10" --post "res>0" --program "res=y+x+HOLE1" --local_vars res:Int HOLE1:Int --input_vars y:Int x:Int --free_vars HOLE1
`

pysv should find the value HOLE1 >= 11.

----

As you may observe, variables need to be explicitly specified together with their types. In the future they may be automatically inferred from the source code of the program.


### Scripts
pysv was originally created as a python library. Example scripts may be found in the *examples* folder. Here is the content of *synth_max.py*:
```python
	code = """
if H1:
	res = H2
else:
	res = H3
	"""
	code_pre = 'True'
	code_post = 'res >= x and res >= y and (res == x or res == y)'

	# Specification of the hole's template in the form of the grammar in SYGUS format.
	sygus_grammar_hole1 = """
	(
		( Start Bool
			( (Constant Bool) (> TermInt TermInt) (>= TermInt TermInt) (= TermInt TermInt) (<= TermInt TermInt) (< TermInt TermInt)
			)
		)
		( TermInt Int
			( (Constant Int) x y )
		)
	)
	"""
	sygus_grammar_hole23 = """
	(
		( Start Int
			( (Constant Int) x y (+ x y) (- x y) (- y x) (+ x ( Constant Int )) (+ y ( Constant Int )) )
		)
	)
	"""
	grammar1 = templates.load_gramar_from_SYGUS_spec(sygus_grammar_hole1)
	grammar23 = templates.load_gramar_from_SYGUS_spec(sygus_grammar_hole23)
	pv = contract.ProgramVars({'x': 'Int', 'y': 'Int'}, {'res': 'Int'})
	h1 = smt_synthesis.HoleDecl('H1', grammar1, pv, True, 2)
	h2 = smt_synthesis.HoleDecl('H2', grammar23, pv, True, 2)
	h3 = smt_synthesis.HoleDecl('H3', grammar23, pv, True, 2)
	hole_decls = [h1, h2, h3]


	# The result is currently only a raw output from the solver, but one can verify from the model
	# that synthesized program is correct.
	env = utils.Options(['--solver', 'z3', '--logic', 'NIA'])
	res = smt_synthesis.synthesize(code, code_pre, code_post, vars, env, hole_decls)
```
